import Langlands.GroupScheme.Reductive.LocalSplitWeylConjugationStatement
import Langlands.GroupScheme.Reductive.LocalSplitRankOneConsequences
import Langlands.GroupScheme.Reductive.LocalSplitTypeG2
import Langlands.GroupScheme.Reductive.LocalSplitTypeB2
import Langlands.LinearAlgebra.RootDatumRankTwoBase

/-! # Commutator relations of Weyl families from Weyl conjugation and rank two -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Words

variable {R : Type u} [CommRing R] {I : Type u} {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The product `n_{j₁} ⋯ n_{jₖ}` of the Weyl points of the letters of a word, over a test
scheme. -/
def wordPoint (u : J → (Ga R ⟶ G)) (l : List J) (Z : Over (Spec (CommRingCat.of R))) :
    Z ⟶ G.X :=
  (l.map fun j => G.constantPoint (rootWeylPoint P u j) Z).prod

theorem rootPoint_wordConj (u : J → (Ga R ⟶ G)) (l : List J) (w : Ga R ⟶ G)
    (Z : Over (Spec (CommRingCat.of R))) (x : Γ(Z.left, ⊤)) :
    rootPoint (wordConj P u l w) Z x =
      wordPoint (P := P) u l Z * rootPoint w Z x * (wordPoint (P := P) u l Z)⁻¹ := by
  induction l with
  | nil => simp [wordConj, wordPoint]
  | cons j l ih =>
    change rootPoint (wordConj P u l w ≫ (G.innerIso (rootWeylPoint P u j)).hom) Z x = _
    rw [rootPoint_comp, GroupScheme.comp_innerIso_hom, ih]
    simp only [wordPoint, List.map_cons, List.prod_cons, mul_inv_rev]
    group

theorem wordConj_scaleHom (u : J → (Ga R ⟶ G)) (l : List J) (κ : R) (w : Ga R ⟶ G) :
    wordConj P u l (scaleHom κ ≫ w) = scaleHom κ ≫ wordConj P u l w := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change wordConj P u l (scaleHom κ ≫ w) ≫ _ = scaleHom κ ≫ (wordConj P u l w ≫ _)
    rw [ih, Category.assoc]

variable {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **Weyl conjugation along a word.** Common conjugation units for the simple Weyl points give
common units for conjugation along any word in the simple reflections. -/
theorem WeylConjugationRelations.wordConj_weylFamily (h : WeylConjugationRelations P b W u u')
    {l : List J} (hl : ∀ c ∈ l, c ∈ b.support) (d : J) :
    ∃ κ : Rˣ, wordConj P u l (weylFamily P W u d) =
        scaleHom (κ : R) ≫ weylFamily P W u (Langlands.LinearAlgebra.wordPerm P l d) ∧
      wordConj P u' l (weylFamily P W u' d) =
        scaleHom (κ : R) ≫ weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P l d) := by
  induction l with
  | nil =>
    refine ⟨1, ?_, ?_⟩ <;>
    · rw [Units.val_one, scaleHom_one, Category.id_comp]
      rfl
  | cons c l ih =>
    obtain ⟨κ, h1, h2⟩ := ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc'))
    obtain ⟨κ₁, e1, e2⟩ := h c (hl c List.mem_cons_self) (Langlands.LinearAlgebra.wordPerm P l d)
    refine ⟨κ₁ * κ, ?_, ?_⟩
    · change wordConj P u l (weylFamily P W u d) ≫ (G.innerIso (rootWeylPoint P u c)).hom = _
      rw [h1, Category.assoc, e1, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_mul]
      rfl
    · change wordConj P u' l (weylFamily P W u' d) ≫ (H.innerIso (rootWeylPoint P u' c)).hom = _
      rw [h2, Category.assoc, e2, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_mul]
      rfl

end Words

section Formulas

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}

theorem baseScalar_overMk {B : Type u} [CommRing B]
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (d : R) :
    baseScalar (Over.mk s) d = (Scheme.ΓSpecIso (CommRingCat.of B)).inv ((Spec.preimage s).hom d) := by
  conv_lhs => rw [← Spec.map_preimage s]
  change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map (Spec.preimage s)).appTop).hom d = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- A term of a commutator formula: a map `𝔾ₐ → G`, a constant `c` and two exponents `i`, `j`,
standing for the point `w(c x^i y^j)`. -/
abbrev CommTerm (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R))) :=
  (Ga R ⟶ G) × R × ℕ × ℕ

/-- The point `w(c x^i y^j)` of a term over a test scheme. -/
def termPoint (Z : Over (Spec (CommRingCat.of R))) (x y : Γ(Z.left, ⊤)) (t : CommTerm R G) :
    Z ⟶ G.X :=
  rootPoint t.1 Z (baseScalar Z t.2.1 * x ^ t.2.2.1 * y ^ t.2.2.2)

/-- **A commutator formula**: over every affine test scheme over `R`,
`(w₁(x) w₂(y))⁻¹ (w₂(y) w₁(x))` is the product of the points of the terms of `L`, in order. -/
def CommRel (w₁ w₂ : Ga R ⟶ G) (L : List (CommTerm R G)) : Prop :=
  ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)),
    (rootPoint w₁ (Over.mk s) x * rootPoint w₂ (Over.mk s) y)⁻¹ *
        (rootPoint w₂ (Over.mk s) y * rootPoint w₁ (Over.mk s) x) =
      (L.map (termPoint (Over.mk s) x y)).prod

/-- Replacing terms by terms with the same points. -/
theorem CommRel.map_terms {w₁ w₂ : Ga R ⟶ G} {L : List (CommTerm R G)} (h : CommRel w₁ w₂ L)
    (f : CommTerm R G → CommTerm R G)
    (hf : ∀ t ∈ L, ∀ (B : Type u) [CommRing B]
      (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (x y : Γ((Over.mk s).left, ⊤)),
      termPoint (Over.mk s) x y (f t) = termPoint (Over.mk s) x y t) :
    CommRel w₁ w₂ (L.map f) := by
  intro B _ s x y
  rw [h B s x y, List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => (hf t ht B s x y).symm

/-- Rescaling the two arguments. -/
theorem CommRel.rescale {w₁ w₂ w₁' w₂' : Ga R ⟶ G} {L : List (CommTerm R G)}
    (h : CommRel w₁ w₂ L) (κ₁ κ₂ : Rˣ) (h₁ : w₁ = scaleHom (κ₁ : R) ≫ w₁')
    (h₂ : w₂ = scaleHom (κ₂ : R) ≫ w₂') :
    CommRel w₁' w₂' (L.map fun t => (t.1, t.2.1 * ((κ₁⁻¹ : Rˣ) : R) ^ t.2.2.1 *
      ((κ₂⁻¹ : Rˣ) : R) ^ t.2.2.2, t.2.2.1, t.2.2.2)) := by
  intro B _ s x y
  have e₁ : ∀ z, rootPoint w₁' (Over.mk s) z =
      rootPoint w₁ (Over.mk s) (baseScalar (Over.mk s) ((κ₁⁻¹ : Rˣ) : R) * z) := by
    intro z
    rw [h₁, rootPoint_scaleHom, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  have e₂ : ∀ z, rootPoint w₂' (Over.mk s) z =
      rootPoint w₂ (Over.mk s) (baseScalar (Over.mk s) ((κ₂⁻¹ : Rˣ) : R) * z) := by
    intro z
    rw [h₂, rootPoint_scaleHom, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
  rw [e₁, e₂, h B s, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, termPoint, map_mul, map_pow]
  congr 1
  ring

/-- Reversing the two arguments. -/
theorem CommRel.symm {w₁ w₂ : Ga R ⟶ G} {L : List (CommTerm R G)} (h : CommRel w₁ w₂ L) :
    CommRel w₂ w₁ (L.reverse.map fun t => (t.1, -t.2.1, t.2.2.2, t.2.2.1)) := by
  intro B _ s x y
  have h' := h B s y x
  have hinv : (rootPoint w₂ (Over.mk s) x * rootPoint w₁ (Over.mk s) y)⁻¹ *
      (rootPoint w₁ (Over.mk s) y * rootPoint w₂ (Over.mk s) x) =
      ((rootPoint w₁ (Over.mk s) y * rootPoint w₂ (Over.mk s) x)⁻¹ *
        (rootPoint w₂ (Over.mk s) x * rootPoint w₁ (Over.mk s) y))⁻¹ := by
    group
  rw [hinv, h', List.prod_inv_reverse]
  simp only [List.map_reverse, List.map_map]
  have hm : ∀ t ∈ L, ((fun z => z⁻¹) ∘ termPoint (Over.mk s) y x) t =
      (termPoint (Over.mk s) x y ∘ fun t => (t.1, -t.2.1, t.2.2.2, t.2.2.1)) t := by
    intro t _
    simp only [Function.comp, termPoint, map_neg]
    rw [← rootPoint_neg]
    congr 1
    ring
  rw [List.map_congr_left hm]

/-- Conjugating a commutator formula along a word. -/
theorem CommRel.conj_word {J : Type u} {I : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
    {w₁ w₂ : Ga R ⟶ G} {L : List (CommTerm R G)} (h : CommRel w₁ w₂ L)
    (u : J → (Ga R ⟶ G)) (l : List J) :
    CommRel (LocalSplitCell.wordConj P u l w₁) (LocalSplitCell.wordConj P u l w₂)
      (L.map fun t => (LocalSplitCell.wordConj P u l t.1, t.2)) := by
  intro B _ s x y
  simp only [rootPoint_wordConj]
  set g := wordPoint (P := P) u l (Over.mk s)
  have hconj : ∀ a b : Over.mk s ⟶ G.X, (g * a * g⁻¹ * (g * b * g⁻¹))⁻¹ *
      (g * b * g⁻¹ * (g * a * g⁻¹)) = g * ((a * b)⁻¹ * (b * a)) * g⁻¹ := by
    intro a b
    group
  rw [hconj, h B s x y, List.map_map]
  have hm : ∀ t ∈ L, (termPoint (Over.mk s) x y ∘
      fun t => (LocalSplitCell.wordConj P u l t.1, t.2)) t =
      (MulAut.conj g) (termPoint (Over.mk s) x y t) := by
    intro t _
    simp only [Function.comp, termPoint, MulAut.conj_apply]
    rw [rootPoint_wordConj]
  rw [List.map_congr_left hm,
    show (fun a => (MulAut.conj g) (termPoint (Over.mk s) x y a)) =
      (MulAut.conj g) ∘ termPoint (Over.mk s) x y from rfl,
    ← List.map_map, ← map_list_prod, MulAut.conj_apply]

/-- Two maps `𝔾ₐ → G` whose points commute over every affine test scheme. -/
def PointsCommute (w w' : Ga R ⟶ G) : Prop :=
  ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (z z' : Γ((Over.mk s).left, ⊤)),
    rootPoint w (Over.mk s) z * rootPoint w' (Over.mk s) z' =
      rootPoint w' (Over.mk s) z' * rootPoint w (Over.mk s) z

theorem PointsCommute.symm {w w' : Ga R ⟶ G} (h : PointsCommute w w') : PointsCommute w' w :=
  fun B _ s z z' => (h B s z' z).symm

theorem PointsCommute.of_scaleHom {w w' v v' : Ga R ⟶ G} (h : PointsCommute v v') (κ κ' : R)
    (hw : w = scaleHom κ ≫ v) (hw' : w' = scaleHom κ' ≫ v') : PointsCommute w w' := by
  intro B _ s z z'
  rw [hw, hw', rootPoint_scaleHom, rootPoint_scaleHom]
  exact h B s _ _

theorem commRel_nil {w₁ w₂ : Ga R ⟶ G} (h : PointsCommute w₁ w₂) : CommRel w₁ w₂ [] := by
  intro B _ s x y
  rw [h B s x y, inv_mul_cancel]
  rfl

/-- Swapping two adjacent terms whose maps have commuting points. -/
theorem CommRel.swap {w₁ w₂ : Ga R ⟶ G} {L₁ L₂ : List (CommTerm R G)} {t t' : CommTerm R G}
    (h : CommRel w₁ w₂ (L₁ ++ t :: t' :: L₂)) (hc : PointsCommute t.1 t'.1) :
    CommRel w₁ w₂ (L₁ ++ t' :: t :: L₂) := by
  intro B _ s x y
  rw [h B s x y]
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  congr 1
  simp only [termPoint]
  rw [← mul_assoc, hc B s, mul_assoc]

omit [CommRing R] in
theorem reorder_four {M : Type*} [Group M] (A₁ A₂ A₃ A₄ D : M) (k : A₂ * A₁ = A₁ * A₂ * D)
    (c31 : A₃ * A₁ = A₁ * A₃) (c32 : A₃ * A₂ = A₂ * A₃) (c41 : A₄ * A₁ = A₁ * A₄)
    (c42 : A₄ * A₂ = A₂ * A₄) (c34 : A₃ * A₄ = A₄ * A₃) (c4D : A₄ * D = D * A₄) :
    A₄ * (A₃ * (A₂ * A₁)) = A₁ * (A₂ * (A₃ * (D * A₄))) := by
  calc A₄ * (A₃ * (A₂ * A₁)) = A₄ * A₃ * (A₂ * A₁) := by group
    _ = A₄ * A₃ * (A₁ * A₂ * D) := by rw [k]
    _ = A₄ * (A₃ * A₁) * A₂ * D := by group
    _ = A₄ * (A₁ * A₃) * A₂ * D := by rw [c31]
    _ = (A₄ * A₁) * (A₃ * A₂) * D := by group
    _ = (A₁ * A₄) * (A₂ * A₃) * D := by rw [c41, c32]
    _ = A₁ * (A₄ * A₂) * A₃ * D := by group
    _ = A₁ * (A₂ * A₄) * A₃ * D := by rw [c42]
    _ = A₁ * A₂ * (A₄ * A₃) * D := by group
    _ = A₁ * A₂ * (A₃ * A₄) * D := by rw [← c34]
    _ = A₁ * A₂ * A₃ * (A₄ * D) := by group
    _ = A₁ * A₂ * A₃ * (D * A₄) := by rw [c4D]
    _ = A₁ * (A₂ * (A₃ * (D * A₄))) := by group

/-- **The reversed `G₂` formula.** From the commutator of `v_a` and `v_c` and that of `p₁`
and `p₂`, with the remaining factors commuting, the commutator of `v_c` and `v_a`. -/
theorem CommRel.g2_reverse {wa wc p₁ p₂ p₃ p₄ : Ga R ⟶ G}
    (h : CommRel wa wc [(p₁, 1, 1, 1), (p₂, 1, 2, 1), (p₃, -1, 3, 1), (p₄, -1, 3, 2)])
    (h12 : CommRel p₁ p₂ [(p₄, -3, 1, 1)]) (c13 : PointsCommute p₁ p₃)
    (c14 : PointsCommute p₁ p₄) (c23 : PointsCommute p₂ p₃) (c24 : PointsCommute p₂ p₄)
    (c34 : PointsCommute p₃ p₄) :
    CommRel wc wa [(p₁, -1, 1, 1), (p₂, -1, 1, 2), (p₃, 1, 1, 3), (p₄, -2, 2, 3)] := by
  intro B _ s x y
  rw [h.symm B s x y]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have k := h12 B s (baseScalar (Over.mk s) (-1) * x ^ 1 * y ^ 1)
    (baseScalar (Over.mk s) (-1) * x ^ 1 * y ^ 2)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at k
  rw [inv_mul_eq_iff_eq_mul] at k
  have e₃ : termPoint (Over.mk s) x y (p₃, -(-1), 1, 3) = termPoint (Over.mk s) x y (p₃, 1, 1, 3) := by
    simp only [neg_neg]
  have e₄ : termPoint (Over.mk s) x y (p₄, -2, 2, 3) =
      termPoint (Over.mk s) (baseScalar (Over.mk s) (-1) * x ^ 1 * y ^ 1)
        (baseScalar (Over.mk s) (-1) * x ^ 1 * y ^ 2) (p₄, -3, 1, 1) *
      termPoint (Over.mk s) x y (p₄, -(-1), 2, 3) := by
    simp only [termPoint]
    rw [← rootPoint_add]
    congr 1
    simp only [map_neg, map_one, map_ofNat]
    ring
  rw [e₄, ← e₃]
  exact reorder_four _ _ _ _ _ k (c13.symm B s _ _) (c23.symm B s _ _) (c14.symm B s _ _)
    (c24.symm B s _ _) (c34 B s _ _) (by simp only [termPoint]; rw [← rootPoint_add,
      ← rootPoint_add, add_comm])

/-- **The reversed `B₂` formula.** -/
theorem CommRel.b2_reverse {wa wc p₁ p₂ : Ga R ⟶ G}
    (h : CommRel wa wc [(p₁, 1, 1, 1), (p₂, 1, 2, 1)]) (c12 : PointsCommute p₁ p₂) :
    CommRel wc wa [(p₁, -1, 1, 1), (p₂, -1, 1, 2)] := by
  have h' := h.symm
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.map_cons, List.map_nil] at h'
  exact CommRel.swap (L₁ := []) (L₂ := []) h' c12.symm

end Formulas

section OrderedProducts

variable {M : Type*} [Monoid M]

/-- An ordered product over `Fin n` whose factors are trivial away from a strictly increasing
list of positions is the product of the factors at those positions. -/
theorem prod_ofFn_eq_prod_map {n : ℕ} (f : Fin n → M) (L : List (Fin n))
    (hL : L.Pairwise (· < ·)) (h1 : ∀ q, q ∉ L → f q = 1) :
    (List.ofFn f).prod = (L.map f).prod := by
  induction L using List.reverseRecOn generalizing f with
  | nil =>
    have : f = fun _ => 1 := funext fun q => h1 q (by simp)
    rw [this, prod_ofFn_one]
    rfl
  | append_singleton L q ih =>
    rw [List.pairwise_append] at hL
    obtain ⟨hL', -, hlt⟩ := hL
    have hlt' : ∀ x ∈ L, x < q := fun x hx => hlt x hx q (by simp)
    rw [prod_ofFn_split f q]
    have h3 : (List.ofFn fun l => if q < l then f l else 1) = List.ofFn fun _ : Fin n => (1 : M) := by
      congr 1
      funext l
      split_ifs with hl
      · refine h1 l fun hmem => ?_
        rcases List.mem_append.mp hmem with h | h
        · exact absurd (hlt' l h) (not_lt.mpr hl.le)
        · exact absurd (List.mem_singleton.mp h) (ne_of_gt hl)
      · rfl
    rw [h3, prod_ofFn_one, mul_one]
    rw [ih (fun l => if l < q then f l else 1) hL' (fun x hx => by
      split_ifs with hxq
      · exact h1 x fun hmem => by
          rcases List.mem_append.mp hmem with h | h
          · exact hx h
          · exact absurd (List.mem_singleton.mp h) (ne_of_lt hxq)
      · rfl)]
    rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]
    congr 1
    congr 1
    exact List.map_congr_left fun x hx => by simp [hlt' x hx]

end OrderedProducts

section Univ

variable {R : Type u} [CommRing R] {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))}

open Polynomial in
/-- **Universal coordinates from a commutator formula.** If the commutator of the factors at
positions `k`, `l` is given by terms at a strictly increasing list of positions, then the
universal commutator coordinates are the corresponding monomials. -/
theorem isUnivComm_of_commRel (v : J → (Ga R ⟶ G)) {n : ℕ} (pos : Fin n → J) (k l : Fin n)
    (L : List (Fin n × R × ℕ × ℕ)) (hL : (L.map Prod.fst).Pairwise (· < ·))
    (h : CommRel (v (pos k)) (v (pos l)) (L.map fun t => (v (pos t.1), t.2)))
    (E : Fin n → Polynomial (Polynomial R))
    (hE : ∀ t ∈ L, E t.1 = C (C t.2.1) * (C X) ^ t.2.2.1 * X ^ t.2.2.2)
    (hE0 : ∀ q, q ∉ L.map Prod.fst → E q = 0) :
    IsUnivComm v pos k l E := by
  unfold IsUnivComm
  set e := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (Polynomial R)))).inv
  rw [posComm, h _ (lineBase R)]
  unfold orderedProduct
  rw [prod_ofFn_eq_prod_map _ (L.map Prod.fst) hL (fun q hq => by
    beta_reduce
    rw [hE0 q hq, map_zero, rootPoint_zero])]
  rw [List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp, termPoint]
  rw [hE t ht, baseScalar_overMk, lineBase, Spec.preimage_map]
  simp only [map_mul, map_pow]
  rfl

theorem exists_fun_of_list {α β : Type*} [DecidableEq α] [Zero β] (L : List (α × β))
    (hnd : (L.map Prod.fst).Nodup) :
    ∃ f : α → β, (∀ t ∈ L, f t.1 = t.2) ∧ ∀ a, a ∉ L.map Prod.fst → f a = 0 := by
  induction L with
  | nil => exact ⟨0, by simp, fun _ _ => rfl⟩
  | cons t L ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨f, hf, hf0⟩ := ih hnd.2
    refine ⟨Function.update f t.1 t.2, fun t' ht' => ?_, fun a ha => ?_⟩
    · rcases List.mem_cons.mp ht' with rfl | ht'
      · exact Function.update_self _ _ _
      · have hne : t'.1 ≠ t.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem ht')
        rw [Function.update_of_ne hne, hf t' ht']
    · rw [List.map_cons, List.mem_cons, not_or] at ha
      rw [Function.update_of_ne ha.1, hf0 a ha.2]

open Polynomial in
/-- **Common universal coordinates.** If the commutator of the factors at positions `k`, `l` is
given in two groups by the same terms, at positions strictly increasing in the enumeration, the
two groups have the same universal commutator coordinates. -/
theorem exists_common_isUnivComm {H : GroupScheme (Spec (CommRingCat.of R))}
    (v : J → (Ga R ⟶ G)) (v' : J → (Ga R ⟶ H)) {n : ℕ} (pos : Fin n → J) (k l : Fin n)
    (L : List (J × R × ℕ × ℕ)) (q : J → Fin n) (hq : ∀ t ∈ L, pos (q t.1) = t.1)
    (hsorted : (L.map fun t => q t.1).Pairwise (· < ·))
    (hG : CommRel (v (pos k)) (v (pos l)) (L.map fun t => (v t.1, t.2)))
    (hH : CommRel (v' (pos k)) (v' (pos l)) (L.map fun t => (v' t.1, t.2))) :
    ∃ E : Fin n → Polynomial (Polynomial R), IsUnivComm v pos k l E ∧ IsUnivComm v' pos k l E := by
  classical
  let L' : List (Fin n × R × ℕ × ℕ) := L.map fun t => (q t.1, t.2)
  have hfst : L'.map Prod.fst = L.map fun t => q t.1 := by
    simp only [L', List.map_map]
    rfl
  have hL' : (L'.map Prod.fst).Pairwise (· < ·) := by
    rw [hfst]
    exact hsorted
  have hconv : ∀ {G₀ : GroupScheme (Spec (CommRingCat.of R))} (v₀ : J → (Ga R ⟶ G₀)),
      (L.map fun t => (v₀ t.1, t.2)) = L'.map fun t => (v₀ (pos t.1), t.2) := by
    intro G₀ v₀
    simp only [L', List.map_map]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp, hq t ht]
  have hk : (L'.map fun t => (t.1, C (C t.2.1) * (C X) ^ t.2.2.1 * X ^ t.2.2.2)).map
      Prod.fst = L'.map Prod.fst := by
    simp only [List.map_map]
    rfl
  obtain ⟨E, hE, hE0⟩ := exists_fun_of_list
    (L'.map fun t => (t.1, C (C t.2.1) * (C X) ^ t.2.2.1 * X ^ t.2.2.2))
    (by rw [hk]; exact hL'.imp ne_of_lt)
  have hE' : ∀ t ∈ L', E t.1 = C (C t.2.1) * (C X) ^ t.2.2.1 * X ^ t.2.2.2 :=
    fun t ht => hE _ (List.mem_map_of_mem ht)
  have hE0' : ∀ q₀, q₀ ∉ L'.map Prod.fst → E q₀ = 0 :=
    fun q₀ hq₀ => hE0 q₀ (by rw [hk]; exact hq₀)
  refine ⟨E, isUnivComm_of_commRel v pos k l L' hL' ?_ E hE' hE0',
    isUnivComm_of_commRel v' pos k l L' hL' ?_ E hE' hE0'⟩
  · rw [← hconv]; exact hG
  · rw [← hconv]; exact hH

end Univ

section Convert

variable {R : Type u} [CommRing R] {I : Type u} {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} {P : RootDatum J (I → ℤ) (I → ℤ)}

theorem wordConj_append (u : J → (Ga R ⟶ G)) (l l' : List J) (w : Ga R ⟶ G) :
    wordConj P u (l ++ l') w = wordConj P u l (wordConj P u l' w) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    change wordConj P u (l ++ l') w ≫ _ = wordConj P u l (wordConj P u l' w) ≫ _
    rw [ih]

/-- The terms of a formula whose maps are conjugates of members of a family along words. -/
def wordTerms (u : J → (Ga R ⟶ G)) (v : J → (Ga R ⟶ G)) (WL : List (List J × J × R × ℕ × ℕ)) :
    List (CommTerm R G) :=
  WL.map fun t => (wordConj P u t.1 (v t.2.1), t.2.2)

/-- The terms of a formula given by indices of a family. -/
def indexTerms (v : J → (Ga R ⟶ G)) (L : List (J × R × ℕ × ℕ)) : List (CommTerm R G) :=
  L.map fun t => (v t.1, t.2)

variable {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **Conversion of formulas along words into formulas of the Weyl families.** A formula among
word conjugates of Weyl-family members, valid in both groups with the same constants, becomes
a formula among Weyl-family members with common constants. -/
theorem WeylConjugationRelations.commRel_convert (h : WeylConjugationRelations P b W u u')
    {l₁ l₂ : List J} {d₁ d₂ : J} (hl₁ : ∀ c ∈ l₁, c ∈ b.support)
    (hl₂ : ∀ c ∈ l₂, c ∈ b.support) (WL : List (List J × J × R × ℕ × ℕ))
    (hWL : ∀ t ∈ WL, ∀ c ∈ t.1, c ∈ b.support)
    (hG : CommRel (wordConj P u l₁ (weylFamily P W u d₁)) (wordConj P u l₂ (weylFamily P W u d₂))
      (wordTerms (P := P) u (weylFamily P W u) WL))
    (hH : CommRel (wordConj P u' l₁ (weylFamily P W u' d₁))
      (wordConj P u' l₂ (weylFamily P W u' d₂)) (wordTerms (P := P) u' (weylFamily P W u') WL)) :
    ∃ L : List (J × R × ℕ × ℕ),
      L.map (fun t => (t.1, t.2.2)) =
        WL.map (fun t => (Langlands.LinearAlgebra.wordPerm P t.1 t.2.1, t.2.2.2)) ∧
      CommRel (weylFamily P W u (Langlands.LinearAlgebra.wordPerm P l₁ d₁))
        (weylFamily P W u (Langlands.LinearAlgebra.wordPerm P l₂ d₂))
        (indexTerms (weylFamily P W u) L) ∧
      CommRel (weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P l₁ d₁))
        (weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P l₂ d₂))
        (indexTerms (weylFamily P W u') L) := by
  classical
  have hex : ∀ (l : List J) (d : J), ∃ κ : Rˣ, (∀ c ∈ l, c ∈ b.support) →
      (wordConj P u l (weylFamily P W u d) =
        scaleHom (κ : R) ≫ weylFamily P W u (Langlands.LinearAlgebra.wordPerm P l d) ∧
      wordConj P u' l (weylFamily P W u' d) =
        scaleHom (κ : R) ≫ weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P l d)) := by
    intro l d
    by_cases hl : ∀ c ∈ l, c ∈ b.support
    · obtain ⟨κ, hκ⟩ := h.wordConj_weylFamily hl d
      exact ⟨κ, fun _ => hκ⟩
    · exact ⟨1, fun h' => absurd h' hl⟩
  choose κf hκf' using hex
  have hκf : ∀ l, (∀ c ∈ l, c ∈ b.support) → ∀ d,
      wordConj P u l (weylFamily P W u d) =
        scaleHom ((κf l d : Rˣ) : R) ≫ weylFamily P W u (Langlands.LinearAlgebra.wordPerm P l d) ∧
      wordConj P u' l (weylFamily P W u' d) =
        scaleHom ((κf l d : Rˣ) : R) ≫
          weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P l d) :=
    fun l hl d => hκf' l d hl
  let κ₁ := κf l₁ d₁
  let κ₂ := κf l₂ d₂
  let L : List (J × R × ℕ × ℕ) := WL.map fun t =>
    (Langlands.LinearAlgebra.wordPerm P t.1 t.2.1,
      ((κf t.1 t.2.1 : Rˣ) : R) * t.2.2.1 * ((κ₁⁻¹ : Rˣ) : R) ^ t.2.2.2.1 *
        ((κ₂⁻¹ : Rˣ) : R) ^ t.2.2.2.2, t.2.2.2)
  have hterm : ∀ {G₀ : GroupScheme (Spec (CommRingCat.of R))} (u₀ : J → (Ga R ⟶ G₀)),
      (∀ t ∈ WL, wordConj P u₀ t.1 (weylFamily P W u₀ t.2.1) =
        scaleHom ((κf t.1 t.2.1 : Rˣ) : R) ≫
          weylFamily P W u₀ (Langlands.LinearAlgebra.wordPerm P t.1 t.2.1)) →
      ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
        (x y : Γ((Over.mk s).left, ⊤)),
      (wordTerms (P := P) u₀ (weylFamily P W u₀) WL).map (termPoint (Over.mk s) x y) =
        (indexTerms (weylFamily P W u₀) (WL.map fun t =>
          (Langlands.LinearAlgebra.wordPerm P t.1 t.2.1,
            ((κf t.1 t.2.1 : Rˣ) : R) * t.2.2.1, t.2.2.2))).map (termPoint (Over.mk s) x y) := by
    intro G₀ u₀ hu₀ B _ s x y
    simp only [wordTerms, indexTerms, List.map_map]
    refine List.map_congr_left fun t ht => ?_
    simp only [Function.comp, termPoint]
    rw [hu₀ t ht, rootPoint_scaleHom, map_mul]
    congr 1
    ring
  have hfinal : ∀ {G₀ : GroupScheme (Spec (CommRingCat.of R))} (u₀ : J → (Ga R ⟶ G₀)),
      (∀ l, (∀ c ∈ l, c ∈ b.support) → ∀ d, wordConj P u₀ l (weylFamily P W u₀ d) =
        scaleHom ((κf l d : Rˣ) : R) ≫
          weylFamily P W u₀ (Langlands.LinearAlgebra.wordPerm P l d)) →
      CommRel (wordConj P u₀ l₁ (weylFamily P W u₀ d₁)) (wordConj P u₀ l₂ (weylFamily P W u₀ d₂))
        (wordTerms (P := P) u₀ (weylFamily P W u₀) WL) →
      CommRel (weylFamily P W u₀ (Langlands.LinearAlgebra.wordPerm P l₁ d₁))
        (weylFamily P W u₀ (Langlands.LinearAlgebra.wordPerm P l₂ d₂))
        (indexTerms (weylFamily P W u₀) L) := by
    intro G₀ u₀ hu₀ hrel
    have h2 : CommRel (wordConj P u₀ l₁ (weylFamily P W u₀ d₁))
        (wordConj P u₀ l₂ (weylFamily P W u₀ d₂))
        (indexTerms (weylFamily P W u₀) (WL.map fun t =>
          (Langlands.LinearAlgebra.wordPerm P t.1 t.2.1,
            ((κf t.1 t.2.1 : Rˣ) : R) * t.2.2.1, t.2.2.2))) := by
      intro B _ s x y
      rw [hrel B s x y, hterm u₀ (fun t ht => hu₀ t.1 (hWL t ht) t.2.1) B s x y]
    have h3 := h2.rescale κ₁ κ₂ (hu₀ l₁ hl₁ d₁) (hu₀ l₂ hl₂ d₂)
    have hL : (indexTerms (weylFamily P W u₀) (WL.map fun t =>
          (Langlands.LinearAlgebra.wordPerm P t.1 t.2.1,
            ((κf t.1 t.2.1 : Rˣ) : R) * t.2.2.1, t.2.2.2))).map (fun t => (t.1,
          t.2.1 * ((κ₁⁻¹ : Rˣ) : R) ^ t.2.2.1 * ((κ₂⁻¹ : Rˣ) : R) ^ t.2.2.2, t.2.2.1, t.2.2.2)) =
        indexTerms (weylFamily P W u₀) L := by
      simp only [indexTerms, L, List.map_map]
      rfl
    rw [hL] at h3
    exact h3
  refine ⟨L, by simp [L], hfinal u (fun l hl d => (hκf l hl d).1) hG,
    hfinal u' (fun l hl d => (hκf l hl d).2) hH⟩

theorem wordTerms_conj (u : J → (Ga R ⟶ G)) (v : J → (Ga R ⟶ G)) (l : List J)
    (WL : List (List J × J × R × ℕ × ℕ)) :
    (wordTerms (P := P) u v WL).map (fun t => (wordConj P u l t.1, t.2)) =
      wordTerms (P := P) u v (WL.map fun t => (l ++ t.1, t.2)) := by
  simp only [wordTerms, List.map_map]
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, wordConj_append]

/-- **Transport of a formula along a word.** A formula in the standard position, valid in both
groups, transported by conjugation along a word in the simple reflections, becomes a formula
among Weyl-family members with common constants. -/
theorem WeylConjugationRelations.transport (h : WeylConjugationRelations P b W u u')
    {l l₁ l₂ : List J} {d₁ d₂ : J} (hl : ∀ c ∈ l, c ∈ b.support)
    (hl₁ : ∀ c ∈ l₁, c ∈ b.support) (hl₂ : ∀ c ∈ l₂, c ∈ b.support)
    (WL : List (List J × J × R × ℕ × ℕ)) (hWL : ∀ t ∈ WL, ∀ c ∈ t.1, c ∈ b.support)
    (hG : CommRel (wordConj P u l₁ (weylFamily P W u d₁)) (wordConj P u l₂ (weylFamily P W u d₂))
      (wordTerms (P := P) u (weylFamily P W u) WL))
    (hH : CommRel (wordConj P u' l₁ (weylFamily P W u' d₁))
      (wordConj P u' l₂ (weylFamily P W u' d₂))
      (wordTerms (P := P) u' (weylFamily P W u') WL)) :
    ∃ L : List (J × R × ℕ × ℕ),
      L.map (fun t => (t.1, t.2.2)) =
        WL.map (fun t => (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1, t.2.2.2)) ∧
      CommRel (weylFamily P W u (Langlands.LinearAlgebra.wordPerm P (l ++ l₁) d₁))
        (weylFamily P W u (Langlands.LinearAlgebra.wordPerm P (l ++ l₂) d₂))
        (indexTerms (weylFamily P W u) L) ∧
      CommRel (weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P (l ++ l₁) d₁))
        (weylFamily P W u' (Langlands.LinearAlgebra.wordPerm P (l ++ l₂) d₂))
        (indexTerms (weylFamily P W u') L) := by
  have hG' := hG.conj_word (P := P) u l
  have hH' := hH.conj_word (P := P) u' l
  rw [← wordConj_append, ← wordConj_append, wordTerms_conj] at hG' hH'
  have happ : ∀ m : List J, (∀ c ∈ m, c ∈ b.support) → ∀ c ∈ l ++ m, c ∈ b.support := by
    intro m hm c hc
    rcases List.mem_append.mp hc with h' | h'
    · exact hl c h'
    · exact hm c h'
  have hll₂ := happ l₂ hl₂
  have hWL' : ∀ t ∈ WL.map (fun t => (l ++ t.1, t.2)), ∀ c ∈ t.1, c ∈ b.support := by
    intro t ht c hc
    obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.mp ht
    rcases List.mem_append.mp hc with h' | h'
    · exact hl c h'
    · exact hWL t₀ ht₀ c h'
  obtain ⟨L, hL, h1, h2⟩ := h.commRel_convert (happ l₁ hl₁) hll₂ _ hWL' hG' hH'
  refine ⟨L, ?_, h1, h2⟩
  rw [hL, List.map_map]
  rfl

end Convert

section RankTwoSetup

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]

/-- **Normalized simple-root data.** The hypotheses on simple-root data `u` of `G` for a base
`b` and words `W` used in this module: `G` is reductive with a fibrewise maximal torus `i` and
fibrewise root datum `P`, the maps `u a`, `u (-a)` are root parametrizations, the points
`rootWeylPoint P u a` are Weyl points acting by `s_a`, the words are descending, and `u` is
rank-one normal at every simple root. -/
structure IsNormalSimpleData (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (b : P.Base) (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) : Prop where
  reductive : IsReductive G
  maximal : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i
  rootDatum : IsFibrewiseRootDatumOf I G i P
  param : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a) ∧
    IsRootParametrization i (P.root (P.reflectionPerm a a)) (u (P.reflectionPerm a a))
  weyl : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)
  words : IsDescendingWords P b W
  rankOne : ∀ a ∈ b.support, RankOneNormal i P u a

variable {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)}

theorem IsNormalSimpleData.weylFamily_simple (hd : IsNormalSimpleData i P b W u) {a : J}
    (ha : a ∈ b.support) : weylFamily P W u a = u a := by
  unfold weylFamily
  rw [(hd.words.1 a ha).1, (hd.words.1 a ha).2]
  rfl

theorem IsNormalSimpleData.isRootParametrization (hd : IsNormalSimpleData i P b W u) (α : J) :
    IsRootParametrization i (P.root α) (weylFamily P W u α) :=
  isRootParametrization_weylFamily (fun a ha => (hd.param a ha).1) hd.weyl W α

/-- The family used for the rank-two computations at two simple roots `a`, `c`: the Weyl
family, with the given opposite parametrizations at `-a` and `-c`. -/
theorem IsNormalSimpleData.exists_family (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c) :
    ∃ v : J → (Ga R ⟶ G), (∀ α, IsRootParametrization i (P.root α) (v α)) ∧
      v a = u a ∧ v c = u c ∧ v (P.reflectionPerm a a) = u (P.reflectionPerm a a) ∧
      v (P.reflectionPerm c c) = u (P.reflectionPerm c c) := by
  classical
  have hapos : b.IsPos a := RootPairing.Base.isPos_of_mem_support ha
  have hcpos : b.IsPos c := RootPairing.Base.isPos_of_mem_support hc
  have hnapos : ¬ b.IsPos (P.reflectionPerm a a) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) a).mp h hapos
  have hncpos : ¬ b.IsPos (P.reflectionPerm c c) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) c).mp h hcpos
  have h1 : a ≠ P.reflectionPerm c c := fun h => hncpos (h ▸ hapos)
  have h2 : c ≠ P.reflectionPerm c c := fun h => hncpos (h ▸ hcpos)
  have h3 : a ≠ P.reflectionPerm a a := fun h => hnapos (h ▸ hapos)
  have h4 : c ≠ P.reflectionPerm a a := fun h => hnapos (h ▸ hcpos)
  have h5 : P.reflectionPerm a a ≠ P.reflectionPerm c c := by
    intro h
    apply hac
    have := congrArg (P.reflectionPerm a) h
    rw [RootPairing.reflectionPerm_self] at this
    apply P.root.injective
    have hr := congrArg P.root h
    rw [RootPairing.root_reflectionPerm, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self, RootPairing.reflection_apply_self] at hr
    exact neg_injective hr
  let v : J → (Ga R ⟶ G) := Function.update (Function.update (weylFamily P W u)
    (P.reflectionPerm a a) (u (P.reflectionPerm a a))) (P.reflectionPerm c c)
    (u (P.reflectionPerm c c))
  refine ⟨v, fun α => ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hα : α = P.reflectionPerm c c
    · subst hα
      simp only [v, Function.update_self]
      exact (hd.param c hc).2
    · by_cases hα' : α = P.reflectionPerm a a
      · subst hα'
        simp only [v, Function.update_of_ne hα, Function.update_self]
        exact (hd.param a ha).2
      · simp only [v, Function.update_of_ne hα, Function.update_of_ne hα']
        exact hd.isRootParametrization α
  · simp only [v, Function.update_of_ne h1, Function.update_of_ne h3]
    exact hd.weylFamily_simple ha
  · simp only [v, Function.update_of_ne h2, Function.update_of_ne h4]
    exact hd.weylFamily_simple hc
  · simp only [v, Function.update_of_ne h5, Function.update_self]
  · simp only [v, Function.update_self]

/-- The square of a simple Weyl point acts on every root group by a sign. -/
theorem IsNormalSimpleData.conj_sq [IsLocalRing R] (hd : IsNormalSimpleData i P b W u) {a : J}
    (ha : a ∈ b.support) (β : J) (w : Ga R ⟶ G) (hw : IsRootParametrization i (P.root β) w)
    (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x : Γ((Over.mk s).left, ⊤)) :
    (G.constantPoint (rootWeylPoint P u a) (Over.mk s) *
        G.constantPoint (rootWeylPoint P u a) (Over.mk s)) * rootPoint w (Over.mk s) x *
        (G.constantPoint (rootWeylPoint P u a) (Over.mk s) *
          G.constantPoint (rootWeylPoint P u a) (Over.mk s))⁻¹ =
      rootPoint w (Over.mk s) ((P.pairingIn ℤ β a).negOnePow • x) :=
  conj_sq_rootPoint hd.rootDatum (hd.rankOne a ha).2.2 hw (Over.mk s) x

omit [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
/-- A commutator formula stated for elements of the rings `B`, viewed as global functions
through `Scheme.ΓSpecIso`. -/
theorem commRel_of_forall {w₁ w₂ : Ga R ⟶ G} {L : List (CommTerm R G)}
    (h : ∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint w₁ (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint w₂ (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint w₂ (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint w₁ (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      (L.map fun t => rootPoint t.1 (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv
        ((Spec.preimage s).hom t.2.1 * x ^ t.2.2.1 * y ^ t.2.2.2))).prod) :
    CommRel w₁ w₂ L := by
  intro B _ s x y
  obtain ⟨x₀, rfl⟩ : ∃ x₀, (Scheme.ΓSpecIso (CommRingCat.of B)).inv x₀ = x :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom x, Iso.hom_inv_id_apply _ _⟩
  obtain ⟨y₀, rfl⟩ : ∃ y₀, (Scheme.ΓSpecIso (CommRingCat.of B)).inv y₀ = y :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom y, Iso.hom_inv_id_apply _ _⟩
  rw [h B s x₀ y₀]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [termPoint, baseScalar_overMk, map_mul, map_pow]

end RankTwoSetup

section TypeG2

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)}

/-- **The standard formulas of type `G₂`**, for `a` short and `c` long, as formulas among word
conjugates of the Weyl family. -/
theorem IsNormalSimpleData.g2_commRels (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3) :
    CommRel (weylFamily P W u a) (weylFamily P W u c) (wordTerms (P := P) u (weylFamily P W u)
      [([c], a, 1, 1, 1), ([a, c], a, 1, 2, 1), ([a], c, -1, 3, 1), ([c, a], c, -1, 3, 2)]) ∧
    CommRel (weylFamily P W u a) (wordConj P u [c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u)
        [([a, c], a, 2, 1, 1), ([a], c, -3, 2, 1), ([c, a], c, -3, 1, 2)]) ∧
    CommRel (weylFamily P W u a) (wordConj P u [a, c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u) [([a], c, -3, 1, 1)]) ∧
    CommRel (weylFamily P W u c) (wordConj P u [a] (weylFamily P W u c))
      (wordTerms (P := P) u (weylFamily P W u) [([c, a], c, -1, 1, 1)]) ∧
    CommRel (wordConj P u [c] (weylFamily P W u a)) (wordConj P u [a, c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u) [([c, a], c, -3, 1, 1)]) := by
  obtain ⟨v, hv, hva, hvc, hvna, hvnc⟩ := hd.exists_family ha hc hac
  have hwa := hd.weylFamily_simple ha
  have hwc := hd.weylFamily_simple hc
  have hna : IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a) := by
    rw [hva, hvna]
    exact hd.weyl a ha
  have hnc : IsWeylPoint i (weylPoint (v c) (v (P.reflectionPerm c c))) (P.reflection c) := by
    rw [hvc, hvnc]
    exact hd.weyl c hc
  have hRa := hd.rankOne a ha
  have hRc := hd.rankOne c hc
  have key := g2_constants hd.reductive hd.maximal hd.rootDatum hv ha hc hac h1 h2 hna hnc
    (by rw [hva, hvna]; exact hRa.1) (by rw [hvc, hvnc]; exact hRc.1)
    (by rw [hva, hvna]; exact fun β w hw B _ s x => hd.conj_sq ha β w hw B s x)
    (by rw [hvc, hvnc]; exact fun β w hw B _ s x => hd.conj_sq hc β w hw B s x)
  simp only [hva, hvc, hvna, hvnc] at key
  obtain ⟨k1, k2, k3, k4, k5⟩ := key
  simp only [wordTerms, wordConj, rootWeylPoint, hwa, hwc]
  refine ⟨commRel_of_forall fun B _ s x y => ?_, commRel_of_forall fun B _ s x y => ?_,
    commRel_of_forall fun B _ s x y => ?_, commRel_of_forall fun B _ s x y => ?_,
    commRel_of_forall fun B _ s x y => ?_⟩
  · rw [k1 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_one,
      map_neg, one_mul, pow_one, neg_mul, mul_assoc, wordConj, rootWeylPoint, hwa, hwc]
  · rw [k2 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_ofNat,
      map_neg, pow_one, neg_mul, mul_assoc, wordConj, rootWeylPoint, hwa, hwc]
  · rw [k3 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_ofNat,
      map_neg, pow_one, neg_mul, mul_assoc, wordConj, rootWeylPoint, hwc]
  · rw [k4 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_one,
      map_neg, one_mul, pow_one, neg_mul, mul_assoc, wordConj, rootWeylPoint, hwc]
  · rw [k5 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_ofNat,
      map_neg, pow_one, neg_mul, mul_assoc, wordConj, rootWeylPoint, hwc]

/-- **The standard formulas of type `B₂`**, for `a` short and `c` long. -/
theorem IsNormalSimpleData.b2_commRels (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) :
    CommRel (weylFamily P W u a) (weylFamily P W u c) (wordTerms (P := P) u (weylFamily P W u)
      [([c], a, 1, 1, 1), ([a], c, 1, 2, 1)]) ∧
    CommRel (weylFamily P W u a) (wordConj P u [c] (weylFamily P W u a))
      (wordTerms (P := P) u (weylFamily P W u) [([a], c, 2, 1, 1)]) := by
  obtain ⟨v, hv, hva, hvc, hvna, hvnc⟩ := hd.exists_family ha hc hac
  have hwa := hd.weylFamily_simple ha
  have hwc := hd.weylFamily_simple hc
  have hna : IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a) := by
    rw [hva, hvna]
    exact hd.weyl a ha
  have hnc : IsWeylPoint i (weylPoint (v c) (v (P.reflectionPerm c c))) (P.reflection c) := by
    rw [hvc, hvnc]
    exact hd.weyl c hc
  have hRa := hd.rankOne a ha
  have hRc := hd.rankOne c hc
  have key := b2_constants hd.reductive hd.maximal hd.rootDatum hv ha hc hac h1 h2 hna hnc
    (by rw [hva, hvna]; exact hRa.1) (by rw [hvc, hvnc]; exact hRc.1)
    (by
      rw [hva, hvna, hvc]
      intro B _ s x
      have := hd.conj_sq ha c (u c) (hd.param c hc).1 B s x
      rw [h2, Int.negOnePow_even _ ⟨-1, by norm_num⟩, one_smul] at this
      exact this)
    (by
      rw [hvc, hvnc, hva]
      intro B _ s x
      have := hd.conj_sq hc a (u a) (hd.param a ha).1 B s x
      rw [h1, Int.negOnePow_odd _ ⟨-1, by norm_num⟩, Units.neg_smul, one_smul] at this
      exact this)
  simp only [hva, hvc, hvna, hvnc] at key
  obtain ⟨k1, k2, -⟩ := key
  simp only [wordTerms, wordConj, rootWeylPoint, hwa, hwc]
  refine ⟨commRel_of_forall fun B _ s x y => ?_, commRel_of_forall fun B _ s x y => ?_⟩
  · rw [k1 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_one,
      one_mul, pow_one, mul_assoc, wordConj, rootWeylPoint, hwa, hwc]
  · rw [k2 B s x y]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_ofNat,
      pow_one, mul_assoc, wordConj, rootWeylPoint, hwc]

omit [IsLocalRing R] in
/-- **The standard formula of type `A₂`.** -/
theorem IsNormalSimpleData.a2_commRel (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -1) :
    CommRel (weylFamily P W u a) (weylFamily P W u c) (wordTerms (P := P) u (weylFamily P W u)
      [([a], c, -1, 1, 1)]) := by
  obtain ⟨v, hv, hva, hvc, hvna, hvnc⟩ := hd.exists_family ha hc hac
  have hwa := hd.weylFamily_simple ha
  have hwc := hd.weylFamily_simple hc
  have hna : IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a) := by
    rw [hva, hvna]
    exact hd.weyl a ha
  have key := a2_constants hd.reductive hd.maximal hd.rootDatum hv ha hc hac h1 h2 hna
  simp only [hva, hvc, hvna] at key
  obtain ⟨k1, -⟩ := key
  simp only [wordTerms, hwa, hwc]
  refine commRel_of_forall fun B _ s x y => ?_
  rw [k1 B s x y]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, map_one,
    map_neg, one_mul, pow_one, neg_mul, wordConj, rootWeylPoint, hwc]

end TypeG2

section PairTools

variable {I J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

theorem wordPerm_nil (d : J) : Langlands.LinearAlgebra.wordPerm P [] d = d := rfl

theorem wordPerm_cons (c : J) (l : List J) (d : J) :
    Langlands.LinearAlgebra.wordPerm P (c :: l) d =
      P.reflectionPerm c (Langlands.LinearAlgebra.wordPerm P l d) := rfl

theorem wordPerm_append (l m : List J) (d : J) :
    Langlands.LinearAlgebra.wordPerm P (l ++ m) d =
      Langlands.LinearAlgebra.wordPerm P l (Langlands.LinearAlgebra.wordPerm P m d) := by
  simp only [Langlands.LinearAlgebra.wordPerm, List.foldr_append]

theorem wordReflect_reverse (l : List J) (x : I → ℤ) :
    wordReflect P l.reverse (wordReflect P l x) = x := by
  induction l generalizing x with
  | nil => rfl
  | cons c l ih =>
    rw [List.reverse_cons]
    simp only [wordReflect, List.foldr_append, List.foldr_cons, List.foldr_nil]
    change wordReflect P l.reverse (P.reflection c (P.reflection c (wordReflect P l x))) = x
    rw [RootPairing.reflection_same]
    exact ih x

theorem wordPerm_reverse (l : List J) (d : J) :
    Langlands.LinearAlgebra.wordPerm P l (Langlands.LinearAlgebra.wordPerm P l.reverse d) = d := by
  apply P.root.injective
  rw [Langlands.LinearAlgebra.root_wordPerm, Langlands.LinearAlgebra.root_wordPerm]
  have := wordReflect_reverse (P := P) l.reverse (P.root d)
  rwa [List.reverse_reverse] at this

theorem wordPerm_injective (l : List J) :
    Function.Injective (Langlands.LinearAlgebra.wordPerm P l) := by
  intro x y h
  have hx := wordPerm_reverse (P := P) l.reverse x
  have hy := wordPerm_reverse (P := P) l.reverse y
  rw [List.reverse_reverse] at hx hy
  exact (hx.symm.trans (congrArg _ h)).trans hy

theorem height_of_root_eq_combo [Finite J] (b : P.Base) {δ β ε : J} {i j : ℤ}
    (h : P.root δ = i • P.root β + j • P.root ε) :
    b.height δ = i * b.height β + j * b.height ε := by
  classical
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int β
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int ε
  rw [RootPairing.Base.height_eq_sum hf, RootPairing.Base.height_eq_sum hg,
    RootPairing.Base.height_eq_sum (f := fun k => i * f k + j * g k) (by
      rw [h, hf, hg, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [add_smul, mul_smul, mul_smul]),
    Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem isPos_of_combo [Finite J] {b : P.Base} {δ β ε : J} {i j : ℕ} (hβ : b.IsPos β)
    (hε : b.IsPos ε) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : P.root δ = (i : ℤ) • P.root β + (j : ℤ) • P.root ε) : b.IsPos δ := by
  have h1 : 0 < b.height β := hβ
  have h2 : 0 < b.height ε := hε
  have hi' : (1 : ℤ) ≤ i := by exact_mod_cast hi
  have hj' : (1 : ℤ) ≤ j := by exact_mod_cast hj
  rw [RootPairing.Base.isPos_iff, height_of_root_eq_combo b h]
  nlinarith

end PairTools

section PairFormula

variable {R : Type u} [CommRing R] {I : Type u} {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b b' : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **A good formula for a pair of roots.** The commutator of `v_β` and `v_ε` in both Weyl
families is given by the same terms, at positive roots whose positions `q` strictly
increase. -/
def PairFormula (b' : P.Base) (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G))
    (u' : J → (Ga R ⟶ H)) {n : ℕ} (q : J → Fin n) (β ε : J) : Prop :=
  ∃ L : List (J × R × ℕ × ℕ), (∀ t ∈ L, b'.IsPos t.1) ∧
    (L.map fun t => q t.1).Pairwise (· < ·) ∧
    CommRel (weylFamily P W u β) (weylFamily P W u ε) (indexTerms (weylFamily P W u) L) ∧
    CommRel (weylFamily P W u' β) (weylFamily P W u' ε) (indexTerms (weylFamily P W u') L)

/-- **Finishing a pair from a standard formula.** -/
theorem WeylConjugationRelations.pairFormula_of_standard [Finite J]
    (h : WeylConjugationRelations P b W u u') {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε)
    {l l₁ l₂ : List J} {d₁ d₂ : J} (hl : ∀ c ∈ l, c ∈ b.support)
    (hl₁ : ∀ c ∈ l₁, c ∈ b.support) (hl₂ : ∀ c ∈ l₂, c ∈ b.support)
    (WL : List (List J × J × R × ℕ × ℕ)) (hWL : ∀ t ∈ WL, ∀ c ∈ t.1, c ∈ b.support)
    (hβ' : Langlands.LinearAlgebra.wordPerm P (l ++ l₁) d₁ = β)
    (hε' : Langlands.LinearAlgebra.wordPerm P (l ++ l₂) d₂ = ε)
    (hroot : ∀ t ∈ WL, P.root (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) =
      (t.2.2.2.1 : ℤ) • P.root β + (t.2.2.2.2 : ℤ) • P.root ε)
    (hexp : ∀ t ∈ WL, 1 ≤ t.2.2.2.1 ∧ 1 ≤ t.2.2.2.2)
    (hsort : WL.Pairwise fun t t' =>
      (t.2.2.2.1 ≤ t'.2.2.2.1 ∧ t.2.2.2.2 ≤ t'.2.2.2.2 ∧
        (t.2.2.2.1, t.2.2.2.2) ≠ (t'.2.2.2.1, t'.2.2.2.2)) ∨
      q (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) <
        q (Langlands.LinearAlgebra.wordPerm P (l ++ t'.1) t'.2.1))
    (hG : CommRel (wordConj P u l₁ (weylFamily P W u d₁)) (wordConj P u l₂ (weylFamily P W u d₂))
      (wordTerms (P := P) u (weylFamily P W u) WL))
    (hH : CommRel (wordConj P u' l₁ (weylFamily P W u' d₁))
      (wordConj P u' l₂ (weylFamily P W u' d₂))
      (wordTerms (P := P) u' (weylFamily P W u') WL)) :
    PairFormula b' W u u' q β ε := by
  obtain ⟨L, hL, h1, h2⟩ := h.transport hl hl₁ hl₂ WL hWL hG hH
  rw [hβ', hε'] at h1 h2
  have hLidx : L.map Prod.fst =
      WL.map fun t => Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1 := by
    have := congrArg (List.map Prod.fst) hL
    simp only [List.map_map] at this
    exact this
  have hβh : 0 < b'.height β := hβ
  have hεh : 0 < b'.height ε := hε
  have hht : ∀ t ∈ WL, b'.height (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) =
      t.2.2.2.1 * b'.height β + t.2.2.2.2 * b'.height ε :=
    fun t ht => height_of_root_eq_combo b' (hroot t ht)
  have hposWL : ∀ t ∈ WL, b'.IsPos (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) := by
    intro t ht
    rw [RootPairing.Base.isPos_iff, hht t ht]
    have := hexp t ht
    have h1' : (1 : ℤ) ≤ t.2.2.2.1 := by exact_mod_cast this.1
    have h2' : (1 : ℤ) ≤ t.2.2.2.2 := by exact_mod_cast this.2
    nlinarith
  refine ⟨L, fun t ht => ?_, ?_, h1, h2⟩
  · have hmem : t.1 ∈ L.map Prod.fst := List.mem_map_of_mem ht
    rw [hLidx] at hmem
    obtain ⟨t₀, ht₀, he⟩ := List.mem_map.mp hmem
    rw [← he]
    exact hposWL t₀ ht₀
  · have hq' : (L.map fun t => q t.1) =
        WL.map fun t => q (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) := by
      have := congrArg (List.map q) hLidx
      simp only [List.map_map] at this
      exact this
    rw [hq', List.pairwise_map]
    refine hsort.imp_of_mem fun {t t'} ht ht' he => ?_
    rcases he with ⟨e1, e2, ne⟩ | hlt
    · apply hq _ _ (hposWL t ht) (hposWL t' ht')
      rw [hht t ht, hht t' ht']
      have e1' : (t.2.2.2.1 : ℤ) ≤ t'.2.2.2.1 := by exact_mod_cast e1
      have e2' : (t.2.2.2.2 : ℤ) ≤ t'.2.2.2.2 := by exact_mod_cast e2
      rcases lt_or_eq_of_le e1 with l1 | l1
      · have : (t.2.2.2.1 : ℤ) < t'.2.2.2.1 := by exact_mod_cast l1
        nlinarith
      · have hne2 : t.2.2.2.2 ≠ t'.2.2.2.2 := fun h' => ne (Prod.ext l1 h')
        have : (t.2.2.2.2 : ℤ) < t'.2.2.2.2 := by exact_mod_cast lt_of_le_of_ne e2 hne2
        nlinarith
    · exact hlt

/-- The sorting condition from exponents alone. -/
theorem pairwise_of_exps {α : Type*} {WL : List (List J × J × α × ℕ × ℕ)}
    {Q : (List J × J × α × ℕ × ℕ) → (List J × J × α × ℕ × ℕ) → Prop}
    (h : (WL.map fun t => (t.2.2.2.1, t.2.2.2.2)).Pairwise
      fun e e' => e.1 ≤ e'.1 ∧ e.2 ≤ e'.2 ∧ e ≠ e') :
    WL.Pairwise fun t t' => (t.2.2.2.1 ≤ t'.2.2.2.1 ∧ t.2.2.2.2 ≤ t'.2.2.2.2 ∧
      (t.2.2.2.1, t.2.2.2.2) ≠ (t'.2.2.2.1, t'.2.2.2.2)) ∨ Q t t' :=
  (List.pairwise_map.mp h).imp Or.inl

end PairFormula

section RankTwoRoots

variable {I J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

theorem pairing_eq_of_pairingIn {x y : J} {z : ℤ} (h : P.pairingIn ℤ x y = z) :
    P.pairing x y = z := by
  rw [← P.algebraMap_pairingIn ℤ, h]
  simp

theorem pairing_combo {α a c : J} {p q : ℤ} (h : P.root α = p • P.root a + q • P.root c)
    (x : J) : P.pairing α x = p * P.pairing a x + q * P.pairing c x := by
  rw [← RootPairing.root_coroot_eq_pairing, h]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
    RootPairing.root_coroot_eq_pairing, smul_eq_mul]

/-- The positive roots of type `G₂` as reflections of the simple roots `a` (short) and `c`. -/
theorem g2_roots {a c : J} (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3) :
    P.root (P.reflectionPerm c a) = P.root a + P.root c ∧
    P.root (P.reflectionPerm a (P.reflectionPerm c a)) = (2 : ℤ) • P.root a + P.root c ∧
    P.root (P.reflectionPerm a c) = (3 : ℤ) • P.root a + P.root c ∧
    P.root (P.reflectionPerm c (P.reflectionPerm a c)) =
      (3 : ℤ) • P.root a + (2 : ℤ) • P.root c := by
  have hac := pairing_eq_of_pairingIn h1
  have hca := pairing_eq_of_pairingIn h2
  have r1 : P.root (P.reflectionPerm c a) = P.root a + P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hac]
    module
  have r3 : P.root (P.reflectionPerm a c) = (3 : ℤ) • P.root a + P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hca]
    module
  refine ⟨r1, ?_, r3, ?_⟩
  · have e : P.pairing (P.reflectionPerm c a) a = -1 := by
      rw [pairing_combo (a := a) (c := c) (p := 1) (q := 1) (by rw [r1]; module) a,
        RootPairing.pairing_same, hca]
      norm_num
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, e, r1]
    module
  · have e : P.pairing (P.reflectionPerm a c) c = -1 := by
      rw [pairing_combo (a := a) (c := c) (p := 3) (q := 1) (by rw [r3]; module) c,
        RootPairing.pairing_same, hac]
      norm_num
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, e, r3]
    module

/-- The non-simple positive roots of type `B₂`, for `a` short and `c` long. -/
theorem b2_roots {a c : J} (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) :
    P.root (P.reflectionPerm c a) = P.root a + P.root c ∧
    P.root (P.reflectionPerm a c) = (2 : ℤ) • P.root a + P.root c := by
  have hac := pairing_eq_of_pairingIn h1
  have hca := pairing_eq_of_pairingIn h2
  constructor
  · rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hac]
    module
  · rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hca]
    module

theorem eq_of_coeffs {a c x y : J} {m₁ n₁ m₂ n₂ : ℤ}
    (hx : P.root x = m₁ • P.root a + n₁ • P.root c)
    (hy : P.root y = m₂ • P.root a + n₂ • P.root c) (h1 : m₁ = m₂) (h2 : n₁ = n₂) : x = y := by
  subst h1 h2
  exact P.root.injective (hx.trans hy.symm)

theorem coeffs_eq_of_eq {a c x y : J} (hli : LinearIndependent ℤ ![P.root a, P.root c])
    {m₁ n₁ m₂ n₂ : ℤ} (hx : P.root x = m₁ • P.root a + n₁ • P.root c)
    (hy : P.root y = m₂ • P.root a + n₂ • P.root c) (hxy : x = y) : m₁ = m₂ ∧ n₁ = n₂ := by
  subst hxy
  have h0 : (m₁ - m₂) • P.root a + (n₁ - n₂) • P.root c = 0 := by
    have : m₁ • P.root a + n₁ • P.root c - (m₂ • P.root a + n₂ • P.root c) = 0 := by
      rw [← hx, ← hy, sub_self]
    rw [← this]
    module
  have := LinearIndependent.pair_iff.mp hli _ _ h0
  omega

/-- **No root in the cone, from coefficients.** Two roots written in the basis of two simple
roots `a`, `c` are not opposite and have no root in their cone, when a classification `Φ` of
the coefficients of roots excludes all `dS • x + dT • y`. -/
theorem noOpp_cone_of_coeffs {a c x y : J} (hli : LinearIndependent ℤ ![P.root a, P.root c])
    {m₁ n₁ m₂ n₂ : ℤ} (hx : P.root x = m₁ • P.root a + n₁ • P.root c)
    (hy : P.root y = m₂ • P.root a + n₂ • P.root c) {Φ : ℤ → ℤ → Prop}
    (hΦ : ∀ (α : J) (m n : ℤ), P.root α = m • P.root a + n • P.root c → Φ m n)
    (hopp : m₁ + m₂ ≠ 0 ∨ n₁ + n₂ ≠ 0)
    (hno : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m₁ + dT * m₂) (dS * n₁ + dT * n₂) → False) :
    P.root x ≠ -P.root y ∧ ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root x + (dT : ℤ) • P.root y ≠ P.root α := by
  refine ⟨fun h => ?_, fun α dS dT hS hT h => ?_⟩
  · have h0 : (m₁ + m₂) • P.root a + (n₁ + n₂) • P.root c = 0 := by
      have : P.root x + P.root y = 0 := by rw [h, neg_add_cancel]
      rw [hx, hy] at this
      rw [← this]
      module
    have := LinearIndependent.pair_iff.mp hli _ _ h0
    omega
  · apply hno dS dT (by exact_mod_cast hS) (by exact_mod_cast hT)
    apply hΦ α
    rw [← h, hx, hy]
    module

end RankTwoRoots

section TwoGroups

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [IsAffineHom H.X.hom] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b b' : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

omit [IsLocalRing R] in
theorem IsNormalSimpleData.pointsCommute (hd : IsNormalSimpleData i P b W u) {x y : J}
    (hxy : P.root x ≠ -P.root y)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root x + (dT : ℤ) • P.root y ≠ P.root α) :
    PointsCommute (weylFamily P W u x) (weylFamily P W u y) :=
  fun _ _ s z w => rootPoint_commute_of_forall_ne hd.reductive hd.maximal hd.rootDatum
    hd.isRootParametrization hxy hcone s z w

omit [IsLocalRing R] [Fintype I] [DecidableEq I] in
theorem root_transport {l m : List J} {d s₁ ε₀ β ε : J} {i j : ℤ}
    (hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε)
    (h : P.root (Langlands.LinearAlgebra.wordPerm P m d) = i • P.root s₁ + j • P.root ε₀) :
    P.root (Langlands.LinearAlgebra.wordPerm P (l ++ m) d) = i • P.root β + j • P.root ε := by
  rw [wordPerm_append, Langlands.LinearAlgebra.root_wordPerm, h,
    Langlands.LinearAlgebra.wordReflect_combo, ← Langlands.LinearAlgebra.root_wordPerm,
    ← Langlands.LinearAlgebra.root_wordPerm, hβl, hεl]

omit [IsLocalRing R] in
/-- **A commuting pair.** If the standard pair has no root in its cone, so does the transported
pair, and the formula is empty. -/
theorem pairFormula_of_commute_std [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {s₁ ε₀ : J} (hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) (hneg : P.root s₁ ≠ -P.root ε₀)
    (hcone : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root s₁ + (dT : ℤ) • P.root ε₀ ≠ P.root α) :
    PairFormula b' W u u' q β ε :=
  hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) hl (by simp) (by simp) []
    (by simp) (by rw [List.append_nil]; exact hβl) (by rw [List.append_nil]; exact hεl)
    (by simp) (by simp) List.Pairwise.nil
    (commRel_nil (hdG.pointsCommute hneg hcone)) (commRel_nil (hdH.pointsCommute hneg hcone))

omit [IsLocalRing R] in
/-- **A commuting pair, from coefficients.** -/
theorem pairFormula_of_commute_coeffs [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c s₁ ε₀ : J} (hli : LinearIndependent ℤ ![P.root a, P.root c])
    (hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {m₁ n₁ m₂ n₂ : ℤ}
    (hx : P.root s₁ = m₁ • P.root a + n₁ • P.root c)
    (hy : P.root ε₀ = m₂ • P.root a + n₂ • P.root c) {Φ : ℤ → ℤ → Prop}
    (hΦ : ∀ (α : J) (m n : ℤ), P.root α = m • P.root a + n • P.root c → Φ m n)
    (hopp : m₁ + m₂ ≠ 0 ∨ n₁ + n₂ ≠ 0)
    (hno : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m₁ + dT * m₂) (dS * n₁ + dT * n₂) → False) :
    PairFormula b' W u u' q β ε :=
  have h := noOpp_cone_of_coeffs hli hx hy hΦ hopp hno
  pairFormula_of_commute_std hdG hdH hU q hq hβ hε hl hβl hεl h.1 h.2

omit [IsLocalRing R] in
/-- Word conjugates of the Weyl families whose roots have no root in their cone commute, in
both groups. -/
theorem WeylConjugationRelations.pointsCommute_wordConj
    (hU : WeylConjugationRelations P b W u u')
    (hdG : IsNormalSimpleData i P b W u) (hdH : IsNormalSimpleData i' P b W u')
    {l₁ l₂ : List J} (hl₁ : ∀ c ∈ l₁, c ∈ b.support) (hl₂ : ∀ c ∈ l₂, c ∈ b.support)
    {d₁ d₂ : J}
    (h : P.root (Langlands.LinearAlgebra.wordPerm P l₁ d₁) ≠
        -P.root (Langlands.LinearAlgebra.wordPerm P l₂ d₂) ∧
      ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
        (dS : ℤ) • P.root (Langlands.LinearAlgebra.wordPerm P l₁ d₁) +
          (dT : ℤ) • P.root (Langlands.LinearAlgebra.wordPerm P l₂ d₂) ≠ P.root α) :
    PointsCommute (wordConj P u l₁ (weylFamily P W u d₁))
        (wordConj P u l₂ (weylFamily P W u d₂)) ∧
      PointsCommute (wordConj P u' l₁ (weylFamily P W u' d₁))
        (wordConj P u' l₂ (weylFamily P W u' d₂)) := by
  obtain ⟨κ₁, e₁, e₁'⟩ := hU.wordConj_weylFamily hl₁ d₁
  obtain ⟨κ₂, e₂, e₂'⟩ := hU.wordConj_weylFamily hl₂ d₂
  exact ⟨PointsCommute.of_scaleHom (hdG.pointsCommute h.1 h.2) _ _ e₁ e₂,
    PointsCommute.of_scaleHom (hdH.pointsCommute h.1 h.2) _ _ e₁' e₂'⟩

/-- **Pairs of type `G₂` with a short first root.** -/
theorem pairFormula_g2_short [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    (hqinj : ∀ x y, b'.IsPos x → b'.IsPos y → q x = q y → x = y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2, r3, r4⟩ := g2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a (P.reflectionPerm c a)) =
      (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by rw [r2]; simp
  have rd3 : P.root (P.reflectionPerm a c) = (3 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r3]; simp
  have rd4 : P.root (P.reflectionPerm c (P.reflectionPerm a c)) =
      (3 : ℤ) • P.root a + (2 : ℤ) • P.root c := r4
  have hla : ∀ x ∈ [a], x ∈ b.support := by simp [ha]
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  have hlac : ∀ x ∈ [a, c], x ∈ b.support := by simp [ha, hc]
  have hlca : ∀ x ∈ [c, a], x ∈ b.support := by simp [ha, hc]
  obtain ⟨g1, g2, g3, -, -⟩ := hdG.g2_commRels ha hc hac h1 h2
  obtain ⟨k1, k2, k3, -, -⟩ := hdH.g2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.g2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · -- `ε₀ = c`
    rw [eq_of_coeffs hε₀ rc rfl rfl] at hεl
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := a) (d₂ := c) hl
      (by simp) (by simp) _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide)) g1 k1
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, rd3, rd4, Nat.cast_one, Nat.cast_ofNat]
      try module
  · -- `ε₀ = a + c`
    have hε₀' : P.reflectionPerm c a = ε₀ := eq_of_coeffs rd1 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [c]) a = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    have hroot : ∀ t ∈ ([([a, c], a, 2, 1, 1), ([a], c, -3, 2, 1), ([c, a], c, -3, 1, 2)] :
        List (List J × J × R × ℕ × ℕ)),
        P.root (Langlands.LinearAlgebra.wordPerm P (l ++ t.1) t.2.1) =
          (t.2.2.2.1 : ℤ) • P.root β + (t.2.2.2.2 : ℤ) • P.root ε := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      all_goals
        refine root_transport hβl hεl ?_
        simp only [wordPerm_cons, wordPerm_nil, rd2, rd3, rd4, hε₀, Nat.cast_one, Nat.cast_ofNat]
        try module
    have hpos₂ : b'.IsPos (Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c) :=
      isPos_of_combo hβ hε (i := 2) (j := 1) (by norm_num) le_rfl
        (hroot ([a], c, -3, 2, 1) (by simp))
    have hpos₃ : b'.IsPos (Langlands.LinearAlgebra.wordPerm P (l ++ [c, a]) c) :=
      isPos_of_combo hβ hε (i := 1) (j := 2) le_rfl (by norm_num)
        (hroot ([c, a], c, -3, 1, 2) (by simp))
    have hne : Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c ≠
        Langlands.LinearAlgebra.wordPerm P (l ++ [c, a]) c := by
      intro h
      rw [wordPerm_append, wordPerm_append] at h
      have h' := wordPerm_injective l h
      simp only [wordPerm_cons, wordPerm_nil] at h'
      have := coeffs_eq_of_eq hli rd3 rd4 h'
      omega
    rcases lt_trichotomy (q (Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c))
        (q (Langlands.LinearAlgebra.wordPerm P (l ++ [c, a]) c)) with hlt | heq | hgt
    · refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [c]) (d₁ := a) (d₂ := a)
        hl (by simp) hlc _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl) hε' hroot
        (by simp) ?_ g2 k2
      refine .cons ?_ (.cons ?_ (.cons (fun _ h => by simp at h) .nil))
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> exact Or.inl (by norm_num)
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        subst ht
        exact Or.inr hlt
    · exact absurd (hqinj _ _ hpos₂ hpos₃ heq) hne
    · have hc23 := hU.pointsCommute_wordConj hdG hdH hla hlca (d₁ := c) (d₂ := c)
        (noOpp_cone_of_coeffs hli rd3 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
      refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [c]) (d₁ := a) (d₂ := a)
        hl (by simp) hlc [([a, c], a, 2, 1, 1), ([c, a], c, -3, 1, 2), ([a], c, -3, 2, 1)]
        (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl) hε'
        (fun t ht => hroot t (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ⊢
          tauto))
        (by simp) ?_ (CommRel.swap (L₁ := [_]) (L₂ := []) g2 hc23.1)
        (CommRel.swap (L₁ := [_]) (L₂ := []) k2 hc23.2)
      refine .cons ?_ (.cons ?_ (.cons (fun _ h => by simp at h) .nil))
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl <;> exact Or.inl (by norm_num)
      · intro t ht
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        subst ht
        exact Or.inr hgt
  · -- `ε₀ = 2 a + c`
    have hε₀' : P.reflectionPerm a (P.reflectionPerm c a) = ε₀ := eq_of_coeffs rd2 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [a, c]) a = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [a, c]) (d₁ := a) (d₂ := a)
      hl (by simp) hlac _ (by simp [ha]) (by rw [List.append_nil]; exact hβl) hε' ?_
      (by simp) (pairwise_of_exps (by simp)) g3 k3
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd3, hε₀, Nat.cast_one]
    module
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Pairs of type `G₂` with a long first root.** -/
theorem pairFormula_g2_long [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3)
    (hβl : Langlands.LinearAlgebra.wordPerm P l c = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀c : ε₀ ≠ c) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2, r3, r4⟩ := g2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a (P.reflectionPerm c a)) =
      (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by rw [r2]; simp
  have rd3 : P.root (P.reflectionPerm a c) = (3 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r3]; simp
  have rd4 : P.root (P.reflectionPerm c (P.reflectionPerm a c)) =
      (3 : ℤ) • P.root a + (2 : ℤ) • P.root c := r4
  have hla : ∀ x ∈ [a], x ∈ b.support := by simp [ha]
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  have hlac : ∀ x ∈ [a, c], x ∈ b.support := by simp [ha, hc]
  have hlca : ∀ x ∈ [c, a], x ∈ b.support := by simp [ha, hc]
  obtain ⟨g1, -, -, g4, g5⟩ := hdG.g2_commRels ha hc hac h1 h2
  obtain ⟨k1, -, -, k4, k5⟩ := hdH.g2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.g2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · -- `ε₀ = a`: the reversed formula
    rw [eq_of_coeffs hε₀ ra rfl rfl] at hεl
    have c13 := hU.pointsCommute_wordConj hdG hdH hlc hla (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd1 rd3 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c14 := hU.pointsCommute_wordConj hdG hdH hlc hlca (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd1 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c23 := hU.pointsCommute_wordConj hdG hdH hlac hla (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd2 rd3 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c24 := hU.pointsCommute_wordConj hdG hdH hlac hlca (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd2 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    have c34 := hU.pointsCommute_wordConj hdG hdH hla hlca (d₁ := c) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd3 rd4 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := c) (d₂ := a) hl
      (by simp) (by simp)
      [([c], a, -1, 1, 1), ([a, c], a, -1, 1, 2), ([a], c, 1, 1, 3), ([c, a], c, -2, 2, 3)]
      (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide))
      (CommRel.g2_reverse g1 g5 c13.1 c14.1 c23.1 c24.1 c34.1)
      (CommRel.g2_reverse k1 k5 c13.2 c14.2 c23.2 c24.2 c34.2)
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, rd3, rd4, Nat.cast_one, Nat.cast_ofNat]
      try module
  · exact absurd (eq_of_coeffs hε₀ rc rfl rfl) hε₀c
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · -- `ε₀ = 3 a + c`
    have hε₀' : P.reflectionPerm a c = ε₀ := eq_of_coeffs rd3 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [a]) c = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [a]) (d₁ := c) (d₂ := c)
      hl (by simp) hla _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl) hε' ?_
      (by simp) (pairwise_of_exps (by simp)) g4 k4
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd4, hε₀, Nat.cast_one]
    module
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Pairs of type `B₂` with a short first root.** -/
theorem pairFormula_b2_short [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2⟩ := b2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a c) = (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r2]; simp
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  obtain ⟨g1, g2⟩ := hdG.b2_commRels ha hc hac h1 h2
  obtain ⟨k1, k2⟩ := hdH.b2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.b2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · -- `ε₀ = c`
    rw [eq_of_coeffs hε₀ rc rfl rfl] at hεl
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := a) (d₂ := c) hl
      (by simp) (by simp) _ (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide)) g1 k1
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, Nat.cast_one, Nat.cast_ofNat]
      try module
  · -- `ε₀ = a + c`
    have hε₀' : P.reflectionPerm c a = ε₀ := eq_of_coeffs rd1 hε₀ rfl rfl
    have hε' : Langlands.LinearAlgebra.wordPerm P (l ++ [c]) a = ε := by
      rw [wordPerm_append, wordPerm_cons, wordPerm_nil, hε₀', hεl]
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := [c]) (d₁ := a) (d₂ := a)
      hl (by simp) hlc _ (by simp [ha]) (by rw [List.append_nil]; exact hβl) hε' ?_
      (by simp) (pairwise_of_exps (by simp)) g2 k2
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd2, hε₀, Nat.cast_one]
    module
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Pairs of type `B₂` with a long first root.** -/
theorem pairFormula_b2_long [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2)
    (hβl : Langlands.LinearAlgebra.wordPerm P l c = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀c : ε₀ ≠ c) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  obtain ⟨r1, r2⟩ := b2_roots h1 h2
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd1 : P.root (P.reflectionPerm c a) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r1]; simp
  have rd2 : P.root (P.reflectionPerm a c) = (2 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [r2]; simp
  have hla : ∀ x ∈ [a], x ∈ b.support := by simp [ha]
  have hlc : ∀ x ∈ [c], x ∈ b.support := by simp [hc]
  obtain ⟨g1, -⟩ := hdG.b2_commRels ha hc hac h1 h2
  obtain ⟨k1, -⟩ := hdH.b2_commRels ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.b2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · -- `ε₀ = a`: the reversed formula
    rw [eq_of_coeffs hε₀ ra rfl rfl] at hεl
    have c12 := hU.pointsCommute_wordConj hdG hdH hlc hla (d₁ := a) (d₂ := c)
      (noOpp_cone_of_coeffs hli rd1 rd2 hΦ (by norm_num) (by intro dS dT h₁ h₂ h; omega))
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := c) (d₂ := a) hl
      (by simp) (by simp) [([c], a, -1, 1, 1), ([a], c, -1, 1, 2)]
      (by simp [ha, hc]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp)
      (pairwise_of_exps (by simp only [List.map_cons, List.map_nil]; decide))
      (CommRel.b2_reverse g1 c12.1) (CommRel.b2_reverse k1 c12.2)
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    all_goals
      refine root_transport hβl hεl ?_
      simp only [wordPerm_cons, wordPerm_nil, rd1, rd2, Nat.cast_one, Nat.cast_ofNat]
      try module
  · exact absurd (eq_of_coeffs hε₀ rc rfl rfl) hε₀c
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl rc hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

omit [IsLocalRing R] in
/-- **Pairs of type `A₂`.** -/
theorem pairFormula_a2 [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -1)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.a2_coeffs ha hc hac h1 h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  have rc : P.root c = (0 : ℤ) • P.root a + (1 : ℤ) • P.root c := by simp
  have rd : P.root (P.reflectionPerm a c) = (1 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
      pairing_eq_of_pairingIn h2]
    module
  have g := hdG.a2_commRel ha hc hac h1 h2
  have k := hdH.a2_commRel ha hc hac h1 h2
  rcases Langlands.LinearAlgebra.a2_coeffs_of_nonneg ha hc hac h1 h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · -- `ε₀ = c`
    rw [eq_of_coeffs hε₀ rc rfl rfl] at hεl
    refine hU.pairFormula_of_standard q hq hβ hε (l₁ := []) (l₂ := []) (d₁ := a) (d₂ := c) hl
      (by simp) (by simp) _ (by simp [ha]) (by rw [List.append_nil]; exact hβl)
      (by rw [List.append_nil]; exact hεl) ?_ (by simp) (pairwise_of_exps (by simp)) g k
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    refine root_transport hβl hεl ?_
    simp only [wordPerm_cons, wordPerm_nil, rd, Nat.cast_one]
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

omit [IsLocalRing R] in
/-- **Pairs of type `A₁ × A₁`.** -/
theorem pairFormula_a1a1 [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) {l : List J} (hl : ∀ c ∈ l, c ∈ b.support)
    {a c ε₀ : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h2 : P.pairingIn ℤ c a = 0)
    (hβl : Langlands.LinearAlgebra.wordPerm P l a = β)
    (hεl : Langlands.LinearAlgebra.wordPerm P l ε₀ = ε) {p₀ q₀ : ℕ}
    (hε₀ : P.root ε₀ = (p₀ : ℤ) • P.root a + (q₀ : ℤ) • P.root c) (hε₀a : ε₀ ≠ a) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hΦ := fun (α : J) (m n : ℤ) (h : P.root α = m • P.root a + n • P.root c) =>
    Langlands.LinearAlgebra.a1a1_coeffs ha hc hac h2 h
  have ra : P.root a = (1 : ℤ) • P.root a + (0 : ℤ) • P.root c := by simp
  rcases Langlands.LinearAlgebra.a1a1_coeffs_of_nonneg ha hc hac h2 (p₀ + q₀)
      (by push_cast; ring) (by positivity) (by positivity) hε₀ with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rw [e1, e2] at hε₀
  · exact absurd (eq_of_coeffs hε₀ ra rfl rfl) hε₀a
  · exact pairFormula_of_commute_coeffs hdG hdH hU q hq hβ hε hl hli hβl hεl ra hε₀ hΦ
      (by norm_num) (by intro dS dT h₁ h₂ h; omega)

/-- **Every pair of distinct positive roots has a good formula.** -/
theorem pairFormula_of_pos [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    {n : ℕ} (q : J → Fin n)
    (hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y)
    (hqinj : ∀ x y, b'.IsPos x → b'.IsPos y → q x = q y → x = y)
    {β ε : J} (hβ : b'.IsPos β) (hε : b'.IsPos ε) (hne : β ≠ ε) :
    PairFormula b' W u u' q β ε := by
  classical
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hli : LinearIndependent ℤ ![P.root β, P.root ε] := by
    by_contra hdep
    rcases RootPairing.IsReduced.eq_or_eq_neg (P := P) β ε hdep with h | h
    · exact hne (P.root.injective h)
    · have h' : β = P.reflectionPerm ε ε := P.root.injective (by
        rw [h, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self])
      rw [h'] at hβ
      exact (RootPairing.Base.IsPos.neg_iff_not (b := b') ε).mp hβ hε
  obtain ⟨l, s₁, s₂, hl, hs₁, hs₂, hs₁₂, hβr, p₀, q₀, hεr⟩ :=
    Langlands.LinearAlgebra.exists_word_rankTwo P b hli
  obtain ⟨ε₀, hεl, hε₀⟩ : ∃ ε₀, Langlands.LinearAlgebra.wordPerm P l ε₀ = ε ∧
      P.root ε₀ = (p₀ : ℤ) • P.root s₁ + (q₀ : ℤ) • P.root s₂ :=
    ⟨Langlands.LinearAlgebra.wordPerm P l.reverse ε, wordPerm_reverse l ε, by
      rw [Langlands.LinearAlgebra.root_wordPerm, hεr, wordReflect_reverse]⟩
  have hβl : Langlands.LinearAlgebra.wordPerm P l s₁ = β :=
    P.root.injective (by rw [Langlands.LinearAlgebra.root_wordPerm, hβr])
  have hε₀s : ε₀ ≠ s₁ := by
    intro h
    apply hne
    rw [← hβl, ← hεl, h]
  have hli₁₂ : LinearIndependent ℤ ![P.root s₁, P.root s₂] :=
    b.linearIndependent_pair_of_ne (i := ⟨s₁, hs₁⟩) (j := ⟨s₂, hs₂⟩)
      (fun h' => hs₁₂ (congrArg Subtype.val h'))
  have hr1 : P.root s₁ ≠ P.root s₂ := fun h => hs₁₂ (P.root.injective h)
  have hr2 : P.root s₁ ≠ -P.root s₂ := by
    intro h
    have := LinearIndependent.pair_iff.mp hli₁₂ 1 1 (by rw [h]; module)
    simp at this
  have hle1 : P.pairingIn ℤ s₁ s₂ ≤ 0 := b.pairingIn_le_zero_of_ne hs₁₂ hs₁ hs₂
  have hle2 : P.pairingIn ℤ s₂ s₁ ≤ 0 := b.pairingIn_le_zero_of_ne hs₁₂.symm hs₂ hs₁
  have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' s₁ s₂ hr1 hr2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  have hε₀' : P.root ε₀ = (q₀ : ℤ) • P.root s₂ + (p₀ : ℤ) • P.root s₁ := by
    rw [hε₀, add_comm]
  rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact pairFormula_a1a1 hdG hdH hU q hq hβ hε hl hs₁ hs₂ hs₁₂ h2 hβl hεl hε₀ hε₀s
  · omega
  · exact pairFormula_a2 hdG hdH hU q hq hβ hε hl hs₁ hs₂ hs₁₂ h1 h2 hβl hεl hε₀ hε₀s
  · omega
  · omega
  · exact pairFormula_b2_short hdG hdH hU q hq hβ hε hl hs₁ hs₂ hs₁₂ h1 h2 hβl hεl hε₀ hε₀s
  · exact pairFormula_b2_long hdG hdH hU q hq hβ hε hl hs₂ hs₁ hs₁₂.symm h2 h1 hβl hεl hε₀'
      hε₀s
  · omega
  · omega
  · exact pairFormula_g2_short hdG hdH hU q hq hqinj hβ hε hl hs₁ hs₂ hs₁₂ h1 h2 hβl hεl hε₀
      hε₀s
  · exact pairFormula_g2_long hdG hdH hU q hq hβ hε hl hs₂ hs₁ hs₁₂.symm h2 h1 hβl hεl hε₀'
      hε₀s

/-- **Common universal coordinates for an enumeration by height.** For an enumeration `pos`
of the positive roots of a base `b'` by increasing `b'`-height, any two positions `k < l` have
the same universal commutator coordinates in the two Weyl families. -/
theorem exists_common_isUnivComm_of_base [Finite J] (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hU : WeylConjugationRelations P b W u u')
    (b' : P.Base) {n : ℕ} (pos : Fin n ≃ {α // b'.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b'.height (pos p : J) ≤ b'.height (pos q : J))
    (k l : Fin n) (hkl : k < l) :
    ∃ E : Fin n → Polynomial (Polynomial R),
      IsUnivComm (weylFamily P W u) (fun k => (pos k : J)) k l E ∧
        IsUnivComm (weylFamily P W u') (fun k => (pos k : J)) k l E := by
  classical
  let q : J → Fin n := fun j => if h : b'.IsPos j then pos.symm ⟨j, h⟩ else k
  have hqpos : ∀ j (h : b'.IsPos j), q j = pos.symm ⟨j, h⟩ := fun j h => by
    simp only [q, h, ↓reduceDIte]
  have hq : ∀ x y, b'.IsPos x → b'.IsPos y → b'.height x < b'.height y → q x < q y := by
    intro x y hx hy hxy
    rw [hqpos x hx, hqpos y hy]
    by_contra hle
    rw [not_lt] at hle
    have := hmono _ _ hle
    simp only [Equiv.apply_symm_apply] at this
    omega
  have hqinj : ∀ x y, b'.IsPos x → b'.IsPos y → q x = q y → x = y := by
    intro x y hx hy hxy
    rw [hqpos x hx, hqpos y hy] at hxy
    exact congrArg Subtype.val (pos.symm.injective hxy)
  have hkl' : (pos k : J) ≠ (pos l : J) :=
    fun h => (ne_of_lt hkl) (pos.injective (Subtype.ext h))
  obtain ⟨L, hLpos, hLsort, hG', hH'⟩ :=
    pairFormula_of_pos hdG hdH hU q hq hqinj (pos k).2 (pos l).2 hkl'
  exact exists_common_isUnivComm (weylFamily P W u) (weylFamily P W u') (fun k => (pos k : J))
    k l L q (fun t ht => by simp only [hqpos t.1 (hLpos t ht), Equiv.apply_symm_apply])
    hLsort hG' hH'

end TwoGroups

end LocalSplitCell

open LocalSplitCell in
/-- **Commutator relations from rank one and Weyl conjugation.** The rank-one normalization
statement and the Weyl-conjugation statement imply the commutator relations of Weyl families
over a local ring. -/
theorem localSplitWeylCommutator_of_weylConjugation
    (hR : LocalSplitRankOneNormalStatement.{u})
    (hC : LocalSplitWeylConjugationStatement.{u}) :
    LocalSplitWeylCommutatorStatement.{u} := by
  intro R _ _ I _ _ J G H _ _ hG hH i i' hi hi' hmax hmax' P hP hP' b W hW u u' hu hw hu' hw'
    n pos hmono
  classical
  have : Finite J := hP.finite
  have hR1 : ∀ a ∈ b.support, RankOneNormal i P u a := hR R G hG I i hi hmax J P hP b u hu hw
  have hR2 : ∀ a ∈ b.support, RankOneNormal i' P u' a :=
    hR R H hH I i' hi' hmax' J P hP' b u' hu' hw'
  have hU := hC R I J G H hG hH i i' hi hi' hmax hmax' P hP hP' b W hW u u' hu hw hu' hw' hR1 hR2
  have hdG : IsNormalSimpleData i P b W u := ⟨hG, hmax, hP, hu, hw, hW, hR1⟩
  have hdH : IsNormalSimpleData i' P b W u' := ⟨hH, hmax', hP', hu', hw', hW, hR2⟩
  exact commutatorRelations_of_isUnivComm hG hmax hP W (fun a ha => (hu a ha).1) hw
    (Finite.equivFin {α // ¬ b.IsPos α}).symm pos
    (fun k l hkl => exists_common_isUnivComm_of_base hdG hdH hU b pos hmono k l hkl)

/-- **Statement: the commutator relations of Weyl families reduce to rank one and Weyl
conjugation.** Over local rings, `LocalSplitRankOneNormalStatement` and
`LocalSplitWeylConjugationStatement` imply `LocalSplitWeylCommutatorStatement`. -/
def LocalSplitWeylCommutatorReductionStatement : Prop :=
  LocalSplitRankOneNormalStatement.{u} → LocalSplitWeylConjugationStatement.{u} →
    LocalSplitWeylCommutatorStatement.{u}

theorem localSplitWeylCommutatorReduction : LocalSplitWeylCommutatorReductionStatement.{u} :=
  localSplitWeylCommutator_of_weylConjugation

end Langlands.GroupScheme
