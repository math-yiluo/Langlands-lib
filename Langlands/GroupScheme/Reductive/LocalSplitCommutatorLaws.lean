import Langlands.GroupScheme.Reductive.LocalSplitPositiveProducts
import Langlands.GroupScheme.Reductive.LocalSplitPositiveLawGluing
import Langlands.GroupScheme.Reductive.LocalWeylNormalizationField

/-! # Laws of the positive cell factors from commutator relations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section ListSplit

variable {M : Type*} [Monoid M]

/-- Splitting an ordered product at a position `k`. -/
theorem prod_ofFn_split {n : ℕ} (f : Fin n → M) (k : Fin n) :
    (List.ofFn f).prod =
      (List.ofFn fun l => if l < k then f l else 1).prod * f k *
        (List.ofFn fun l => if k < l then f l else 1).prod := by
  induction n with
  | zero => exact k.elim0
  | succ n ih =>
    rw [List.ofFn_succ', List.ofFn_succ', List.ofFn_succ', List.prod_concat, List.prod_concat,
      List.prod_concat]
    refine Fin.lastCases ?_ (fun k' => ?_) k
    · have h1 : (List.ofFn fun l : Fin n => if (Fin.castSucc l) < Fin.last n then
          f (Fin.castSucc l) else 1) = List.ofFn fun l => f (Fin.castSucc l) := by
        congr 1
        funext l
        simp only [Fin.castSucc_lt_last, ↓reduceIte]
      have h2 : (List.ofFn fun l : Fin n => if Fin.last n < Fin.castSucc l then
          f (Fin.castSucc l) else 1) = List.ofFn fun _ : Fin n => (1 : M) := by
        congr 1
        funext l
        simp only [not_lt.mpr (Fin.castSucc_lt_last l).le, ↓reduceIte]
      simp only [h1, h2, lt_self_iff_false, ↓reduceIte, List.ofFn_const,
        List.prod_replicate, one_pow, mul_one]
    · have h := ih (fun l => f (Fin.castSucc l)) k'
      have h1 : (List.ofFn fun l : Fin n => if Fin.castSucc l < Fin.castSucc k' then
          f (Fin.castSucc l) else 1) =
          List.ofFn fun l => if l < k' then f (Fin.castSucc l) else 1 := by
        congr 1
      have h2 : (List.ofFn fun l : Fin n => if Fin.castSucc k' < Fin.castSucc l then
          f (Fin.castSucc l) else 1) =
          List.ofFn fun l => if k' < l then f (Fin.castSucc l) else 1 := by
        congr 1
      have hlt : Fin.castSucc k' < Fin.last n := Fin.castSucc_lt_last k'
      have hnlt : ¬ Fin.last n < Fin.castSucc k' := not_lt.mpr hlt.le
      simp only [h1, h2, hlt, hnlt, ↓reduceIte, mul_one]
      rw [h]
      simp only [mul_assoc]

theorem prod_ofFn_one {n : ℕ} : (List.ofFn fun _ : Fin n => (1 : M)).prod = 1 := by
  rw [List.ofFn_const, List.prod_replicate, one_pow]

end ListSplit

section PosGood

variable {R : Type u} [CommRing R] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))}
  (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)) {n : ℕ} (pos : Fin n → J)
  (Z : Over (Spec (CommRingCat.of R)))

/-- A pair `(g, h)` of points of `G` and `H` is *positive-good* if right multiplication by `g`
keeps products of the positive cell factors of `G` in that form, and every resulting law
`P(w) · g = P(z)` of `G` gives `P'(w) · h = P'(z)` in `H`. -/
def PosGood (g : Z ⟶ G.X) (h : Z ⟶ H.X) : Prop :=
  (∀ w : Fin n → Γ(Z.left, ⊤), ∃ z, orderedProduct u pos Z w * g = orderedProduct u pos Z z) ∧
    ∀ w z : Fin n → Γ(Z.left, ⊤), orderedProduct u pos Z w * g = orderedProduct u pos Z z →
      orderedProduct u' pos Z w * h = orderedProduct u' pos Z z

variable {u u' pos Z}

theorem PosGood.one (hinj : Function.Injective (orderedProduct u pos Z)) :
    PosGood u u' pos Z 1 1 := by
  refine ⟨fun w => ⟨w, mul_one _⟩, fun w z h => ?_⟩
  rw [mul_one] at h ⊢
  rw [hinj h]

theorem PosGood.mul {g₁ g₂ : Z ⟶ G.X} {h₁ h₂ : Z ⟶ H.X} (h1 : PosGood u u' pos Z g₁ h₁)
    (h2 : PosGood u u' pos Z g₂ h₂) : PosGood u u' pos Z (g₁ * g₂) (h₁ * h₂) := by
  refine ⟨fun w => ?_, fun w z hwz => ?_⟩
  · obtain ⟨z₁, hz₁⟩ := h1.1 w
    obtain ⟨z, hz⟩ := h2.1 z₁
    exact ⟨z, by rw [← mul_assoc, hz₁, hz]⟩
  · obtain ⟨z₁, hz₁⟩ := h1.1 w
    have e₂ : orderedProduct u pos Z z₁ * g₂ = orderedProduct u pos Z z := by
      rw [← hz₁, mul_assoc, hwz]
    rw [← mul_assoc, h1.2 w z₁ hz₁, h2.2 z₁ z e₂]

theorem PosGood.prod_ofFn (hinj : Function.Injective (orderedProduct u pos Z)) {m : ℕ}
    (f : Fin m → (Z ⟶ G.X)) (f' : Fin m → (Z ⟶ H.X))
    (hf : ∀ l, PosGood u u' pos Z (f l) (f' l)) :
    PosGood u u' pos Z (List.ofFn f).prod (List.ofFn f').prod := by
  induction m with
  | zero => simpa using PosGood.one hinj
  | succ m ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    exact (hf 0).mul (ih _ _ fun l => hf l.succ)

/-- The commutator `(u_k(x) u_l(y))⁻¹ (u_l(y) u_k(x))` of two positive cell factors. -/
def posComm (u : J → (Ga R ⟶ G)) (pos : Fin n → J) (Z : Over (Spec (CommRingCat.of R)))
    (k l : Fin n) (x y : Γ(Z.left, ⊤)) : Z ⟶ G.X :=
  (rootPoint (u (pos k)) Z x * rootPoint (u (pos l)) Z y)⁻¹ *
    (rootPoint (u (pos l)) Z y * rootPoint (u (pos k)) Z x)

theorem inv_mul_rootPoint_mul (u : J → (Ga R ⟶ G)) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n) (x y : Γ(Z.left, ⊤)) :
    (rootPoint (u (pos k)) Z x)⁻¹ * rootPoint (u (pos l)) Z y * rootPoint (u (pos k)) Z x =
      rootPoint (u (pos l)) Z y * posComm u pos Z k l x y := by
  simp only [posComm]
  group

/-- **Right multiplication by a positive cell factor, moved into place.** Right multiplying the
product `P(w)` of the positive cell factors by `u_k(x)` adds `x` to the `k`-th coordinate,
drops the later coordinates, and multiplies on the right by the conjugates of the later
factors, each written as the factor times a commutator. -/
theorem orderedProduct_mul_rootPoint_eq (u : J → (Ga R ⟶ G)) (pos : Fin n → J)
    (Z : Over (Spec (CommRingCat.of R))) (w : Fin n → Γ(Z.left, ⊤)) (k : Fin n)
    (x : Γ(Z.left, ⊤)) :
    orderedProduct u pos Z w * rootPoint (u (pos k)) Z x =
      orderedProduct u pos Z (fun l => if l < k then w l else if l = k then w k + x else 0) *
        (List.ofFn fun l => if k < l then
          rootPoint (u (pos l)) Z (w l) * posComm u pos Z k l x (w l) else 1).prod := by
  set g := rootPoint (u (pos k)) Z x
  set F : Fin n → (Z ⟶ G.X) := fun l => rootPoint (u (pos l)) Z (w l)
  have hP : orderedProduct u pos Z w = (List.ofFn F).prod := rfl
  have hv : orderedProduct u pos Z
      (fun l => if l < k then w l else if l = k then w k + x else 0) =
      (List.ofFn fun l => if l < k then F l else 1).prod * (F k * g) := by
    rw [orderedProduct, prod_ofFn_split _ k]
    have h1 : (List.ofFn fun l => if l < k then rootPoint (u (pos l)) Z
        (if l < k then w l else if l = k then w k + x else 0) else 1) =
        List.ofFn fun l => if l < k then F l else 1 := by
      congr 1
      funext l
      by_cases hlk : l < k
      · simp only [hlk, ↓reduceIte, F]
      · simp only [hlk, ↓reduceIte]
    have h2 : (List.ofFn fun l => if k < l then rootPoint (u (pos l)) Z
        (if l < k then w l else if l = k then w k + x else 0) else 1) =
        List.ofFn fun _ : Fin n => (1 : Z ⟶ G.X) := by
      congr 1
      funext l
      by_cases hkl : k < l
      · simp only [hkl, not_lt.mpr hkl.le, ne_of_gt hkl, ↓reduceIte, rootPoint_zero]
      · simp only [hkl, ↓reduceIte]
    rw [h1, h2, prod_ofFn_one, mul_one]
    simp only [lt_self_iff_false, ↓reduceIte, rootPoint_add, F, g]
  have hT : (List.ofFn fun l => if k < l then
      rootPoint (u (pos l)) Z (w l) * posComm u pos Z k l x (w l) else 1).prod =
      g⁻¹ * (List.ofFn fun l => if k < l then F l else 1).prod * g := by
    have hc : (List.ofFn fun l => if k < l then
        rootPoint (u (pos l)) Z (w l) * posComm u pos Z k l x (w l) else 1) =
        List.map (MulAut.conj g⁻¹) (List.ofFn fun l => if k < l then F l else 1) := by
      rw [List.map_ofFn]
      congr 1
      funext l
      simp only [Function.comp_apply]
      split_ifs
      · rw [← inv_mul_rootPoint_mul, MulAut.conj_apply, inv_inv]
      · rw [map_one]
    rw [hc, ← map_list_prod, MulAut.conj_apply, inv_inv]
  rw [hP, prod_ofFn_split F k, hv, hT]
  group

/-- Products of positive cell factors whose coordinates vanish up to position `k` are
positive-good if all factors after position `k` are. -/
theorem PosGood.orderedProduct (hinj : Function.Injective (orderedProduct u pos Z)) (k : Fin n)
    (IH : ∀ p : Fin n, k < p → ∀ c, PosGood u u' pos Z (rootPoint (u (pos p)) Z c)
      (rootPoint (u' (pos p)) Z c))
    (e : Fin n → Γ(Z.left, ⊤)) (he : ∀ p, p ≤ k → e p = 0) :
    PosGood u u' pos Z (orderedProduct u pos Z e) (orderedProduct u' pos Z e) := by
  refine PosGood.prod_ofFn hinj _ _ fun p => ?_
  by_cases hp : k < p
  · exact IH p hp (e p)
  · rw [he p (not_lt.mp hp), rootPoint_zero, rootPoint_zero]
    exact PosGood.one hinj

/-- Commutators of positive cell factors are products of positive cell factors when right
multiplication by every positive cell factor preserves such products. -/
theorem exists_posComm_eq (hex : ∀ (w : Fin n → Γ(Z.left, ⊤)) (p : Fin n) (c : Γ(Z.left, ⊤)),
      ∃ z, orderedProduct u pos Z w * rootPoint (u (pos p)) Z c = orderedProduct u pos Z z)
    (k l : Fin n) (x y : Γ(Z.left, ⊤)) :
    ∃ e, posComm u pos Z k l x y = orderedProduct u pos Z e := by
  have hc : posComm u pos Z k l x y =
      orderedProduct u pos Z 0 * rootPoint (u (pos l)) Z (-y) * rootPoint (u (pos k)) Z (-x) *
        rootPoint (u (pos l)) Z y * rootPoint (u (pos k)) Z x := by
    rw [orderedProduct_zero, one_mul, rootPoint_neg, rootPoint_neg, posComm]
    group
  obtain ⟨z₁, h₁⟩ := hex 0 l (-y)
  obtain ⟨z₂, h₂⟩ := hex z₁ k (-x)
  obtain ⟨z₃, h₃⟩ := hex z₂ l y
  obtain ⟨z₄, h₄⟩ := hex z₃ k x
  exact ⟨z₄, by rw [hc, h₁, h₂, h₃, h₄]⟩

/-- **Laws of the positive cell factors from commutator relations.** Over a test object `Z`,
suppose the coordinates of products of positive cell factors of `G` are unique, right
multiplication by every positive cell factor preserves such products, and for all positions
`k < l` the commutator `(u_k(x) u_l(y))⁻¹ (u_l(y) u_k(x))` has positive coordinates vanishing
up to position `k`. If moreover every such commutator law of `G` holds with the same
coordinates in `H`, then every positive cell factor `u_k(x)` of `G` and its partner in `H`
form a positive-good pair. -/
theorem posGood_rootPoint (hinj : Function.Injective (orderedProduct u pos Z))
    (hex : ∀ (w : Fin n → Γ(Z.left, ⊤)) (p : Fin n) (c : Γ(Z.left, ⊤)),
      ∃ z, orderedProduct u pos Z w * rootPoint (u (pos p)) Z c = orderedProduct u pos Z z)
    (hsupp : ∀ k l : Fin n, k < l → ∀ (x y : Γ(Z.left, ⊤)) (e : Fin n → Γ(Z.left, ⊤)),
      posComm u pos Z k l x y = orderedProduct u pos Z e → ∀ p, p ≤ k → e p = 0)
    (htrans : ∀ k l : Fin n, k < l → ∀ (x y : Γ(Z.left, ⊤)) (e : Fin n → Γ(Z.left, ⊤)),
      posComm u pos Z k l x y = orderedProduct u pos Z e →
        posComm u' pos Z k l x y = orderedProduct u' pos Z e)
    (k : Fin n) (x : Γ(Z.left, ⊤)) :
    PosGood u u' pos Z (rootPoint (u (pos k)) Z x) (rootPoint (u' (pos k)) Z x) := by
  suffices h : ∀ d : ℕ, ∀ k : Fin n, n - (k : ℕ) ≤ d → ∀ x,
      PosGood u u' pos Z (rootPoint (u (pos k)) Z x) (rootPoint (u' (pos k)) Z x) from
    h _ k le_rfl x
  intro d
  induction d with
  | zero =>
    intro k hk
    have := k.isLt
    omega
  | succ d ih =>
    intro k hk x
    have IH : ∀ p : Fin n, k < p → ∀ c, PosGood u u' pos Z (rootPoint (u (pos p)) Z c)
        (rootPoint (u' (pos p)) Z c) := by
      intro p hp c
      have hp' : (k : ℕ) < p := hp
      exact ih p (by have := p.isLt; omega) c
    refine ⟨fun w => hex w k x, fun w z hwz => ?_⟩
    rw [orderedProduct_mul_rootPoint_eq] at hwz ⊢
    have hX : PosGood u u' pos Z
        (List.ofFn fun l => if k < l then
          rootPoint (u (pos l)) Z (w l) * posComm u pos Z k l x (w l) else 1).prod
        (List.ofFn fun l => if k < l then
          rootPoint (u' (pos l)) Z (w l) * posComm u' pos Z k l x (w l) else 1).prod := by
      refine PosGood.prod_ofFn hinj _ _ fun l => ?_
      by_cases hkl : k < l
      · simp only [hkl, ↓reduceIte]
        obtain ⟨e, he⟩ := exists_posComm_eq hex k l x (w l)
        rw [he, htrans k l hkl x (w l) e he]
        exact (IH l hkl (w l)).mul
          (PosGood.orderedProduct hinj k IH e (hsupp k l hkl x (w l) e he))
      · simp only [hkl, ↓reduceIte]
        exact PosGood.one hinj
    exact hX.2 _ z hwz

end PosGood

section CommutatorSupport

open Polynomial

/-- A polynomial in two variables vanishing on both coordinate axes is divisible by the
product of the variables. Here `B[S][T]` is `Polynomial (Polynomial B)`, with `S = C X` and
`T = X`. -/
theorem exists_eq_X_mul_C_X_mul {B : Type*} [CommRing B] (h : Polynomial (Polynomial B))
    (hT : Polynomial.eval 0 h = 0)
    (hS : Polynomial.map (Polynomial.evalRingHom (0 : B)) h = 0) :
    ∃ r, h = X * C X * r := by
  obtain ⟨h₁, rfl⟩ : X ∣ h := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hT
  have h₁0 : Polynomial.mapRingHom (Polynomial.evalRingHom (0 : B)) h₁ = 0 := by
    rw [Polynomial.map_mul, Polynomial.map_X] at hS
    rw [Polynomial.coe_mapRingHom]
    exact (Polynomial.monic_X.mul_right_eq_zero_iff).mp hS
  have hmem : h₁ ∈ Ideal.span {(C X : Polynomial (Polynomial B))} := by
    have := (RingHom.mem_ker).mpr h₁0
    rw [Polynomial.ker_mapRingHom, Polynomial.ker_evalRingHom, map_zero, sub_zero,
      Ideal.map_span, Set.image_singleton] at this
    exact this
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨r, by rw [← hr, mul_comm r, mul_assoc]⟩

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {ch : J → I → ℤ} {u : J → (Ga R ⟶ G)}
  {m n : ℕ} {neg : Fin m → J} {pos : Fin n → J}

theorem comp_posComm {Z W : Over (Spec (CommRingCat.of R))} (f : W ⟶ Z) (k l : Fin n)
    (x y : Γ(Z.left, ⊤)) :
    f ≫ posComm u pos Z k l x y =
      posComm u pos W k l (f.left.appTop x) (f.left.appTop y) := by
  simp only [posComm, MonObj.comp_mul, GrpObj.comp_inv, comp_rootPoint]

theorem posComm_zero_left (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n)
    (y : Γ(Z.left, ⊤)) : posComm u pos Z k l 0 y = 1 := by
  rw [posComm, rootPoint_zero]
  group

theorem posComm_zero_right (Z : Over (Spec (CommRingCat.of R))) (k l : Fin n)
    (x : Γ(Z.left, ⊤)) : posComm u pos Z k l x 0 = 1 := by
  rw [posComm, rootPoint_zero]
  group

theorem torus_mul_posComm_mul_inv (hu : TorusEquivariant i ch u)
    {Z : Over (Spec (CommRingCat.of R))} (t : Z ⟶ (splitTorus (Spec (CommRingCat.of R)) I).X)
    (k l : Fin n) (x y : Γ(Z.left, ⊤)) :
    (t ≫ i.hom.hom) * posComm u pos Z k l x y * (t ≫ i.hom.hom)⁻¹ =
      posComm u pos Z k l (torusChar (ch (pos k)) Z t * x) (torusChar (ch (pos l)) Z t * y) := by
  rw [posComm, posComm, ← hu (pos k) Z t x, ← hu (pos l) Z t y]
  group

/-- Right translation of the positive cell factor by a positive root point over an arbitrary
ring. -/
theorem exists_orderedProduct_mul_rootPoint_eq_pos_of_ring
    [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) {α : J} (hα : 0 < coPairing (ch α) ν)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (w : Fin n → Γ((Over.mk s).left, ⊤)) (a : Γ((Over.mk s).left, ⊤)) :
    ∃ z : Fin n → Γ((Over.mk s).left, ⊤),
      orderedProduct u pos (Over.mk s) w * rootPoint (u α) (Over.mk s) a =
        orderedProduct u pos (Over.mk s) z := by
  have he : ∀ k, 0 < coPairing (ch ((Fin.snoc pos α : Fin (n + 1) → J) k)) ν := by
    intro k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · rw [Fin.snoc_last]; exact hα
    · rw [Fin.snoc_castSucc]; exact hpos k
  obtain ⟨z, hz⟩ := exists_orderedProduct_eq_pos_of_ring (pos := pos) hu ν hneg _ he s
    (Fin.snoc w a)
  exact ⟨z, by rw [← orderedProduct_snoc, hz]⟩

/-- Coordinates of commutators over a ring, as elements of the ring. -/
theorem exists_posComm_eq_ring [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) {L : Type u} [CommRing L]
    (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)) (k l : Fin n) (a b : L) :
    ∃ c : Fin n → L, posComm u pos (Over.mk s) k l
        ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv b) =
      orderedProduct u pos (Over.mk s)
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (c q)) := by
  obtain ⟨e, he⟩ := exists_posComm_eq (u := u) (pos := pos) (Z := Over.mk s)
    (fun w p c => exists_orderedProduct_mul_rootPoint_eq_pos_of_ring hu ν hneg hpos (hpos p) s w c)
    k l _ _
  refine ⟨fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).hom (e q), ?_⟩
  rw [he]
  congr 1
  funext q
  exact (Iso.hom_inv_id_apply _ _).symm

/-- Pulling back commutator coordinates along a ring map. -/
theorem posComm_specHom {L L' : Type u} [CommRing L] [CommRing L'] (κ : L →+* L')
    {s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R)}
    {s' : Spec (CommRingCat.of L') ⟶ Spec (CommRingCat.of R)}
    (hs : Spec.map (CommRingCat.ofHom κ) ≫ s = s') (k l : Fin n) (a b : L) (c : Fin n → L)
    (h : posComm u pos (Over.mk s) k l
        ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a) ((Scheme.ΓSpecIso (CommRingCat.of L)).inv b) =
      orderedProduct u pos (Over.mk s)
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (c q))) :
    posComm u pos (Over.mk s') k l ((Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ a))
        ((Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ b)) =
      orderedProduct u pos (Over.mk s')
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ (c q))) := by
  have key : ∀ a : L, (specHom κ hs).left.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of L)).inv a) =
      (Scheme.ΓSpecIso (CommRingCat.of L')).inv (κ a) := specMap_appTop_ΓSpecIso_inv κ
  have h' := congrArg (fun g => specHom κ hs ≫ g) h
  simp only [comp_posComm, comp_orderedProduct, key] at h'
  exact h'

/-- Equality of ring coordinates from equality of positive cell products. -/
theorem coord_eq_of_orderedProduct_eq [IsOpenImmersion (cellMap i u neg pos).left]
    {L : Type u} [CommRing L] (s : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R))
    {c c' : Fin n → L}
    (h : orderedProduct u pos (Over.mk s)
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (c q)) =
      orderedProduct u pos (Over.mk s)
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of L)).inv (c' q))) : c = c' := by
  have h' := orderedProduct_pos_injective (i := i) (neg := neg) _ h
  funext q
  have hq := congrArg (Scheme.ΓSpecIso (CommRingCat.of L)).hom (congrFun h' q)
  rwa [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at hq

/-- **Support of commutators of positive cell factors.** Let `ν` be a cocharacter pairing
negatively with the characters of the negative cell factors and positively with those of the
positive ones. Over every ring, the commutator of the positive cell factors at positions `k`
and `l` is a product of positive cell factors whose coordinates vanish at every position `p`
with `⟨ch (pos p), ν⟩ < ⟨ch (pos k), ν⟩ + ⟨ch (pos l), ν⟩`. -/
theorem posComm_coord_eq_zero [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν) (k l : Fin n)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)) (e : Fin n → Γ((Over.mk s).left, ⊤))
    (he : posComm u pos (Over.mk s) k l x y = orderedProduct u pos (Over.mk s) e) (p : Fin n)
    (hp : coPairing (ch (pos p)) ν < coPairing (ch (pos k)) ν + coPairing (ch (pos l)) ν) :
    e p = 0 := by
  classical
  -- the exponents
  obtain ⟨dk, hdk⟩ : ∃ d : ℕ, coPairing (ch (pos k)) ν = d :=
    ⟨_, (Int.toNat_of_nonneg (hpos k).le).symm⟩
  obtain ⟨dl, hdl⟩ : ∃ d : ℕ, coPairing (ch (pos l)) ν = d :=
    ⟨_, (Int.toNat_of_nonneg (hpos l).le).symm⟩
  obtain ⟨dp, hdp⟩ : ∃ d : ℕ, coPairing (ch (pos p)) ν = d :=
    ⟨_, (Int.toNat_of_nonneg (hpos p).le).symm⟩
  have hlt : dp < dk + dl := by
    rw [hdk, hdl, hdp] at hp
    exact_mod_cast hp
  -- ring coordinates
  obtain ⟨x0, rfl⟩ : ∃ x0 : B,
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x0 : Γ((Over.mk s).left, ⊤)) = x :=
    ⟨_, Iso.hom_inv_id_apply _ _⟩
  obtain ⟨y0, rfl⟩ : ∃ y0 : B,
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y0 : Γ((Over.mk s).left, ⊤)) = y :=
    ⟨_, Iso.hom_inv_id_apply _ _⟩
  obtain ⟨e0, rfl⟩ : ∃ e0 : Fin n → B,
      (fun q => ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e0 q) : Γ((Over.mk s).left, ⊤))) =
        e :=
    ⟨fun q => (Scheme.ΓSpecIso (CommRingCat.of B)).hom (e q),
      funext fun q => Iso.hom_inv_id_apply _ _⟩
  suffices h0 : e0 p = 0 by simp only [h0, map_zero]
  -- the two-variable line `B[S][T]`, with the commutator of `u_k(S x)` and `u_l(T y)`
  obtain ⟨s2, hs2⟩ : ∃ s2 : Spec (CommRingCat.of (Polynomial (Polynomial B))) ⟶
      Spec (CommRingCat.of R),
      s2 = Spec.map (CommRingCat.ofHom (Polynomial.C.comp Polynomial.C)) ≫ s := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ := exists_posComm_eq_ring (neg := neg) hu ν hneg hpos s2 k l
    (Polynomial.C (Polynomial.C x0 * Polynomial.X)) (Polynomial.C (Polynomial.C y0) * Polynomial.X)
  -- vanishing at `T = 0`
  have hT : ∀ q, Polynomial.eval 0 (h q) = 0 := by
    have H := posComm_specHom (Polynomial.evalRingHom (0 : Polynomial B)) (s := s2) rfl k l _ _
      h hh
    have hb : Polynomial.evalRingHom (0 : Polynomial B)
        (Polynomial.C (Polynomial.C y0) * Polynomial.X) = 0 := by simp
    rw [hb, map_zero, posComm_zero_right] at H
    have H0 : orderedProduct u pos (Over.mk (Spec.map (CommRingCat.ofHom
        (Polynomial.evalRingHom (0 : Polynomial B))) ≫ s2))
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).inv
          ((0 : Fin n → Polynomial B) q)) = 1 := by
      simp only [Pi.zero_apply, map_zero]
      exact orderedProduct_zero u pos _
    have := coord_eq_of_orderedProduct_eq (i := i) (neg := neg) _ (H0.trans H)
    intro q
    exact (congrFun this q).symm
  -- vanishing at `S = 0`
  have hS : ∀ q, Polynomial.map (Polynomial.evalRingHom (0 : B)) (h q) = 0 := by
    have H := posComm_specHom (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : B)))
      (s := s2) rfl k l _ _ h hh
    have hb : Polynomial.mapRingHom (Polynomial.evalRingHom (0 : B))
        (Polynomial.C (Polynomial.C x0 * Polynomial.X)) = 0 := by simp
    rw [hb, map_zero, posComm_zero_left] at H
    have H0 : orderedProduct u pos (Over.mk (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Polynomial.evalRingHom (0 : B)))) ≫ s2))
        (fun q => (Scheme.ΓSpecIso (CommRingCat.of (Polynomial B))).inv
          ((0 : Fin n → Polynomial B) q)) = 1 := by
      simp only [Pi.zero_apply, map_zero]
      exact orderedProduct_zero u pos _
    have := coord_eq_of_orderedProduct_eq (i := i) (neg := neg) _ (H0.trans H)
    intro q
    exact (congrFun this q).symm
  obtain ⟨r, hr⟩ := exists_eq_X_mul_C_X_mul (h p) (hT p) (hS p)
  -- the diagonal line `S = U ^ dk`, `T = U ^ dl`
  let σ : Polynomial (Polynomial B) →+* Polynomial B :=
    Polynomial.eval₂RingHom (Polynomial.eval₂RingHom Polynomial.C (Polynomial.X ^ dk))
      (Polynomial.X ^ dl)
  have hσC : σ.comp (Polynomial.C.comp Polynomial.C) = Polynomial.C := by
    ext b
    simp [σ]
  have hσs : Spec.map (CommRingCat.ofHom σ) ≫ s2 =
      Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) ≫ s := by
    rw [hs2, specMap_comp_specMap, hσC]
  have H5 := posComm_specHom σ hσs k l _ _ h hh
  have hσx : σ (Polynomial.C (Polynomial.C x0 * Polynomial.X)) =
      Polynomial.C x0 * Polynomial.X ^ dk := by simp [σ]
  have hσy : σ (Polynomial.C (Polynomial.C y0) * Polynomial.X) =
      Polynomial.C y0 * Polynomial.X ^ dl := by simp [σ]
  rw [hσx, hσy] at H5
  have H6 := posComm_specHom (Polynomial.C : B →+* Polynomial B) (s := s) rfl k l x0 y0 e0 he
  -- Laurent polynomials, where `U` is a unit
  have H5L := posComm_specHom (Polynomial.toLaurent (R := B)) rfl k l _ _ _ H5
  have H6L := posComm_specHom (Polynomial.toLaurent (R := B)) rfl k l _ _ _ H6
  set Z := Over.mk (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := B))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* Polynomial B)) ≫ s) with hZ
  set gm := (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial B))).inv with hgm
  let uT : (Γ(Z.left, ⊤))ˣ :=
    Units.map gm.hom.toMonoidHom (LaurentPolynomial.isUnit_T (R := B) 1).unit
  have huT : ((uT : (Γ(Z.left, ⊤))ˣ) : Γ(Z.left, ⊤)) = gm (LaurentPolynomial.T 1) := rfl
  have hpow : ∀ d : ℕ, (gm (LaurentPolynomial.T 1)) ^ d = gm (LaurentPolynomial.T (d : ℤ)) :=
    fun d => by rw [← map_pow, LaurentPolynomial.T_pow, mul_one]
  have hmul : ∀ a b : LaurentPolynomial B,
      ((gm a : Γ(Z.left, ⊤)) * (gm b : Γ(Z.left, ⊤))) = gm (a * b) :=
    fun a b => (map_mul _ a b).symm
  have hχ : ∀ {q : Fin n} {d : ℕ}, coPairing (ch (pos q)) ν = d →
      torusChar (ch (pos q)) Z (cocharPoint ν Z uT) = gm (LaurentPolynomial.T d) := by
    intro q d hd
    rw [torusChar_cocharPoint_of_eq hd, huT]
    exact hpow d
  have Hc := congrArg (fun g => (cocharPoint ν Z uT ≫ i.hom.hom) * g *
    (cocharPoint ν Z uT ≫ i.hom.hom)⁻¹) H6L
  simp only at Hc
  rw [torus_mul_posComm_mul_inv hu, torus_mul_orderedProduct_mul_inv hu, hχ hdk, hχ hdl,
    hmul, hmul] at Hc
  have hxk : LaurentPolynomial.T (dk : ℤ) * Polynomial.toLaurent (Polynomial.C x0) =
      Polynomial.toLaurent (Polynomial.C x0 * Polynomial.X ^ dk) := by
    rw [Polynomial.toLaurent_C_mul_X_pow, Polynomial.toLaurent_C, mul_comm]
  have hyl : LaurentPolynomial.T (dl : ℤ) * Polynomial.toLaurent (Polynomial.C y0) =
      Polynomial.toLaurent (Polynomial.C y0 * Polynomial.X ^ dl) := by
    rw [Polynomial.toLaurent_C_mul_X_pow, Polynomial.toLaurent_C, mul_comm]
  rw [hxk, hyl, H5L] at Hc
  have hinj := orderedProduct_pos_injective (i := i) (neg := neg) (u := u) (pos := pos) Z Hc
  have hpq := congrFun hinj p
  simp only at hpq
  rw [hχ hdp, hmul] at hpq
  have hpq' := congrArg (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial B))).hom hpq
  rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply] at hpq'
  have hL : σ (h p) = Polynomial.X ^ dp * Polynomial.C (e0 p) := by
    apply Polynomial.toLaurent_injective
    rw [hpq', map_mul, Polynomial.toLaurent_X_pow]
  have hσr : σ (h p) = Polynomial.X ^ (dl + dk) * σ r := by
    rw [hr]
    simp [σ, pow_add, mul_assoc]
    ring
  have hcoeff := congrArg (fun f => Polynomial.coeff f dp) (hσr.symm.trans hL)
  simp only [Polynomial.coeff_X_pow_mul', Polynomial.coeff_C_zero, le_refl, ↓reduceIte,
    Nat.sub_self] at hcoeff
  simp only [show ¬ (dl + dk ≤ dp) by omega, ↓reduceIte] at hcoeff
  exact hcoeff.symm

/-- Commutator coordinates vanish up to position `k` for an enumeration of the positive cell
factors whose pairings with `ν` increase. -/
theorem posComm_coord_eq_zero_of_monotone [IsOpenImmersion (cellMap i u neg pos).left]
    (hu : TorusEquivariant i ch u) (ν : I → ℤ) (hneg : ∀ k, coPairing (ch (neg k)) ν < 0)
    (hpos : ∀ k, 0 < coPairing (ch (pos k)) ν)
    (hmono : ∀ p q : Fin n, p ≤ q → coPairing (ch (pos p)) ν ≤ coPairing (ch (pos q)) ν)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (k l : Fin n) (x y : Γ((Over.mk s).left, ⊤)) (e : Fin n → Γ((Over.mk s).left, ⊤))
    (he : posComm u pos (Over.mk s) k l x y = orderedProduct u pos (Over.mk s) e) (p : Fin n)
    (hp : p ≤ k) : e p = 0 :=
  posComm_coord_eq_zero hu ν hneg hpos k l s x y e he p
    (by have := hmono p k hp; have := hpos l; omega)

end CommutatorSupport

section WeylFamilies

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Commutator relations of the positive cell factors of the Weyl families transfer from `G`
to `H`: over local test rings with separably closed residue fields, for all positions
`k < l`, every expression of the commutator of `u_W(pos k)(x)` and `u_W(pos l)(y)` as a
product of positive cell factors of `G` holds with the same coordinates in `H`. -/
def CommutatorRelations (b : P.Base) (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G))
    (u' : J → (Ga R ⟶ H)) {n : ℕ} (pos : Fin n → J) : Prop :=
  ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
    (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (k l : Fin n), k < l →
    ∀ (x y : Γ((Over.mk s).left, ⊤)) (e : Fin n → Γ((Over.mk s).left, ⊤)),
    posComm (weylFamily P W u) pos (Over.mk s) k l x y =
        orderedProduct (weylFamily P W u) pos (Over.mk s) e →
      posComm (weylFamily P W u') pos (Over.mk s) k l x y =
        orderedProduct (weylFamily P W u') pos (Over.mk s) e

/-- The commutator relations give the positive-factor laws of the Weyl families, for an
enumeration of the positive roots by increasing height and words that are trivial on the
simple roots. -/
theorem positiveLawRelations_of_commutatorRelations (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) {b : P.Base} (W : ∀ α, SimpleWord P b α)
    (hW : ∀ a ∈ b.support, (W a).simple = a ∧ (W a).word = [])
    {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}
    (hu : ∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a))
    (hw : ∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a))
    {m n : ℕ} (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α})
    (hmono : ∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J))
    (hC : CommutatorRelations b W u u' (fun k => (pos k : J))) :
    PositiveLawRelations b W u u' (fun k => (pos k : J)) := by
  have hWf := isRootParametrization_weylFamily hu hw W
  have := LocalSplitBigCell.isOpenImmersion_cellMap hG hmax hP b _ hWf neg pos
  obtain ⟨d, hd, ν, hν⟩ := exists_coPairing_eq_height P b
  have hneg : ∀ k, coPairing (P.root (neg k : J)) ν < 0 := by
    intro k
    rw [hν]
    have h0 := b.height_ne_zero (neg k : J)
    have h1 := (neg k).2
    rw [RootPairing.Base.isPos_iff] at h1
    exact mul_neg_of_pos_of_neg hd (by omega)
  have hpos : ∀ k, 0 < coPairing (P.root (pos k : J)) ν := by
    intro k
    rw [hν]
    exact mul_pos hd (pos k).2
  have hmono' : ∀ p q : Fin n, p ≤ q →
      coPairing (P.root (pos p : J)) ν ≤ coPairing (P.root (pos q : J)) ν := by
    intro p q hpq
    rw [hν, hν]
    exact mul_le_mul_of_nonneg_left (hmono p q hpq) hd.le
  have hequiv : TorusEquivariant i (fun α => P.root α) (weylFamily P W u) :=
    fun α Z t c => (hWf α).equivariant Z t c
  intro A _ _ _ s a ha c w z hwz
  obtain ⟨k, hk⟩ : ∃ k, (pos k : J) = a :=
    ⟨pos.symm ⟨a, RootPairing.Base.isPos_of_mem_support ha⟩, by simp⟩
  have hWa : ∀ v : J → (Ga R ⟶ G), weylFamily P W v a = v a := by
    intro v
    rw [weylFamily, (hW a ha).2, wordConj, (hW a ha).1]
  have hWa' : ∀ v : J → (Ga R ⟶ H), weylFamily P W v a = v a := by
    intro v
    rw [weylFamily, (hW a ha).2, wordConj, (hW a ha).1]
  have hgood := posGood_rootPoint (u := weylFamily P W u) (u' := weylFamily P W u')
    (pos := fun k => (pos k : J)) (Z := Over.mk s)
    (orderedProduct_pos_injective (i := i) (neg := fun k => (neg k : J)) _)
    (fun w q c => exists_orderedProduct_mul_rootPoint_eq_pos (neg := fun k => (neg k : J))
      hequiv ν hneg hpos (hpos q) s w c)
    (fun k l _ x y e he p hp => posComm_coord_eq_zero_of_monotone (neg := fun k => (neg k : J))
      hequiv ν hneg hpos hmono' s k l x y e he p hp)
    (fun k l hkl x y e he => hC A s k l hkl x y e he) k c
  rw [hk, hWa, hWa'] at hgood
  exact hgood.2 w z hwz

end WeylFamilies

end LocalSplitCell

open LocalSplitCell in
/-- Big-cell gluing over an arbitrary commutative ring from commutator relations of the
positive cell factors. Let `G` and `H` be reductive with fibrewise maximal coordinate split
tori `i`, `i'` carrying the same fibrewise root datum `P`, and take Weyl-normalized simple-root
data `u`, `u'` for a base `b`, with words `W` that are trivial on the simple roots. Enumerate the
positive roots by increasing height. Suppose that, over local test rings with separably closed
residue fields, every expression of the commutator of two positive cell factors of the Weyl
family of `G` as a product of positive cell factors also holds in `H`, and that right
translation by the points `u_{-a}(-1)` transfers relations between big-cell points. Then
`G ≅ H` matching the two big-cell maps. -/
def LocalSplitCommutatorLawIsomorphismStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (J : Type u)
    (G H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom] [IsAffineHom H.X.hom],
    IsReductive G → IsReductive H →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
      (i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H),
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
      IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i' →
      ∀ (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G i P → IsFibrewiseRootDatumOf I H i' P →
      ∀ (b : P.Base) (W : ∀ α, SimpleWord P b α),
      (∀ a ∈ b.support, (W a).simple = a ∧ (W a).word = []) →
      ∀ (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)),
      (∀ a ∈ b.support, IsRootParametrization i (P.root a) (u a)) →
      (∀ a ∈ b.support, IsWeylPoint i (rootWeylPoint P u a) (P.reflection a)) →
      (∀ a ∈ b.support, IsRootParametrization i' (P.root a) (u' a)) →
      (∀ a ∈ b.support, IsWeylPoint i' (rootWeylPoint P u' a) (P.reflection a)) →
      ∀ (m n : ℕ) (neg : Fin m ≃ {α // ¬ b.IsPos α}) (pos : Fin n ≃ {α // b.IsPos α}),
      (∀ p q : Fin n, p ≤ q → b.height (pos p : J) ≤ b.height (pos q : J)) →
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
        (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) (k l : Fin n), k < l →
        ∀ (x y : Γ((Over.mk s).left, ⊤)) (e : Fin n → Γ((Over.mk s).left, ⊤)),
        posComm (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) k l x y =
            orderedProduct (weylFamily P W u) (fun k => (pos k : J)) (Over.mk s) e →
          posComm (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) k l x y =
            orderedProduct (weylFamily P W u') (fun k => (pos k : J)) (Over.mk s) e) →
      (∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsSepClosed (IsLocalRing.ResidueField A)]
        (s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
        (x y : Over.mk s ⟶ cellObj R I m n) (a : J), a ∈ b.support →
        (x ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J))) *
            rootPoint (u (P.reflectionPerm a a)) (Over.mk s) (-1) =
          y ≫ cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) →
        (x ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) *
            rootPoint (u' (P.reflectionPerm a a)) (Over.mk s) (-1) =
          y ≫ cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))) →
      ∃ ψ : G ≅ H,
        cellMap i (weylFamily P W u) (fun k => (neg k : J)) (fun k => (pos k : J)) ≫
            ψ.hom.hom.hom =
          cellMap i' (weylFamily P W u') (fun k => (neg k : J)) (fun k => (pos k : J))

/-- Commutator relations of the positive cell factors and the negative simple relations
suffice for big-cell gluing of the Weyl families. -/
theorem localSplitCommutatorLawIsomorphism :
    LocalSplitCommutatorLawIsomorphismStatement.{u} := by
  intro R _ I _ _ J G H _ _ hG hH i i' hmax hmax' P hP hP' b W hW u u' hu hw hu' hw' m n neg pos
    hmono hC hN
  exact localSplitPositiveLawIsomorphism R I J G H hG hH i i' hmax hmax' P hP hP' b W u u'
    hu hw hu' hw' m n neg pos
    (LocalSplitCell.positiveLawRelations_of_commutatorRelations hG hmax hP W hW hu hw neg pos
      hmono hC) hN

end Langlands.GroupScheme
