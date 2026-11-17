import Langlands.GroupScheme.Reductive.LocalSplitWeylCommutatorReduction
import Langlands.GroupScheme.Reductive.LocalRootParametrizationRigidity
import Langlands.GroupScheme.Reductive.LocalSplitFieldComparison

/-! # Common rescalings along words, rank-two Weyl actions and braid relations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Basic

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The sign `(-1)^k` as a unit of a ring. -/
def signUnit (R : Type u) [CommRing R] (k : ℤ) : Rˣ :=
  Units.map (Int.castRingHom R).toMonoidHom k.negOnePow

theorem signUnit_val (k : ℤ) : (signUnit R k : R) = ((k.negOnePow : ℤˣ) : ℤ) := rfl

theorem signUnit_add (k l : ℤ) : signUnit R (k + l) = signUnit R k * signUnit R l := by
  rw [signUnit, signUnit, signUnit, Int.negOnePow_add, map_mul]

theorem signUnit_neg (k : ℤ) : signUnit R (-k) = signUnit R k := by
  rw [signUnit, signUnit, Int.negOnePow_neg]

theorem signUnit_even {k : ℤ} (h : Even k) : signUnit R k = 1 := by
  rw [signUnit, Int.negOnePow_even _ h, map_one]

theorem signUnit_odd {k : ℤ} (h : Odd k) : signUnit R k = -1 := by
  apply Units.ext
  rw [signUnit_val, Int.negOnePow_odd _ h]
  simp

theorem signUnit_mul_self (k : ℤ) : signUnit R k * signUnit R k = 1 := by
  rw [← signUnit_add]
  exact signUnit_even ⟨k, rfl⟩

theorem negOnePow_smul_eq (Z : Over (Spec (CommRingCat.of R))) (k : ℤ) (x : Γ(Z.left, ⊤)) :
    k.negOnePow • x = baseScalar Z (signUnit R k : R) * x := by
  rw [signUnit_val, map_intCast, Units.smul_def, zsmul_eq_mul]

/-- The test scheme `Spec R` over itself. -/
abbrev baseTest (R : Type u) [CommRing R] : Over (Spec (CommRingCat.of R)) :=
  Over.mk (𝟙 (Spec (CommRingCat.of R)))

theorem baseScalar_baseTest_injective : Function.Injective (baseScalar (baseTest R)) := by
  intro x y h
  have hb : ∀ z : R, baseScalar (baseTest R) z = (Scheme.ΓSpecIso (CommRingCat.of R)).inv z := by
    intro z
    simp [baseScalar, baseTest]
  rw [hb, hb] at h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom h
  simpa using this

theorem baseScalar_baseTest (z : R) :
    baseScalar (baseTest R) z = (Scheme.ΓSpecIso (CommRingCat.of R)).inv z := by
  simp [baseScalar, baseTest]

/-- **Rigidity at the base point.** Two parametrizations of the same root over a local ring
satisfy `w = (x ↦ κ x) ≫ z` as soon as `w(1) = z(κ)` over the base. -/
theorem eq_scaleHom_of_base [IsLocalRing R] [IsAffineHom G.X.hom]
    (hP : IsFibrewiseRootDatumOf I G i P) {α : J} {w z : Ga R ⟶ G}
    (hw : IsRootParametrization i (P.root α) w) (hz : IsRootParametrization i (P.root α) z)
    (κ : Rˣ)
    (h : rootPoint w (baseTest R) 1 = rootPoint z (baseTest R) (baseScalar (baseTest R) κ)) :
    w = scaleHom (κ : R) ≫ z := by
  obtain ⟨κ₀, hκ₀, -⟩ := hw.existsUnique_unit_of_rootDatum hP α hz
  have h' := h
  rw [hκ₀, rootPoint_scaleHom, mul_one] at h'
  have := baseScalar_baseTest_injective (hz.rootPoint_injective _ h')
  rw [hκ₀, Units.val_injective this]

/-- Conjugation along a word is conjugation by the product of the Weyl points of its
letters. -/
def wordBase (u : J → (Ga R ⟶ G)) (l : List J) : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X :=
  (l.map fun j => rootWeylPoint P u j).prod

omit [Fintype I] in
theorem wordConj_eq_innerIso (u : J → (Ga R ⟶ G)) (l : List J) (w : Ga R ⟶ G) :
    wordConj P u l w = w ≫ (G.innerIso (wordBase (P := P) u l)).hom := by
  induction l with
  | nil =>
    simp only [wordConj, wordBase, List.map_nil, List.prod_nil]
    rw [GroupScheme.innerIso_one_hom, Category.comp_id]
  | cons j l ih =>
    simp only [wordConj, wordBase, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih, GroupScheme.innerIso_mul_hom, Category.assoc]

omit [Fintype I] in
theorem wordConj_congr_of_wordBase {u : J → (Ga R ⟶ G)} {l l' : List J}
    (h : wordBase (P := P) u l = wordBase (P := P) u l') (w : Ga R ⟶ G) :
    wordConj P u l w = wordConj P u l' w := by
  rw [wordConj_eq_innerIso, wordConj_eq_innerIso, h]

/-- **Squares of simple Weyl points.** Conjugation by `n_a²` acts on a parametrization of a
root `β` by the sign `(-1)^⟨β, a^∨⟩`. -/
theorem wordConj_sq [IsLocalRing R] [IsAffineHom G.X.hom] (hP : IsFibrewiseRootDatumOf I G i P)
    {u : J → (Ga R ⟶ G)}
    {a : J} (hN : RankOneNormal i P u a) {β : J} {w : Ga R ⟶ G}
    (hw : IsRootParametrization i (P.root β) w) :
    wordConj P u [a, a] w = scaleHom (signUnit R (P.pairingIn ℤ β a) : R) ≫ w := by
  apply hom_ext_rootPoint
  intro Z x
  rw [rootPoint_wordConj, rootPoint_scaleHom, ← negOnePow_smul_eq]
  have := conj_sq_rootPoint hP hN.2.2 hw Z x
  simp only [wordPoint, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact this

end Basic

section Univ

variable {R : Type u} [CommRing R] {I : Type u} {J : Type u}
  {G H : GroupScheme (Spec (CommRingCat.of R))} {P : RootDatum J (I → ℤ) (I → ℤ)}

theorem scaleHom_cancel {X Y : Ga R ⟶ G} (κ : Rˣ) (h : scaleHom (κ : R) ≫ X = Y) :
    X = scaleHom (↑κ⁻¹ : R) ≫ Y := by
  rw [← h, ← Category.assoc, scaleHom_comp_scaleHom, Units.mul_inv, scaleHom_one,
    Category.id_comp]

variable (P) in
/-- **Common rescaling along a word.** Conjugation along the word `l` carries `w₁` to `w₂` in
`G` and `z₁` to `z₂` in `H`, up to the same unit `κ`. -/
def UnivRel (u : J → (Ga R ⟶ G)) (u' : J → (Ga R ⟶ H)) (l : List J) (w₁ w₂ : Ga R ⟶ G)
    (z₁ z₂ : Ga R ⟶ H) : Prop :=
  ∃ κ : Rˣ, wordConj P u l w₁ = scaleHom (κ : R) ≫ w₂ ∧
    wordConj P u' l z₁ = scaleHom (κ : R) ≫ z₂

variable {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

theorem UnivRel.of_eq {l : List J} {w₁ w₂ : Ga R ⟶ G} {z₁ z₂ : Ga R ⟶ H}
    (h₁ : wordConj P u l w₁ = w₂) (h₂ : wordConj P u' l z₁ = z₂) :
    UnivRel P u u' l w₁ w₂ z₁ z₂ :=
  ⟨1, by rw [Units.val_one, scaleHom_one, Category.id_comp, h₁],
    by rw [Units.val_one, scaleHom_one, Category.id_comp, h₂]⟩

theorem UnivRel.refl (w : Ga R ⟶ G) (z : Ga R ⟶ H) : UnivRel P u u' [] w w z z :=
  UnivRel.of_eq rfl rfl

theorem UnivRel.trans {l₁ l₂ : List J} {w₁ w₂ w₃ : Ga R ⟶ G} {z₁ z₂ z₃ : Ga R ⟶ H}
    (h : UnivRel P u u' l₁ w₁ w₂ z₁ z₂) (h' : UnivRel P u u' l₂ w₂ w₃ z₂ z₃) :
    UnivRel P u u' (l₂ ++ l₁) w₁ w₃ z₁ z₃ := by
  obtain ⟨κ, e₁, e₂⟩ := h
  obtain ⟨κ', e₁', e₂'⟩ := h'
  refine ⟨κ' * κ, ?_, ?_⟩
  · rw [wordConj_append, e₁, wordConj_scaleHom, e₁', ← Category.assoc, scaleHom_comp_scaleHom,
      Units.val_mul]
  · rw [wordConj_append, e₂, wordConj_scaleHom, e₂', ← Category.assoc, scaleHom_comp_scaleHom,
      Units.val_mul]

theorem UnivRel.cancel {l₁ l₂ : List J} {w₁ w₂ w₃ : Ga R ⟶ G} {z₁ z₂ z₃ : Ga R ⟶ H}
    (h : UnivRel P u u' (l₂ ++ l₁) w₁ w₃ z₁ z₃) (h' : UnivRel P u u' l₁ w₁ w₂ z₁ z₂) :
    UnivRel P u u' l₂ w₂ w₃ z₂ z₃ := by
  obtain ⟨κ, e₁, e₂⟩ := h
  obtain ⟨κ₀, f₁, f₂⟩ := h'
  rw [wordConj_append, f₁, wordConj_scaleHom] at e₁
  rw [wordConj_append, f₂, wordConj_scaleHom] at e₂
  refine ⟨κ₀⁻¹ * κ, ?_, ?_⟩
  · rw [scaleHom_cancel κ₀ e₁, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_mul,
      mul_comm]
  · rw [scaleHom_cancel κ₀ e₂, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_mul,
      mul_comm]

theorem UnivRel.rescale {l : List J} {w₁ w₂ w₃ : Ga R ⟶ G} {z₁ z₂ z₃ : Ga R ⟶ H}
    (h : UnivRel P u u' l w₁ w₂ z₁ z₂) (κ₀ : Rˣ) (hw : w₂ = scaleHom (κ₀ : R) ≫ w₃)
    (hz : z₂ = scaleHom (κ₀ : R) ≫ z₃) : UnivRel P u u' l w₁ w₃ z₁ z₃ := by
  obtain ⟨κ, e₁, e₂⟩ := h
  refine ⟨κ₀ * κ, ?_, ?_⟩
  · rw [e₁, hw, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_mul]
  · rw [e₂, hz, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_mul]

theorem UnivRel.congr_word {l l' : List J} {w₁ w₂ : Ga R ⟶ G} {z₁ z₂ : Ga R ⟶ H}
    (h : UnivRel P u u' l w₁ w₂ z₁ z₂) (hG : wordConj P u l w₁ = wordConj P u l' w₁)
    (hH : wordConj P u' l z₁ = wordConj P u' l' z₁) : UnivRel P u u' l' w₁ w₂ z₁ z₂ := by
  obtain ⟨κ, e₁, e₂⟩ := h
  exact ⟨κ, hG ▸ e₁, hH ▸ e₂⟩

/-- **Inversion of a one-letter rescaling**, given the action of the square of the letter. -/
theorem UnivRel.inv {k : J} {w₁ w₂ : Ga R ⟶ G} {z₁ z₂ : Ga R ⟶ H}
    (h : UnivRel P u u' [k] w₁ w₂ z₁ z₂) (hsq : UnivRel P u u' [k, k] w₁ w₁ z₁ z₁) :
    UnivRel P u u' [k] w₂ w₁ z₂ z₁ :=
  UnivRel.cancel (l₁ := [k]) (l₂ := [k]) hsq h

end Univ

section RankTwo

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [IsAffineHom H.X.hom] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
theorem pairingIn_eq_pairing (x y : J) : P.pairingIn ℤ x y = P.pairing x y := by
  rw [← P.algebraMap_pairingIn ℤ]
  rfl

omit [IsLocalRing R] in
theorem IsNormalSimpleData.isRootParametrization_wordConj (hd : IsNormalSimpleData i P b W u)
    {l : List J} (hl : ∀ c ∈ l, c ∈ b.support) {β : J} {w : Ga R ⟶ G}
    (hw : IsRootParametrization i (P.root β) w) :
    IsRootParametrization i (P.root (Langlands.LinearAlgebra.wordPerm P l β))
      (wordConj P u l w) := by
  rw [Langlands.LinearAlgebra.root_wordPerm]
  exact _root_.Langlands.GroupScheme.LocalSplitCell.isRootParametrization_wordConj l
    (fun j hj => hd.weyl j (hl j hj)) hw

/-- **Squares in both groups.** -/
theorem univRel_sq (hdG : IsNormalSimpleData i P b W u) (hdH : IsNormalSimpleData i' P b W u')
    {k : J} (hk : k ∈ b.support) {β : J} {w : Ga R ⟶ G} {z : Ga R ⟶ H}
    (hw : IsRootParametrization i (P.root β) w) (hz : IsRootParametrization i' (P.root β) z) :
    UnivRel P u u' [k, k] w w z z :=
  ⟨signUnit R (P.pairingIn ℤ β k), wordConj_sq hdG.rootDatum (hdG.rankOne k hk) hw,
    wordConj_sq hdH.rootDatum (hdH.rankOne k hk) hz⟩

/-- **Inversion of a one-letter rescaling between root parametrizations.** -/
theorem UnivRel.inv_of_param (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') {k : J} (hk : k ∈ b.support) {β : J}
    {w₁ w₂ : Ga R ⟶ G} {z₁ z₂ : Ga R ⟶ H}
    (hw : IsRootParametrization i (P.root β) w₁) (hz : IsRootParametrization i' (P.root β) z₁)
    (h : UnivRel P u u' [k] w₁ w₂ z₁ z₂) : UnivRel P u u' [k] w₂ w₁ z₂ z₁ :=
  h.inv (univRel_sq hdG hdH hk hw hz)

/-- **Commuting root groups are fixed.** If a root `β` is orthogonal to the simple root `c`
and neither `β + ℕc` nor `β - ℕc` meets a root in the relevant cones, conjugation by `n_c` fixes
every parametrization of `β`. -/
theorem IsNormalSimpleData.wordConj_fix (hd : IsNormalSimpleData i P b W u) {c : J}
    (hc : c ∈ b.support) {β : J} {w : Ga R ⟶ G} (hw : IsRootParametrization i (P.root β) w)
    (hpair : P.pairingIn ℤ β c = 0) (h₁ : P.root β ≠ -P.root c)
    (hc₁ : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root c ≠ P.root α)
    (h₂ : P.root β ≠ -P.root (P.reflectionPerm c c))
    (hc₂ : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root β + (dT : ℤ) • P.root (P.reflectionPerm c c) ≠ P.root α) :
    wordConj P u [c] w = w := by
  classical
  have hrc : P.root (P.reflectionPerm c c) = -P.root c := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hβc : β ≠ c := by
    rintro rfl
    exact h₂ (by rw [hrc, neg_neg])
  have hβnc : β ≠ P.reflectionPerm c c := by
    rintro rfl
    exact h₁ hrc
  have hcnc : c ≠ P.reflectionPerm c c := by
    intro h
    have := congrArg P.root h
    rw [hrc] at this
    exact P.ne_zero c (by
      have h2 : (2 : ℤ) • P.root c = 0 := by rw [two_smul]; nth_rw 1 [this]; exact neg_add_cancel _
      exact (smul_eq_zero.mp h2).resolve_left (by norm_num))
  let v : J → (Ga R ⟶ G) := Function.update (Function.update (weylFamily P W u)
    (P.reflectionPerm c c) (u (P.reflectionPerm c c))) β w
  have hvβ : v β = w := by simp only [v, Function.update_self]
  have hvnc : v (P.reflectionPerm c c) = u (P.reflectionPerm c c) := by
    simp only [v, Function.update_of_ne hβnc.symm, Function.update_self]
  have hvc : v c = u c := by
    simp only [v, Function.update_of_ne hβc.symm, Function.update_of_ne hcnc]
    exact hd.weylFamily_simple hc
  have hv : ∀ α, IsRootParametrization i (P.root α) (v α) := by
    intro α
    by_cases hα : α = β
    · subst hα
      rw [hvβ]
      exact hw
    · by_cases hα' : α = P.reflectionPerm c c
      · subst hα'
        rw [hvnc]
        exact (hd.param c hc).2
      · simp only [v, Function.update_of_ne hα, Function.update_of_ne hα']
        exact hd.isRootParametrization α
  have e₁ := rootPoint_commute_of_forall_ne hd.reductive hd.maximal hd.rootDatum hv h₁ hc₁
    (𝟙 (Spec (CommRingCat.of R))) 1 1
  have e₂ := rootPoint_commute_of_forall_ne hd.reductive hd.maximal hd.rootDatum hv h₂ hc₂
    (𝟙 (Spec (CommRingCat.of R))) 1 (-1)
  rw [hvβ, hvc] at e₁
  rw [hvβ, hvnc] at e₂
  have hroot : Langlands.LinearAlgebra.wordPerm P [c] β = β := by
    apply P.root.injective
    rw [Langlands.LinearAlgebra.root_wordPerm]
    change P.reflection c (P.root β) = P.root β
    rw [RootPairing.reflection_apply_root, pairing_eq_of_pairingIn hpair, zero_smul, sub_zero]
  have hw' := hd.isRootParametrization_wordConj (l := [c]) (by simpa using hc) hw
  rw [hroot] at hw'
  have key := eq_scaleHom_of_base hd.rootDatum hw' hw 1 (by
    rw [Units.val_one, map_one, rootPoint_wordConj]
    simp only [wordPoint, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      rootWeylPoint, constantPoint_weylPoint]
    have hcomm : Commute
        (rootPoint (u (P.reflectionPerm c c)) (baseTest R) (-1) * rootPoint (u c) (baseTest R) 1 *
          rootPoint (u (P.reflectionPerm c c)) (baseTest R) (-1)) (rootPoint w (baseTest R) 1) :=
      ((Commute.mul_left e₂.symm e₁.symm).mul_left e₂.symm)
    rw [hcomm.eq, mul_inv_cancel_right])
  rw [key, Units.val_one, scaleHom_one, Category.id_comp]

/-- **Weyl action in type `A₂`.** For simple roots `c`, `j` with Cartan entries `-1`,
`n_c u_j n_c⁻¹ = u'` where `u'(x) = n_j u_c(-x) n_j⁻¹`. -/
theorem IsNormalSimpleData.wordConj_a2 (hd : IsNormalSimpleData i P b W u) {c j : J}
    (hc : c ∈ b.support) (hj : j ∈ b.support) (hcj : c ≠ j)
    (h1 : P.pairingIn ℤ c j = -1) (h2 : P.pairingIn ℤ j c = -1) :
    wordConj P u [c] (u j) = scaleHom ((-1 : Rˣ) : R) ≫ wordConj P u [j] (u c) := by
  obtain ⟨v, hv, hvc, hvj, hvnc, hvnj⟩ := hd.exists_family hc hj hcj
  have hnc : IsWeylPoint i (weylPoint (v c) (v (P.reflectionPerm c c))) (P.reflection c) := by
    rw [hvc, hvnc]
    exact hd.weyl c hc
  have hnj : IsWeylPoint i (weylPoint (v j) (v (P.reflectionPerm j j))) (P.reflection j) := by
    rw [hvj, hvnj]
    exact hd.weyl j hj
  have k1 := (a2_constants hd.reductive hd.maximal hd.rootDatum hv hc hj hcj h1 h2 hnc).1 R
    (𝟙 _) 1 1
  have k2 := (a2_constants hd.reductive hd.maximal hd.rootDatum hv hj hc hcj.symm h2 h1 hnj).1 R
    (𝟙 _) 1 1
  simp only [hvc, hvj, hvnc, hvnj, map_one, mul_one, map_neg] at k1 k2
  have hr : P.root (P.reflectionPerm c j) = P.root (P.reflectionPerm j c) := by
    rw [RootPairing.root_reflectionPerm, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_root, RootPairing.reflection_apply_root,
      pairing_eq_of_pairingIn h1, pairing_eq_of_pairingIn h2]
    module
  have hw := hd.isRootParametrization_wordConj (l := [c]) (by simpa using hc)
    (hd.param j hj).1
  have hz := hd.isRootParametrization_wordConj (l := [j]) (by simpa using hj)
    (hd.param c hc).1
  change IsRootParametrization i (P.root (P.reflectionPerm c j)) _ at hw
  change IsRootParametrization i (P.root (P.reflectionPerm j c)) _ at hz
  rw [← hr] at hz
  apply eq_scaleHom_of_base hd.rootDatum hw hz
  rw [Units.val_neg, Units.val_one, map_neg, map_one]
  change rootPoint (u j ≫ (G.innerIso (rootWeylPoint P u c)).hom) _ 1 =
    rootPoint (u c ≫ (G.innerIso (rootWeylPoint P u j)).hom) _ (-1)
  rw [rootWeylPoint, rootWeylPoint, ← k2, ← inv_inv (rootPoint _ _ 1), ← rootPoint_neg, ← k1]
  group

/-- **Weyl action in type `B₂`.** For `a` short and `c` long, `n_a` acts on
`p₁ = n_c u_a n_c⁻¹` by `x ↦ -x`. -/
theorem IsNormalSimpleData.wordConj_b2 (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) :
    wordConj P u [a] (wordConj P u [c] (u a)) =
      scaleHom ((-1 : Rˣ) : R) ≫ wordConj P u [c] (u a) := by
  obtain ⟨v, hv, hva, hvc, hvna, hvnc⟩ := hd.exists_family ha hc hac
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
  have k3 := key.2.2 R (𝟙 _) 1
  have hr1 : P.root (P.reflectionPerm c a) = P.root a + P.root c := (b2_roots h1 h2).1
  have hp : P.pairing (P.reflectionPerm c a) a = 0 := by
    rw [pairing_combo (a := a) (c := c) (p := 1) (q := 1) (by rw [hr1]; module) a,
      RootPairing.pairing_same,
      pairing_eq_of_pairingIn h2]
    norm_num
  have hroot : Langlands.LinearAlgebra.wordPerm P [a] (Langlands.LinearAlgebra.wordPerm P [c] a) =
      Langlands.LinearAlgebra.wordPerm P [c] a := by
    apply P.root.injective
    change P.root (P.reflectionPerm a (P.reflectionPerm c a)) = P.root (P.reflectionPerm c a)
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hp, zero_smul,
      sub_zero]
  have hz := hd.isRootParametrization_wordConj (l := [c]) (by simpa using hc) (hd.param a ha).1
  have hw := hd.isRootParametrization_wordConj (l := [a]) (by simpa using ha) hz
  rw [← List.singleton_append, ← wordPerm_append, List.singleton_append] at hw
  change IsRootParametrization i (P.root (Langlands.LinearAlgebra.wordPerm P [a]
    (Langlands.LinearAlgebra.wordPerm P [c] a))) _ at hw
  rw [hroot] at hw
  apply eq_scaleHom_of_base hd.rootDatum hw hz
  rw [Units.val_neg, Units.val_one, map_neg, map_one, rootPoint_wordConj]
  simp only [wordPoint, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  exact k3

/-- **Fixed root groups, from coefficients.** A root `β = m c + n j` orthogonal to the simple
root `c`, such that a classification `Φ` of the coefficients of roots excludes every root in
the cones of `(β, c)` and `(β, -c)`, has all its parametrizations fixed by `n_c`. -/
theorem IsNormalSimpleData.wordConj_fix_of_coeffs (hd : IsNormalSimpleData i P b W u)
    {c j : J} (hc : c ∈ b.support) (hj : j ∈ b.support) (hcj : c ≠ j) {β : J}
    {w : Ga R ⟶ G} (hw : IsRootParametrization i (P.root β) w)
    (hpair : P.pairingIn ℤ β c = 0) {m n : ℤ}
    (hβ : P.root β = m • P.root c + n • P.root j) {Φ : ℤ → ℤ → Prop}
    (hΦ : ∀ (α : J) (m n : ℤ), P.root α = m • P.root c + n • P.root j → Φ m n)
    (hopp₁ : m + 1 ≠ 0 ∨ n + 0 ≠ 0)
    (hno₁ : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m + dT * 1) (dS * n + dT * 0) → False)
    (hopp₂ : m + -1 ≠ 0 ∨ n + 0 ≠ 0)
    (hno₂ : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m + dT * -1) (dS * n + dT * 0) → False) :
    wordConj P u [c] w = w := by
  have hli : LinearIndependent ℤ ![P.root c, P.root j] :=
    b.linearIndependent_pair_of_ne (i := ⟨c, hc⟩) (j := ⟨j, hj⟩)
      (fun h' => hcj (congrArg Subtype.val h'))
  have hc' : P.root c = (1 : ℤ) • P.root c + (0 : ℤ) • P.root j := by module
  have hnc' : P.root (P.reflectionPerm c c) = (-1 : ℤ) • P.root c + (0 : ℤ) • P.root j := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    module
  have k₁ := noOpp_cone_of_coeffs hli hβ hc' hΦ hopp₁ hno₁
  have k₂ := noOpp_cone_of_coeffs hli hβ hnc' hΦ hopp₂ hno₂
  exact hd.wordConj_fix hc hw hpair k₁.1 k₁.2 k₂.1 k₂.2

end RankTwo

section WeylPoints

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Products of Weyl points are Weyl points. -/
theorem IsWeylPoint.mul' {n m : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X}
    {f g : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (hn : IsWeylPoint i n f) (hm : IsWeylPoint i m g) :
    IsWeylPoint i (n * m) (f.trans g) := by
  apply isWeylPoint_of_isNormalizingPoint
  have h := hn.isNormalizingPoint.mul hm.isNormalizingPoint
  convert h using 1
  apply Iso.ext
  change splitTorus.exponentHom _ I I (f.trans g).toLinearMap =
    splitTorus.exponentHom _ I I g.toLinearMap ≫ splitTorus.exponentHom _ I I f.toLinearMap
  rw [splitTorus.exponentHom_comp]
  rfl

/-- Inverses of Weyl points are Weyl points. -/
theorem IsWeylPoint.inv' {n : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X}
    {f : (I → ℤ) ≃ₗ[ℤ] (I → ℤ)} (hn : IsWeylPoint i n f) : IsWeylPoint i n⁻¹ f.symm := by
  apply isWeylPoint_of_isNormalizingPoint
  have h := hn.isNormalizingPoint.inv
  convert h using 1
  apply Iso.ext
  rfl

omit [Fintype I] [DecidableEq I] in
/-- Conjugating both factors of a Weyl point conjugates the Weyl point. -/
theorem weylPoint_innerIso (w z : Ga R ⟶ G) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X) :
    weylPoint (w ≫ (G.innerIso x).hom) (z ≫ (G.innerIso x).hom) = x * weylPoint w z * x⁻¹ := by
  rw [weylPoint_comp, GroupScheme.comp_innerIso_hom]
  have hx : G.constantPoint x (𝟙_ (Over (Spec (CommRingCat.of R)))) = x := by
    change (𝟙 _) ≫ x = x
    exact Category.id_comp x
  rw [hx]

/-- **Weyl points along a word.** Conjugating the Weyl point of a simple root `k` by the
product of the Weyl points of a word `l` gives a Weyl point for the reflection of the root
`w_l(k)`. -/
theorem isWeylPoint_wordBase_conj {u : J → (Ga R ⟶ G)} :
    ∀ {l : List J}, (∀ j ∈ l, IsWeylPoint i (rootWeylPoint P u j) (P.reflection j)) →
      ∀ {k : J}, IsWeylPoint i (rootWeylPoint P u k) (P.reflection k) →
      IsWeylPoint i (wordBase (P := P) u l * rootWeylPoint P u k * (wordBase (P := P) u l)⁻¹)
        (P.reflection (Langlands.LinearAlgebra.wordPerm P l k))
  | [], _, k, hk => by
    simp only [wordBase, List.map_nil, List.prod_nil, one_mul, inv_one, mul_one]
    exact hk
  | j :: l, hl, k, hk => by
    have ih := isWeylPoint_wordBase_conj (l := l) (fun j' hj' => hl j' (List.mem_cons_of_mem _ hj'))
      hk
    have hj := hl j List.mem_cons_self
    have key := (hj.mul' ih).mul' hj.inv'
    have e₁ : wordBase (P := P) u (j :: l) * rootWeylPoint P u k *
        (wordBase (P := P) u (j :: l))⁻¹ =
        rootWeylPoint P u j * (wordBase (P := P) u l * rootWeylPoint P u k *
          (wordBase (P := P) u l)⁻¹) * (rootWeylPoint P u j)⁻¹ := by
      simp only [wordBase, List.map_cons, List.prod_cons]
      group
    have e₂ : ((P.reflection j).trans (P.reflection (Langlands.LinearAlgebra.wordPerm P l k))).trans
        (P.reflection j).symm =
        P.reflection (Langlands.LinearAlgebra.wordPerm P (j :: l) k) := by
      rw [wordPerm_cons, RootPairing.reflection_reflectionPerm]
      rfl
    rw [e₁, ← e₂]
    exact key

end WeylPoints

section Braids

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)}

variable (P) in
/-- **Partner uniqueness** for a group: a parametrization `xp` of a root `a` has at most one
partner `xm` of `-a` whose Weyl point `weylPoint xp xm` acts by `s_a`. -/
def PartnerUnique (G : GroupScheme (Spec (CommRingCat.of R)))
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) : Prop :=
  ∀ (a : J) {xp xm xm' : Ga R ⟶ G}, IsRootParametrization i (P.root a) xp →
    IsRootParametrization i (-P.root a) xm → IsRootParametrization i (-P.root a) xm' →
    IsWeylPoint i (weylPoint xp xm) (P.reflection a) →
    IsWeylPoint i (weylPoint xp xm') (P.reflection a) → xm' = xm

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
theorem wordBase_append (l l' : List J) :
    wordBase (P := P) u (l ++ l') = wordBase (P := P) u l * wordBase (P := P) u l' := by
  simp only [wordBase, List.map_append, List.prod_append]

omit [IsLocalRing R] in
/-- **Conjugate simple Weyl points.** If conjugation along a word `l` carries `u_k` to `u_{k'}`
for simple roots `k`, `k'`, then partner uniqueness gives `x n_k x⁻¹ = n_{k'}`, where `x` is the
product of the Weyl points of `l`; equivalently `x n_k = n_{k'} x`. -/
theorem IsNormalSimpleData.wordBase_braid (hd : IsNormalSimpleData i P b W u)
    (hPU : PartnerUnique P G i) {l : List J} (hl : ∀ j ∈ l, j ∈ b.support) {k k' : J}
    (hk : k ∈ b.support) (hk' : k' ∈ b.support)
    (hroot : Langlands.LinearAlgebra.wordPerm P l k = k') (h : wordConj P u l (u k) = u k') :
    wordBase (P := P) u (l ++ [k]) = wordBase (P := P) u (k' :: l) := by
  have hW := isWeylPoint_wordBase_conj (u := u) (fun j hj => hd.weyl j (hl j hj)) (hd.weyl k hk)
  rw [hroot] at hW
  have e : wordBase (P := P) u l * rootWeylPoint P u k * (wordBase (P := P) u l)⁻¹ =
      weylPoint (wordConj P u l (u k)) (wordConj P u l (u (P.reflectionPerm k k))) := by
    rw [wordConj_eq_innerIso, wordConj_eq_innerIso, weylPoint_innerIso]
    rfl
  rw [e, h] at hW
  have hm' : IsRootParametrization i (-P.root k') (wordConj P u l (u (P.reflectionPerm k k))) := by
    have := hd.isRootParametrization_wordConj hl (hd.param k hk).2
    rwa [Langlands.LinearAlgebra.root_wordPerm, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self, wordReflect_neg, ← Langlands.LinearAlgebra.root_wordPerm,
      hroot] at this
  have hm : IsRootParametrization i (-P.root k') (u (P.reflectionPerm k' k')) := by
    have := (hd.param k' hk').2
    rwa [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] at this
  have hq := hPU k' (hd.param k' hk').1 hm hm' (hd.weyl k' hk') hW
  rw [hq] at e
  have e' : wordBase (P := P) u l * rootWeylPoint P u k = rootWeylPoint P u k' *
      wordBase (P := P) u l := by
    rw [← mul_inv_eq_iff_eq_mul, e, h]
    rfl
  have hk1 : wordBase (P := P) u [k] = rootWeylPoint P u k := by
    simp only [wordBase, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [wordBase_append, hk1, e']
  simp only [wordBase, List.map_cons, List.prod_cons]

end Braids

section Negative

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)}

variable (P) in
/-- **Inverse rescaling of Weyl points** for a group: rescaling a Weyl-normalized pair by
`κ` and `κ⁻¹` keeps a Weyl point acting by `s_a`. -/
def PartnerRescales (G : GroupScheme (Spec (CommRingCat.of R)))
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) : Prop :=
  ∀ (a : J) {xp xm : Ga R ⟶ G}, IsRootParametrization i (P.root a) xp →
    IsRootParametrization i (-P.root a) xm →
    IsWeylPoint i (weylPoint xp xm) (P.reflection a) → ∀ κ : Rˣ,
    IsWeylPoint i (weylPoint (scaleHom (κ : R) ≫ xp) (scaleHom ((κ⁻¹ : Rˣ) : R) ≫ xm))
      (P.reflection a)

omit [IsLocalRing R] [IsAffineHom G.X.hom] in
/-- Conjugating a Weyl point for `s_k` by a Weyl point for `s_j` gives one for
`s_{s_j k}`. -/
theorem IsWeylPoint.conj_reflection {n m : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G.X}
    {j k : J} (hn : IsWeylPoint i n (P.reflection j)) (hm : IsWeylPoint i m (P.reflection k)) :
    IsWeylPoint i (n * m * n⁻¹) (P.reflection (P.reflectionPerm j k)) := by
  have key := (hn.mul' hm).mul' hn.inv'
  have e : ((P.reflection j).trans (P.reflection k)).trans (P.reflection j).symm =
      P.reflection (P.reflectionPerm j k) := by
    rw [RootPairing.reflection_reflectionPerm]
    rfl
  rwa [e] at key

/-- The Weyl point `n_s` maps `u_s` to `u_{-s}(-x)`, as maps. -/
theorem IsNormalSimpleData.wordConj_simple_self (hd : IsNormalSimpleData i P b W u) {s : J}
    (hs : s ∈ b.support) :
    wordConj P u [s] (u s) = scaleHom ((-1 : Rˣ) : R) ≫ u (P.reflectionPerm s s) := by
  have hw := hd.isRootParametrization_wordConj (l := [s]) (by simpa using hs) (hd.param s hs).1
  apply eq_scaleHom_of_base hd.rootDatum hw (hd.param s hs).2
  have k := (hd.rankOne s hs).1 R (𝟙 _) 1
  rw [Units.val_neg, Units.val_one, map_neg, map_one, rootPoint_wordConj]
  simp only [wordPoint, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    rootWeylPoint]
  exact k

/-- The opposite partner `q_γ = n_w u_{-s} n_w⁻¹` of the Weyl family at a root `γ` with word
`w` and simple root `s`. -/
def oppositeFamily (W : ∀ α, SimpleWord P b α) (u : J → (Ga R ⟶ G)) (g : J) : Ga R ⟶ G :=
  wordConj P u (W g).word (u (P.reflectionPerm (W g).simple (W g).simple))

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
theorem reflectionPerm_neg_self (g : J) :
    P.reflectionPerm (P.reflectionPerm g g) (P.reflectionPerm g g) = g := by
  apply P.root.injective
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self,
    RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg]

/-- The Weyl family at `-γ`, for positive `γ`, is `x ↦ q_γ(-x)`. -/
theorem IsNormalSimpleData.weylFamily_neg (hd : IsNormalSimpleData i P b W u) {g : J}
    (hg : b.IsPos g) :
    weylFamily P W u (P.reflectionPerm g g) = scaleHom ((-1 : Rˣ) : R) ≫ oppositeFamily W u g := by
  have hng : ¬ b.IsPos (P.reflectionPerm g g) :=
    fun h => (RootPairing.Base.IsPos.neg_iff_not (b := b) g).mp h hg
  obtain ⟨hsimple, hword⟩ := hd.words.2.2 _ hng
  rw [reflectionPerm_neg_self] at hsimple hword
  unfold weylFamily oppositeFamily
  rw [hword, hsimple, wordConj_append, hd.wordConj_simple_self (W g).simple_mem,
    wordConj_scaleHom]

omit [IsLocalRing R] in
theorem IsNormalSimpleData.isRootParametrization_opposite (hd : IsNormalSimpleData i P b W u)
    (g : J) : IsRootParametrization i (-P.root g) (oppositeFamily W u g) := by
  have := hd.isRootParametrization_wordConj (W g).word_mem
    (hd.param (W g).simple (W g).simple_mem).2
  rwa [Langlands.LinearAlgebra.root_wordPerm, RootPairing.root_reflectionPerm,
    RootPairing.reflection_apply_self, wordReflect_neg, (W g).root_eq] at this

omit [IsLocalRing R] in
theorem IsNormalSimpleData.isWeylPoint_opposite (hd : IsNormalSimpleData i P b W u) (g : J) :
    IsWeylPoint i (weylPoint (weylFamily P W u g) (oppositeFamily W u g)) (P.reflection g) := by
  have hW := isWeylPoint_wordBase_conj (u := u) (fun j hj => hd.weyl j ((W g).word_mem j hj))
    (hd.weyl (W g).simple (W g).simple_mem)
  have hroot : Langlands.LinearAlgebra.wordPerm P (W g).word (W g).simple = g :=
    P.root.injective (by rw [Langlands.LinearAlgebra.root_wordPerm, (W g).root_eq])
  rw [hroot] at hW
  unfold weylFamily oppositeFamily
  rw [wordConj_eq_innerIso, wordConj_eq_innerIso, weylPoint_innerIso]
  exact hW

/-- **Weyl conjugation at negative roots.** If `n_c` carries `v_α` to `κ v_{s_c α}` for positive
roots `α`, `s_c α`, then it carries `v_{-α}` to `κ⁻¹ v_{-s_c α}`. -/
theorem IsNormalSimpleData.conj_neg (hd : IsNormalSimpleData i P b W u)
    (hPU : PartnerUnique P G i) (hSC : PartnerRescales P G i) {c : J} (hc : c ∈ b.support)
    {α : J} (hα : b.IsPos α) (hcα : b.IsPos (P.reflectionPerm c α)) {κ : Rˣ}
    (h : wordConj P u [c] (weylFamily P W u α) =
      scaleHom (κ : R) ≫ weylFamily P W u (P.reflectionPerm c α)) :
    wordConj P u [c] (weylFamily P W u (P.reflectionPerm α α)) =
      scaleHom ((κ⁻¹ : Rˣ) : R) ≫ weylFamily P W u (P.reflectionPerm c (P.reflectionPerm α α)) := by
  set β := P.reflectionPerm c α with hβdef
  have hidx : P.reflectionPerm c (P.reflectionPerm α α) = P.reflectionPerm β β := by
    apply P.root.injective
    rw [RootPairing.root_reflectionPerm, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self, map_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self, hβdef, RootPairing.root_reflectionPerm]
  rw [hidx, hd.weylFamily_neg hα, hd.weylFamily_neg hcα, wordConj_scaleHom]
  -- the conjugated opposite partner
  have hW₁ := (hd.weyl c hc).conj_reflection (hd.isWeylPoint_opposite α)
  rw [← weylPoint_innerIso] at hW₁
  change IsWeylPoint i (weylPoint (wordConj P u [c] (weylFamily P W u α))
    (wordConj P u [c] (oppositeFamily W u α))) _ at hW₁
  rw [h] at hW₁
  have hW₂ := hSC β (hd.isRootParametrization β) (hd.isRootParametrization_opposite β)
    (hd.isWeylPoint_opposite β) κ
  have hm' : IsRootParametrization i (-P.root β) (wordConj P u [c] (oppositeFamily W u α)) := by
    have hopp : IsRootParametrization i (P.root (P.reflectionPerm α α)) (oppositeFamily W u α) := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      exact hd.isRootParametrization_opposite α
    have := hd.isRootParametrization_wordConj (l := [c]) (by simpa using hc) hopp
    have hr : P.root (Langlands.LinearAlgebra.wordPerm P [c] (P.reflectionPerm α α)) =
        -P.root β := by
      change P.root (P.reflectionPerm c (P.reflectionPerm α α)) = _
      rw [hidx, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    rwa [hr] at this
  have hq := hPU β ((hd.isRootParametrization β).scale κ)
    ((hd.isRootParametrization_opposite β).scale κ⁻¹) hm' hW₂ hW₁
  rw [hq, ← Category.assoc, ← Category.assoc, scaleHom_comp_scaleHom, scaleHom_comp_scaleHom,
    mul_comm]

end Negative

section RankTwoConj

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)}

omit [IsLocalRing R] in
theorem neg_one_units_mul_inv : ((-1 : Rˣ) : R) * ((-1 : Rˣ)⁻¹ : Rˣ) = 1 := Units.mul_inv _

/-- **Type `A₂`:** `n_c n_j u_c (n_c n_j)⁻¹ = u_j`. -/
theorem IsNormalSimpleData.conj_a2 (hd : IsNormalSimpleData i P b W u) {c j : J}
    (hc : c ∈ b.support) (hj : j ∈ b.support) (hcj : c ≠ j)
    (h1 : P.pairingIn ℤ c j = -1) (h2 : P.pairingIn ℤ j c = -1) :
    wordConj P u [c, j] (u c) = u j := by
  have hT := scaleHom_cancel (-1) (hd.wordConj_a2 hc hj hcj h1 h2).symm
  change wordConj P u [c] (wordConj P u [j] (u c)) = u j
  rw [hT, wordConj_scaleHom]
  change scaleHom _ ≫ wordConj P u [c, c] (u j) = u j
  rw [wordConj_sq hd.rootDatum (hd.rankOne c hc) (hd.param j hj).1, h2,
    signUnit_odd ⟨-1, by norm_num⟩, ← Category.assoc, scaleHom_comp_scaleHom,
    neg_one_units_mul_inv, scaleHom_one, Category.id_comp]

/-- **Type `B₂`**, `a` short, `c` long: `n_a n_c n_a` fixes `u_c`. -/
theorem IsNormalSimpleData.conj_b2 (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -2) :
    wordConj P u [a, c, a] (u c) = u c := by
  classical
  have := hd.rootDatum.finite
  have : P.IsReduced := hd.rootDatum.isReduced
  have hw₁ := hd.isRootParametrization_wordConj (l := [a]) (by simpa using ha) (hd.param c hc).1
  change IsRootParametrization i (P.root (P.reflectionPerm a c)) _ at hw₁
  have hr : P.root (P.reflectionPerm a c) = (1 : ℤ) • P.root c + (2 : ℤ) • P.root a := by
    rw [(b2_roots h1 h2).2]
    module
  have hpair : P.pairingIn ℤ (P.reflectionPerm a c) c = 0 := by
    rw [pairingIn_eq_pairing, pairing_combo (a := c) (c := a) hr c, RootPairing.pairing_same,
      pairing_eq_of_pairingIn h1]
    norm_num
  have hfix := hd.wordConj_fix_of_coeffs hc ha hac.symm hw₁ hpair hr
    (Φ := fun m n => (n = 1 ∧ m = 0) ∨ (n = 0 ∧ m = 1) ∨ (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 1) ∨
      (n = -1 ∧ m = 0) ∨ (n = 0 ∧ m = -1) ∨ (n = -1 ∧ m = -1) ∨ (n = -2 ∧ m = -1))
    (fun g m n h => Langlands.LinearAlgebra.b2_coeffs ha hc hac h1 h2 (by rw [h, add_comm]))
    (by omega) (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega)
  change wordConj P u [a] (wordConj P u [c] (wordConj P u [a] (u c))) = u c
  rw [hfix]
  change wordConj P u [a, a] (u c) = u c
  rw [wordConj_sq hd.rootDatum (hd.rankOne a ha) (hd.param c hc).1, h2,
    signUnit_even ⟨-1, by norm_num⟩, Units.val_one, scaleHom_one, Category.id_comp]

theorem IsNormalSimpleData.conj_g2_fix (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3) :
    wordConj P u [a] (wordConj P u [c] (wordConj P u [a] (u c))) =
      wordConj P u [c] (wordConj P u [a] (u c)) := by
  classical
  have := hd.rootDatum.finite
  have : P.IsReduced := hd.rootDatum.isReduced
  have hw₁ := hd.isRootParametrization_wordConj (l := [a]) (by simpa using ha) (hd.param c hc).1
  have hw₂ := hd.isRootParametrization_wordConj (l := [c]) (by simpa using hc) hw₁
  have hr : P.root (Langlands.LinearAlgebra.wordPerm P [c]
      (Langlands.LinearAlgebra.wordPerm P [a] c)) = (3 : ℤ) • P.root a + (2 : ℤ) • P.root c :=
    (g2_roots h1 h2).2.2.2
  have hpair : P.pairingIn ℤ (Langlands.LinearAlgebra.wordPerm P [c]
      (Langlands.LinearAlgebra.wordPerm P [a] c)) a = 0 := by
    rw [pairingIn_eq_pairing, pairing_combo (a := a) (c := c) hr a, RootPairing.pairing_same,
      pairing_eq_of_pairingIn h2]
    norm_num
  exact hd.wordConj_fix_of_coeffs ha hc hac hw₂ hpair hr
    (Φ := fun m n => ((m = 1 ∧ n = 0) ∨ (m = 0 ∧ n = 1) ∨ (m = 1 ∧ n = 1) ∨ (m = 2 ∧ n = 1) ∨
      (m = 3 ∧ n = 1) ∨ (m = 3 ∧ n = 2)) ∨ ((m = -1 ∧ n = 0) ∨ (m = 0 ∧ n = -1) ∨
      (m = -1 ∧ n = -1) ∨ (m = -2 ∧ n = -1) ∨ (m = -3 ∧ n = -1) ∨ (m = -3 ∧ n = -2)))
    (fun g m n h => Langlands.LinearAlgebra.g2_coeffs ha hc hac h1 h2 h)
    (by omega) (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega)

/-- **Type `G₂`**, `a` short, `c` long: `n_a n_c n_a n_c n_a` fixes `u_c`. -/
theorem IsNormalSimpleData.conj_g2 (hd : IsNormalSimpleData i P b W u) {a c : J}
    (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -3) :
    wordConj P u [a, c, a, c, a] (u c) = u c := by
  have hw₁ := hd.isRootParametrization_wordConj (l := [a]) (by simpa using ha) (hd.param c hc).1
  have r3' : P.root (Langlands.LinearAlgebra.wordPerm P [a] c) =
      (3 : ℤ) • P.root a + (1 : ℤ) • P.root c := by
    rw [show Langlands.LinearAlgebra.wordPerm P [a] c = P.reflectionPerm a c from rfl,
      (g2_roots h1 h2).2.2.1]
    module
  have hp₁ : P.pairingIn ℤ (Langlands.LinearAlgebra.wordPerm P [a] c) c = -1 := by
    rw [pairingIn_eq_pairing, pairing_combo (a := a) (c := c) r3' c, RootPairing.pairing_same,
      pairing_eq_of_pairingIn h1]
    norm_num
  have e₁ : wordConj P u [a, c, a, c, a] (u c) = wordConj P u [a]
      (wordConj P u [c] (wordConj P u [a] (wordConj P u [c] (wordConj P u [a] (u c))))) := by
    simp only [← wordConj_append, List.singleton_append]
  rw [e₁, hd.conj_g2_fix ha hc hac h1 h2]
  have e₂ : wordConj P u [c] (wordConj P u [c] (wordConj P u [a] (u c))) =
      wordConj P u [c, c] (wordConj P u [a] (u c)) := by
    rw [← wordConj_append]
    rfl
  rw [e₂, wordConj_sq hd.rootDatum (hd.rankOne c hc) hw₁, hp₁, signUnit_odd ⟨-1, by norm_num⟩,
    wordConj_scaleHom]
  have e₃ : wordConj P u [a] (wordConj P u [a] (u c)) = wordConj P u [a, a] (u c) := by
    rw [← wordConj_append]
    rfl
  rw [e₃, wordConj_sq hd.rootDatum (hd.rankOne a ha) (hd.param c hc).1, h2,
    signUnit_odd ⟨-2, by norm_num⟩, ← Category.assoc, scaleHom_comp_scaleHom, Units.val_neg,
    Units.val_one, neg_one_mul, neg_neg, scaleHom_one, Category.id_comp]

end RankTwoConj

end LocalSplitCell

end Langlands.GroupScheme
