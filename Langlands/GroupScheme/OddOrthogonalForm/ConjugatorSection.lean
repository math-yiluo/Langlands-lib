import Langlands.GroupScheme.OddOrthogonalForm.LocalConjugation

/-! # Unique conjugating sections on a splitting cover -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.OddOrthogonalForm

open OddOrthogonalMatrix

variable {K : Type u} [Field K] {N : Type u} [Field N] [Algebra K N] {n : ℕ}

/-- Original-field points over the extension test are the points of the
extension-field split model over its own base. -/
def fieldPointsEquiv :
    (Over.mk (𝟙 (Spec (CommRingCat.of N))) ⟶ (splitGroup N n).X) ≃*
      (ringTest K N ⟶ (splitGroup K n).X) :=
  (pointsIsoEquiv (splitBaseChangeIso K N n).symm _).trans
    (LocalGroupIso.coverPointsEquiv (splitGroup K n) (𝟙 (ringTest K N)))

/-- The chosen conjugating point as a section of the original group over the cover. -/
def conjugatorSection (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N)) :
    ringTest K N ⟶ (splitGroup K n).X :=
  fieldPointsEquiv (conjugatorPoint hn χ)

/-- On each test the chosen section has precisely the coefficient extension
of the original conjugator matrix. -/
theorem splitMatrix_conjugatorSection (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N))
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N) :
    splitMatrix (s ≫ conjugatorSection hn χ) = (conjugatorMatrix hn χ).val.map (sectionScalars s) := by
  let p := conjugatorPoint hn χ
  let c := splitBaseChangeIso K N n
  let T₀ := Over.mk (𝟙 (Spec (CommRingCat.of N)))
  have hbase : splitMatrix (conjugatorSection hn χ) = (pointMatrix N T₀ p).val := by
    have h := splitMatrix_coverPointsEquiv (𝟙 (ringTest K N)) (p ≫ c.inv.hom.hom)
    change (pointMatrix N T₀ ((p ≫ c.inv.hom.hom) ≫ c.hom.hom.hom)).val =
      splitMatrix (conjugatorSection hn χ) at h
    rw [Category.assoc, ← Grp.comp_hom_hom, c.inv_hom_id, Grp.id_hom_hom, Category.comp_id] at h
    exact h.symm
  have hrat := pointMatrix_constantPoint_rational N p T₀
  rw [GroupScheme.constantPoint_self] at hrat
  have hsc (a : N) : s.left.appTop.hom (scalarMap T₀ a) = sectionScalars s a := by
    change s.left.appTop.hom
      (((Scheme.ΓSpecIso (CommRingCat.of N)).inv ≫ (𝟙 (Spec (CommRingCat.of N)) : Spec (CommRingCat.of N) ⟶ Spec (CommRingCat.of N)).appTop).hom a) = _
    rw [Scheme.Hom.id_appTop, Category.comp_id]
    rfl
  change (pointMatrix K V (s ≫ conjugatorSection hn χ)).val = _
  rw [pointMatrix_naturality]
  change (splitMatrix (conjugatorSection hn χ)).map s.left.appTop.hom = _
  rw [hbase, hrat]
  apply Matrix.ext
  intro i j
  exact hsc _

/-- The local automorphism is actual conjugation by the pulled-back cover section. -/
theorem localAutomorphism_eq_conjugation (hn : 2 ≤ n)
    (χ : LocalGroupIso (splitGroup K n) (splitGroup K n) (ringTest K N))
    {V : Over (Spec (CommRingCat.of K))} (s : V ⟶ ringTest K N)
    (x : V ⟶ (splitGroup K n).X) :
    χ.toFun s x = (s ≫ conjugatorSection hn χ) * x * (s ≫ conjugatorSection hn χ)⁻¹ := by
  have hunit : pointMatrix K V (s ≫ conjugatorSection hn χ) =
      Matrix.GeneralLinearGroup.map (sectionScalars s) (conjugatorMatrix hn χ) :=
    Units.ext (splitMatrix_conjugatorSection hn χ s)
  apply pointMatrix_injective K V
  apply Units.ext
  simp only [_root_.map_mul, _root_.map_inv, Units.val_mul, hunit]
  exact splitMatrix_localAutomorphism hn χ s x

/-- Equality of conjugation on every relative test determines a section uniquely,
because the full odd model has trivial scheme-theoretic centre. -/
theorem section_eq_of_conjugation_eq (hn : 2 ≤ n)
    {U : Over (Spec (CommRingCat.of K))} (g h : U ⟶ (splitGroup K n).X)
    (he : ∀ (V : Over (Spec (CommRingCat.of K))) (s : V ⟶ U) (x : V ⟶ (splitGroup K n).X),
      (s ≫ g) * x * (s ≫ g)⁻¹ = (s ≫ h) * x * (s ≫ h)⁻¹) : g = h := by
  have hc : g⁻¹ * h ∈ (center (splitGroup K n)).carrier U := by
    intro V s x
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    have he' := congrArg (fun z => (s ≫ g)⁻¹ * z * (s ≫ h)) (he V s x)
    change (s ≫ g)⁻¹ * (s ≫ h) * x = x * ((s ≫ g)⁻¹ * (s ≫ h))
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he'.symm
  rw [(TypeBNumbering.isAdjoint_groupScheme (K := K) hn).center_eq_bot,
    SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.mp hc

end Langlands.GroupScheme.OddOrthogonalForm
