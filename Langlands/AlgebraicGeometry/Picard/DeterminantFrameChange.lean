import Langlands.AlgebraicGeometry.Picard.DeterminantFrames
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleGauge

/-! # Coherent determinant comparison under changes of local frames -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}
  {ι I : Type u} [Fintype I] {T : ι → X.Opens}
  (e f g : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))

private local instance : DecidableEq I := Classical.decEq I

/-- Both systems of actual frames, indexed by the disjoint union of their chart indices. -/
def pairFrames (i : ι ⊕ ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over (Sum.elim T T i)) I ≅
      M.over (Sum.elim T T i) :=
  Sum.rec e f i

/-- The determinant of the old frame expressed in the new frame on each chart. -/
def changeUnit (i : ι) : (Γ(X, T i))ˣ :=
  unit (pairFrames e f) (Sum.inr i) (Sum.inl i) le_rfl le_rfl

lemma changeUnit_self (i : ι) : (changeUnit e e i : Γ(X, T i)) = 1 := by
  change ((basis e i le_rfl).toMatrix (basis e i le_rfl)).det = 1
  rw [Module.Basis.toMatrix_self, Matrix.det_one]

lemma changeUnit_mul (i : ι) :
    (changeUnit e f i : Γ(X, T i)) * (changeUnit f g i : Γ(X, T i)) =
      (changeUnit e g i : Γ(X, T i)) := by
  change ((basis f i le_rfl).toMatrix (basis e i le_rfl)).det *
      ((basis g i le_rfl).toMatrix (basis f i le_rfl)).det =
    ((basis g i le_rfl).toMatrix (basis e i le_rfl)).det
  rw [mul_comm, ← Matrix.det_mul, Module.Basis.toMatrix_mul_toMatrix]

/-- The determinant changes of frame intertwine the actual determinant cocycles. -/
lemma isGaugeFamily_changeUnit :
    CocycleGluing.IsGaugeFamily (cocycle e) (cocycle f)
      (fun i => (changeUnit e f i : Γ(X, T i))) := by
  intro i j
  change X.presheaf.map (homOfLE (inf_le_left : T i ⊓ T j ≤ T i)).op
        (unit (pairFrames e f) (Sum.inr i) (Sum.inl i) (U := T i)
          le_rfl le_rfl).val *
      (unit (pairFrames e f) (Sum.inl i) (Sum.inl j) (U := T i ⊓ T j)
        inf_le_left inf_le_right).val =
    (unit (pairFrames e f) (Sum.inr i) (Sum.inr j) (U := T i ⊓ T j)
        inf_le_left inf_le_right).val *
      X.presheaf.map (homOfLE (inf_le_right : T i ⊓ T j ≤ T j)).op
        (unit (pairFrames e f) (Sum.inr j) (Sum.inl j) (U := T j)
          le_rfl le_rfl).val
  rw [unit_restrict, unit_restrict]
  simp only [unit_val]
  rw [← Matrix.det_mul, ← Matrix.det_mul, matrix_mul, matrix_mul]

/-- Canonical comparison of the actual determinant sheaves for two frames on one cover. -/
def changeIso :
    CocycleGluing.glued (cocycle e) ≅ CocycleGluing.glued (cocycle f) :=
  CocycleGluing.gaugeIso (changeUnit e f)
    ((CocycleGluing.isGauge_iff _ _ _).mpr (isGaugeFamily_changeUnit e f))

/-- The comparison sends local scalar coordinates to their actual frame-change multiples. -/
lemma comp_changeIso_hom_app {U : X.Opens}
    (m : Γ(CocycleGluing.glued (cocycle e), U)) (i : ι) :
    CocycleGluing.comp (cocycle f) ((changeIso e f).hom.app U m) i =
      X.presheaf.map (homOfLE (inf_le_right : U ⊓ T i ≤ T i)).op
        (changeUnit e f i : Γ(X, T i)) * CocycleGluing.comp (cocycle e) m i :=
  rfl

@[simp]
lemma changeIso_self : changeIso e e = Iso.refl _ := by
  apply Iso.ext
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  apply CocycleGluing.eq_of_comp (cocycle e)
  intro i
  rw [comp_changeIso_hom_app, changeUnit_self, map_one, one_mul]
  rfl

/-- Canonical frame comparison is transitive as an equality of actual isomorphisms. -/
lemma changeIso_trans : changeIso e f ≪≫ changeIso f g = changeIso e g := by
  apply Iso.ext
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext m
  apply CocycleGluing.eq_of_comp (cocycle g)
  intro i
  change CocycleGluing.comp (cocycle g)
      ((changeIso f g).hom.app U ((changeIso e f).hom.app U m)) i =
    CocycleGluing.comp (cocycle g) ((changeIso e g).hom.app U m) i
  rw [comp_changeIso_hom_app, comp_changeIso_hom_app, comp_changeIso_hom_app,
    ← mul_assoc, ← map_mul, mul_comm (changeUnit f g i : Γ(X, T i)), changeUnit_mul]

/-- The induced coherent comparison in the category of actual line bundles. -/
def lineBundleChangeIso (hT : (⨆ i, T i) = ⊤) :
    lineBundle e hT ≅ lineBundle f hT :=
  ObjectProperty.isoMk _ (changeIso e f)

@[simp]
lemma lineBundleChangeIso_self (hT : (⨆ i, T i) = ⊤) :
    lineBundleChangeIso e e hT = Iso.refl _ := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (changeIso_self e)

lemma lineBundleChangeIso_trans (hT : (⨆ i, T i) = ⊤) :
    lineBundleChangeIso e f hT ≪≫ lineBundleChangeIso f g hT =
      lineBundleChangeIso e g hT := by
  apply Iso.ext
  apply ObjectProperty.hom_ext
  exact congrArg Iso.hom (changeIso_trans e f g)

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
