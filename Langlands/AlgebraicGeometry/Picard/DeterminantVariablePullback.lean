import Langlands.AlgebraicGeometry.Picard.DeterminantVariableIso
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundlePullback
import Langlands.AlgebraicGeometry.Picard.LineBundlePullback
import Langlands.AlgebraicGeometry.LocalChartDeterminantPullback

/-! # Pullback of variable-rank determinant frame systems -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames

open Langlands.Scheme.Modules

open DeterminantFrames (eqToIso_hom_app_genSec)

variable {X Y : Scheme.{u}} {M : X.Modules} {ι : Type u}
  {T : ι → X.Opens} {n : ι → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))

/-- A frame vector as a local morphism from the actual structure sheaf. -/
def frameGenerator (i : ι) {V : X.Opens} (hi : V ≤ T i) (a : Fin (n i)) :
    LocalHom (SheafOfModules.unit X.ringCatSheaf) M V :=
  LocalHom.restrict (homOfLE hi) (SheafOfModules.ιFree (ULift.up a) ≫ (e i).hom)

lemma frameGenerator_section (i : ι) {V : X.Opens} (hi : V ≤ T i) (a : Fin (n i)) :
    localUnitSection M V (frameGenerator e i hi a) = basis e i hi a :=
  (localSectionBasis_apply (e i) (Over.mk (homOfLE hi)) (ULift.up a)).symm.trans
    (basis_apply e i hi a).symm

/-- Expand one actual local generator in the other chart's generators. -/
lemma frameGenerator_expansion (i j : ι) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ T j) (b : Fin (n j)) :
    frameGenerator e j hj b =
      ∑ a, ((basis e i hi).repr (basis e j hj b) a) • frameGenerator e i hi a := by
  apply localUnitSection_injective M V
  rw [map_sum]
  simp only [map_smul, frameGenerator_section]
  exact ((basis e i hi).sum_repr (basis e j hj b)).symm

/-- The actual free chart constructed by pulling back each supplied frame. -/
def pullbackFrames (q : Y ⟶ X) (i : ι) :
    SheafOfModules.free (R := Y.ringCatSheaf.over (q ⁻¹ᵁ T i)) (ULift.{u} (Fin (n i))) ≅
      ((Scheme.Modules.pullback q).obj M).over (q ⁻¹ᵁ T i) :=
  chartFreePullbackIso q (T i) (e i)

set_option maxHeartbeats 800000 in
/-- The pulled-back generator is the pullback of the original local map,
with the canonical structure-module comparison. -/
lemma frameGenerator_pullback (q : Y ⟶ X) (i : ι) {V : X.Opens}
    (hi : V ≤ T i) (a : Fin (n i)) :
    frameGenerator (pullbackFrames e q) i (q.preimage_mono hi) a =
      (pullbackUnitIso q).inv.over (q ⁻¹ᵁ V) ≫
        localHomPullback q V (frameGenerator e i hi a) := by
  have h := congrArg
    (LocalHom.restrict (M := SheafOfModules.unit Y.ringCatSheaf)
      (N := (Scheme.Modules.pullback q).obj M) (homOfLE (q.preimage_mono hi)))
    (chartFreePullbackIso_generator q (T i) (e i) (ULift.up a))
  change frameGenerator (pullbackFrames e q) i (q.preimage_mono hi) a =
    (pullbackUnitIso q).inv.over (q ⁻¹ᵁ V) ≫
      LocalHom.restrict ((Opens.map q.base).map (homOfLE hi))
        (localHomPullback q (T i) (SheafOfModules.ιFree (ULift.up a) ≫ (e i).hom)) at h
  exact h.trans (congrArg
    (fun t => (pullbackUnitIso q).inv.over (q ⁻¹ᵁ V) ≫ t)
    (localHomPullback_restrict q (SheafOfModules.unit X.ringCatSheaf) M
      (homOfLE hi) (SheafOfModules.ιFree (ULift.up a) ≫ (e i).hom)).symm)

set_option maxRecDepth 2048 in
/-- Pullback carries the actual coordinates between any two finite local bases. -/
lemma basis_repr_pullback (q : Y ⟶ X) (i j : ι) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ T j) (a : Fin (n i)) (b : Fin (n j)) :
    q.app V ((basis e i hi).repr (basis e j hj b) a) =
      (basis (pullbackFrames e q) i (q.preimage_mono hi)).repr
        (basis (pullbackFrames e q) j (q.preimage_mono hj) b) a := by
  have h := congrArg
    (fun t => (pullbackUnitIso q).inv.over (q ⁻¹ᵁ V) ≫ localHomPullback q V t)
    (frameGenerator_expansion e i j hi hj b)
  rw [← frameGenerator_pullback e q j hj b,
    localHomPullback_sum, Preadditive.comp_sum] at h
  simp only [localHomPullback_smul q (SheafOfModules.unit X.ringCatSheaf) M V,
    localHom_comp_smul,
    ← frameGenerator_pullback] at h
  have hs := congrArg
    (localUnitSection ((Scheme.Modules.pullback q).obj M) (q ⁻¹ᵁ V)) h
  rw [map_sum] at hs
  simp only [map_smul, frameGenerator_section] at hs
  have hc := congrArg
    (fun x => (basis (pullbackFrames e q) i (q.preimage_mono hi)).repr x a) hs
  rw [Module.Basis.repr_sum_self] at hc
  exact hc.symm

set_option maxRecDepth 2048 in
/-- The determinant transition unit is carried to the unit for the pulled-back frames. -/
lemma unit_pullback (q : Y ⟶ X) (i j : ι) {V : X.Opens}
    (hi : V ≤ T i) (hj : V ≤ T j) :
    q.app V (unit e i j hi hj : Γ(X, V)) =
      (unit (pullbackFrames e q) i j
        (q.preimage_mono hi) (q.preimage_mono hj) : Γ(Y, q ⁻¹ᵁ V)) := by
  apply Langlands.LinearAlgebra.FiniteBasisDeterminant.map_unit
  intro a b
  exact basis_repr_pullback e q i j hi hj a b

/-- The determinant cocycle of the constructed frames is the actual pulled-back cocycle. -/
lemma cocycle_pullback (q : Y ⟶ X) :
    cocycle (pullbackFrames e q) = CocycleGluing.pullbackCocycle q (cocycle e) := by
  funext i j
  apply Units.ext
  calc
    _ = q.app (T i ⊓ T j) (cocycle e i j : Γ(X, T i ⊓ T j)) :=
      (unit_pullback e q i j inf_le_left inf_le_right).symm
    _ = _ := ConcreteCategory.congr_hom (q.app_eq_appLE (U := T i ⊓ T j))
      (cocycle e i j : Γ(X, T i ⊓ T j))

/-- The actual pullback of the determinant sheaf, compared with the determinant
constructed from the actual pulled-back module frames. -/
def pullbackIso (q : Y ⟶ X) (hT : (⨆ i, T i) = ⊤) :
    (Scheme.Modules.pullback q).obj (CocycleGluing.glued (cocycle e)) ≅
      CocycleGluing.glued (cocycle (pullbackFrames e q)) :=
  CocycleGluing.pullbackIso q (cocycle e) hT (isCocycle e) ≪≫
    eqToIso (congrArg CocycleGluing.glued (cocycle_pullback e q).symm)

/-- The determinant pullback comparison preserves the actual local generators. -/
lemma pullbackIso_hom_app_genSec (q : Y ⟶ X) (hT : (⨆ i, T i) = ⊤)
    (i : ι) {V : X.Opens} (hi : V ≤ T i) :
    (pullbackIso e q hT).hom.app (q ⁻¹ᵁ V)
        (Scheme.Modules.pullbackLocalSection q
          (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi)) =
      CocycleGluing.genSec (cocycle (pullbackFrames e q))
        (isCocycle (pullbackFrames e q)) i (q.preimage_mono hi) := by
  change (eqToIso (congrArg CocycleGluing.glued (cocycle_pullback e q).symm)).hom.app
    (q ⁻¹ᵁ V)
    ((CocycleGluing.pullbackIso q (cocycle e) hT (isCocycle e)).hom.app (q ⁻¹ᵁ V)
      (Scheme.Modules.pullbackLocalSection q
        (CocycleGluing.genSec (cocycle e) (isCocycle e) i hi))) = _
  rw [CocycleGluing.pullbackIso_hom_app_genSec]
  exact DeterminantFrames.eqToIso_hom_app_genSec (cocycle_pullback e q).symm _ _ i (q.preimage_mono hi)

/-- The same comparison as an isomorphism of actual line bundles. -/
def lineBundlePullbackIso (q : Y ⟶ X) (hT : (⨆ i, T i) = ⊤) :
    (LineBundle.pullback q).obj (lineBundle e hT) ≅
      lineBundle (pullbackFrames e q) (q.iSup_preimage_eq_top hT) :=
  ObjectProperty.isoMk _ (pullbackIso e q hT)

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
