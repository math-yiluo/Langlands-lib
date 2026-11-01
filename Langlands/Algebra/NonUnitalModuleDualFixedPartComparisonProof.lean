import Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonStatements
import Langlands.Algebra.NonUnitalModuleDualFixedPartProof

/-!
Full-fixed and right-corner comparisons for the original dual actions.
Worker 691 reuses the published basic complex fixed-part duality proof.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonProof

open NonUnitalModuleCorner (FixedPart)
open NonUnitalModuleDualFixedPartMaps
open NonUnitalModuleDualFixedPartComparison
open NonUnitalModuleDualFixedPartComparisonStatements

universe uA uM uN

/-- The prescribed full-fixed and right-corner duality comparisons are natural. -/
theorem fixedPartComparisons : FixedPartComparisons.{uA, uM, uN} := by
  intro A _ _ _ _ M _ _ hA hM e
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := rightFixedModule hA hM e
  let _ := fullRightFixedModule hA hM e
  let _ := fixedPartDualCornerModule hA hM e
  let _ := NonUnitalModuleDual.fullAction hA hM
  let _ := NonUnitalModuleDual.dualAction hA hM
  have hInv : FullFixedInverseIdentities hA hM e := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply LinearMap.ext
      intro psi
      exact Subtype.ext rfl
    · apply LinearMap.ext
      intro phi
      exact Subtype.ext (Subtype.ext rfl)
    · apply LinearMap.ext
      intro psi
      exact Subtype.ext rfl
    · apply LinearMap.ext
      intro phi
      exact Subtype.ext (Subtype.ext rfl)
  let E : RightFixedPart hA hM e ≃ₗ[ℂ] FullRightFixedPart hA hM e :=
    LinearEquiv.ofLinearMap (toFullFixed hA hM e) (fromFullFixed hA hM e)
      hInv.1 hInv.2.1
  let C : RightFixedPart hA hM e ≃ₗ[Idempotent.Corner (oppositeIdempotent e)]
      FullRightFixedPart hA hM e :=
    LinearEquiv.ofLinearMap (toFullFixedCorner hA hM e)
      (fromFullFixedCorner hA hM e) hInv.2.2.1 hInv.2.2.2
  have hBasic := (NonUnitalModuleDualFixedPart.fixedPartDuality.{uA, uM, uN}
    hA hM e).1
  let B : RightFixedPart hA hM e ≃ₗ[ℂ] Module.Dual ℂ (FixedPart e M) :=
    LinearEquiv.ofLinearMap (restriction hA hM e) (extension hA hM e)
      hBasic.1 hBasic.2
  have hCorner₁ :
      (restrictionCorner hA hM e).comp (extensionCorner hA hM e) = LinearMap.id := by
    apply LinearMap.ext
    intro ell
    exact DFunLike.congr_fun hBasic.1 ell
  have hCorner₂ :
      (extensionCorner hA hM e).comp (restrictionCorner hA hM e) = LinearMap.id := by
    apply LinearMap.ext
    intro phi
    exact DFunLike.congr_fun hBasic.2 phi
  let BC : RightFixedPart hA hM e ≃ₗ[Idempotent.Corner (oppositeIdempotent e)]
      Module.Dual ℂ (FixedPart e M) :=
    LinearEquiv.ofLinearMap (restrictionCorner hA hM e) (extensionCorner hA hM e)
      hCorner₁ hCorner₂
  refine ⟨hInv, ?_, ?_, ?_⟩
  · refine ⟨E, C, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · apply AddMonoidHom.ext
      intro phi
      rfl
    · apply AddMonoidHom.ext
      intro psi
      rfl
  · exact ⟨BC, E.symm.trans B, C.symm.trans BC,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro N _ _ hN f
    let _ := NondegenerateScalars.complexModule hA hN
    let _ := NonUnitalModuleCorner.complexModule hA hN e
    let _ := rightFixedModule hA hN e
    let _ := fullRightFixedModule hA hN e
    let _ := fixedPartDualCornerModule hA hN e
    let _ := NonUnitalModuleDual.fullAction hA hN
    let _ := NonUnitalModuleDual.dualAction hA hN
    let RC := NonUnitalModuleCorner.restrict (oppositeIdempotent e)
      (NonUnitalModuleDual.pullback hA hM hN f)
    let SC := NonUnitalModuleCorner.restrict (oppositeIdempotent e)
      (NonUnitalModuleDual.fullPullback hA hM hN f)
    let Dℂ := (NonUnitalModuleCorner.restrictLinear hA hM hN e f).dualMap
    let Rℂ : RightFixedPart hA hN e →ₗ[ℂ] RightFixedPart hA hM e :=
      { toFun := RC
        map_add' := RC.map_add
        map_smul' _ _ := Subtype.ext (Subtype.ext (by ext m; rfl)) }
    let Sℂ : FullRightFixedPart hA hN e →ₗ[ℂ] FullRightFixedPart hA hM e :=
      { toFun := SC
        map_add' := SC.map_add
        map_smul' _ _ := Subtype.ext (by ext m; rfl) }
    let DC : Module.Dual ℂ (FixedPart e N) →ₗ[Idempotent.Corner (oppositeIdempotent e)]
        Module.Dual ℂ (FixedPart e M) :=
      { toFun := Dℂ
        map_add' := Dℂ.map_add
        map_smul' a ell := by
          apply LinearMap.ext
          intro x
          change ell ((cornerUnop e a) •
              (NonUnitalModuleCorner.restrictLinear hA hM hN e f x)) =
            ell (NonUnitalModuleCorner.restrictLinear hA hM hN e f
              ((cornerUnop e a) • x))
          apply congrArg ell
          exact Subtype.ext (f.map_smul a.val.unop x.val).symm }
    refine ⟨Rℂ, Sℂ, DC, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply LinearMap.ext
      intro phi
      exact Subtype.ext rfl
    · apply LinearMap.ext
      intro psi
      exact Subtype.ext (Subtype.ext rfl)
    · apply LinearMap.ext
      intro phi
      exact Subtype.ext rfl
    · apply LinearMap.ext
      intro psi
      exact Subtype.ext (Subtype.ext rfl)
    · apply LinearMap.ext
      intro phi
      apply LinearMap.ext
      intro x
      rfl
    · apply LinearMap.ext
      intro ell
      apply Subtype.ext
      apply Subtype.ext
      apply LinearMap.ext
      intro m
      change ell (NonUnitalModuleCorner.projection e (f m)) =
        ell (NonUnitalModuleCorner.restrictLinear hA hM hN e f
          (NonUnitalModuleCorner.projection e m))
      apply congrArg ell
      exact Subtype.ext (f.map_smul (e : A) m).symm
    · apply LinearMap.ext
      intro psi
      apply LinearMap.ext
      intro x
      rfl
    · apply LinearMap.ext
      intro ell
      apply Subtype.ext
      apply LinearMap.ext
      intro m
      change ell (NonUnitalModuleCorner.projection e (f m)) =
        ell (NonUnitalModuleCorner.restrictLinear hA hM hN e f
          (NonUnitalModuleCorner.projection e m))
      apply congrArg ell
      exact Subtype.ext (f.map_smul (e : A) m).symm

example : FixedPartComparisons.{uA, uM, uN} := @fixedPartComparisons.{uA, uM, uN}
example : FixedPartComparisons.{0, 1, 2} := @fixedPartComparisons.{0, 1, 2}
example : FixedPartComparisons.{2, 1, 0} := @fixedPartComparisons.{2, 1, 0}

end Langlands.Algebra.NonUnitalModuleDualFixedPartComparisonProof
