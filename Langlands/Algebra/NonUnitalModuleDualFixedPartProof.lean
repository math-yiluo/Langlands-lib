import Langlands.Algebra.NonUnitalModuleDualFixedPartStatements

/-!
Canonical fixed-part duality for the original nonunital actions.
Proof by Worker 1149, using the published statement and map constructions.
-/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualFixedPart

open NonUnitalModuleCorner (FixedPart)
open NonUnitalModuleDualFixedPartMaps

universe uA uM uN

/-- Canonical restriction and projection-extension are inverse and natural. -/
theorem fixedPartDuality : FixedPartDuality.{uA, uM, uN} := by
  intro A _ _ _ _ M _ _ hA hM e
  let _ := NondegenerateScalars.complexModule hA hM
  let _ := NonUnitalModuleCorner.complexModule hA hM e
  let _ := rightFixedModule hA hM e
  have hInv : InverseIdentities hA hM e := by
    constructor
    · apply LinearMap.ext
      intro ell
      apply LinearMap.ext
      intro x
      change ell (NonUnitalModuleCorner.projection e x.val) = ell x
      exact congrArg ell (Subtype.ext x.property)
    · apply LinearMap.ext
      intro φ
      apply Subtype.ext
      apply Subtype.ext
      apply LinearMap.ext
      intro m
      exact rightFixedPart_fixed_apply hA hM e φ m
  refine ⟨hInv, ?_, ?_⟩
  · exact ⟨LinearEquiv.ofLinearMap (restriction hA hM e) (extension hA hM e)
      hInv.1 hInv.2, rfl, rfl⟩
  · intro N _ _ hN f
    let _ := NondegenerateScalars.complexModule hA hN
    let _ := NonUnitalModuleCorner.complexModule hA hN e
    let _ := rightFixedModule hA hN e
    let _ := NonUnitalModuleDual.fullAction hA hM
    let _ := NonUnitalModuleDual.fullAction hA hN
    let _ := NonUnitalModuleDual.dualAction hA hM
    let _ := NonUnitalModuleDual.dualAction hA hN
    let raw := NonUnitalModuleCorner.restrict (oppositeIdempotent e)
      (NonUnitalModuleDual.pullback hA hM hN f)
    let T : RightFixedPart hA hN e →ₗ[ℂ] RightFixedPart hA hM e :=
      { toFun := raw
        map_add' := raw.map_add
        map_smul' _ _ := Subtype.ext (Subtype.ext (by ext m; rfl)) }
    refine ⟨T, rfl, ?_, ?_⟩
    · apply LinearMap.ext
      intro φ
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

example : FixedPartDuality.{uA, uM, uN} := fixedPartDuality.{uA, uM, uN}
example : FixedPartDuality.{0, 1, 2} := fixedPartDuality.{0, 1, 2}
example : FixedPartDuality.{2, 1, 0} := fixedPartDuality.{2, 1, 0}

end Langlands.Algebra.NonUnitalModuleDualFixedPart
