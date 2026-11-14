import Langlands.Geometry.Building.Kottwitz.ZeroKernelStatement
import Langlands.Geometry.Building.Kottwitz.ReductiveMapStatement
import Langlands.Geometry.Building.UnramifiedZeroDescentStatement
import Langlands.Geometry.Building.KPZeroDatumConstruction
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Reduction of the rational Kottwitz kernel to the unramified kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.Kottwitz

/-- The unramified kernel equality on the original group's actual coefficient points. -/
def UnramifiedZeroKernelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (k : Type u) [Field k] [Algebra k (UnramifiedClosure F)]
    [Algebra k (SeparableClosure F)] [IsScalarTower k (UnramifiedClosure F) (SeparableClosure F)]
    [IsSepClosure k (SeparableClosure F)] [Normal k (UnramifiedClosure F)]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (E : UnramifiedZeroDatum F (baseChanged k (UnramifiedClosure F) G)),
    E.zeroPoints = (reductiveKottwitz F k G hG).ker.comap
      (baseChangeCoeffEquiv k (UnramifiedClosure F) G).toMonoidHom

/-- Descent of the actual maps and zero subgroups suffices to descend the kernel equality. -/
theorem zeroKernel_of_unramified
    (hmap : ReductiveKottwitzDescentStatement.{u})
    (hzero : UnramifiedZeroDescentStatement.{u})
    (hkernel : UnramifiedZeroKernelStatement.{u}) :
    ZeroKernelStatement.{u} := by
  intro F _ _ _ _ G hG S Z i j d
  have hGK := connectedReductiveFieldExtensionStatement F (UnramifiedClosure F) G hG
  obtain ⟨D, C, dK, π, hcover⟩ :=
    simplyConnectedDerivedCoverExistence (UnramifiedClosure F)
      (baseChanged F (UnramifiedClosure F) G) hGK
  let E := UnramifiedZeroDatum.ofDerivedCover dK π hcover
  have hdes := ((hzero F G hG).2 E).2 i j d
  have hrestr := (hmap.2 F G hG).2.2
  have hinj : Function.Injective (reductiveInvariantInclusion F G hG) := by
    intro a b hab
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact hab
  rw [← hdes, hkernel F F G hG E]
  ext x
  change reductiveKottwitz F F G hG
      (baseChangeCoeffEquiv F (UnramifiedClosure F) G
        (rationalExtend F (UnramifiedClosure F) G x)) = 1 ↔
    reductiveKottwitzRational F G hG x = 1
  rw [baseChangeCoeffEquiv_rationalExtend, ← hrestr x]
  constructor
  · intro hx
    apply hinj
    simpa using hx
  · intro hx
    simp [hx]

end Langlands.Geometry.Building.Kottwitz
