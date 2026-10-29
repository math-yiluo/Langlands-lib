import Langlands.AbelianScheme.FieldAmpleMultiplicationKernelStatement
import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleProof
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.ProperAmpleTrivialFiniteProof

/-! # Finite multiplication kernel from an ample pullback identity -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

/-- The whole scheme-theoretic multiplication kernel is finite over the field
when an ample line bundle has the stated positive multiplication pullback identity. -/
theorem fieldAmpleMultiplicationKernel : FieldAmpleMultiplicationKernelStatement.{u} := by
  intro K _ G _ _ hproper _ L hL n hn hiso
  let : IsProper G.X.hom := hproper
  let f := multiplication G (n : ℤ)
  let i := (kernelι f).hom.hom.left
  let p := (kernel f).X.hom
  let e := η[G.X].left
  let M : LineBundle G.X.left := (LineBundle.pullback f.hom.hom.left).obj L
  let N : LineBundle (kernel f).X.left := (LineBundle.pullback i).obj M
  have hM : M.IsAmple := positiveTensorPowerAmple G.X.left L M (n * n) (Nat.mul_pos hn hn) hL hiso
  have hN : N.IsAmple := closedImmersionPullbackAmple G.X.left (kernel f).X.left i M inferInstance hM
  have hp : IsProper p := by
    change IsProper (kernel f).X.hom
    rw [← (kernelι f).hom.hom.w]
    infer_instance
  obtain ⟨he⟩ := fieldLineBundleTriviality K ((LineBundle.pullback e).obj L)
  apply properAmpleTrivialFinite K (kernel f).X.left p N hp hN
  refine ⟨?_⟩
  exact (Scheme.Modules.pullbackComp i f.hom.hom.left).app L.obj ≪≫
    (Scheme.Modules.pullbackCongr (kernel_isPullback_scheme f).w).app L.obj ≪≫
    ((Scheme.Modules.pullbackComp p e).app L.obj).symm ≪≫
    (Scheme.Modules.pullback p).mapIso he ≪≫
    Langlands.Scheme.Modules.pullbackUnitIso p

end Langlands.GroupScheme
