import Langlands.Representation.Plancherel.TorusNormKernelCompactnessStatement
import Langlands.BruhatTits.RationalPoints.SmoothRealStructureStatement
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplittingDescentHelpers

/-! # Torus norm-kernel compactness from central norm-kernel compactness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every affine torus over a field is a connected reductive group. -/
theorem IsTorus.isConnectedReductive {k : Type u} [Field k]
    {T : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom T.X.hom] (hT : IsTorus T) :
    IsConnectedReductive T := by
  refine ⟨hT.smooth, inferInstance, hT.connectedSpace, ?_⟩
  obtain ⟨K, hK, hA, hfin, -, hs⟩ := torusFiniteGaloisSplitting k T hT
  let : Field K := hK
  let : Algebra k K := hA
  have : FiniteDimensional k K := hfin
  have : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let f : K →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let : Algebra K (AlgebraicClosure k) := f.toRingHom.toAlgebra
  have : IsScalarTower k K (AlgebraicClosure k) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  exact (IsSplitTorus.baseChange_fieldTower k K (AlgebraicClosure k) T
    hs).hasTrivialUnipotentRadical

/-- The scheme center of a commutative group scheme over a field contains every rational
point. -/
theorem schemeCenterPoints_eq_top_of_isCommMonObj {k : Type u} [Field k]
    (T : GroupScheme (Spec (CommRingCat.of k))) [IsCommMonObj T.X] :
    schemeCenterPoints T = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  intro T' a h
  exact Commute.all _ _

end Langlands.GroupScheme

namespace Langlands.Plancherel

open GroupScheme

set_option linter.defProp false in
/-- Compactness of central norm-kernel points for every connected reductive group gives
compactness of the whole norm kernel of every affine finite-type torus. The central
compactness proposition remains an explicit input. -/
def torusNormKernelCompactness_of_centralNormKernelCompactness
    (h : BruhatTits.RationalPoints.CentralNormKernelCompactnessStatement.{u}) :
    TorusNormKernelCompactnessStatement.{u} := by
  intro F _ _ _ _ T _ _ hT
  have hC := h F T hT.isConnectedReductive
  have : IsCommMonObj T.X := hT.isCommMonObj
  unfold BruhatTits.RationalPoints.CentralNormKernelCompactness at hC
  rw [schemeCenterPoints_eq_top_of_isCommMonObj T] at hC
  simpa using hC

end Langlands.Plancherel
