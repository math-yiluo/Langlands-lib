import Langlands.GroupScheme.Reductive.GeometricReductivityShift
import Langlands.GroupScheme.Dynamic.GeneralLinearDecomposition
import Langlands.GroupScheme.Rational.SemistandardIntersection

/-! # Geometric reductivity of `GL_n` and the radicals of its block parabolics -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.GeneralLinear

/-- Two geometric structure assertions for the matrix-coordinate group `GL_n`.
(1) Over every algebraically closed field, `GL_n` is geometrically reductive in Haboush's
sense. (2) Over every field and for every weight function `e`, the block unipotent subgroup
scheme, mapped into the block parabolic subgroup scheme through the kernel of the block limit
homomorphism, is the geometric unipotent radical of the block parabolic. -/
def GeometricStructureStatement : Prop :=
  (∀ (k : Type u) [Field k] [IsAlgClosed k] (n : Type) [Fintype n] [DecidableEq n],
      IsGeometricallyReductive (groupScheme n (CommRingCat.of k))) ∧
    ∀ (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n] (e : n → ℤ),
      IsGeometricUnipotentRadical
        ((blockUnipotentIsoKernel n (CommRingCat.of k) e).hom ≫
          kernelι (blockLimitHom n (CommRingCat.of k) e))

end Langlands.GroupScheme.GeneralLinear
