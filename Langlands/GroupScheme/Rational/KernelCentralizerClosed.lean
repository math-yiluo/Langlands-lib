import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.FixedRepresentabilityStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Dynamic.ActionConjugation

/-! # Closed-representability reductions for character-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}

/-- The actual character kernel, retaining the inherited commutative group law. -/
abbrev characterKernelComm (a : characterLattice T) : CommGroupScheme B where
  toGrp := characterKernel a

/-- The character kernel of an affine commutative group scheme is affine. -/
theorem characterKernel_isAffineHom [IsAffineHom T.X.hom] (a : characterLattice T) :
    IsAffineHom (characterKernel a).X.hom := by
  let : IsAffineHom (Gm B).X.hom := isSplitTorus_gm.isAffineHom
  rw [← (characterKernelι a).hom.hom.w]
  infer_instance

/-- The kernel centralizer is the ordinary all-test centralizer of its inclusion. -/
theorem kernelCentralizer_eq_torusCentralizer (i : T.toGrp ⟶ G)
    (a : characterLattice T) :
    kernelCentralizer i a =
      torusCentralizer (T := characterKernelComm a) (characterKernelι a ≫ i) := by
  rw [kernelCentralizer, AutomorphicAction.restrict_conjugation,
    AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer
      (C := characterKernelComm a)]

/-- Field fixed-subgroup representability specializes to the actual kernel centralizer. -/
theorem kernelCentralizer_isClosedRepresentable_of_fieldFixed
    (h : FieldFixedSubgroupRepresentabilityStatement.{u})
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.X.hom]
    (i : S.toGrp ⟶ U) (a : characterLattice S) :
    (kernelCentralizer i a).IsClosedRepresentable :=
  h k (characterKernel a) U (characterKernel_isAffineHom a)
    ((AutomorphicAction.conjugation i).restrict (characterKernelι a))

/-- Field centralizer representability also specializes directly to the same kernel. -/
theorem kernelCentralizer_isClosedRepresentable_of_fieldCentralizer
    (h : FieldCentralizerRepresentabilityStatement.{u})
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom S.X.hom]
    (i : S.toGrp ⟶ U) (a : characterLattice S) :
    (kernelCentralizer i a).IsClosedRepresentable := by
  rw [kernelCentralizer_eq_torusCentralizer]
  exact h k (characterKernelComm a) U (characterKernel_isAffineHom a)
    (characterKernelι a ≫ i)

end Langlands.GroupScheme.RelativeRoot
