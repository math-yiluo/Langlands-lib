module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.RingTheory.Nullstellensatz
public import StacksCore.FieldTheory.MvRatFunc.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseFibreShrinking
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.FibreOfOpenRestriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.DenseOpenIso
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.ReducedReduction
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The residue field at the generic point of a scheme with geometrically integral generic fibre

Let `R` be a domain with fraction field `K`, let `f : X ⟶ Spec R` be a morphism locally of finite
type with `X` integral, and suppose the generic point of `X` lies over the generic point `η` of
`Spec R`. The generic fibre `f.fiber η` is then an integral `K`-scheme whose generic point is
carried to the generic point of `X` by the inclusion of the fibre, so the residue field of `X` at
its generic point is the function field of the generic fibre. When the generic fibre is
geometrically irreducible and geometrically reduced over `K`, that function field is a
geometrically integral extension of `K`, and in particular stays a domain after base change to
an algebraic closure of `K`.

## Main results

* `AlgebraicGeometry.genericResidueFieldIsDomainTensor`: the residue field of `X` at its generic
  point stays a domain after base change to an algebraic closure of `K`.
* `AlgebraicGeometry.geometricallyIrreducibleAfterShrinkingOverDomain` and
  `AlgebraicGeometry.geometricallyIrreducibleAfterShrinking`: **Stacks Tag 0559**, over a domain
  base and in general.

## Implementation notes

Geometric irreducibility of the function field of the generic fibre is read off the fibre by
`AlgebraicGeometry.geometricallyIrreducible_tfae_functionField`, and geometric reducedness by
`AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk`, which speaks
about the local ring rather than the residue field; the two agree at the generic point of an
integral scheme. Both are stated for the algebra structure obtained by evaluating global
sections, whereas the statement to be proved uses the residue field map of `f`. The two agree
because a ring homomorphism out of `K` is determined by its restriction to `R`, `K` being a
field of fractions of `R`.

## References

* [Stacks Project, Tag 054Q](https://stacks.math.columbia.edu/tag/054Q)
* [Stacks Project, Tag 035W](https://stacks.math.columbia.edu/tag/035W)
* [Stacks Project, Tag 05DY](https://stacks.math.columbia.edu/tag/05DY)
* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559), the first proof
-/

@[expose] public section

open CategoryTheory CommRingCat

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The canonical morphism from the spectrum of a residue field of an affine scheme is the
spectrum of the canonical map of the base ring into that residue field. -/
theorem fromSpecResidueField_eq_specMap (R : CommRingCat.{u}) (x : Spec R) :
    (Spec R).fromSpecResidueField x =
      Spec.map (CommRingCat.ofHom (@algebraMap ↥R ↥((Spec R).residueField x) _ _
        (specResidueFieldAlgebra R x))) := by
  have : x.asIdeal.IsPrime := x.isPrime
  have h : CommRingCat.ofHom (@algebraMap ↥R ↥((Spec R).residueField x) _ _
        (specResidueFieldAlgebra R x)) =
      CommRingCat.ofHom (algebraMap ↥R x.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R x).inv := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv]
    rfl
  rw [h, Spec.map_comp, Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]

section Fibre

variable {R : CommRingCat.{u}} [IsDomain R] {X : Scheme.{u}} [IrreducibleSpace X]
  (f : X ⟶ Spec R) (hgen : f (genericPoint X) = genericPoint (Spec R))

end Fibre

end AlgebraicGeometry

end
