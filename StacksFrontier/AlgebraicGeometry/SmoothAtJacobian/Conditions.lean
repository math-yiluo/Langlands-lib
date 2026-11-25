module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Smooth.InfinitesimalLifting
public import StacksFrontier.Topology.Dimension.Krull

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# The six characterizations of smoothness at a point

Stacks Tag 01V9 asserts, for a morphism of schemes locally of finite presentation and a point
of its source, the equivalence of six conditions: smoothness at the point; flatness of the
induced map of local rings together with smoothness of the scheme-theoretic fibre; two numerical
conditions on the relative differentials, one on their stalk and one on its residue-field fibre;
the existence of an affine neighbourhood over an affine open of the base on which the morphism
is standard smooth; and the existence of an affine presentation whose chosen Jacobian minor does
not vanish at the point.

**This file only states the six conditions.**  It names each of them separately, so that the
implications between them can be proved and recorded one at a time, and collects them in the
order the source uses.  `StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Jacobian` proves the
equivalence of the first, the fifth and the sixth.

## Main definitions

* `Stacks.SmoothAtJacobian.GeneratedByAtMost`: a module admits a finite generating set whose
  cardinality is bounded by a given extended natural number.
* `Stacks.SmoothAtJacobian.relativeDifferentialStalk`, with its module structure
  `relativeDifferentialStalkModule`: the stalk at the point of the sheaf of relative
  differentials.
* `Stacks.SmoothAtJacobian.relativeCotangentSpace`: the residue-field fibre of that stalk, and
  `fiberRelativeCotangentSpace` the corresponding space computed on the scheme-theoretic fibre.
* `Stacks.SmoothAtJacobian.IsFiberDifferentialsTensorEquiv` and
  `FiberDifferentialsTensorIdentification`: the specification of the canonical comparison between
  those two spaces, and the data of a comparison satisfying it together with its uniqueness.
  These are the vocabulary of the displayed equality in condition (4) of the source.
* `Stacks.SmoothAtJacobian.Condition1` through `Condition6`: the six conditions.
* `Stacks.SmoothAtJacobian.conditions`: the six conditions as a list, in the source's order.

## Implementation notes

Conditions (3) and (4) are stated with the actual stalk of the universal sheaf of relative
differentials, `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, which is the representing
object for relative derivations of the structure sheaf along
`AlgebraicGeometry.inverseImageStructureMap`.  Its module structure over the stalk of the
structure sheaf is the one Mathlib puts on the stalk of a presheaf of modules; instance search
does not find it through the definition `AlgebraicGeometry.Scheme.Modules`, so
`relativeDifferentialStalkModule` names it.

The displayed equality in condition (4) of the source is an equality of modules, which is not a
statement Lean can carry; it is represented here by the existence of a unique linear equivalence
subject to a specification on germs of universal differentials.  Both cotangent spaces are
extended to the residue field of the point; on the fibre side that scalar structure comes from
the canonical residue-field point `AlgebraicGeometry.Scheme.Hom.asFiberHom`.

Condition (6) records a pre-submersive presentation, which carries the quotient presentation
together with the injection selecting the variables used for the Jacobian minor.  This is the
invariant form of the source's choice of the first `c` of the `n` variables.

## References

* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u v

namespace Stacks.SmoothAtJacobian

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- Condition (1) of the source: `f` is smooth at `x`. -/
public def Condition1 : Prop :=
  InfinitesimalLifting.SmoothAt f x

/-- Condition (2) of the source: the induced map of local rings is flat, and the
scheme-theoretic fibre through `x` is smooth at `x`. -/
public def Condition2 : Prop :=
  (f.stalkMap x).hom.Flat ∧
    InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f x)) (f.asFiber x)

end Stacks.SmoothAtJacobian

end
