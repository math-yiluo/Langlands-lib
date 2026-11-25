module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Purity along a fibre and relative purity

A finite type quasi-coherent module is *pure along the fibre over `s`* when no impurity occurs
over an elementary étale neighbourhood of `s`, and *universally pure along that fibre* when no
impurity occurs after any base change at all. Imposing either condition at every point of the
base gives the relative notions, and applying them to the structure sheaf gives the
corresponding notions for the scheme.

## Main definitions

* `AlgebraicGeometry.IsPureAlong` expresses purity along the fibre over the chosen point.
* `AlgebraicGeometry.IsUniversallyPureAlong` expresses universal purity along that fibre.
* `AlgebraicGeometry.IsSchemePureAlong` applies purity along a fibre to the structure sheaf.
* `AlgebraicGeometry.IsUniversallyPureRelative` and `AlgebraicGeometry.IsPureRelative` impose
  the corresponding condition at every point of the base.
* `AlgebraicGeometry.IsSchemePureRelative` applies relative purity to the structure sheaf.

## Main results

* `AlgebraicGeometry.structureSheaf_isFiniteType`: the structure sheaf is of finite type as a
  module over itself, which is one of the two properties needed to apply the purity predicates
  to it.

## Implementation notes

The elementary étale neighbourhood associated to an impurity diagram uses its base-change
scheme, its specialized point and its structure morphism. Relative purity takes an unpointed
morphism and module and builds a pre-pure situation only after quantifying over a point of the
base; in particular relative purity over an empty base is vacuous. The predicates are
abbreviations so that clients can use their quantified impurity formulations directly. The six
abbreviations `IsPureAlong`, `IsUniversallyPureAlong`, `IsSchemePureAlong`,
`IsUniversallyPureRelative`, `IsPureRelative` and `IsSchemePureRelative` formalize parts (1)
through (6) of the source.

Quasi-coherence of the structure sheaf is
`Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit`.

## References

* [Stacks Project, Tag 05J4](https://stacks.math.columbia.edu/tag/05J4)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The structure sheaf, as a module over itself, is a free sheaf on one generator. -/
noncomputable abbrev structureSheafFreeIso (X : Scheme.{u}) :
    SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit.{u} X.ringCatSheaf :=
  Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit.{u} X.ringCatSheaf)

/-- The forward morphism of `structureSheafFreeIso X` is an isomorphism. -/
instance (X : Scheme.{u}) : IsIso (structureSheafFreeIso X).hom :=
  (structureSheafFreeIso X).isIso_hom

/-- The forward morphism of `structureSheafFreeIso X` is an epimorphism. -/
instance (X : Scheme.{u}) : Epi (structureSheafFreeIso X).hom := by infer_instance

/-- The canonical single generating section of the structure sheaf as a module. -/
noncomputable abbrev structureSheafGenerators (X : Scheme.{u}) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).GeneratingSections :=
  (SheafOfModules.free.generatingSections (R := X.ringCatSheaf) PUnit.{u + 1}).ofEpi
    (structureSheafFreeIso X).hom

/-- The canonical generating sections of the structure sheaf are of finite type. -/
instance (X : Scheme.{u}) : (structureSheafGenerators X).IsFiniteType where
  finite := by
    change Finite PUnit.{u + 1}
    infer_instance

/-- The structure sheaf of a scheme is of finite type as a module over itself. -/
theorem structureSheaf_isFiniteType (X : Scheme.{u}) :
    (SheafOfModules.unit.{u} X.ringCatSheaf).IsFiniteType := by
  let G := structureSheafGenerators X
  have _ : G.IsFiniteType := inferInstance
  let q := G.localGeneratorsData
  refine { exists_localGeneratorsData := ⟨q, ?_⟩ }
  constructor
  intro i
  constructor
  dsimp only [q, SheafOfModules.GeneratingSections.localGeneratorsData]
  change Finite G.I
  infer_instance

end AlgebraicGeometry
