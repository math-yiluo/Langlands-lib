module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.Tactic.CrossRefAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.NormalizationStalkAmbient.Reduction
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components
public import StacksFrontier.RingTheory.Ideal.Over.HeightOne
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Quasi-finiteness and finiteness in codimension one

Let `f : X ⟶ Y` be locally of finite type and let `y` be a point of `Y` whose local ring is
Noetherian of dimension at most one. If `f` is generically quasi-finite — in any one of four
standard senses — then `f` is quasi-finite at every point of `X` above `y`; if moreover `f` is
proper, then `f` is finite over an open neighbourhood of `y`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.genericPoints_mem_dense_open` and
  `AlgebraicGeometry.scheme_genericPoints_mem_dense_open`: a generic point of a Noetherian space,
  respectively of a locally Noetherian scheme, lies in every dense open.
* `AlgebraicGeometry.quasiFiniteAt_of_target_stalk_dimension_le_one`: quasi-finiteness at every
  point above `y`.
* `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_ringKrullDim_stalk_le_one`: for a proper
  morphism, an open neighbourhood of `y` over which `f` is finite.

## Implementation notes

Generic points of irreducible components are the points of `genericPoints`. The parenthetical
formulation of the source is used for the residue-field hypotheses: for a morphism locally of
finite type, algebraicity of `κ(η)/κ(f η)` is equivalent to finiteness. The algebra structures
are the canonical ones induced by `AlgebraicGeometry.Scheme.Hom.residueFieldMap`, and
specialization of `f η` to `y` is `Specializes (f η) y`. The fourth alternative, that `f` is
quasi-finite at a dense set of points, is expressed by density of the set of points at which it
is quasi-finite. Restriction of a morphism over an open subscheme is Mathlib's `f ∣_ V`.

## References

* [Stacks Project, Tag 0AB6](https://stacks.math.columbia.edu/tag/0AB6)
* [Stacks Project, Tag 0AB7](https://stacks.math.columbia.edu/tag/0AB7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A generic point of a Noetherian space lies in every dense open.** The irreducible
component of which it is the generic point has a nonempty open subset, which meets the dense
open, and the generic point specializes to any point of that subset. -/
public lemma genericPoints_mem_dense_open {Y : Type*} [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] {D : Set Y} (hD : IsOpen D)
    (hd : Dense D) {y : Y} (hy : y ∈ genericPoints Y) : y ∈ D := by
  obtain ⟨V, hV, hVne, hVZ⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (closure {y}) hy
  obtain ⟨z, hzV, hzD⟩ := hd.inter_open_nonempty V hV hVne
  exact (specializes_iff_mem_closure.mpr (hVZ hzV)).mem_open hD hzD

/-- **A generic point of a locally Noetherian scheme lies in every dense open.** A locally
Noetherian scheme need not be a Noetherian space, so
`AlgebraicGeometry.genericPoints_mem_dense_open` is applied on an affine open containing the
point, which is Noetherian and in which the point is still a generic point. -/
public lemma scheme_genericPoints_mem_dense_open (Y : Scheme.{u})
    [IsLocallyNoetherian Y] {D : Set Y} (hD : IsOpen D)
    (hd : Dense D) {y : Y} (hy : y ∈ genericPoints Y) : y ∈ D := by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : CompactSpace V := isCompact_iff_compactSpace.mp hV.isCompact
  have : IsNoetherian V := { __ := isLocallyNoetherian_of_isOpenImmersion V.ι }
  let v : V := ⟨y, hyV⟩
  have hcomp : V.ι ⁻¹' closure ({y} : Set Y) ∈ irreducibleComponents V :=
    preimage_mem_irreducibleComponents hy V.ι.isOpenEmbedding
      ⟨y, subset_closure (Set.mem_singleton y), v, rfl⟩
  have hv : v ∈ genericPoints V := by
    change closure ({v} : Set V) ∈ irreducibleComponents V
    convert hcomp using 1
    rw [V.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      V.ι.continuous]
    congr 1
    ext z
    exact Subtype.ext_iff
  have hvD := genericPoints_mem_dense_open
    (hD.preimage V.ι.continuous) (hd.preimage V.ι.isOpenEmbedding.isOpenMap) hv
  change V.ι v ∈ D at hvD
  simpa [v] using hvD

end AlgebraicGeometry

end
