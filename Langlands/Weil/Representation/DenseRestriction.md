# Restriction of continuous representations along a map with dense image

Module `Langlands.Weil.Representation.DenseRestriction`. It shows that restriction along a
monoid homomorphism `φ : H →* G` with dense image preserves and reflects intertwiners,
isomorphism, subrepresentations, irreducibility and closed conditions on matrix entries. This
holds for representations of `G` whose action map is continuous for the module topology on the
endomorphisms. This is the density argument used for continuous Galois representations and
their restrictions to a Weil group. The results are derived and are not taken from a source.
They follow from `DenseRange.induction_on` (a closed set containing a dense image is
everything) and the closedness lemmas below.

## Setting

- `E` is a field with a topology. Continuity of matrix coefficients needs
  `IsTopologicalRing E`; the closedness results also need `T2Space E`. `E` need not be
  complete: the Library applies the module to `PadicAlgCl ℓ`, which is not complete.
- `G` is a monoid with a topology (no topological-group axioms are used), `H` is a monoid
  and `φ : H →* G` is a homomorphism with `DenseRange φ`.
- A representation `ρ : Representation E G V` is called continuous here when `ρ`, as a map
  `G → Module.End E V`, is continuous for a topology on `Module.End E V` that is the module
  topology (`IsModuleTopology E (Module.End E V)`). The results in the namespace
  `Langlands.Representation` take such instances. `V` and `W` are arbitrary `E`-vector spaces
  there, with no finiteness condition.
- The two results in the namespace `Langlands.FiniteRepresentation` take the continuity
  hypothesis in the form
  `letI := moduleTopology E (Module.End E A); Continuous A.representation`. This is the form of
  `Langlands.Henniart.LocalNumerical.IsLadicContinuous`, which is the case
  `E = PadicAlgCl ℓ`.

## Closed conditions

- `continuous_dual_apply`: for continuous `ρ`, a linear functional `ψ` on `V` and `v : V`, the
  matrix coefficient `g ↦ ψ (ρ g v)` is continuous. The map `T ↦ ψ (T v)` is `E`-linear on
  `Module.End E V`, hence continuous for the module topology
  (`IsModuleTopology.continuous_of_linearMap`).
- `isClosed_setOf_eq_of_continuous_dual`: let `α, β : G → W` be maps such that `g ↦ ψ (α g)`
  and `g ↦ ψ (β g)` are continuous for every linear functional `ψ`. Then `{g | α g = β g}` is
  closed. A vector of a vector space on which every linear functional vanishes is zero
  (`Module.forall_dual_apply_eq_zero_iff`), so the set is the intersection over `ψ` of the
  equalizers of `g ↦ ψ (α g)` and `g ↦ ψ (β g)`. These equalizers are closed because `E` is
  Hausdorff.
- `isClosed_setOf_intertwines`: for continuous `ρ`, `σ` and a linear map `f : V →ₗ[E] W`, the
  set `{g | ∀ v, f (ρ g v) = σ g (f v)}` is closed. It is an intersection over `v`, and the
  previous lemma applies with the functionals `ψ ∘ f` and `ψ`.
- `isClosed_setOf_mapsTo`: for continuous `ρ` and a subspace `U`, the set
  `{g | ∀ v ∈ U, ρ g v ∈ U}` is closed. A vector lies in `U` if and only if every functional
  of the dual annihilator of `U` vanishes on it
  (`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`). So the set is the intersection
  of the closed sets `{g | ψ (ρ g v) = 0}` for `v ∈ U` and `ψ` in the dual annihilator.
- `isClosed_setOf_repr_mem`: for continuous `ρ`, a basis `b` and a closed set `S ⊆ E`, the set
  `{g | b.repr (ρ g (b j)) i ∈ S}` is closed. It is the preimage of `S` under the matrix
  coefficient for `b.coord i` and `b j`. This lemma does not need `E` to be Hausdorff.

Testing with linear functionals instead of using closed subspaces avoids completeness. Mathlib's
`Submodule.closed_of_finiteDimensional` needs a complete field, and `PadicAlgCl ℓ` is not
complete.

## Restriction along `φ`

In each of the following, `hφ : DenseRange φ` and the representations are continuous.

- `intertwines_iff_of_denseRange`: `f` intertwines `ρ` and `σ` if and only if it intertwines
  them at every `φ h`.
- `mapsTo_iff_of_denseRange`: a subspace is stable under every `ρ g` if and only if it is
  stable under every `ρ (φ h)`.
- `repr_mem_of_denseRange`: if the `(i, j)` entries in the basis `b` of all `ρ (φ h)` lie in
  the closed set `S`, then so do the entries of all `ρ g`.
- `nonempty_equiv_iff_of_denseRange`: `ρ` and `σ` are equivalent (`Representation.Equiv`) if
  and only if `ρ.comp φ` and `σ.comp φ` are. An equivalence of `ρ` and `σ` restricts. In the
  other direction, the linear equivalence underlying an equivalence of the restrictions
  intertwines `ρ` and `σ` by `intertwines_iff_of_denseRange`.
- `subrepresentationOrderIsoOfDenseRange`: the order isomorphism
  `Subrepresentation ρ ≃o Subrepresentation (ρ.comp φ)` that sends a subrepresentation to the
  one with the same subspace. The inverse uses `mapsTo_iff_of_denseRange`. Both orders are
  inclusion of the underlying sets, so the map and its inverse are mutually inverse and
  preserve the order by definition.
- `isIrreducible_comp_iff_of_denseRange`: `ρ` is irreducible if and only if `ρ.comp φ` is.
  Mathlib's `Representation.IsIrreducible ρ` is `IsSimpleOrder (Subrepresentation ρ)`, which the
  order isomorphism transports (`OrderIso.isSimpleOrder_iff`).

For finite-dimensional representations (`Langlands.FiniteRepresentation`, restriction
`Langlands.FiniteRepresentation.restrict`, whose action is `A.representation.comp φ` on the
same carrier):

- `FiniteRepresentation.isIsomorphic_restrict_iff_of_denseRange`: `IsIsomorphic A B` if and
  only if `IsIsomorphic (restrict φ A) (restrict φ B)`.
- `FiniteRepresentation.isIrreducible_restrict_iff_of_denseRange`: `A.representation` is
  irreducible if and only if `(restrict φ A).representation` is.

Both put the module topology on the endomorphisms and apply the corresponding results above.

## Dependencies

The module imports `Langlands.Weil.Representation.Restriction` and the Mathlib modules
`Mathlib.LinearAlgebra.Dual.Lemmas`, `Mathlib.RepresentationTheory.Irreducible`,
`Mathlib.Topology.Algebra.Module.ModuleTopology` and `Mathlib.Topology.DenseEmbedding`. Its
import closure does not contain weil-conjectures.
