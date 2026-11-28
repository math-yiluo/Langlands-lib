# Test functions on the center and on its orthogonal

The module `Langlands.HarmonicAnalysis.UnitConjugation.CenterDecomposition` makes the
decomposition `A = z ⊕ V`, `V = z^⊥` the trace-form orthogonal of the center
(`isCompl_center_centerOrthogonal`, module
`Langlands.HarmonicAnalysis.UnitConjugation.TraceFormPairing`), topological, for a
finite-dimensional semisimple algebra `A` over a topological field of characteristic zero with
its module topology, and transports test functions and orbital integrals along it. All
declarations are in the namespace `Langlands.HarmonicAnalysis.UnitConjugation`.

## Topology

- `isModuleTopology_submodule`: a subspace of a vector space with its module topology carries
  the module topology. Proof: by `IsModuleTopology.of_continuous_id` it suffices that the
  identity from the subspace topology to the module topology is continuous; the module topology
  of `W` is coinduced by the projection along a complement (Mathlib's
  `ModuleTopology.eq_coinduced_of_surjective`), and the identity of `W` is the projection
  composed with the inclusion.
- `centerSubmodule F A`, the center as a subspace; instances `isModuleTopology_centerSubmodule`
  and `isModuleTopology_centerOrthogonal`.
- `centerDecomposition : z × V ≃L[F] A`, `(Z, Y) ↦ Z + Y` (`centerDecomposition_apply`), the
  linear equivalence `Submodule.prodEquivOfIsCompl`, continuous in both directions because
  linear maps out of spaces with the module topology are continuous. Lemmas:
  `centerDecomposition_symm_apply_eq`, `centerDecomposition_symm_add`,
  `centerDecomposition_symm_of_mem`, `centerDecomposition_symm_add_central`.
- `centerOrthogonalConj u`: conjugation by `u` restricted to `V`;
  `centerDecomposition_symm_conj`: conjugation fixes the central component and conjugates the
  `V`-component.

## Test functions

- `restrictCenterOrthogonal f`: the restriction of `f` to `V` (a Schwartz–Bruhat function,
  through the projection to `V` as continuous left inverse of the inclusion).
- `extendTest α β` pulls `SchwartzBruhat.tensor α β` back along
  `(centerDecomposition F A).symm`, which sends `X` to its components `(Z, Y)`.
  Thus `extendTest_apply` gives `extendTest α β X = α(Z) β(Y)`.
  The lemma `extendTest_apply_coe` gives `extendTest α β Y = α(0) β(Y)` for `Y ∈ V`.
  By `translateTest_extendTest`, central translation acts on `α`. By
  `scalarDilation_extendTest`, dilation acts on both factors.
- `CenterOrthogonalVanishing F A β`: for every test function `α` on `z` and every regular
  `Y ∈ V`, `OrbitalVanishingAt Y (extendTest α β)`; it is the `D₀` of `V`, and
  `centerOrthogonalVanishingSubmodule` is this subspace.

## Results

- `CenterOrthogonalVanishing.regularOrbitalVanishing`: if `β` lies in the `D₀` of `V`, then
  `extendTest α β ∈ D₀` for every `α`. A regular `X` is `Y + Z` with `Z` central and `Y ∈ V`
  regular; by `orbitalVanishingAt_add_central_iff` and `translateTest_extendTest` the orbital
  integrals of `extendTest α β` at `X` are those of `extendTest (α(· + Z)) β` at `Y`.
- `RegularOrbitalVanishing.centerOrthogonalVanishing_restrict`: the restriction to `V` of a
  function of `D₀` lies in the `D₀` of `V`: on the orbit of `Y ∈ V`, contained in `V`,
  `extendTest α (f|_V) = α(0) f`.
- `CenterOrthogonalVanishing.add`, `.smul`, `centerOrthogonalVanishing_zero`: linearity;
  `CenterOrthogonalVanishing.scalarDilation`: stability under `β ↦ β_s`, from
  `scalarDilation_extendTest` and the dilation stability of `D₀`.

## Source

This is the splitting `D(g) = D(z) ⊗ D(g₁)` by which Harish-Chandra reduces Theorem 3.1 to the
case of semisimple groups: Harish-Chandra, *Admissible invariant distributions on reductive
p-adic groups*, with notes by S. DeBacker and P. J. Sally, Jr., University Lecture Series 16,
AMS, 1999, source ID `harish-chandra-1999-admissible-invariant-distributions`, §3.4,
Lemma 3.11, printed p. 26 (PDF p. 41).
