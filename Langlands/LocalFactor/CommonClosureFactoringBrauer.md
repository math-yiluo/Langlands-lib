# Unitary classes factoring through a finite Galois quotient, after transport

Author: Worker 5134. Module `Langlands.LocalFactor.CommonClosureFactoringBrauer`,
namespace `Langlands.LocalFactor.CommonClosure`. It builds on
`Langlands.LocalFactor.CommonClosureBoundedBrauer`. Universes: `uK` (the p-adic
field `K`), `uF` (a second p-adic field `F`), `uQ` (the finite group), `uV`
(extra carrier universe; the carriers live in `max uF uV`).

Throughout, `K : PadicField.{uK} p`, `W_K = localWeilGroup K` is its actual
local Weil group with projection `proj = localProjection K` to the absolute
Galois group of `K`, and `q : Gal(K̄/K) →* Q` is a group homomorphism to a
finite group `Q` (no continuity of `q` is assumed).

## Definition: `factoringKernelClosure`

`factoringKernelClosure K q` is the topological closure in `W_K` of the kernel
of `q ∘ proj : W_K →* Q`:

```lean
(q.comp (localProjection K).toMonoidHom).ker.topologicalClosure
```

## Results

- `ker_le_factoringKernelClosure`: the kernel of `q ∘ proj` is contained in it.
- Instances `factoringKernelClosure_normal` and
  `factoringKernelClosure_finiteIndex`: it is normal (closure of a normal
  subgroup in a topological group) and of finite index (it contains the kernel
  of a homomorphism to a finite group).
- `factoringKernelClosure_isOpen`: it is open, being closed of finite index.
- `exists_realizeExact_generator_eq`: for a continuous irreducible basis class
  `b` of `W_K` (carrier universe `uV`) that factors through `q ∘ proj` in the
  sense of `Weil.FactorsThrough`, there is a continuous representation `B` in
  the class `b`, trivial on `factoringKernelClosure K q`, such that
  `Weil.realizeExact (generator b)` is the exact class of `B`.
- `realizeExact_includeUnitary_mem_map_span`: let `F : PadicField.{uF} p` and
  let `T : W_K ≃ₜ* W_F` be an isomorphism of topological groups. Put
  `N = T(factoringKernelClosure K q)`, written as the preimage under `T⁻¹`.
  For every `x` in `LocalWeil.unitaryFiniteFactoringSupported K q` (carrier
  universe `max uF uV`), the exact class
  `LocalWeil.realizeExact K (LocalWeil.includeUnitary K x)` is the restriction
  along `T` (`ExactGrothendieckGroup.continuousRestrict T`) of an element of
  the `ℤ`-span of `inducedCharacterClassesAbove F N`.

## Proofs

`exists_realizeExact_generator_eq`. Choose a representative `B` of the class
`b`; it is continuous and irreducible. Factoring through `q ∘ proj` means that
`B` is isomorphic to `A ∘ q ∘ proj` for a representation `A` of `Q`. An
isomorphism conjugates the two actions (`Representation.Equiv.conj_apply_self`),
so `B` is trivial on the kernel of `q ∘ proj`. The kernel of `B` is closed
(`FiniteRepresentation.isClosed_ker_of_isContinuous`), so it contains the
closure of that kernel. The realization of the generator is the exact class
of the chosen representative by definition of `realizeExact` and
`basisContinuousClass`.

`realizeExact_includeUnitary_mem_map_span`. The subgroup `N` is open (preimage
of an open set under the continuous `T⁻¹`), normal and of finite index
(preimages of such subgroups). The support condition `unitaryFiniteFactoringSupported`
is `Finsupp.supported` on the unitary classes that factor through
`q ∘ proj`, which is the `ℤ`-span of their generators
(`Finsupp.supported_eq_span_single`); since the realization map, the inclusion
of unitary classes and the restriction along `T` are `ℤ`-linear, it suffices
to treat one generator `b`. Take `B` from `exists_realizeExact_generator_eq`
and let `B' = B ∘ T⁻¹`, a continuous representation of `W_F` trivial on `N`.
By `ofRepresentation_mem_span_inducedCharacterClassesAbove` (Brauer induction
for `W_F / N`) the exact class of `B'` is in the span; its restriction along
`T` is the restriction along `T` of the restriction along `T⁻¹` of `[B]`,
which is `[B]` (`continuousRestrictEquivalence T`).

## Provenance

Internal. The subgroup `factoringKernelClosure` is an auxiliary construction
for the proof of Henniart's Théorème 3.1 (relative form): it bounds every
continuous representation in the support of a class factoring through `q`, so
that Brauer induction can be applied in one finite quotient of the Weil group.
The transport along `T` moves the problem to the Weil group of the completion
of a number field, as in the statement of `RelativeGaloisGlobalization`.
