# Universe-polymorphic lifting from the profinite integers

`Langlands.Weil.profiniteIntegerLifting.{u}` proves exactly the published
`Langlands.Weil.ProfiniteIntegerLifting.{u}`. Its entire unapplied type is

```lean
Langlands.Weil.profiniteIntegerLifting.{u} :
  Langlands.Weil.ProfiniteIntegerLifting.{u}
```

Unfolding the proposition gives the complete telescope

```lean
∀ (G : Type u) [Group G] [TopologicalSpace G]
  [NonarchimedeanGroup G] [CompactSpace G] [T2Space G]
  (f : Langlands.Weil.Degree →* G),
  ∃! F : Langlands.Weil.ProfiniteIntegers →ₜ* G,
    F.toMonoidHom.comp Langlands.Weil.frobenius.toMonoidHom = f
```

The theorem has no term parameters outside this proposition. The target universe
`u` is arbitrary, while `Degree`, `ProfiniteIntegers`, and `frobenius` retain
the definitions in `Langlands.Weil.Pullback`. In particular, the source remains
the genuine small profinite completion of `Multiplicative ℤ`.

## Implemented proof

The construction first works with a finite group `H` in any universe. For a
homomorphism `f : Degree →* H`, its kernel is a finite-index normal subgroup of
`Degree`. The private `finiteKernel` packages this subgroup. The private
`liftFinite` evaluates a profinite integer at that kernel, obtaining an element
of the small quotient `Degree ⧸ f.ker`, and applies `QuotientGroup.lift` to reach
`H`. This is a homomorphism because both maps are homomorphisms. It is continuous
because the coordinate projection is continuous and its finite source quotient
has the discrete topology. The restriction to `frobenius` is definitionally `f`,
as recorded in `liftFinite_frobenius`.

For an arbitrary `P : ProfiniteGrp.{u}`, every open normal subgroup `U` gives a
finite quotient `P ⧸ U`. The private `component` applies `liftFinite` to the
composite of `f` with this quotient map. `component_frobenius` identifies its
integer restriction with the corresponding coordinate of `toLimitFun P (f n)`.
For every transition map between these quotients, the two resulting continuous
maps agree on the image of `Degree`. Mathlib's
`ProfiniteCompletion.denseRange` and `DenseRange.equalizer` extend that agreement
to the full completion. Thus the components form a point of the inverse limit.
The private `liftToLimit` assembles these points into a continuous homomorphism:
its group laws hold coordinatewise, and continuity follows from continuity into
the product and its induced subtype topology.

The private `liftProfinite` composes this map with the inverse of Mathlib's
`continuousMulEquivLimittoFiniteQuotientFunctor P`. The lemma
`liftProfinite_frobenius` applies that equivalence and checks equality in every
coordinate, proving the required restriction formula.

Finally, a Hausdorff nonarchimedean group is totally separated, hence totally
disconnected, by the imported Mathlib instances. Together with compactness and
the topological group structure supplied by `NonarchimedeanGroup`, this lets the
proof use `ProfiniteGrp.of G`. The constructed lift gives existence. Two
continuous lifts with the specified restriction agree on the dense image of
`frobenius`, so `DenseRange.equalizer` proves their equality in the Hausdorff
target, giving uniqueness.

## Universes and provenance

All cross-universe maps are ordinary bundled continuous homomorphisms. The proof
does not apply Mathlib's category-level `ProfiniteCompletion.lift`, whose source
and target share a universe. Instead, each finite target quotient uses a kernel
inside the fixed small `Degree`, and the resulting coordinate maps assemble into
the target's inverse limit in universe `u`. There is no countability,
metrizability, smallness, section, or supplied-extension assumption on `G`.

This is an internally derived completion result, not a statement quoted from
local-field literature. The finite-target construction follows the private
`finiteKernel` and `liftFinite` construction in the published
[finite-field comparison proof](../Galois/FiniteField/ComparisonProof.lean).
Its general target assembly uses the pinned Mathlib sources at commit
`5ed2965256430c3649e86755f9576b54eca72435`:

- `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean`, for the actual
  completion, its finite quotient coordinates, and density of `etaFn`;
- `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Limits.lean`, for the diagram of
  open normal quotients and its continuous multiplicative limit equivalence;
- `Mathlib/Topology/Algebra/Nonarchimedean/TotallyDisconnected.lean`, for total
  separatedness of Hausdorff nonarchimedean groups.

All helpers are private to this proof module. No imported definition or
statement is changed.

## Development verification

The proof module compiled without errors or warnings. Separate development
examples assigned `@Langlands.Weil.profiniteIntegerLifting.{u}`, without applied
arguments, both to the published proposition and to the complete expanded
telescope displayed above; both compiled. Declaration inspection reports a
theorem with the single universe parameter `u` and only the standard assumptions
`propext`, `Classical.choice`, and `Quot.sound`. The proof introduces no axioms or
proof holes. These development checks do not replace the submission's exact
proof-target validation, independent semantic review, or Library publication.
