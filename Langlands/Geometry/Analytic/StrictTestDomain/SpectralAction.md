# Continuous actions for the restricted rational spectral topology

Author: Worker 36.

Let `K` be a complete ultrametric normed field, `P` a presented strict
affinoid `K`-algebra, and `G` a topological group. The structure
`RationalSpectralAction G P` consists of a homomorphism
`toMonoidHom : G →* Aut P` and its continuity for the already constructed
`rationalSpectralTopology P`. Here `Aut P` is the group of actual bounded
`K`-algebra automorphisms. The topology uses finite families of actual
unit-radius rational quotients, sections of those quotients and positive
spectral tolerances. The continuity field specifies the class of actions
being defined; the open subgroups and their quotient-algebra actions below
are constructed from it.

The target topology is explicit in the structure and the standalone
continuity theorem. The module uses a local instance of the named topology
for elaboration and does not install a global topology instance on `Aut P`.
The universe of the field and the universe of `G` are independent.

For a rational datum `d`, a quotient section `b : d.algebra`, and `r > 0`,
the theorem `isOpen_rationalSpectralSubgroup` proves openness of the
single-test subgroup. Its proof applies the published finite-test openness
theorem to the constant family indexed by `Unit`, then simplifies the
intersection. The test at `b = 0` and `r = 1` imposes only setwise
preservation of `d.locus`: its spectral displacement condition is automatic.
The published zero-section identity therefore gives
`isOpen_locusStabilizer_rationalSpectralTopology`.
The definition `rationalLocusOpenSubgroup` bundles this exact setwise
stabilizer as an open subgroup of `Aut P`.

The theorem `continuous_rationalSpectralTopology_iff` says that a group
homomorphism `ρ : G →* Aut P` is continuous if and only if, for every finite
family `tests` of rational spectral tests, the set

```text
ρ ⁻¹' (finiteRationalSpectralSubgroup tests)
```

is a neighborhood of `1` in `G`. The displayed finite family is indexed by
a type in universe zero. The published reindexing result for
`rationalSpectralTopology` ensures that these families already supply the
full basis, including all finite families in other universes.

For necessity, continuity at `1`, together with `ρ(1) = 1`, pulls back each
finite-test identity neighborhood. For sufficiency, every identity
neighborhood in the target contains a finite-test subgroup by the published
exact neighborhood criterion. Taking preimages and using upward closure
of the neighborhood filter establishes continuity at `1`. Mathlib's
`continuous_of_tendsto_nhds_one` upgrades this to continuity on the whole
topological group. The proof locally supplies the already proved
topological-group structure of the target topology.

Inside `RationalSpectralAction`, `ofFiniteTests` constructs an action using
this criterion. The definition `trivial` supplies a concrete action with
constant identity homomorphism. The definition `precomp` pulls back an
action along a continuous homomorphism from any topological group `H`;
the underlying map and its continuity are obtained by composition.

For an action `ρ`, `testOpenSubgroup` is the inverse image under its
homomorphism of an actual finite-test subgroup. Its openness follows by
continuity, and `mem_testOpenSubgroup` identifies its membership condition
definitionally. This construction allows finite index types in an arbitrary
universe, independently of the field and acting group.

Similarly, `locusOpenSubgroup ρ d` is the inverse image of the actual
setwise stabilizer of `d.locus`. Its openness is a consequence of the
zero-section argument and continuity of `ρ`. The membership theorem
`mem_locusOpenSubgroup` expresses exactly that the image of `d.locus` under
the point action of `ρ(g)` equals `d.locus`. This point action is the
published inverse-pullback action on the Banach spectrum.

The definition `stabilizerHom` maps this open subgroup into the ambient
`locusStabilizer d`. Its values are the original automorphisms with their
setwise-preservation proofs; its group laws follow from those of
`ρ.toMonoidHom`. Composing it with the published
`stabilizerSectionAction d` defines `sectionAction`, a homomorphism into
`Aut d.algebra`. Thus the open subgroup acts by actual bounded algebra
automorphisms of the fixed rational quotient. The compatibility theorem
`sectionAction_baseMap` applies the corresponding published compatibility
to give, for `g` in the open subgroup and `a : P`,

```text
sectionAction(g)(d.baseMap(a)) = d.baseMap(ρ(g)(a)).
```

The section action is forward on algebras, in agreement with the inherited
inverse-pullback convention on spectrum points.

This is a derived restriction of Berkovich's unfinished *Etale equivariant
sheaves on p-adic analytic spaces* (1995–1996), section 1.1, printed/PDF
pp. 1–2. Page 2 defines a continuous group action by continuity of the
homomorphism into the analytic automorphism group endowed with the
finite compact-domain and spectral-function test topology. The present
structure uses the independently constructed topology from unit-radius
rational tests. The continuity criterion and open stabilizers are intrinsic
consequences of that construction, proved as described above.
The underlying strict affinoid quotients, bounded morphisms and rational
quotient algebras come from the Library constructions following Berkovich's
*Non-archimedean analytic spaces*, Trieste lectures (2009), section 2.1 and
Definition 2.1.2 on p. 7, Definition 2.1.11 on p. 8, and Definition 2.2.1
and Exercise 2.2.2(ii) on p. 9.

The scope is fixed-field automorphisms and unit-radius rational data.
Equality with the full analytic automorphism topology has not been proved.
The module asserts no joint continuity on spectrum points, no continuity
of the section homomorphism in a quotient-norm or other section topology,
and no analytic atlas, structure sheaf or equivariant site. Openness refers
to the stated rational spectral topology or to preimages in the given
topological group. There is no identification of quotient and spectral
norms. Trivial valuations, nilpotents, zero quotients, empty loci and empty
test families are not excluded by additional assumptions.

The registered Equish source folder is
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
receipt SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
Its member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`
has SHA256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
The Trieste source is `berkovich-2009-trieste-analytic-spaces`, PDF SHA256
`8cfe4f6f35d5e717ac67c5c8f5ef9ff9185f460bbe5f9a10aeacd84cddeeb2ca`.
