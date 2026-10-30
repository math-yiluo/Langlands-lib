# Cohomological triviality and the comparison theorem

This module states three Prop-valued propositions about Mathlib's actual Tate
cohomology `tateCohomology` of finite groups. They are three ingredients of
Serre's proof of Tate's theorem (Chapter IX of *Local Fields*). No proof is
given in this module. Each proposition is proved, with exactly the coefficient
ring and universe scope stated below, in a companion module:
`Langlands.Tate.pGroupTateVanishing` in
[PGroupTateVanishingProof](PGroupTateVanishingProof.md),
`Langlands.Tate.sylowTateVanishing` in
[SylowTateVanishingProof](SylowTateVanishingProof.md), and
`Langlands.Tate.tateComparison` in
[TateComparisonProof](TateComparisonProof.md). The last is derived from the
other two.

Throughout, `IntegralScalar.{u}` is `ULift ℤ` (module `ZeroDefinitions`), so a
`Rep.{u} IntegralScalar.{u} G` is a `G`-module in universe `u`. Restriction of
a representation to a subgroup `P` is `Rep.res P.1.subtype`, and the map on
Tate cohomology induced by a morphism `f` of representations is
`(tateCohomologyFunctor n).map f`; for the restricted morphism this is
`(tateCohomologyFunctor n).map ((Rep.resFunctor P.1.subtype).map f)`.

## `Langlands.Tate.PGroupTateVanishing`

For every prime `p`, every finite group `P : Type u` that is a `p`-group
(`IsPGroup p P`), every `C : Rep.{u} IntegralScalar.{u} P` and every integer `q`:
if `tateCohomology C q` and `tateCohomology C (q + 1)` are zero objects
(`IsZero`), then `tateCohomology C n` is a zero object for every integer `n`.

Source: Serre, *Local Fields*, Chapter IX, §5, Theorem 8, implication i) ⇒ ii),
printed page 145 (PDF page 151), in the case where the group is itself a
`p`-group, so that it is its own Sylow `p`-subgroup and the Sylow subgroups for
the other primes are trivial. For `p`-groups this is also the content of §4,
Theorem 5 (modules killed by `p`, printed pages 142–143, PDF pages 148–149) and
Theorem 6 (modules without `p`-torsion, printed page 143, PDF page 149), to
which Serre's proof reduces. Serre's conclusion "cohomologically trivial" asserts
vanishing for every subgroup and every degree; the Lean proposition asserts only
vanishing for the group `P` itself in every degree. The module is arbitrary: no
torsion or freeness hypothesis is made.

## `Langlands.Tate.SylowTateVanishing`

For every commutative ring `R`, every finite group `G` (both in `Type u`), every
`C : Rep.{u} R G` and every integer `n`: if for every prime `p` and every Sylow
`p`-subgroup `P : Sylow p G` the group `tateCohomology (Rep.res P.1.subtype C) n`
is a zero object, then `tateCohomology C n` is a zero object.

Source: Serre, Chapter IX, §2, Corollary to Theorem 4, printed page 140 (PDF
page 146): if `Ĥⁿ(G_p, A) = 0` for a Sylow `p`-subgroup `G_p` for every prime
`p`, then `Ĥⁿ(G, A) = 0`. The Lean proposition requires the vanishing for every
Sylow subgroup, not one chosen subgroup per prime; this is formally a stronger
hypothesis and hence a formally weaker statement, and the two agree by Sylow
conjugacy. It is stated over an arbitrary commutative coefficient ring, which
specializes to `G`-modules for `R = IntegralScalar`. The `[Fintype P.1]`
instance binder only supplies the finiteness instance used by
`tateCohomology` for the subgroup; every Sylow subgroup of a finite group has
such an instance.

## `Langlands.Tate.TateComparison`

For every finite group `G : Type u`, representations
`D E : Rep.{u} IntegralScalar.{u} G` and morphism `f : D ⟶ E`: suppose that for
every prime `p` and every Sylow `p`-subgroup `P` there is an integer `m` such
that, on the restrictions to `P`, the induced map on Tate cohomology is
surjective in degree `m`, bijective in degree `m + 1` and injective in degree
`m + 2`. Then `(tateCohomologyFunctor n).map f : Ĥⁿ(G, D) → Ĥⁿ(G, E)` is
bijective for every integer `n`.

Source: Serre, Chapter IX, §7, Theorem 12, printed pages 147–148 (PDF pages
153–154), with `A' = D`, `A = E`, the integer `m` playing the role of `n_p`.
The Lean proposition is the "in particular" conclusion of Theorem 12, namely
bijectivity of `Ĥⁱ(g, A') → Ĥⁱ(g, A)` (the case `B = ℤ`), and only for the
subgroup `g = G`. It makes no claim about tensor products with another module
`B` or about proper subgroups. As above the hypothesis is required for every
Sylow subgroup, and the integer `m` may depend on the Sylow subgroup.

## Use

These propositions are prerequisites for `Langlands.Tate.TateCupIsomorphism`
(module `TateTheoremStatement`): writing the degree-two class through dimension
shifting as a degree-zero class turns cup product with it into the map induced
by a morphism of representations, to which `TateComparison` applies with
`m = -1`. The proof `Langlands.Tate.tateCupIsomorphism` in
[TateTheoremProof](TateTheoremProof.md) follows this route with the proved
`tateComparison`. `TateComparison` itself follows from the other two
propositions by Serre's mapping-cone argument (`tateComparison_of`).
