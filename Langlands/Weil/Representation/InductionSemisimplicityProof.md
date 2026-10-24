# Semisimplicity of actual finite-index induction

Worker 365 proves the published proposition
`Langlands.Weil.RepresentationInductionSemisimplicity.{uG,uV}` by the closed theorem
`Langlands.Weil.representationInductionSemisimplicity`. Import
`Langlands.Weil.Representation.InductionSemisimplicityProof` to use it.

The complete unapplied type is exactly the named proposition. Thus for any group
`G : Type uG`, finite-index subgroup `H`, finite-dimensional complex vector space
`V : Type uV`, and `ρ : Representation ℂ H V`, the conclusion is

```lean
Representation.IsSemisimpleRepresentation (ρ.ind H.subtype) ↔
  Representation.IsSemisimpleRepresentation ρ
```

The universes `uG` and `uV` are independent. The induced representation is Mathlib's
actual action on `Representation.IndV H.subtype ρ`, the tensor/coinvariant carrier.
No normality of `H`, topology, continuity, finite image, irreducibility, positive
dimension, or finite dimension of the induced carrier is assumed. The same proof
includes dimension zero.

## Implemented proof

The helper declarations below lie in
`Langlands.Weil.InductionSemisimplicity`.

`semisimple_of_surjective` translates semisimplicity into semisimplicity of the
associated group-algebra module using Mathlib's
`Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule`.
`Representation.IntertwiningMap.equivLinearMapAsModule` turns the given
intertwiner into a group-algebra linear map, and
`IsSemisimpleModule.of_surjective` gives semisimplicity of its image.
`semisimple_equiv` applies this argument to an equivalence and its inverse.

For a normal subgroup `N ≤ H`, `conjugateInclusion H N hNH g` is the group
homomorphism `n ↦ g*n*g⁻¹` from `N` into `H`. Normality places the conjugate in
`N`, and inclusion places it in `H`. `range_conjugate` proves that
`ρ.comp (conjugateInclusion H N hNH g)` has the same operator image as
`ρ.comp (N.subgroupOf H).subtype`. Its reverse inclusion uses conjugation by
`g⁻¹`. Thus the published same-image semisimplicity lemma applies even though
the two subgroup types differ.

The coinduced carrier consists of functions satisfying
`f(h*x) = ρ(h)(f(x))`, with `G` acting by right translation.
`evaluation H N hNH ρ g` evaluates such a function at `g`. It intertwines the
restriction of coinduction to `N` with the conjugated restriction of `ρ` because

```text
(n • f)(g) = f(g*n) = f((g*n*g⁻¹)*g) = ρ(g*n*g⁻¹)(f(g)).
```

`coind_semisimple` proves preservation in this model as follows.

1. Take `N = H.normalCore`, which is normal, finite index in `G`, and contained
   in `H`. The published finite-index restriction theorem, applied inside `H`,
   makes `ρ` restricted to `N.subgroupOf H` semisimple.
2. By `range_conjugate` and the published same-image lemma, each conjugated
   restriction indexed by a chosen right-coset representative is semisimple.
3. Convert their evaluation intertwiners to `ℂ[N]`-linear maps and combine them
   with `LinearMap.pi`. This gives a map from restricted coinduction to the
   finite product of the conjugated modules. Equality of all these evaluations
   implies equality of functions by injectivity of the existing linear
   equivalence `Langlands.FiniteRepresentation.Induction.coordinates`.
4. Mathlib's finite-product semisimplicity instance and
   `IsSemisimpleModule.of_injective` give semisimplicity on `N`. The published
   `Langlands.finiteIndexSemisimplicityAscent` then gives semisimplicity on `G`.

For reflection, `evaluationOne H ρ` evaluates at `1` and intertwines the
restriction of coinduction to `H` with `ρ`. `evaluationOne_surjective` constructs
an explicit preimage of every `v`. Write `a = Induction.factor H 1`. The inverse
of `Induction.coordinates` applied to the constant coordinate family
`ρ(a⁻¹)(v)` evaluates at `1` to `ρ(a)(ρ(a⁻¹)(v)) = v`. No nonzero-vector choice
or dimension positivity is involved.

The closing theorem first constructs the genuine representation equivalence
`Representation.equivOfIso (Rep.indCoindIso (Rep.of ρ))` from actual induction
to coinduction. `semisimple_equiv` transfers the goal across this equivalence.
For the reflection direction, the published `representationInductionDimension`
supplies finite dimension of the actual induced carrier; its underlying linear
equivalence transports that to the coinduced carrier. The published finite-index
restriction theorem then gives semisimplicity on `H`, and the surjective
`evaluationOne` gives semisimplicity of `ρ`. Preservation uses `coind_semisimple`.
Thus the final result concerns actual induction, with the function model used
only within its proof.

## Provenance and dependencies

This is derived generic algebraic representation theory, not a verbatim theorem
of Tate. The source context is John Tate, *Number theoretic background*, in
*Automorphic Forms, Representations and L-Functions*, Proc. Sympos. Pure Math.
33, Part II (1979), section 2.1, printed pages 9–10 / PDF pages 18–19.
Registered source: `tate-1979-number-theoretic-background`; retained file
`/home/taskhub/central-library/Borel-Casselman--Automorphic Forms, Representations and L-Functions (Corvallis)--1979/Part II.pdf`;
SHA-256 `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
Those original pages were read for this proof. Tate introduces continuous
finite-dimensional complex representations and Weil restriction on page 9;
on page 10 he gives finite-index Weil induction and Frobenius reciprocity on
virtual representation groups. He does not state this generic semisimplicity
equivalence there. This distinction agrees with
[`InductionFinitenessStatements`](InductionFinitenessStatements.md) and
[`RestrictionInduction`](RestrictionInduction.md).

The two direct imports are the published
[`InductionDimensionProof`](InductionDimensionProof.md) and
[`FiniteIndexRestrictionSemisimplicityProof`](FiniteIndexRestrictionSemisimplicityProof.md).
They supply the dimension and restriction theorems, the same-image transport
lemma, the existing coset coordinates, and finite-index ascent. All are reused
by Lean name. Mathlib supplies the actual coinduced action, the actual
induction/coinduction equivalence, group-algebra interpretation of intertwiners,
and semisimplicity of finite products, submodules and quotients. The new content
is the conjugation and evaluation argument and its assembly into the exact target.

Only this Lean/Markdown proof pair is added. The statement pair and its import
closure are preserved. The other finiteness components, aggregate assembly,
topology, compatibility, actual local specialization and LLC are separate tasks.

## Type and universe checks

Two closing examples assign the entire unapplied theorem both to the named
proposition and to its fully unfolded universally quantified formula, retaining
independent `uG` and `uV`. The coefficient field `ℂ` is in universe zero, so
Mathlib's comparison with carrier universe `max uV 0` imposes no extra universe
relation. The coinduced carrier may live in `Type (max uG uV)`; restriction is
applied at that carrier universe.

The proof is checked in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, with
Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.
The development Lake build completed without errors or warnings. Full declaration
inspection reports level parameters `uG`, `uV` and only the axioms `propext`,
`Classical.choice`, and `Quot.sound`. A private `#check` also prints the entire
constant as `RepresentationInductionSemisimplicity` at two independent universes.
