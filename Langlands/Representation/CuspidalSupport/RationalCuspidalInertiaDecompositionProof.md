# Renard VI.3.3.1 for proper-standard cuspidal representations: proof

`Langlands.CuspidalSupport.rationalCuspidalInertiaDecomposition.{uF, uV}` proves
exactly the published proposition
`Langlands.CuspidalSupport.RationalCuspidalInertiaDecompositionStatement.{uF, uV}`
(module `Langlands.Representation.CuspidalSupport.RationalInertiaDecompositionStatement`).
[Statement](RationalInertiaDecompositionStatement.md)
The theorem has no hypotheses. Its type is that proposition with the two
independent universe parameters `uF` (the field) and `uV` (the representation
carrier). Its axioms are `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Let `F : Type uF` be a nonarchimedean local field of either characteristic and
`G` a connected reductive group scheme over `F`, possibly nonsplit, possibly of
relative rank zero and possibly with empty relative root system. Let
`i : T.toGrp ⟶ G` be an actual maximal split torus and `ν` a generic cocharacter.
Assume `StandardCocharacterStatement`, `HasRelativeRootSystem i` and closedness of
every actual standard unipotent point subgroup `unipotent i ν I`. Give the
rational-point group the canonical topology `rationalPointTopology F G.X`, with
the displayed locally compact, nonarchimedean and Hausdorff instances. The full
simple-root index set comes from `simpleRelativeRootFintype`, and the semidirect
decompositions come from `isSemidirectDecomposition_of_standardCocharacterStatement`.
These are the derived constructions of the statement itself.

Let `π` be an irreducible smooth complex representation on a carrier in universe
`uV`. Suppose `Aubert.General.IsCuspidal` holds for the actual standard
parabolic, Levi and unipotent family: the normalized Jacquet module vanishes for
every proper subset of the full simple-root set, including the empty subset
when it is proper. Then `IsRationalInertiaCategoryDecomposition G π` holds. Every
smooth representation, of any length, is the vertex of an actual coproduct cofan
with one component in each factor below, and every morphism between the two
factors vanishes, in both directions:

- `true`: every irreducible subquotient is isomorphic to an unramified twist of `π`;
- `false`: no irreducible subquotient is.

No compact-restriction, special-compact, Cartan, basis, central-character,
admissibility, finite-length or projector premise is added.

This is equation (VI.3.3.1) of David Renard, *Représentations des groupes
réductifs p-adiques*, French edition dated 9 July 2026, VI.3.3, printed
pp.144–145 / PDF pp.150–151, source ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The source
assumes `π` supercuspidal: every proper parabolic has zero normalized Jacquet
module (definition of VI.2.1, printed p.137 / PDF p.143). By its first remark it
is enough to test proper standard parabolics. The Lean statement takes that
standard form.

## Proof

The Lean term is one application:

```
rationalCuspidalInertiaDecomposition_of_jointBasis
  rationalCompactRestrictionInertiaDecomposition.{uF, uV}
  Aubert.General.rationalCuspidalCompactRestriction.{uF, uV}
  BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{uF}
```

The reduction `rationalCuspidalInertiaDecomposition_of_jointBasis` (module
`RationalCuspidalInertiaDecompositionReduction`) takes three propositions. Each
is supplied by a published theorem without hypotheses:

1. `RationalCompactRestrictionInertiaDecompositionStatement.{uF, uV}` is supplied
   by `rationalCompactRestrictionInertiaDecomposition` (module
   `RationalCompactRestrictionInertiaDecompositionProof`). This is the
   decomposition for an irreducible representation whose restriction to the
   actual common norm kernel `Plancherel.rationalCommonNormKernel G` (Renard's
   `⁰G`) has compact smooth-dual coefficients. It composes the published proofs
   of VI.3.2(ii) (`rationalNormKernelFiniteRestriction`) and VI.3.2(iii)
   (`rationalNormKernelTwistEquivalence`) with the IV.1.5 projector assembly.
   [Proof](RationalCompactRestrictionInertiaDecompositionProof.md)
2. `Aubert.General.RationalPointFamily.RationalCuspidalCompactRestrictionStatement.{uF, uV}`
   (VI.2.1, (a) ⇒ (c)) is supplied by
   `Aubert.General.rationalCuspidalCompactRestriction` (module
   `Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionProof`).
   [Proof](../Aubert/General/RationalCuspidalCompactRestrictionProof.md)
3. `BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{uF}`
   (V.5.1–V.5.2 at one geometric special vertex) is supplied by
   `BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence` (module
   `Langlands.BruhatTits.SpecialCompact.JointBasisProof`).
   [Proof](../../BruhatTits/SpecialCompact/JointBasisProof.md)

### Discharging the extra premises of VI.2.1

The VI.2.1 statement has premises that the target lacks: an apartment datum
`D : KPApartmentData i (localFieldOrder F)`, a point `x`, and four properties
of the one subgroup `K0 = D.specialCompactSubgroup x`. These are
`D.IsSpecialApartmentVertex x`, `SpecialCompactProperties F i ν K0`,
`SimultaneousStandardBasisAt i ν K0` and `FiniteCartanCovering F i ν K0`. Inside
the reduction, `rationalSpecialVertexCompactInputs_of_jointBasis` obtains them
from the joint theorem, applied to the target's own `F`, `G`, `hG`, `T`, `i`, `hi`,
`ν` and `hν`:

- the joint witness supplies `D`, `x`, a represented torus centralizer `j`, its
  factorization `s` and a restriction-evaluation bijection `h`;
- the special-vertex, special-compact-property and simultaneous-basis conjuncts
  of the same witness are used directly;
- `FiniteCartanCovering` for the same `K0` comes from the published
  `Aubert.General.RationalPointFamily.rationalPositiveCartanCover`. It is
  applied to the witness's centralizer representation, the factorization
  `s ≫ j = i` and its `SpecialCompactRenardComparison D x ν j s h`.

So the reduction constructs the additional special-vertex, special-compact,
simultaneous-basis and Cartan inputs of VI.2.1 for the target's group, maximal
split torus and generic cocharacter. It passes the target's shared structural,
topological and cuspidality hypotheses (`hG`, `hi`, `hν`, the standard
cocharacter hypothesis, `HasRelativeRootSystem i`, closedness of the unipotent
point subgroups, the three topology instances and `hcusp`) unchanged to VI.2.1.

### Actual-data and universe comparisons

The reduction's Lean proof passes data between the three statements without
transport lemmas. Each comparison holds by definitional unfolding, checked by
Lean when the reduction module is compiled; this module only checks that the
three theorems have exactly the types of the reduction's hypotheses:

- `RationalPoint F G.X` in the VI.2.1 statement and `GroupScheme.rationalPoints G`
  in the target abbreviate the same morphism type. Both carry
  `rationalPointTopology F G.X`, and the target's three topology instances are
  passed unchanged.
- VI.2.1 and the target use the same `simpleRelativeRootFintype i hRoots
  hi.isSplitSubtorus.1 ν` and the same semidirect family. Hence the cuspidality
  hypothesis `hcusp` of the target is literally the cuspidality premise of
  VI.2.1.
- The VI.2.1 conclusion and the compact-restriction premise use the same norm
  kernel `Plancherel.rationalCommonNormKernel G` and the same restricted
  representation.
- The smoothness instance `hG.smooth` occurs in the target and the
  compact-restriction statement but in no type passed to or from the VI.2.1
  statement.
- The field universe `uF` and the carrier universe `uV` stay independent. The
  joint existence theorem and `StandardCocharacterStatement` live at `uF` alone.
  The compact-restriction decomposition and VI.2.1 are instantiated at
  `{uF, uV}`.

## Source comparisons implemented and not implemented

The proof runs on the actual standard family of the target: the shared maximal
split torus, the generic cocharacter, its simple relative roots and the
normalized Jacquet functor. It implements:

- the source's proof chain for VI.3.3.1 on this family: VI.2.1 (a) ⇒ (c), then
  VI.3.2(ii),(iii) and the IV.1.5 projectors;
- the discharge of the special-compact, simultaneous-basis and Cartan inputs of
  VI.2.1 from V.5.1–V.5.2 on the same actual group.

It does not implement:

- the comparison of the cocharacter and simple-relative-root indexing with the
  source's standard parabolic subgroups;
- the reduction from all proper parabolics to proper standard ones (first
  remark of VI.2.1, with its conjugacy argument);
- the correspondence between the Library's normalization of the Jacquet functor
  and the source's normalization;
- independence of the initial choices of torus and cocharacter.

These comparisons belong to the general framework, as the statement's Markdown
records. Nor does the theorem prove the remarks after VI.3.3.1: the finite
stabilizer `X(G)(π)`, the complex algebraic-torus structure on the inertia
class, its coordinate ring `ℂ[G/⁰G]^{X(G)(π)}`, and the bijection between
inertia classes of supercuspidal representations and `G`-orbits of compact
irreducible representations of `⁰G`.

## Dependencies

The theorem uses no Howe finiteness, Bernstein decomposition, finite-length or
classification result as a premise. Its only inputs are the three published
theorems above, which have no hypotheses, and the reduction module.
