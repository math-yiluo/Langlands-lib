# Proof: reductive fibral identity components are open, closed and of étale index

The theorem `Langlands.GroupScheme.identityComponentClopen.{u}` proves the Library proposition
`Langlands.GroupScheme.IdentityComponentClopenStatement.{u}`, imported from
[`Reductive.IdentityComponentClopenStatement`](IdentityComponentClopenStatement.md), in every
universe `u`, with its statement unchanged and no additional hypotheses.

```lean
theorem identityComponentClopen : IdentityComponentClopenStatement.{u}
```

## Statement proved

Let `S : Scheme.{u}` be an arbitrary scheme and `G : GroupScheme S` a group scheme with
`Smooth G.X.hom`, `IsSeparated G.X.hom` and `QuasiCompact G.X.hom`. Let `i : H ⟶ G` be a
homomorphism with `IsRelativeIdentityComponent G i`, so that `H` is the open subgroup `G⁰`,
and suppose that for every `s : S` the residue-field fibre
`RelativeIdentityComponent.residueFiber H s` is `IsConnectedReductive`. Then:

1. `IsReductive H`;
2. `IsClosedImmersion i.hom.hom.left`;
3. there are `E : GroupScheme S` and `q : G ⟶ E` with
   `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q`, and `E → S` is `Etale`,
   `IsSeparated` and `QuasiCompact`.

This is Proposition 3.1.3 of Brian Conrad, *Reductive group schemes* (2014); the statement
page records the correspondence between the source and the Lean encoding.

## Proof

The proof term is

```lean
identityComponentClopenReduction
  reductiveFiberAffineness
  reductiveMonomorphismClosedImmersion
  RelativeIdentityComponent.clopenQuotient
```

The theorem `identityComponentClopenReduction` (module
[`Reductive.IdentityComponentClopenReduction`](IdentityComponentClopenReduction.md)) proves
`IdentityComponentClopenReductionStatement.{u}`, the implication

```lean
ReductiveFiberAffinenessStatement.{u} →
  ReductiveMonomorphismClosedImmersionStatement.{u} →
    RelativeIdentityComponent.ClopenQuotientStatement.{u} →
      IdentityComponentClopenStatement.{u}
```

Each of its three premises is a theorem of the Library in the same universe `u`, and is
passed as it stands.

1. **Affineness from connected reductive residue fibres.**
   `ReductiveFiberAffinenessStatement.{u}` (a smooth separated quasi-compact group scheme
   over an arbitrary base all of whose residue-field fibres are connected reductive is
   affine over the base) is proved by `reductiveFiberAffineness` (module
   [`Reductive.FiberwiseAffinenessProof`](FiberwiseAffinenessProof.md)).
2. **Monomorphisms out of reductive group schemes are closed immersions.**
   `ReductiveMonomorphismClosedImmersionStatement.{u}` (for a reductive `S`-group and a
   separated `S`-group of finite presentation, every homomorphism whose underlying morphism
   is a monomorphism is a closed immersion) is proved by
   `reductiveMonomorphismClosedImmersion` (module
   [`Reductive.MonomorphismClosedImmersionProof`](MonomorphismClosedImmersionProof.md)).
3. **Quotient by a clopen relative identity component.**
   `RelativeIdentityComponent.ClopenQuotientStatement.{u}` (a closed relative identity
   component of a smooth separated quasi-compact group scheme has a homogeneous quotient
   scheme) is proved by `RelativeIdentityComponent.clopenQuotient` (module
   [`RelativeIdentityComponent.ClopenQuotientProof`](../RelativeIdentityComponent/ClopenQuotientProof.md)).

Inside the reduction, `H → S` inherits smoothness and separatedness from `G → S` through the
open immersion `i`, and quasi-compactness comes from the residue fibres; the first premise
then makes `H` affine over `S`, hence reductive. The second premise, applied to the
monomorphism `i`, makes `i` a closed immersion. The third premise gives a homogeneous
quotient scheme, from which the étale, separated and quasi-compact fppf quotient `E` and the
projection `q` are obtained. These steps are carried out in the imported modules; this
module adds no further argument.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas et
Synthèses 42–43, SMF, 2014, Proposition 3.1.3, p.82, proof pp.82–83. The proof follows the
source's outline: `G⁰` is affine by SGA 3, Exposé XVI, Theorem 5.2(i), hence reductive; the
open immersion `G⁰ ⟶ G` is a monic homomorphism out of a reductive group, hence a closed
immersion (Conrad, Theorem 5.3.5); and the quotient `G/G⁰` is a separated étale scheme. For
that last point, `RelativeIdentityComponent.clopenQuotient` applies the schemehood theorem
`Langlands.AlgebraicGeometry.AlgebraicSpace.separatedEtaleScheme` (a separated algebraic
space over an arbitrary base with a surjective étale scheme atlas that is étale over the
base is a scheme) to the algebraic-space quotient, instead of Knutson's criterion after a
reduction to a Noetherian base.
