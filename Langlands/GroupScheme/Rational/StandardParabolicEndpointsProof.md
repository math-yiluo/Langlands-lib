# Proof: the endpoints of standard parabolics

Author: Worker 293.

`Langlands.GroupScheme.standardParabolicEndpoints : StandardParabolicEndpointsStatement.{u}`
proves the published statement `StandardParabolicEndpointsStatement` of
`Langlands.GroupScheme.Rational.StandardParabolicEndpointsStatement` at an arbitrary universe
`u`. The statement covers a field `k : Type u`, a connected reductive group scheme `G` over
`Spec k`, a maximal split torus `i : T.toGrp ⟶ G` and a generic cocharacter `ν` of `T`. Write
`Δ = simpleRelativeRoots i ν`. It gives five equalities of subgroup functors, each on all test
schemes:

1. `standardParabolic i ν ∅` is `Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)`;
2. `standardLevi i ν ∅` is `torusCentralizer i`;
3. `standardParabolic i ν Δ` is the full subgroup functor `⊤`;
4. `standardLevi i ν Δ` is `⊤`;
5. `standardUnipotent i ν Δ` is the identity subgroup functor `⊥`.

The theorem has no premises. No assumption of characteristic, perfectness, splitness,
quasi-splitness or reducedness of the relative roots is added, and `Δ` may be empty.

## Proof as implemented

The theorem applies the conditional theorem
`standardParabolicEndpoints_of_relativeRootNegation`
(module `Rational.StandardParabolicEndpointsNegation`) to the published proof
`relativeRootNegation : RelativeRootNegationStatement` (module
`Rational.RelativeRootNegationProof`). That statement says that the actual relative roots
of a maximal split torus in a connected reductive group over any field are stable under
negation. The Markdown of each of the two modules describes its argument in full.

In outline, the conditional theorem works as follows. Negation stability and genericity of
`ν` imply that two cocharacters standard for the same index set `J` have the same signs on
every relative root. Signs on positive roots are fixed by `J`, by induction on the pairing
with `ν`; every other root is the negative of a positive one. The published
`relativeRootSignsDetermineDynamic` turns equal signs into equal dynamic subgroup functors.
So each standard parabolic, Levi and unipotent subgroup functor equals the dynamic one of any
cocharacter standard for its index. At `J = ∅` the cocharacter `ν` is standard, which gives
clause 1. Clause 2 then follows from the published `genericCentralizer`, which identifies
the dynamic centralizer of `ν` with `torusCentralizer i`. At `J = Δ` the zero cocharacter is
standard, and its dynamic parabolic and centralizer are `⊤`, which gives clauses 3 and 4.
Clause 5 holds with no premise (`standardUnipotent_simple_eq_bot`).

## Provenance

The target is Borel–Tits, *Groupes réductifs* (1965), §5.12 and §4.2(ii), and Renard,
*Représentations des groupes réductifs p-adiques*, V.3.8. The statement module documents the
cited sources and the derived parts of the formulation. The route through negation
stability of the relative roots is a derived argument of this Library: classically the
relative roots form a (possibly nonreduced) root system, and here negation stability is
supplied by its published proof. This module adds no hypotheses.

Source IDs: `borel-tits-1965-groupes-reductifs`,
`renard-2026-representations-groupes-reductifs-padiques`.
