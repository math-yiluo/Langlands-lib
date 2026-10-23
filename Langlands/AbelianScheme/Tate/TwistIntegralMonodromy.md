# Geometric monodromy on integral roots-of-unity limits

This internal construction lifts `Geometry.levelMonodromy` to the existing
selected divisibility limit `Divisibility.Integral Ω P`, including its full
and prime-to-p specializations. The carrier, transition maps, scalar actions,
and topology are those of `TwistDivisibility`; no compatible roots are chosen.

## Hypotheses and provenance

Let `S` be a scheme, `Ω` a field, and `s : Spec Ω → S`.
As in `TwistFiniteMonodromy`, `hfin` asserts finiteness of the fibres of the
actual finite étale covers at `s`. The group is the existing natural
automorphism group `FundamentalGroup s hfin`, with its evaluation topology.
For each selected positive integer `n : Index P`, the construction explicitly
requires `hμfin n : IsFinite (mu S n.val).X.hom` and
`hμet n : Etale (mu S n.val).X.hom`. The selected families are explicit named instance parameters. These hypotheses concern the actual
multiplication kernel of the multiplicative group scheme.

The intended geometric application has an algebraically closed field and a
connected locally noetherian base, with the retained torsion orders invertible
on the base. This module proves a more general conditional construction; it
does not derive the finite-étale hypotheses from invertibility, or establish a
Galois-category identification.

The derivation is internal: apply the published finite-level geometric
evaluation action coordinatewise, use its transition equivariance to obtain
coherence, and use the existing residue scalar actions and product-subspace
topology. The neighboring abelian-scheme integral monodromy construction
provides the same inverse-limit pattern, but is specialized to abelian schemes;
the present construction uses actual roots of unity and their own limit.

## Coordinate construction and action laws

`integralMonodromyHom s hfin P (hμfin := hμfin) (hμet := hμet) g` applies
`levelMonodromy s hfin n.val g` to coordinate `n`. It is constructed by
`Divisibility.lift`. The finite-level transition law and the coherence of the
input prove that its output is coherent.
`evaluation_integralMonodromyHom` and `evaluation_integralMonodromy` identify
each coordinate with this actual geometric evaluation, rather than with an
arbitrary compatible action supplied as data.

The identity and multiplication formulas are checked at every coordinate:

`ρ(1)(x) = x`, and `ρ(g * h)(x) = ρ(g)(ρ(h)(x))`.

`integralMonodromy` bundles the additive equivalence; its inverse evaluates at
`g⁻¹`. `integralMonodromyAction` is an instance-reducible definition that can
be installed locally as a distributive action. It uses this same function.

## Topology and scalars

`continuous_integralMonodromy` proves joint continuity of `(g,x) ↦ ρ(g)(x)`.
Each coordinate is the composite of the continuous pair consisting of the
group element and the existing projection with the jointly continuous finite
action. The product and subtype continuity criteria assemble these coordinates.
`integralMonodromyAction_continuousSMul` states the corresponding property for
the locally installed action.

The existing full profinite-integer action is given at level `n` by the
residue of the scalar in `ZMod n.val`. Finite-level residue linearity therefore
gives `integralMonodromy_full_smul`. `integralMonodromyLinearEquiv` and
`integralRepresentation` bundle these maps and their left-action laws.
`integralMonodromyContinuousLinearEquiv` also records continuity of each map
and its inverse, obtained by fixing `g` or `g⁻¹` in the joint action.

## Full and away systems

`fullMonodromy` uses `P = fun _ => True`, so its hypotheses range over all
positive integers. `awayMonodromy` uses `P n = Nat.Coprime n p`, so its
hypotheses concern only the retained positive orders. This definition works
for any natural modulus `p`; no primality assertion is implicit.

The away action also preserves the existing prime-to-p profinite-integer
scalar action. This is bundled by `awayMonodromyLinearEquiv`,
`awayRepresentation`, and `awayMonodromyContinuousLinearEquiv`. Finally,
`restrictAway_monodromy` states that restriction of a full coherent family
commutes with the geometric action. The away finite-étale hypotheses in this
formula are exactly the restrictions of the full hypotheses. The equation
holds coordinatewise by definition.

This unit establishes the integral actions and their compatibility with full
and away scalar structures and restriction. Prime-adic and rational actions,
path transport, finite-étaleness theorems, Weil pairings, and PEL level
structures are separate obligations. It makes no trivialization of the twist.
