# Rational scalar actions on roots-of-unity Tate twists

This module extends the integral residue actions on the actual roots-of-unity
limits to their rationalizations. It constructs full finite-adelic actions
under the explicit scalar-comparison hypothesis, proves naturality for ring
maps and restriction, and shows that the existing root automorphism and
field-Galois actions commute with these scalars. The namespace is
`Langlands.TateTwist.Divisibility`.

## Carriers and scalar extension

For a commutative ring `R` and a predicate `P : ℕ → Prop`, the imported carrier is

\[
\operatorname{Rational}(R,P)
  =\mathbb Q\otimes_{\mathbb Z}\operatorname{Integral}(R,P).
\]

The integral factor consists of compatible families of actual roots of unity,
at positive orders satisfying `P`, with quotient-power transition maps.
The full case uses the constant true predicate. The away case uses
`Nat.Coprime n p`, for any natural number `p`; its usual prime-to-p
interpretation applies when `p` is prime. No field, rank, characteristic,
finiteness or primitive-root assumption is used here.

`rationalScalarAction R P` specializes
`Langlands.TateScalarExtension.action` to the full residue-ring action on the
integral root limit. It is a rational-algebra homomorphism

\[
\mathbb Q\otimes_{\mathbb Z}\widehat{\mathbb Z}_{\mathrm{res}}
 \longrightarrow
 \operatorname{End}_{\mathbb Q}(\operatorname{Rational}(R,P)).
\]

Here the residue ring is the existing
`Langlands.Global.ProfiniteIntegerRing`, not a new coefficient model.
`rationalAwayScalarAction R p` uses the existing
`Global.PrimeToProfiniteIntegerRing p` and the actual away limit.
The two `*_tmul` lemmas specialize the generic formula

\[
(q\otimes a)(r\otimes x)=qr\otimes(a\mathbin{\cdot}x).
\]

Thus the integral action in this expression is precisely the published action
of compatible residues on the coordinates of the root families.

## Conditional finite-adelic action

Every finite-adelic construction explicitly takes
`h : Global.RationalProfiniteIntegerAdeleComparison`.
The imported `rationalEquiv h` is a rational-algebra equivalence from the
rationalized full residue ring to `Global.FiniteAdeles ℚ`. It is chosen
together with `integralEquiv h` from the same witness in that proposition,
and satisfies the imported normalization

\[
e(q\otimes a)=\operatorname{diag}(q)e_0(a).
\]

`finiteAdeleAction R P h` composes `rationalScalarAction` with the inverse of
this equivalence. `finiteAdeleModule R P h` exposes its associated module
structure for local installation; it is not registered as a global instance.
`finiteAdeleModule_smul` identifies scalar multiplication with evaluation of
the algebra action. `finiteAdeleAction_diagonal` proves that diagonal
rational scalars act by the existing rational scalar multiplication, and
`finiteAdeleModule_scalarTower` supplies the corresponding scalar tower.

`finiteAdeleAction_integral_tmul` recovers the actual integral action:

\[
e_0(a)(q\otimes x)=q\otimes(a\mathbin{\cdot}x).
\]

Its proof applies the coupled normalization to `1 ⊗ a`, cancels the
equivalence with its inverse, and uses the generic tensor-action formula.
The construction assumes the comparison proposition and makes no assertion
of independence from its chosen witnesses.

## Restriction and naturality

`rationalScalarAction_eq_away` says that the action of the rationalized full
residue ring on an away root limit equals the action obtained by restricting
the scalars. The scalar map is the already constructed
`Langlands.GroupScheme.Tate.rationalScalarRestrictAway p`; this module
introduces no duplicate scalar map. `rationalRestrictAway_scalarAction`
asserts the corresponding compatibility for the map that restricts a full
root family to the away indices. Both proofs use tensor induction in the
scalar and vector variables. On pure tensors they reduce to the integral
full/away action identity and integral restriction law, respectively.

For a ring homomorphism `f : R →+* S`, `rationalMap_scalarAction` and
`rationalMap_awayScalarAction` prove that the existing root-induced map
intertwines the full and away rational residue actions.
`rationalMap_finiteAdeleAction` proves the same result for finite-adelic
scalars, using the same `h` on source and target. These results apply the
generic `TateScalarExtension.map_action` to the published integral
`fullLinearMap` or `awayLinearMap`.

`finiteAdeleMap P h f` bundles that existing map as linear over
`Global.FiniteAdeles ℚ`, installing the source and target module structures
locally. Its application lemma identifies it with `rationalMap P f`.

## Automorphisms and Galois actions

`rationalAutomorphismAction_finiteAdeleAction` shows that the existing action
of any ring automorphism of `R` commutes with the finite-adelic action.
`rationalAutomorphismAction_awayScalarAction` proves the corresponding
commutation with rationalized away residue scalars. Their proofs identify
the underlying rational linear equivalence with `rationalMap` and apply
the naturality results.

For fields `K`, `L` with a `K`-algebra structure on `L`,
`rationalGaloisAction_finiteAdeleAction` and
`rationalGaloisAction_awayScalarAction` specialize these results along the
canonical homomorphism from `Gal(L/K)` to ring automorphisms.
They use the previously constructed action on the actual roots. They do
not assume normality or separability of the extension, choose a basis, or
replace the action by a trivial one.

## Provenance and scope

This is a derived extension of `TwistDivisibility` and `TwistRational`.
It reuses the generic scalar-extension construction and the coupled comparison
witnesses from `RationalScalars`. The finite-adelic module and restriction
proof patterns are adapted from Worker 142's implementation there; Worker 142
is credited as a coauthor.

The underlying original source is B. Edixhoven, G. van der Geer and
B. Moonen, *Abelian Varieties*, preliminary draft built 2012-02-08,
Chapter X (10.8), printed p.144 (PDF p.148), with the field and prime
convention on printed p.141 (PDF p.145). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
That passage describes the actual prime-adic roots-of-unity twist and its
natural Galois action. The original was read for the imported twist
construction, and its retained extract was reread for this extension;
no source-specific errata note was found in the available Library.

The arbitrary-ring full/away rationalized scalar actions and their
compatibilities are internal consequences of the published integral
constructions and tensor functoriality, not additional assertions quoted
from that passage. The finite-adelic action remains conditional on the
existing comparison proposition. This module proves neither that
proposition nor its witness independence. It defines no prime-to-p
finite-adele ring or comparison, and asserts no rational topology or
continuity. Ranks, restricted-product comparisons, the comparison with
scheme-theoretic multiplicative-group torsion, geometric monodromy, Weil
pairings and cyclotomic scalar formulas remain separate obligations.
