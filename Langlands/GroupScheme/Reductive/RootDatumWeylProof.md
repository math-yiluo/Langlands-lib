# The Weyl group of a split maximal torus and its supplied root datum

Workers 1446 and 1577.

`Langlands.GroupScheme.weylGroup` has exactly the published type
`Langlands.GroupScheme.WeylGroupStatement.{u}`. For every field in universe
`u`, connected reductive group, split maximal torus embedding `i`, and
supplied datum `P` satisfying `IsRootDatumOf i P`, it proves both equalities:
the actual rational normalizer's image on the full integral character
lattice equals `P.weylGroup.map (RootPairing.Equiv.weightHom P)`, and the
kernel of `weylAction i` equals the centralizer subgroup of the normalizer.

## Implemented proof

Connected reductivity supplies affineness and smoothness, and maximality
supplies the closed immersion of the torus. The published finite Lie-weight
support and generic-cocharacter results produce a finite set of actual
roots and a generic integral cocharacter. A split maximal torus is a maximal
split torus, so `hasTrivialPositiveRootStabilizer` applies.

That theorem uses the proved finiteness of the actual rational quotient
`N(k)/Z(k)`. The subgroup preserving the positive roots of the generic
cocharacter fixes the sum of its integral cocharacter translates. Every
root pairs with all summands with the same strict sign, so the sum remains
generic. Fixedness puts a normalizing representative in its dynamic
centralizer; `genericCentralizer` identifies that functor with the torus
centralizer. Thus the positive-root stabilizer is trivial. The construction
uses an integral sum and applies in every characteristic.

The `IsRootDatumOf` bridge extracts actual rational normalizing
representatives for all reflections of the supplied datum. Its exact
root-range and pairing identities give `RelativeRootReflectionData` on the
actual roots. The published chamber-generation theorem then shows that
these representatives generate the actual quotient. Mapping this equality
through the full integral character action proves inclusion of the actual
image in the abstract Weyl image. The reverse inclusion follows because
every abstract reflection has a supplied actual representative.
`IsSplitTorus.weylAction_ker` supplies the full kernel equality by separation
of torus morphisms by characters.

Every structural hypothesis in these applications is discharged from the
published target's hypotheses or proved Library results. The finite-root
type used by the chamber argument is the actual finite root subtype.
Consequently the proof works for every supplied `J : Type u` and `P`
without requiring `Finite J` or `P.IsReduced` as additional premises.

## Original-source comparison

Milne, *Algebraic Groups* (2017), registered source
`milne-2017-algebraic-groups`, Proposition 21.1 (printed p.424, PDF p.440),
Theorem 21.37 (printed pp.435–436, PDF pp.451–452), and Corollary 21.38
(printed p.436, PDF p.452) give the rational-point Weyl quotient for a split
group, reflection generation, and the canonical abstract comparison.
The registered 2017 errata has no correction to these passages.

The source defines the Weyl group as a finite constant group scheme and
uses split-torus cohomology to identify its points with the rational
normalizer quotient. Its generation proof passes to an algebraic closure
and compares the simply transitive actions on chambers and on Borels
containing the torus. The published Lean target expresses the comparison
through the actual integral character action and includes its centralizer
kernel. The implemented proof works directly over the original field:
finite integral averaging and the proved generic-centralizer theorem give
the trivial stabilizer needed by the chamber argument. The theorem uses
the supplied datum and its rational reflection witnesses; it makes no
root-datum existence assertion.
