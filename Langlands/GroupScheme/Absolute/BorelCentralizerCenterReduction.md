# Borel centralizer equality from homomorphism rigidity

This internal reduction follows the inner-automorphism argument in Milne,
*Algebraic Groups* (2017), Proposition 17.22, printed p.359, using Proposition 17.21.
It imports both published statement definitions unchanged. Its last theorem is conditional
on `BorelHomomorphismRigidityStatement`; this module does not claim the unconditional target.

For an arbitrary base scheme `S : Scheme.{u}` and group-scheme homomorphism `i : B ⟶ G`,
the `Prop`-valued definition `AffineEndomorphismRestrictionRigidity i` means that for every
commutative ring `A : CommRingCat.{u}` and every `b : Spec A ⟶ S`, two endomorphisms of
the actual base change `G_b` are equal whenever their composites with `i_b` are equal.
This is an internal condition used to state the reduction; it does not assert rigidity
for any given homomorphism.

`center_map_mem_centralizer_range` maps the commutation equation of a central point through
a group-scheme homomorphism. The existing `SubgroupFunctor.center_le_centralizer` observes that a central point commutes
with every point of any subgroup functor. Both lemmas hold over an arbitrary scheme.

`commute_of_baseChange_restriction_rigidity` lifts a centralizing point over a new base to
a section of the base-changed group. Conjugation by that section restricts to the identity
on the base-changed subgroup. The supplied restriction rigidity makes conjugation the
identity on the entire group; evaluating it at another section gives the desired commutation.

`centralizer_range_eq_center_of_affine_restriction_rigidity` applies the preceding argument
under the explicit condition `AffineEndomorphismRestrictionRigidity i`.
An affine cover of each test scheme detects equality of the
two multiplication morphisms, so the result holds for the all-test centre and centralizer,
including nonreduced and nonaffine test schemes.

`borelCentralizerCenter_of_homomorphismRigidity` installs the algebra structure induced by
an arbitrary affine scheme's morphism to the field base and applies the exact published
rigidity statement with both ambient groups equal to `G`. No smoothness, connectedness,
affineness or field hypotheses beyond those already in the target are added to this implication.

The generic condition and affine-cover reduction are derived from the Library's actual
point groups, inner automorphisms, base-change point equivalences and scheme affine covers.
Milne states his centralizer argument on arbitrary test algebras; the affine-cover step
explains the extension to the Library's all-test-scheme statement.

Source: James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over
a field* (2017), registered as `milne-2017-algebraic-groups`, Proposition 17.22, printed p.359,
one-based PDF p.375. The registered official errata snapshot
`milne-2017-algebraic-groups-errata-2026-11-02` lists Chapter 17 corrections on pp.360,
364 and 386; none concerns Proposition 17.22.
