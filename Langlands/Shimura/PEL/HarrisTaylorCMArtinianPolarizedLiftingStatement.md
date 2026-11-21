# Artinian lifting of the actual positive polarized action

`DivisionCMPolarizedActionArtinianLiftingStatement` isolates the geometric
lift needed for the normalized Harris CM presheaf. Its elementary surjection
of local Artinian rings and arbitrary structure map to the spectrum of the
CM base field `F` are the tests in the published division-case criterion. The input is a positive
polarized abelian scheme with the actual rational action and normalized joint
Lie determinant and dimension condition. The output is a positive polarized
abelian scheme with rational action on the thicker base and an equivariant
rational isomorphism on the thinner base.

`PositivePolarizedActionIsometricReduction` asks that the same isomorphism
transport the actual pulled-back polarization with multiplier one. The
built-in dual base-change map and relative dual map additivity express this
as the rational dual pullback equation for every constrained dual evaluation
data on the actual restricted abelian scheme. This permits the class
presheaf to use its prescribed choice of those data.

The geometric route is motivated by the formal smoothness of polarized
abelian schemes with endomorphisms in Kai-Wen Lan's 14 March 2021 thesis
revision, Proposition 2.2.4.9 and Corollary 2.2.4.8, printed pages 157–159.
Lan works with an integral endomorphism structure and the residue-field
conventions of Section 2.2.1. The comparison to the rational action on the
Library's actual schemes and the unrestricted residue fields of these tests
are part of the proof obligation. The upper normalized determinant and
dimension can be recovered by `harrisTaylorCMArtinianNormalization` from
the specified rational isomorphism. Level transport is handled by the
class comparison after this geometric lift.
