# Source character measure at the full standard Levi

This derived unit compares precisely the character measures in the two
group-Levi packet constructions used for Waldspurger VIII.4.2, printed p.330
(PDF p.96). It retains the I.1 character normalization from printed p. 239
(PDF p. 5).

For the full standard Levi, `rationalFullLeviSplitComponent` factors the
supplied ambient split component through `rationalFullLeviSchemeIso`. Its
source torus is unchanged, and it is proved to be a split component of the
actual standard Levi scheme by the existing `IsSplitComponent.comp_iso`.

`rationalFullLeviCharacterEquiv` first transports ambient unitary unramified
characters to this intrinsic Levi scheme, then applies the published
intrinsic-to-literal character homeomorphism. Its evaluation theorem gives the
original ambient character at the literal Levi element.

`map_rationalFullLeviCharacterEquiv_Haar` identifies the full-root packet's
`standardLeviUnitaryUnramifiedCharacterHaar` with the pushforward of the ambient
`rationalUnitaryUnramifiedCharacterHaar` for the originally supplied split
component. The finite-index valuation-image hypotheses on both sides follow
from the published split-component theorem. The proof uses the actual
restriction-kernel cardinality preservation under the scheme isomorphism and
the defining measure transport to the literal Levi. No measure is changed to
the defining measure transport to the literal Levi. In this split-component
application the kernel-scaled Haar measure realizes Waldspurger's local
restriction normalization. The measure theorem takes an affine structure on
the source torus as input, as in
the existing character-measure interfaces; split-torus structure provides it
when the theorem is applied.

The comparison applies to connected reductive groups over nonarchimedean local
fields of arbitrary characteristic, including nonsplit groups.
