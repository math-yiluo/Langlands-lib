# Original Haar characters on a represented intersection Levi

This is an internal adapter for the local represented geometric lemma. It uses
the published intersection datum and actual Haar characters. Its provenance is
the functorial point maps, the datum's conjugation identity, and the published
conjugation invariance of Haar modulus; it asserts no additional structure
theorem for parabolics.

`leviInducingHalfCharacter` pulls the canonical positive complex square root
of the actual radical Haar character back to the represented Levi's own
rational points. The closed radical supplies local compactness, and the open
kernel of the Haar character supplies smoothness.

`targetCommonLeviPointsEquiv` identifies the rational points of the datum's
`L'` with the literal intersection
`L(F) ∩ z⁻¹ M(F) z`, viewed inside the target Levi image. Its underlying
ambient point is the original composite point map of `lQ'`, `q'`, `lQ`, and
`q`. `sourceCorrectionTransport_commonLevi` identifies the generic inverse
conjugation map at that point with the actual source-Levi inclusion after
`D.e`. The proof applies the datum's conjugation identity, retaining all
intermediate subgroup copies.

`inducingHalfCharacter_commonLevi` then identifies the original inducing
positive half, restricted through `D.e`, with the positive half of the actual
Haar modulus of the conjugate radical `z⁻¹ N(F) z`. The implemented proof
first uses the published Haar-conjugation equality to return to the original
radical, then uses the point-map identity above.

`targetInverseHalfCharacter_commonLevi` identifies the original target
Jacquet inverse half with the inverse half of the actual target radical Haar
modulus at the same common-Levi point. Both characters evaluate the same
normalizer element, so the proof is functoriality of the target point map.

The field and group topology hypotheses are those needed by these existing
point identifications and Haar characters. No root presentation, dynamic
realization, standardness, or modulus-balance premise is used. The two
radicals remain distinct. This module does not prove their five-subgroup
balance, identify the two inner endpoint characters, or prove the local
orbit-comparison statement.
