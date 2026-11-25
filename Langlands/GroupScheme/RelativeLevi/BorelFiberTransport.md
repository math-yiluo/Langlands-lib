# Field fibres and base change of the Borel locus

These are internal transport lemmas for the Borel-locus proof. They use the
published parabolic field-extension theorem, reductivity of actual field-valued
fibres, the field transport lemmas in `BorelFieldTransport`, and naturality of
the published comparison between successive and composite pullbacks.

Every field-valued point factors through the residue field of its image. The
relative parabolic hypothesis makes the residue-field inclusion closed and
parabolic. Reductivity of that fibre and parabolic ascent therefore imply
parabolicity at the original field-valued point. Geometric Borel ascent and
reflection identify the Borel predicates at the two fibres.

The imported `ParabolicBaseChange` module proves parabolicity at every
field-valued point and preservation of relative parabolicity under arbitrary
base change. This module uses the residue-field comparison to prove that the
set of geometric Borel residue fibres pulls back under any scheme morphism. The arguments use the actual pullback homomorphisms, with the source
and ambient isomorphisms inserted explicitly.
