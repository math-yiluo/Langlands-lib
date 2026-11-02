# Comparison with Cartesian projective atlases

This is derived internal infrastructure for comparing actual gluings
with different projective atlases.

For a strict coordinate cocycle on a small thin locally directed open
cover, `CartesianAtlas` consists of actual projective chart morphisms
into an actual scheme over the same base. The morphisms satisfy the
specified transition equations and each chart is Cartesian over its
base-cover member.

`desc` is the colimit morphism from the previously constructed glued
projective scheme. The Cartesian hypothesis implies the atlas charts
are open immersions and cover the target scheme. Pullback pasting shows
that the base change of `desc` to every atlas chart is the identity.
Since being an isomorphism is local on the target, `desc` is an
isomorphism. `schemeIso` is the resulting actual scheme isomorphism; it
commutes with the structure morphisms, has the specified chart equations,
and is the unique morphism with those equations.

The input target scheme and atlas are used only to compare actual
projective gluings. They are not a representing object or universal
family for the ordinary polarized moduli functor. This construction
does not prove the host representability statement.
