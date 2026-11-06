# Monicity of a closed subgroup over the base

`IsClosedSubgroup.mono_overHom` is the existing proof of
`Langlands.Aubert.General.RepresentedParabolic.mono_hom_hom_of_isClosedSubgroup`
from `Representation.Geometric.RepresentedGeometricLemmaGeometryReduction`,
placed in the group-scheme layer for shared use. It retains the same arbitrary
base scheme, group schemes, homomorphism and closed-subgroup hypothesis.
A closed immersion of schemes is monic; `Over.mono_of_mono_left` gives monicity
over the base. The original named theorem and the parabolic Levi-intersection
wrapper both reuse this proof. No mathematical hypothesis or conclusion changes.
