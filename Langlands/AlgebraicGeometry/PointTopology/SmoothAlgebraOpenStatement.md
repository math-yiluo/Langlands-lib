# Smooth algebra maps on complete-field points

Author: Worker 208.

`SmoothAlgebraPointOpenStatement` asserts that, for a complete nontrivially
normed field K and commutative K-algebras A and B with a compatible A-algebra
structure on B, smoothness of B over A implies openness of restriction

    AlgPoint K B K → AlgPoint K A K.

The field and two algebra universes are independent. The map is composition
with the actual coefficient inclusion `IsScalarTower.toAlgHom K A B`, and both
point spaces carry their published evaluation topologies. Mathlib's
`Algebra.Smooth A B` includes formal smoothness and finite presentation over A.
No finite-type hypothesis over K, characteristic restriction, local compactness,
nonarchimedean condition or surjectivity assumption is imposed.

This is a derived affine algebra-map version of the local smooth-openness
discussion in Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed p.11, after Proposition 4.4 and before Theorem 4.5.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The arbitrary K-algebra formulation is an implementation generality of the
source reduction: at the kernel of each actual K-valued point, the smooth
algebra admits a principal localization standard etale over a finite polynomial
algebra over A. Standard etale point openness and relative polynomial
projection openness then give openness on this neighborhood. These
neighborhoods cover the point space.

This file states the proposition; it does not prove the local normal-form
reduction or openness. The comparison with actual affine scheme points, gluing
for arbitrary nonaffine schemes, and the adelic application remain separate
obligations of the parent program.
