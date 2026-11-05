# The rational determinant character of the full adjoint action

Author: Worker 107.

For an affine group scheme G over a field k, with locally finite type
structure morphism, `Lie.adjointDeterminantCharacter G` is the actual
rational algebraic character det(Ad): G → Gm. The definition specializes
`AutomorphicAction.determinantCharacter` to conjugation of G on itself
and the existing natural `Lie.finiteCoordinates G`. These coordinates
come from the actual dual-number identity kernel and its proved scalar
extension, using a finite basis over k. The field and group have arbitrary
universe `u`; dimension zero is included. Smoothness, connectedness and
reductivity are unnecessary for this algebraic construction.

`adjointDeterminantCharacter_affinePoints` evaluates the character on every
commutative k-algebra of the same universe as the unit determinant of the
actual conjugation differential. `adjointDeterminantCharacter_val` identifies
its underlying scalar with `LinearMap.det (adjoint G A g)` on the actual
Lie kernel. The first result is the existing all-affine-test determinant
formula. The second uses `differential_conjugation` to identify the two
endomorphisms before taking determinants. Thus this definition does not
substitute an unrelated matrix character for the adjoint determinant.

The construction implements Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §3.6, equation (3.13), printed p.90, using the
Library's existing algebraic action machinery. This module makes no
claim about analytic Haar scaling, reductive triviality or subgroup
Haar invariance. Those require further proofs.

Source: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§3.6, printed pp.87–90, especially equation (3.13). The October 2026
author errata has no correction to this passage.
