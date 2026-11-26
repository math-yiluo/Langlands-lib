# Enveloping centers under restriction to a rational Levi

`infiniteLeviRestriction` is the linear restriction of a smooth archimedean
function to the actual Levi points after a fixed right translation by \(a\).
The function is plot-smooth by smoothness of right translation followed by
regular pullback.

`ParabolicLeviCenterRestrictionStatement` asks for a finite complex algebra
map from the ambient enveloping center to the Levi enveloping center for each
fixed \(a\). For a smooth function invariant under left multiplication by the
archimedean radical, restricting the ambient central derivative must agree
with applying the transferred central derivative to the restricted function.
The statement uses the unnormalized restriction \(m\mapsto f(l(m)a)\) and the
existing right differential actions on both actual point groups.

The source is Mœglin–Waldspurger, *Spectral Decomposition and Eisenstein
Series* (1995), I.2.17, printed pp. 37–38, PDF pp. 20–21, registered as
`moeglin-waldspurger-1995-growth-and-constant-terms`, SHA-256
`296dcb3e7170bb0c2689cf0c79136a43cd86976df2b4c51f027cf9365f7fe988`.
The finite homomorphism there is expressed using a modulus twist and a left
center action. On the Levi one converts between left and right central
differential operators. The modulus twist gives an automorphism of the
Levi enveloping algebra, since the differential of the twisting character
vanishes on brackets. Composing with this automorphism gives the raw
restriction convention. In Harish-Chandra, *Automorphic Forms on Semisimple
Lie Groups* (1968), §6, printed p. 19, PDF p. 29, the shift is given explicitly
by half the adjoint trace on the radical. The retained file is registered as
`provided-d0ff4732ff6b5d8ecf8562752577df639622e8aad2899ef307bc320213b534af`,
SHA-256 `c4711298f946d817aa3c888c7fd7fd1190800b2016abe5d3c2a363f6d7a51c31`.
For a translate by \(a\), right
translation conjugates the ambient operator by \(\operatorname{Ad}(a)\) and
preserves left radical invariance. Precomposing with this center
automorphism preserves finiteness of the homomorphism.

`exists_cofinite_center_ideal_of_leviRestriction` proves the ideal transfer
from a finite map satisfying the operator identity. It extends the ambient
ideal by `Ideal.map` and uses `Langlands.Algebra.quotientFinite_map` to show
that the extended ideal has finite codimension. Each generator acts by zero
on the restricted function by the operator identity. Linearity and
multiplicativity of the actual center action extend the vanishing to the
whole ideal. The new ideal depends only on the original ideal and the
comparison map, so it works for the entire family of restrictions. The
existence of the finite map with the operator identity is the entry
proposition.
