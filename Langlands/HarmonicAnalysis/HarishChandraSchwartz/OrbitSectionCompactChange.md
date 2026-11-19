# Change of compact picture for the original orbit sections

For two compact open Iwasawa factors `K` and `L` of the same parabolic, the
underlying actual product-induced orbit sections have the same finite scalar
smoothness condition. `orbitSectionLevelChangeCompact` sends a section of
level `H` for the `K` picture to the same actual section of level `H ⊓ L`
for the `L` picture. This map is complex-linear and continuous in the
existing section-level seminorm topologies. Any finite supremum of target
derivative seminorms on this map is bounded by a constant times a finite
supremum of the source derivative seminorms.

The proof covers the compact set `L × L` by finitely many left translates
of `K × K` with representatives in the product parabolic. Choose one
covering translate for each evaluation point. Within each translate, the
normalized covariance law and `productCompactTwistTensorEquiv_inducing`
express the new evaluation as a fixed linear map of the original compact
restriction times one Laurent character. The injective compact evaluation
map and its linear left inverse give a finite-sum formula for the whole
new compact restriction. This formula proves preservation of finite scalar
smoothness. After applying a linear functional to the same formula, the
Leibniz bound controls each target derivative seminorm by finitely many
source seminorms. The continuous seminorm bound then applies to finite
suprema.

This derived comparison allows estimates in Waldspurger VI.3.1 to use a
compact subgroup adapted to the standard-Levi intersections. The section's
values in the actual product-induced representations are preserved.
