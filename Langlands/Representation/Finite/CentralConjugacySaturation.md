# Central translates of the conjugates of a coset

For a subgroup `U` of a group `G` and an element `x`, `centralConjugacySaturation U x`
consists of the products `z * (a⁻¹ * x * a) * u` with `z` central and `u ∈ U`.
When `U` is normal this is the union of the central translates of the conjugates of `xU`.
It contains `xU` and is stable under central translations and right multiplication by `U`.
Normality of `U` gives stability under conjugation. For open `U`, the saturation and its
complement are both unions of open left cosets of `U` in a topological group.

Assume `U` is normal and `f` is a centrally covariant class function constant on `xU`.
The indicator truncation of `f` to the saturation retains central covariance and conjugation
invariance and is right `U`-invariant. Moving the final factor `u` through the conjugation
puts the argument back in `xU`, so on the saturation the value is the central multiplier
times `f x`. In a topological group with `U` open, right `U`-invariance gives local
constancy on all of `G`. This supplies a finite-level test function for the character
completeness argument on the group of division units in Deligne–Kazhdan–Vignéras, 1984,
B.1.g, printed pp. 81–82 (`bdkv-1984-representations-local-field`).
