# Positive mixed Euler coefficients of nonzero homomorphism pullbacks

This internal derived helper proves
`Langlands.AbelianScheme.mixedLineBundleEulerCoefficient_pullback_pos_of_ne_zero`
over an arbitrary field `k : Type u`. For actual abelian schemes `A` and `B`
over `Spec k`, a positive relative dimension `g` of `A`, an ample line bundle
`LA` on `A`, an ample line bundle `LB` on `B`, and an actual nonzero
homomorphism `f : A ⟶ B`, it gives

```lean
0 < mixedLineBundleEulerCoefficient A.X.hom LA
  ((LineBundle.pullback (hom f)).obj LB) g
```

The mixed coefficient and pullback are the existing constructions on actual
line bundles and actual scheme morphisms. Neither a relative dimension for
`B` nor algebraic closedness or characteristic zero is required. This
stronger field scope specializes to the hypotheses of
`HomLocalLatticeStatement`.

The implementation generalizes the published
`Langlands.AlgebraicGeometry.Picard.NonzeroPullbackPowerSection` construction
from endomorphisms to maps with different source and target. First, a private
lemma shows that a homomorphism whose point image is contained in the target
unit section is zero: the source is integral, hence reduced, so
`ComponentConstancy.eq_comp_of_range_subset_range` factors its underlying
scheme map through the target unit section. Its map over `Spec k` then
identifies it with the actual zero homomorphism by extensionality.

Consequently, a nonzero homomorphism has a point whose image avoids the
closed target unit section. The ample-section basis theorem on `B` supplies
a section of a positive power of `LB` which frames at that image point and
whose frame open avoids the target unit section. Pulling the section back
along `hom f` produces a frame point on `A`. Preservation of the unit
section by a group homomorphism makes the source unit point a nonframe
point of the pulled-back section.

Write `g = d + 1`. The published
`mixedLineBundleEulerCoefficient_pos_of_section` applies to this section of
a tensor power of the pullback bundle, with ample twisting bundle `LA` on
`A`. It gives a strictly positive mixed coefficient for that power. The
published `mixedLineBundleEulerCoefficient_tensorPow` rewrites this as the
natural tensor exponent times the desired coefficient. Since that exponent
is nonnegative, the desired coefficient is positive. Field abelian-scheme
geometry supplies integrality, Noetherianity, separation, geometric
connectedness, and the topological dimension bound used in these steps.

This is a composite of existing geometric and coherent-cohomological
results, and an internal prerequisite for the cube/mixed-Euler proof of
local finite generation. It asserts no trace identity or finite-freeness
result, and has no dependency on `HomFiniteFreeStatement` or the desired
local-lattice conclusion.
