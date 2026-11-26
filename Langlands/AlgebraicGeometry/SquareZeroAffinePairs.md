# Affine pushouts for comparing square-zero lifts

The ring of pairs congruent modulo a square-zero ideal `J` of `C` is the split
extension `C ⋉ J`, with projections `(a, x) ↦ a` and `(a, x) ↦ a + x`. When
`J` is a `D`-module whose action restricts to the original `C`-action along a
surjection `C → D`, this same ring is the pullback of `C` and `D ⋉ J` over
`D`. The shared coefficient in the second pullback is `x`. The published affine
pushout theorem turns both ring pullbacks into pushouts of schemes.

The two pushouts give an affine form of SGA 1, Exposé III, Proposition 5.1.
The difference of two lifts is encoded by a map from the split test to the
target. Write `f : C → D` for the coefficient map, and let `α, β : A → C`
be the two lift maps on an affine target. The maps agree modulo `J`. The
coordinate map from `A` to `D ⋉ J` sends `a` to
`(f(α(a)), β(a) − α(a))`. Its constant term is shared by the two lifts
when `f ∘ α = f ∘ β`, as happens when `f` kills `J`. The pushout universal
properties give the comparison for arbitrary scheme targets.

Source for the infinitesimal comparison: `sga1-arxiv-math-0206203v2`, printed
pp. 59–60 (PDF pp. 75–76), SHA-256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.

The triple test `C ⋉ (J × J)` records successive increments in
`(a, a + x, a + x + y)`. Its first and second pair maps make its spectrum the
pushout of the two pair spectra along their common middle term. Over `D`, the
shift `a + x` reduces to the same base coordinate as `a` when `C → D` kills
`J`. The reduced pair maps select the first increment, the second increment,
and their sum. The split test with two coefficients also supplies the pushout
of two split tests along their common zero section.
