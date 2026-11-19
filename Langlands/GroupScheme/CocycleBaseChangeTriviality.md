# Cover changes and base changes of trivial cocycles

`Cocycle.baseChangePullback` uses the canonical pullback cover to base change a natural cocycle. `Cocycle.IsTrivial.baseChange` pulls a trivializing cochain to any compatible cover over the new base by the multiplicative pullback adjunction.

The imported `Cocycle.IsTrivial.of_refine_fpqcCover` reflects triviality along a refinement whose structure morphism to the base is fpqc. The relative descent theorem applied over the terminal object gives a cochain on the product of the original cover with that object. Restricting along the canonical section gives a cochain on the original cover. This permits a field cover mapping into a component of a pulled-back finite étale cover.

`Cocycle.isTrivial_baseChangePullback_twice` transports a trivialization across a commutative square of bases. The universal property gives a map from the successive pullback cover to the pullback through the other side of the square. The relative cochain restricts along this map. The composed multiplicative pullback adjunction transfers its identity to the successive base change. These are internal comparisons for arithmetic cocycles on Weil restrictions.
