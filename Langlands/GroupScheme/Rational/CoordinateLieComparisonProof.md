# Actual augmentation cotangent and Lie-kernel weight comparison

`coordinateLieComparison` proves the exact proposition `CoordinateLieComparisonStatement` at arbitrary universe `u`. It assembles the actual augmentation duality, the actual base-cotangent action pairing, and the intrinsic support comparison. The source is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), §3.3, printed p.107 / PDF p.133.

The first component uses `kernelCotangentDuality`: an actual dual-number identity-kernel point determines its coordinate derivation, which descends through products in the augmentation ideal to the actual quotient `I/I²`. The resulting equivalence is linear over every commutative coefficient algebra and has the prescribed coordinate evaluation on each augmentation class.

The second component uses `cotangentActionPairing`: tensor extension of the actual kernel coordinate map gives the duality on the actual base-changed cotangent. Evaluation after direct coordinate pullback equals evaluation at the actual point acted on by the constant dual-number lift. This preserves the source's direct convention and the required equality of underlying scheme points.

The third component uses `cotangentLieSupport`, whose published proof applies `cotangentLieSupport_of_coordinateWeightDecomposition` to `coordinateWeightDecomposition`. Under the retained affine, locally finite type and split-torus hypotheses, actual cotangent weight spaces and intrinsic Lie weight spaces span. The actual transpose pairing makes distinct character labels orthogonal; perfect duality and spanning then identify their nonzero supports. The published comparison between the intrinsic Lie weight spaces and `RelativeRoot.actionWeightSupport` gives the target equality, including character zero when present.

The conjunction uses these component proofs without adding hypotheses. Every field characteristic and all coefficient algebras in the exact statement are retained. The component modules give the derived tensor, derivation and linear-algebra proof details; this module only assembles their conclusions and assumes neither semigroup realization nor a commutator result.
