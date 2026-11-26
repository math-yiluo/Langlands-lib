# Weil pair L-factors on continuous exact classes

`LocalWeil.exactPairLFactorHom` sends two exact classes of continuous Weil representations to the L-factor of their tensor, with values in the additive notation for units of the rational-function field. It composes `ExactGrothendieckGroup.continuousTensor` with `Weil.Local.InertiaEuler.lFactorHom`.

`LocalWeil.unitaryRealize` maps the unitary lattice into the continuous exact group. A basis element and its zero-monodromy pair class have the same continuous representative by `exists_unitaryRealize_generator`. On two such representatives, `arithmeticPairLFactor_zeroMonodromy` identifies the exact-group evaluation with the arithmetic pair L-factor. Expanding the two virtual classes into their signed basis sums proves `unitaryPairLFactor_eq_exact`. Substitution of any two witnessed exact expansions then gives `unitaryPairLFactor_eq_of_expansion`.

This identifies the Weil-side factor in `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement` with an integer-bilinear map.
