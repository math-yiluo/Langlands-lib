# The first affected degree of the standard Lubin–Tate equation

`standardPolynomial` applies `πT + T^q` to a formal series. `intertwinerDefect` gives the difference between applying that polynomial after the series and substituting it into its variables before applying the series.

`coeff_intertwinerDefect_sub` computes the change in a coefficient of the defect when both input series have zero constant term and their difference starts in degree `n`. Up to degree `n`, the nonlinear power contributes no change. Substitution in the difference has the same coefficients through degree `n` as substitution of the linear terms, which multiplies each coefficient by `π` to its total degree. Together these give the correction factor `π − π^degree`.

This is the degree calculation used for the particular choice `πT + T^q` in Lubin and Tate, *Formal Complex Multiplication in Local Fields* (1965), §1 Lemma 1, printed pp. 381–382.
