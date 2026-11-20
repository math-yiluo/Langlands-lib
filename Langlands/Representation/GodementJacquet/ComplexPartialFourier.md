# Last-column Fourier decay

The last-column integral in Jacquet’s §7.3, formula (7.7), takes a Schwartz
test on a rectangular complex matrix space. Lean proves continuity in the
fixed square block and the last-column frequency. It also bounds the integral
by a constant times arbitrary inverse powers of `1 + ‖X‖` and `1 + ‖y‖`,
where `X` is the fixed block and `y` is the frequency. The phase is the positive
trace character for the specified parameter. The primal recursion uses the
parameter `-a`.

Integration against the bounded phase gives arbitrary decay in the fixed
block. To bound the same integral in the frequency, the proof forms the full
Fourier transform on the two coordinate blocks. This transform is Schwartz by
transport from the combined finite coordinate space. Affine inversion in the
first block writes the partial transform as a slice integral of the full
transform. Its Schwartz estimates give arbitrary decay in the frequency.
Comparing the two block norms yields the product estimate. For continuity,
the Schwartz bound with degree zero in the fixed block gives an integrable
majorant independent of both parameters. The integrand is continuous at each
integration point, so dominated convergence applies.

This internal estimate supplies the partial Fourier bound used in the
absolute convergence argument for Jacquet’s Proposition 7.2.

Source. H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
§7.3, printed and PDF pp. 47–50.
