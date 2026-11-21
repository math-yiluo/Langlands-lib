# Invariant differentiation of the convergent Eisenstein sum

`parameterDirectionalSection` twists the scalar section by the actual
Iwasawa height power, differentiates its infinite slice in the given
left-invariant direction and applies the inverse twist. Group multiplication
on the two adelic factors and covariance under left translation identify
the derivative of each Eisenstein term with the term for the differentiated
section.

`directionalValue_eisensteinSeries` assumes that the twisted section and
the sum have smooth infinite slices. Summable majorants on compact sets
for the input and all first derivative terms yield locally uniform limits
of the finite sums and their invariant derivatives. The chart calculation
in `SmoothGroupDirectionalLimit` identifies the derivative of the sum
with the limit for the differentiated section.

This is the termwise differentiation step for the Eisenstein series of
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*
(2024), §2.2, equation (2.1), and the operator covariance used in
Langlands, *On the notion of an automorphic representation* (1979),
proof of Proposition 2, printed pp. 205–206 (Corvallis Part I PDF
pp. 200–201). The majorant hypotheses are expressed on the original
Eisenstein terms.
