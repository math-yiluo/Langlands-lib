# Matrix height in the alternate complex tail chart

`complexGapAlternateHeight` bounds the matrix height in the right-tail
chart when the upper rectangle has only its first column. There is a
fixed polynomial cost in the norm of the first physical tail column
and in the norm of the inverse-transpose trailing columns. The remaining
factor is the exponential of twice the sum of the absolute logarithmic
tail coordinates.

The inverse block formula bounds the full inverse matrix by the first
rectangle column and the inverse tail block. The observed column and the
inverse-transpose tail control those two entries through
`alternateTail_norm_bounds`. Apply the matrix height estimate with its
determinant multiplier to the full inverse. Its determinant modulus is
the exponential of twice the sum of the logarithmic tail coordinates.
The reciprocal of that multiplier gives the stated exponential factor.

This is a derived bound for the leading Schwartz pullback in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), §10.4, Lemma 10.7, author
pp. 79–81. It uses the chart with one retained rectangular column in
§10.2, after (10.5), pp. 72–73.
[Registered author edition](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
