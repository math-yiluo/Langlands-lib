# From the generic truncation estimate to the holomorphic comparison

`GenericTruncationComparisonStatement` expresses the last step of
Delorme's Theorem 7.1 for the actual characteristic and regularized
pairings. Its inputs include continuity and integrability of the
characteristic pairing, a generically holomorphic representative of
the regularized pairing with a local affine pole presentation, and the
uniform exponential estimate on the generic imaginary parameters.
The finite label list gives the open dense generic region once each
coroot denominator has a nonvanishing imaginary value.

For a fixed regular truncation parameter \(T\), take
\(\delta=R/(\|T\|+1)>0\). The bound \(\delta\|T\|\leq R\) puts \(T\) in
the sector of this \(\delta\). The generic estimate for fixed \(T\) and
central translate then bounds the difference from the continuous
characteristic pairing on each bounded set of imaginary parameters.
The local division theorem and the maximal extension give one
holomorphic representative on an open set containing the entire
imaginary slice. Its values on the generic slice agree with the
actual regularized pairing.

For each prescribed sector and bounded parameter set, first apply the
generic estimate on an open ball containing that set. Density in the ball
and continuity of the two pairings extend the estimate to every parameter
in the original set. The same constants apply to all regular truncation
parameters in the sector and all central translates. This step uses the
given generic estimate and pole presentation.

The source is P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, Theorem 7.1 and the final
paragraph of its proof on p. 32.
