# Iterated decay from contraction modulo a left invariance subgroup

`HasUnipotentContractionModulo` expresses a bound on displacement by
archimedean points of a unipotent subgroup. For each compact set of these
points, a left factor in a designated subgroup can be removed and the
right displacement written as \(\Psi(v)\). The map \(\Psi\) is smooth
from a finite-dimensional real normed space to the archimedean group
and takes zero to the identity. The parameter \(v\) has norm at most
a constant times the contraction factor \(\varepsilon(t)\), which is
nonnegative and uniformly bounded on the parameter set.

`AdelicUnipotentDecayModuloStatement` fixes a compact set \(Y_f\) in the
finite adelic group, an open finite right level, a derivative order
\(n\), and a compact set \(K\) of right factors. It gives a compact
\(K'\supseteq K\) and a constant \(C\) uniform in the evaluation
factors and the function. The estimate applies at \(y=p a(t) k\) with
\(k\in K\) and \(y_f\in Y_f\). The function \(f\) is continuous,
smooth on the archimedean slices, invariant on the left under the
rational unipotent group and the designated subgroup, and invariant
on the right under the fixed finite level. If its unipotent constant
term vanishes, any nonnegative bound \(M\) for all basis derivative
words of length \(n\) at \(p a(t) k'\) with \(k'\in K'\) and
\(k'_f=k_f\) gives
\[
  |f(p a(t) k)| \le C\,\varepsilon(t)^n M.
\]

The one-step estimate uses `adelicUnipotentArchimedeanRepresentatives`
with \(Y_f\) to replace arbitrary unipotent translates at the allowed
evaluation points by a uniform compact set of archimedean translates,
using rational and finite-level invariance. The contraction hypothesis
bounds the displacement parameter after the allowed left multiplication.
`smoothGroupCompactCoordinateEstimate` bounds the difference of function
values by the parameter norm times the supremum of the first derivatives.
Averaging the difference over the normalized unipotent quotient gives
the first power estimate. For the iteration, the normalized integral
commutes with the invariant derivatives by
`adelicUnipotentConstantTermDifferentiation`. The left invariance is
preserved by right-orbit differentiation. Induction applies the one-step
estimate to the derivatives and gains one power at a time.

The proof extends the argument of `AdelicMaximalUnipotentDecay` to
contraction modulo a left invariance subgroup. The intended application
is to the alternating constant terms in Arthur 2005, §13, (13.7),
printed pp. 71–72. Their left invariance under the radical of the upper
parabolic allows contraction to be checked in its Levi.
