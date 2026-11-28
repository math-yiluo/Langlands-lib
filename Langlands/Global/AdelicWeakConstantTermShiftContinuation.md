# Continuation of the nonunitary constant-term equation

`splitShiftProduct` acts on functions on \(G(\mathbb A)\) by a finite
product of powers of differences. Each factor subtracts a scalar from
left translation by a fixed point of the positive split component.
The scalar roots can depend meromorphically on the Eisenstein parameter.

For each fixed evaluation point, the shifted value is meromorphic.
The proof inducts on a power of a difference and then on the number
of factors. Each difference uses two pointwise evaluations and
multiplication by its scalar root. The scalar meromorphic identity
theorem extends the zero equation from a nonempty open set to the
common open dense domain.

For a finite normalized exponent decomposition of the remainder,
the product preserves each exponent. Directness therefore says it
annihilates each component separately. At a unitary exponent, the
raw eigenvalue has the norm of the half modulus. Each factor acts
injectively on that exponent space if its scalar root has a different
norm. Thus the unitary components of the remainder vanish. Regrouping
the decompositions of the proposed unitary part and the remainder
gives `IsWeakConstantTerm` for the actual constant term.

`weakConstantTermShiftContinuation` combines these arguments. It
requires a meromorphic remainder, its equation on the convergence
set, and the exponent decompositions and root separation on the
parameters under consideration. The source is the analytic passage
following (4.3) in P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 16–17. The
constant-term remainder and its exponent constraints there come from
E. Lapid, *On the asymptotic inner product formula for Eisenstein
series*, (12)–(13) and Lemma 6, pp. 321–323.
