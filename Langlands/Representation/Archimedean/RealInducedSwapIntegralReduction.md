# The integral parameters remaining in the two-induced-block swap

This internal reduction for Task 7172 uses the generic GL4 swap and the
equal-parameter identity. Write \(p=|d.\mathrm{weight}|\),
\(q=|e.\mathrm{weight}|\), and
\(\nu=(\mathrm{chB}\ d).\mathrm{exponent}-
(\mathrm{chA}\ e).\mathrm{exponent}
=d.\mathrm{exponent}-e.\mathrm{exponent}-(p+q)/2\).

`IntegralWindow d e m` says that \(m\) is a natural number,
\(\min(p,q)\le m\), \(2m\le p+q\), and \(\nu=-m\).
`IntegralSwapStatement` asks for the actual injective standard intertwiner in
rank four for every such window, with both weights nonzero and \(p\ne q\).
It adds no exponent-order or unlinkedness assumption: those are consequences
of this window.

`generic_of_not_integer` proves that a nonintegral \(\nu\) makes all four
constituent parameters generic. The other three differences are
\(\nu+p,\nu+q,\nu+p+q\), so their integrality would imply that of \(\nu\).
The imported generic construction therefore supplies the swap in this case.

`integralWindow_of_integer` proves that an ordered unlinked pair with integral
\(\nu=z\) lies in the window. The identity
\(|p-q|+2\min(p,q)=p+q\) shows that \(z+\min(p,q)>0\)
would give a positive integer in the forbidden linking condition. Hence
\(m=-z\ge\min(p,q)\); the exponent order gives \(2m\le p+q\).
Conversely, `order_unlinked_of_integralWindow` recovers the order from the
second inequality, and a putative linking value would imply
\(\min(p,q)=m+k\) for some positive natural \(k\), a contradiction.

If \(p=q\), the two inequalities force \(m=p\), and the parameter equation
forces the two complex exponents equal. `exponent_eq_of_equal_weights`
records this fact, allowing the published identity swap.

The actual swap corollaries include arbitrary surrounding lists:
`injective_of_not_integer` handles nonintegral \(\nu\), `injective_of_im_ne`
handles unequal imaginary exponents, and `injective_of_equal_weights` proves
the ordered unlinked swap for equal absolute weights. The first two corollaries
require only the total-rank equality besides their stated parameter condition;
the equal-weight corollary retains both nonzero-weight hypotheses, the order,
and unlinkedness.

`realInducedSwap_iff_integral` proves an equivalence between the original full
`RealInducedSwapStatement` and `IntegralSwapStatement`. The forward implication
specializes the original statement to rank four. The reverse implication
splits on integrality, uses the equal-parameter identity when the weights agree,
and otherwise applies the supplied integral result followed by the proved
induction-in-stages theorem.

This is a proved reduction, not a proof of `IntegralSwapStatement` or of the
full swap. Its provenance is internal arithmetic from the Library definitions,
the explicit generic construction, the equal-parameter identity, and induction
in stages. No external mathematical result is assumed.
