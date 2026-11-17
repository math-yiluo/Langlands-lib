# From a diagonal Mellin bound to a gauge–Schwartz quotient integral

This internal module applies the compact torus criterion to a supplied
simple-root gauge and a last-row Schwartz–Bruhat factor on the actual adelic
group. It retains every natural rank, including zero, and any fixed real
determinant exponent.

`gaugeSchwartzKernel` is the product of the gauge value, the extended norm
of the Schwartz function on the last row, and the real determinant power
embedded in the nonnegative extended reals. The gauge predicate supplies
measurability and left unipotent invariance. Continuity of the Schwartz
function and last-row map supplies measurability of their composite.
The determinant norm is positive and continuous, so its fixed real power
is continuous. These facts prove measurability of the entire kernel.
The last row and determinant norm are unchanged under left adelic
unipotent multiplication, proving the corresponding invariance.

`gaugeSchwartzTorusMajorant` is the separated diagonal kernel: the inverse
positive-root modulus, the original simple-root norm weight, a Schwartz
norm on the simple-root row, a one-dimensional Schwartz norm of the last
diagonal idele, and the diagonal determinant power.

The theorem `lintegral_gaugeSchwartzKernel_lt_top_of_torusMajorant` assumes
finiteness of these diagonal majorants for all pairs of Schwartz functions,
using any one supplied Haar measure on the full idele torus. For a compact
set of right translates, the previously proved compact kernel theorem
produces two such Schwartz functions and a nonnegative real constant A.
Multiplying its pointwise estimate by the inverse modulus and integrating
gives one uniform bound: `ofReal(A)` times the finite majorant integral.
The constant is finite, so its extraction from the lower integral requires
no additional measurability premise. The actual Whittaker quotient
criterion applies with the measurability and invariance already proved.

This is a derived composition of published analytic and quotient
infrastructure. The diagonal Mellin finiteness hypothesis remains explicit;
this supporting theorem alone does not assert a convergence half-plane or
prove the unconditional Whittaker–Schwartz statement.
