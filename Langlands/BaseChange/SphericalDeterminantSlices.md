# Determinant-order slices of spherical Hecke functions

Let \(F\) be a \(p\)-adic field and \(n \geq 1\). On \(\mathrm{GL}_n(F)\)
the determinant order is the additive valuation of the determinant,
normalized to give a uniformizer order one. It is continuous into the
discrete integers, additive under multiplication, and zero on
\(\mathrm{GL}_n(\mathcal O_F)\). Cutting a spherical Hecke function on
one determinant order preserves compact support, local constancy, and
invariance under this subgroup on both sides. The resulting
`sphericalDeterminantSlice` equals the original function on its selected
order and vanishes everywhere else.

`SphericalDeterminantSlicesStatement` expresses the original function as
a finite sum of these slices. The proof takes the image of its topological
support under the determinant order. That image is compact in the discrete
integers, hence finite. At each group element at most one summand contributes.

Henniart–Lemaire, *Changement de base et induction automorphe pour GLₙ en
caractéristique non nulle* (2011), I.6.10, printed pp. 51–52 (PDF pp. 59–60),
reduce to a Cartan double coset whose determinant order is the sum of its
exponents. Grouping Cartan double cosets by this sum gives the corresponding
reduction by determinant order. The Lean proof obtains the slices directly
from compact support and the continuity of determinant order.
