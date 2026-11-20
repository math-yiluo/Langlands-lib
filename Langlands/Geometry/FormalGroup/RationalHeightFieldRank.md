# Kernel ranks over fields

`Hom.finrank_finiteKernel_eq_pow_residueCard` is the fibre calculation for
the rational-height existence proof. Let \(O\) be a discrete valuation
ring with finite residue field of size \(q\), and let \(k\) be an
\(O\)-algebra that is a field. For an isogeny from a strict formal
\(O\)-module of finite \(q\)-normalized height to a strict
\(\pi\)-divisible formal \(O\)-module, the dimension over \(k\) of the
coordinate algebra of any finite kernel model is a power of \(q\).

The published isogeny dual and kernel composition results show that this
dimension divides the rank of a source scalar-power kernel, hence divides
a power of \(q\). The jet dimension bound applied to the map and its dual
gives equality of the two coordinate counts. The uniformizer is nilpotent
on the base and therefore maps to zero in \(k\), so the residue field of
\(O\) embeds in \(k\).

Choose a generator of the multiplicative group of that residue field,
with image \(c\) in \(k\). To lift it to a scalar with \((q-1)\)-st power
equal to one modulo a sufficiently high power of \(\pi\), start with any
lift and successively raise it to the \(q\)-th power. The geometric sum
identity increases the divisibility by \(\pi\) at each step. Choose the
precision using the \(\pi\)-torsion bounds of the two tautological points.
The jet linearization then gives weight-\(c\) equations at two deep
characteristic-power widths. Both widths compute the actual kernel
dimension. Reindexing the equations by the source variables and choosing
a sufficiently large \(q\)-power for the perturbation degree shows that
this dimension is congruent to one modulo \(q-1\).

Write \(q=p^s\). The divisibility makes the dimension a power \(p^a\).
Reducing \(a\) modulo \(s\) in the congruence, any positive remainder
would give a positive multiple of \(p^s-1\) strictly smaller than
\(p^s-1\). Thus \(s\) divides \(a\), proving the claimed normalization.
