# Cyclic representative gauges over algebraically closed fields

Worker 1317. This is internal support for the split Steinberg quotient proof,
derived from actual torus ratios, the full normalizer Weyl action, the actual
Coxeter torus commutator, and rational lifting for locally finite type morphisms
over an algebraically closed field. It has no external source claim.

For any two actual normalizer points with equal action on the full character
lattice, their ratio has trivial Weyl action. Split character separation makes
this ratio centralize the torus, and maximal-torus self-centralization places it
in the range of the actual torus inclusion. This proves
`exists_torus_mul_of_weylAction_eq` over an arbitrary field.

For every ordering and two supplied simple-reflection representative families,
their full ordered normalizer products have the same Coxeter action. They
therefore differ by a rational torus point `q`. If the actual group is semisimple,
the proved actual Coxeter torus commutator is surjective. Over an algebraically
closed field its locally finite type morphism lifts `q⁻¹` to a rational torus
point `t`. The commutator formula then yields full-product conjugacy by `t`.
The rational lift uses `exists_rationalPoint_lift_of_mem_range` and verifies its
finite type hypothesis from smoothness of the split torus; it is not an inference
from geometric surjectivity over a general field.

A finite recursion starts at `t₀ = t` and satisfies
`t_(j+1) = m_j⁻¹ t_j n_j` after the torus inclusion. Each step remains in the
torus: `m_j n_j⁻¹` is the previously constructed rational torus ratio, and
conjugation by `n_j⁻¹` is the actual inverse of its supplied torus automorphism.
The private finite-path construction and product telescope show that full-product
conjugacy forces `t_r = t₀`, using monicity of the torus inclusion. This is
`nonempty_cyclicTorusGauge_of_conjugate`, which itself needs no algebraic-closedness
assumption when the conjugating point is supplied. Rank zero is included by the
same finite recursion.

Consequently `nonempty_cyclicTorusGauge` and the chosen `cyclicTorusGauge`
construct an actual cyclic comparison for every supplied family over an
algebraically closed field under semisimplicity. There is no restriction on the
ordering or on the choice of representatives. Applying the already constructed
all-test diagonal parameter isomorphism and quotient conjugation comparison gives
`isIso_quotient_iff_representatives`: the isomorphism property for the actual
Steinberg product followed by the canonical `ClassFunctions.rho` is independent
of those supplied representatives, with the same supplied normalized root maps.

The construction permits arbitrary characteristic and universe. Algebraic
closedness is retained in the gauge-existence and unconditional transport
conclusions. This file supplies neither descent to a general base field nor
fundamental representations, invariant generation or a proof of the canonical
quotient isomorphism for even one representative family.
