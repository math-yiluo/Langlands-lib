# A form and commutant reduction for real tempered standard modules

This internal module supports Task 7158. It proves a conditional reduction to
the unchanged `RealTemperedStandardIrreducibleStatement`. It does not establish
the form or scalar commutant premises, and does not assert the unconditional
irreducibility target.

All spaces and actions are the Library's actual function model:
`KF n ds` abbreviates the `O(n)`-finite functions of `realStandardModule n ds`,
and the actions are `realStandardRep n ds` and `realStandardLie n ds`.

`HasTemperedForm n ds` asks that this space be nonzero and admit a
sesquilinear form `B`, linear in its first variable and conjugate-linear in its
second, such that:

* `B v v = 0` implies `v = 0`;
* `B` is invariant under the actual `O(n)` action;
* for every real matrix `X` there is a complex scalar `c` such that
  `B(π(1 ⊗ X)v,w) + B(v,π(1 ⊗ X)w) = c B(v,w)` for every `v,w`.

A positive definite Hermitian form satisfies the first condition, but positivity
and Hermitian symmetry are not additional assumptions of this algebraic
interface. The scalar term allows a real determinant twist. The explicit
nontriviality condition is necessary: an anisotropic form on the zero space
alone would not prove nontriviality.

`HasScalarCommutant n ds` says every complex linear endomorphism commuting with
both the compact and the complexified Lie actions is multiplication by a scalar.
`RealTemperedFormStatement` and `RealTemperedScalarCommutantStatement` ask for
these respective properties for every list of total rank `n` whose real block
exponents are equal. Both are proposition-valued, unproved prerequisites.

The implemented proof first shows that evaluation at the identity separates
vectors along their compact orbits. Indeed vanishing of all these evaluations
means vanishing on `O(n)`, hence on `GL_n(ℝ)` by the real Iwasawa decomposition
and the principal-series transformation law, using
`eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact`. Every vector is finite
under the compact action by `isRealGKModule_realStandardModule`. The generic
finite-saturation orthogonal-complement theorem in `GKModuleOrthogonal` therefore
supplies algebraic complements of compact invariant subspaces.

The real infinitesimal identity makes an invariant subspace's orthogonal stable
under each `π(1 ⊗ X)`. Tensor induction and complex linearity extend this to the
whole complexified Lie algebra. Thus the complements are invariant under both
actions. The generic scalar-projection criterion then proves irreducibility
from the two properties at a fixed list. Quantifying this argument gives
`realTemperedStandardIrreducible_of_form_of_scalarCommutant`, with both premises
retained explicitly.

The definitions and reduction are internal derived content. They isolate
sufficient algebraic inputs for the Library target; they are not quotations of
the literature's irreducibility theorem. The orthogonal proof follows the
existing complex analogue, through the generic support module, and imports no
Langlands quotient or tied Langlands classification result. The existing target
and all of its imported Lean/Markdown pairs remain unchanged.

The generic module `GKModuleOrthogonal` exports the shared orthogonal-complement
declarations in `ComplexTemperedComplement` and its new irreducibility interfaces
in `GKModuleOrthogonal`; this reduction uses both.
