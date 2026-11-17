# Factorization through a supplied full-kernel quotient

This internal construction packages existing fpqc homomorphism descent for
the full kernel of a group-scheme homomorphism. Its provenance is derived
from the Library's actual kernel and fppf quotient predicates,
`FpqcHomDescent.hom`, its factorization and uniqueness theorems, and
`FpqcHomDescent.mono_of_kernel_range_le`.

Let `f : H ⟶ G` and `q : H ⟶ Q` be homomorphisms of group schemes over any
scheme `S`. Assume that `q` is the actual fppf quotient by the full subgroup
functor represented by `kernelι f`, and that its underlying scheme map is
quasi-compact.

`factor f q hq : Q ⟶ G` is the descended homomorphism. The theorem `fac`
states that `q ≫ factor f q hq = f`; `mono_factor` proves that the
underlying morphism in `Over S` is a monomorphism. The theorem `unique`
characterizes this factor by its composition with `q`. Finally,
`exists_mono_factor` supplies the factor when `q` is affine, using
quasi-compactness of an affine morphism.

The implemented proof first uses equality of full kernel subgroup functors
to show `kernelι q ≫ f = 0`. Flatness, surjectivity, and quasi-compactness
allow the existing fpqc descent construction to descend `f`. The full
kernel equality also gives the inclusion required by the existing
monomorphism theorem. That theorem checks triviality of the kernel of
the factor after local lifting along `q`. Uniqueness is the existing
fpqc descent uniqueness theorem.

The construction assumes a represented full-kernel quotient. It does
not prove that such a quotient exists or establish multiplicative type
of either its target or the original kernel.
