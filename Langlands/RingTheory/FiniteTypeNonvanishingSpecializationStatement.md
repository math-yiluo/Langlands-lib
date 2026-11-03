# Finite-type specialization with prescribed nonvanishing

`Langlands.RingTheory.FiniteTypeNonvanishingSpecializationStatement.{u,v}`
is a proposition target. This module states it and supplies no proof.

Let `k : Type u` be an algebraically closed field and let `A : Type v`
be a commutative `k`-algebra of finite type. For a finite set `s` of
elements of `A`, assume that their product is not nilpotent. The
proposition asserts the existence of a `k`-algebra homomorphism
`φ : A →ₐ[k] k` such that `φ a ≠ 0` for every `a ∈ s`.
The universes of `k` and `A` are independent. There is no assumption
on characteristic, reducedness or integrality of `A`.

The product condition says that the basic open defined by the product
is nonempty. It is stronger than merely saying that the product is
nonzero when `A` is not reduced. The conclusion chooses a ground-field
point in that open and records nonvanishing of every factor. The empty
finite set is included: its product is `1`, so the hypothesis excludes
the zero ring and the conclusion is existence of a ground-field point.
For an algebra contained in a field, nonzero prescribed elements
satisfy the hypothesis because their product is nonzero and the
algebra is a domain.

This is an internal commutative-algebra interface for finite-data
specialization in the connected-reductivity field-extension proof.
Its mathematical justification combines the finite-type Jacobson
property, a maximal ideal avoiding the product, Zariski's lemma for
the residue field, and algebraic closedness of `k`. The relevant
existing Mathlib interfaces are
`isJacobsonRing_of_finiteType`,
`Ideal.radical_eq_jacobson`,
`finite_of_finite_type_of_isJacobsonRing`, and `IsAlgClosed.lift`.
The particular finite-set packaging is derived for this project and
is not asserted to be a literal statement from an original source.

This proposition concerns only the choice of a specialization.
It supplies no descent of group schemes or subgroups, preservation
of their geometric properties in families, or invariance of the
unipotent radical.
