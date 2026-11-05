# Torus quotients of split-torus-dominated solvable groups

Author: Worker 1485.

`SplitTorusDominatedSolvableQuotientStatement.{u}` is a proposition target.
For every field `k : Type u`, it concerns a smooth connected affine actual
group scheme `H` that is solvable and has
`HasPointedSplitTorusDomination H`. The domination predicate supplies an
actual finite-rank split torus over `k` and a dominant morphism of relative
schemes to `H` that preserves the identity section. This morphism need not
be a homomorphism. All characteristics, finite fields, and imperfect
fields are retained.

The conclusion supplies actual group schemes `U` and `D` and
homomorphisms `i : U ⟶ H` and `q : H ⟶ D` over that same field. The
inclusion is closed, and `U` is smooth, connected, and unipotent in the
existing representation-based sense. The predicate
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q` requires the
underlying projection to be flat, surjective, and locally of finite
presentation. It also identifies the range of its full scheme kernel
with `SubgroupFunctor.range i` on every relative test scheme. In
particular the kernel is not replaced by its reduced subscheme or by a
kernel on rational points. Its normality follows from being the full
kernel. The quotient `D` is a torus in the existing sense.

This is a derived structural consequence of T. A. Springer, *Linear
Algebraic Groups*, second edition (1998), Theorem 14.3.8(i), printed
pp.245–246 / one-based PDF pp.259–260, together with Proposition 14.1.4
and Proposition 14.1.2, printed pp.237–238 / PDF pp.251–252. The registered
source is `springer-1998-linear-algebraic-groups`, SHA256
`44d69662b47d85998f4e65baba1dd1454a3a30e065bcd58342c227d59a73aabf`.
The theorem characterizes split solvable groups by dominant
parametrizations from products of affine space and split tori; here the
affine-space factor has dimension zero, and pointedness further
restricts the hypothesis. Proposition 14.1.4 then gives triangularity,
and Proposition 14.1.2 supplies the ground-field geometric radical and
the split torus quotient. The present target asks only for a torus
quotient and a smooth connected unipotent full kernel. Translating the
source into these actual group-scheme predicates, including the full
kernel, its smoothness, and its fppf quotient comparison, remains part
of the proof.

This file does not prove the target or assert splitness of `U`. It
isolates the initial quotient construction needed before the existing
kernel-domination and finite-Galois descent results apply. It requires
neither maximal-torus conjugacy nor an algebraically closed ground
field.
