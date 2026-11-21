# Equivariant factor-set averaging

Author: Worker 3502 (Task 7944). Module
`Langlands.GroupScheme.Trigonalizable.FiniteGroupAveraging`.

`EtaleExtensionSplit.exists_equivariant_averaged_section` takes a group
homomorphism `f : E →* Q` with a supplied set section `s`, where `Q` is
finite of order `m`. The kernel is abelian and killed by a natural number
`p > 1` coprime to `m`. The lemma returns a homomorphic section equivariant
under every supplied pair of automorphisms of `E` and `Q` compatible with
`f` and `s`. It does not require a linear action on the kernel, or that `s`
preserve the identity.

Set `c(a,b) = s(a)s(b)s(ab)⁻¹` in the kernel and let `J_a` be conjugation
by `s(a)` there. Associativity gives

```
c(a,b)c(ab,z) = J_a(c(b,z))c(a,bz).
```

Multiply this identity over `z ∈ Q`. Left translation by `b` permutes the
factors in the last product. Choose `r` with `m r ≡ 1 (mod p)`; taking the
`r`-th power undoes raising to `m` on the kernel. Thus if
`B(a) = (∏_z c(a,z))^r`, the product identity becomes
`c(a,b)B(ab) = J_a(B(b))B(a)`. This is the identity ensuring that
`t(a) = B(a)⁻¹s(a)` is multiplicative. The correction is kernel-valued,
so `t` is still a section. For each compatible automorphism pair, the
automorphism of `E` restricts to the kernel and transforms the factor
set according to the automorphism of `Q`. Reindexing the product by the
latter proves equivariance of `B` and then of `t`.

This is the derived group-theoretic step used in
[`EtaleVectorExtension`](EtaleVectorExtension.md). It implements the
degree-two factor-set instance of the averaging over the last argument in
Raynaud, SGA 3 XVII, Lemme 5.2.4 (printed p.347, PDF p.23 in
`sga3-expose-xvii-gille-polo-2008`;
[full citation](EtaleExtensionSplitStatement.md)), specialized to a
kernel killed by `p`. It does not prove general cohomology vanishing.
