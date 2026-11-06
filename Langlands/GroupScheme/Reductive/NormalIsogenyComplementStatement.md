# Semisimple normal complements over an arbitrary field

Authors: Worker 1371.

`SemisimpleNormalIsogenyComplementStatement.{u}` is a proposition definition,
with no proof supplied. For every field `k : Type u`, every semisimple group
scheme `G` over `Spec k`, and a prescribed closed normal inclusion `j : H → G`
with `H` smooth and connected, it asserts that `H` is semisimple and that there
are a semisimple group `K` and a closed normal inclusion `i : K → G` such that:

- The images of `H` and `K` commute on every test scheme.
- The product group `H ⊗ K` is semisimple.
- Its multiplication homomorphism to `G` is a central isogeny.

All fields and characteristics are included, without a perfectness, splitting,
or isotropy assumption. Normality refers to `SubgroupFunctor.range` on all test
schemes. The product is the cartesian monoidal product of actual group schemes.
The witness `hc` supplies the multiplication homomorphism already defined in
`Reductive.CommutingMultiplication`. `IsCentralIsogeny` means that this actual
homomorphism is finite, flat, surjective and locally of finite presentation,
and that its full scheme-theoretic kernel is central. Neither the kernel nor
the intersection of the factors is assumed smooth.

## Source and derivation

J. S. Milne, *Algebraic Groups*, corrected reprint 2022, registered source
`milne-2022-algebraic-groups`, Theorem 21.51 and Corollary 21.52, printed
pp.439–441 / PDF pp.450–452, supply the structural source. The theorem expresses
`G` as an almost-direct product of its finitely many almost-simple normal
subgroups. A prescribed smooth connected normal `H` is the product of the
factors it contains, and is centralized by the remaining factors. Take `K` to
be the product of those remaining factors. The theorem gives closed normal
subgroups, commutation, surjective multiplication and a finite kernel;
Corollary 21.52 gives semisimplicity of both normal subgroups. Finite products
of semisimple groups are semisimple.

The central-kernel and scheme-morphism formulation is derived from that
structural assertion. On every test scheme, an element `(h,k)` in the kernel
satisfies `j(h) = i(k)⁻¹`. Each image then commutes with its own factor because
the other factor centralizes it. Since both inclusions are monomorphisms,
`(h,k)` is central in `H × K`. A surjective homomorphism of algebraic groups
onto the smooth group `G` is flat; together with the finite kernel this gives
a finite flat surjection, and finite type over a field gives the required
local finite presentation. These are provenance arguments, not proofs supplied
by this module. The registered author errata for the 2022 reprint, snapshot
2026-11-04, were read; they do not correct Theorem 21.51 or Corollary 21.52.

This differs from `SemisimpleNormalComplementStatement`, which concerns an
algebraically closed field, allows a nonsmooth complement, and asks only for
flat surjective multiplication. Here the field is arbitrary, the complement
and product are semisimple, and multiplication is a central isogeny.

For a simply connected target, the defining property of simple connectedness
would make this multiplication an isomorphism. That consequence and rational
almost-simple generation remain separate proof obligations.
