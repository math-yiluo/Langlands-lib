# Factorization through a generic subgroup closure

Worker 671. This module extends `GenericSubgroupClosure` by the factorization
property for flat sources over a Dedekind domain.

Let `R` be a Dedekind domain with specified fraction field `K`, let `G` be an
arbitrary group scheme over `Spec R`, and let `j : H → G_K` be a closed subgroup
homomorphism. Given a flat group scheme `M` over `Spec R`, a homomorphism
`f : M → G`, and `h : M_K → H` with `h ≫ j = f_K`, the construction `factor`
is a homomorphism `M → closureGroup G j`. Its composite with the closure
inclusion is `f`, it is unique, and its generic fibre is `h` followed by the
canonical isomorphism from `H` to the generic fibre of the closure.
If the underlying map of `f` is a monomorphism, so is that of `factor`.
Moreover, `isClosedImmersion_iff_factor` proves that `f` is a closed immersion
if and only if its factor is.

The generic-fibre projection of a flat source is quasi-compact and
schematically dominant: it is the flat base change of the quasi-compact
schematically dominant map `Spec K → Spec R`. The generic factorization,
viewed over `Spec R`, gives a lift of the composite of this projection and
`f` through the closed inclusion. The imported
`exists_over_factor_of_schematic_precomp` then yields `factorOver`. Cancelling
the monomorphic inclusion proves that the factor preserves the group
operations. The same cancellation proves uniqueness and the generic
compatibility equation.
Monicity of the composite implies monicity of the factor. The
closed-immersion equivalence uses composition in one direction and
cancellation through the separated closure inclusion in the other.

This is a derived universal-property consequence of the imported closure
construction and schematic-dominance factorization lemma. It formalizes
the flat-source factorization used when replacing the ambient group by
the schematic closure in Conrad, *Reductive group schemes* (2014),
proof of Theorem 5.3.5, printed/PDF p.166, registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
The Dedekind-domain scope and general flat-source interface are internally
derived; they are not attributed as verbatim statements to Conrad.
The construction imposes no separatedness, finite type, affineness,
smoothness or reductivity on the flat source or the ambient group.
