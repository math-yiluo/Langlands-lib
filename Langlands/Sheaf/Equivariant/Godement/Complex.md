# The equivariant Godement cokernel complex

Author: Worker 61. Combines the companion degree-zero construction
`Langlands.Sheaf.Equivariant.Godement.Zero`, the abelian structure in
`Langlands.Sheaf.Equivariant.Abelian`, and Worker 13's published functorial
cokernel construction `Langlands.Cohomology.CokernelComplex`.

Let `R` be a commutative ring, and let a group `G` act on a topological space
`X` by continuous individual operators, all in one universe `u`. The
degree-zero functor `zeroFunctor R G X` sends an equivariant module sheaf `F`
to the equivariant sheaf of arbitrary families of stalk elements. Its
transport maps are the stalk transport maps, and `coaugmentation R G X` sends a
section to its family of germs.

The instance `zeroFunctor_additive` proves that this functor is additive:
on each open, the sum of two morphisms acts on a family of stalk elements
through the sum of the induced stalk maps. The supporting lemma
`stalkFunctor_map_add` derives this from the additivity of forgetting the
group labels and Mathlib's additivity instance for the ordinary stalk
functor. Exactness of `zeroFunctor` is not proved here.

`complexFunctor R G X` applies the published cokernel construction to this
coaugmented endofunctor of the abelian category
`TopologicalSheaf G X (ModuleCat.{u} R)`. Write `Q⁰ = F` and let `Q^{n+1}`
be the cokernel of the coaugmentation `Qⁿ → C⁰(Qⁿ)`, where `C⁰ = zeroFunctor`.
The degree-`n` term is `C⁰(Qⁿ)`, so degree `0` is `zeroSheaf F`
(`complex_X_zero`). The differential `dⁿ` is the cokernel projection
`C⁰(Qⁿ) → Q^{n+1}` followed by the coaugmentation of `Q^{n+1}`. Each
cokernel projection is an epimorphism, so `Q^{n+1}` is canonically the
cokernel of `d^{n-1}`, with `d^{-1}` the coaugmentation of `F`. The
construction is a functor from equivariant module sheaves to nonnegative
cochain complexes in that category. Its maps of complexes are induced by the
functoriality of `zeroFunctor` and of cokernels. `complex F` is the complex of
one sheaf.

`augmentation R G X F` is the map `F → C⁰(F)`, which is the coaugmentation
(`augmentation_eq`). `augmentation_d` proves that it composes to zero with the
first differential, and the accompanying instance proves it is a monomorphism
(using the proved `mono_coaugmentation`). The cokernels are those of the
transported abelian structure, namely sheafified sectionwise cokernels for the
transport topology.

This is the recipe of Berkovich, *Etale equivariant sheaves on p-adic analytic
spaces* (unfinished 1995–1996 manuscript), section 1.5, printed page 10, items
(a)–(b): `C⁰(F)` with the adjunction morphism `d^{-1}`, and
`C^{m+1}(F) = C⁰(Coker d^{m-1})`, matched above up to the canonical
identification of cokernels. Here it is carried out for the
ordinary-topological transport site, with `C⁰` the equivariant sheaf of stalk
families rather than Berkovich's `ν_* ν^*` on the analytic equivariant étale
site. In particular, for a one-point space the construction keeps the given
group module and has no coinduction factors. The properties (i)–(iii) listed by
Berkovich on page 10 (flabbiness, exactness of `F ↦ C^m(F)`, split stalk
resolutions), as well as softness, acyclicity and exactness of the augmented
complex, are not asserted here. They remain separate theorem obligations. Harris,
*Galois properties of cohomological automorphic forms on GL(n)* (1999),
section 2, printed page 304, describes Berkovich's construction as a smooth
equivariant version of the Godement resolution. Smoothness is not imposed
here.

Sources: registered folder
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`
(digest `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member PDF SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`) and
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`
(SHA-256 `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`).
Worker 61 read the cited passages. Lean 4.34.0, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
