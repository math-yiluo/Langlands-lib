# Equivariant cohomology through the Godement complex

Author: Worker 13. Built on Worker 61's published equivariant Godement complex
`Langlands.Sheaf.Equivariant.Godement.Complex`, Worker 13's section complexes
`Langlands.Cohomology.EquivariantSections` and the left-exactness instances in
`Langlands.Cohomology.EquivariantDerivedSections`.

## Degree zero of a cokernel complex

The first section works in any abelian category `A`. Let `T` be an
endofunctor of `A` and `η : 𝟭 A ⟶ T` a coaugmentation whose components are all
monomorphisms. The published cokernel construction
`Langlands.Cohomology.CokernelComplex` gives a complex with degree-zero term
`T M`. Its first differential is the cokernel projection of `η M` followed by
the coaugmentation of that cokernel.

`augmentationIsKernel` proves that the augmentation `η M : M ⟶ T M` is a kernel
of this first differential. The proof proceeds in three steps. Evaluation at
`M` preserves the functor-category cokernel, so the projection is a cokernel of
`η M`. In an abelian category a monomorphism is the kernel of its cokernel
(Mathlib's `Abelian.monoIsKernelOfCokernel`). Finally, composing with the monic
coaugmentation of the cokernel does not change the kernel (`isKernelCompMono`).
Exactness of `T` is not used.

Let `Φ : A ⥤ B` be an additive functor into an abelian category that preserves
finite limits. `mappedComplex T η Φ` applies `Φ` termwise to the cokernel
complex. Since `Φ` preserves the kernel above, `cyclesIso` identifies `Φ M`
with the degree-zero cycles of the mapped complex, compatibly with the
inclusion of cycles (`cyclesIso_hom_iCycles`) and naturally in `M`
(`cyclesIso_naturality`). For a cochain complex indexed by `ℕ`, degree-zero
cycles are degree-zero homology. Hence `homologyIso` and the natural
isomorphism `homologyZeroIso` identify degree-zero homology of the mapped
complex with `Φ`.

## Godement cohomology representations

Now let `R` be a commutative ring and let a group `G` act on a topological
space `X` by continuous translations, all in one universe `u`. Let `F` be an
equivariant module sheaf, an object of `TopologicalSheaf G X (ModuleCat R)`.
`globalComplex R G X` and `compactComplex R G X` send `F` to the cochain
complexes of representations obtained by applying the global-section and
compact-section representation functors termwise to the equivariant Godement
complex `Godement.complexFunctor R G X F`. Their homology functors are

- `globalCohomology R G X q`, with values in `Rep R G`;
- `compactCohomology R G X q`, with values in `Rep R G`.

Every value therefore carries an action of `G`, and every morphism of
equivariant sheaves induces an intertwining map. `forgetSupport` is the natural
map from compactly supported to global Godement cohomology induced by the
inclusion of compact sections.

The coaugmentation of the equivariant Godement complex is monic
(`Godement.mono_coaugmentation`). The section representation and the compact
section representation are additive and preserve finite limits by the
published modules above. The general result therefore gives the degree-zero
isomorphisms `globalCohomologyZeroIso` with `sectionRepresentation R G X` and
`compactCohomologyZeroIso` with `CompactSections.functor R G X`.
`compactCohomologyDiagram` applies `compactCohomology R G X q` to a diagram of
equivariant sheaves. An example is an inverse system of torsion coefficient
sheaves. It keeps every transition map and takes no limit.

## Smooth variant

Suppose in addition that `G` is a topological group. `smoothCompactComplex`
applies the published smooth compact-section functor to each Godement term,
giving a cochain complex in the category `SmoothRep R G` of smooth
representations. That functor takes the smooth vectors of the
compact-section representation, namely the compactly supported sections fixed
by some open subgroup. It does not assume that all compactly supported sections
are smooth. `smoothCompactCohomology R G X q` is the homology of this complex.
It is computed in `Rep R G` by the published
`EquivariantSections.smoothCategoryHomology` and bundled in `SmoothRep R G`
with its proved smoothness. `forgetSmooth` is the natural map from its
underlying representation to `compactCohomology R G X q`, induced by the
inclusion of smooth vectors.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.5, printed p.10, defines the Godement
resolution `C^•(F)` of an equivariant sheaf. Printed p.11 defines compactly
supported sections and `H^q_c(X(G), F)`. Harris, *Galois properties of
cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ. 39-2 (1999),
section 2, printed p.304, uses Berkovich's construction, "a smooth
G-equivariant version of the Godement flasque resolution". It embeds each
étale sheaf of smooth torsion `S(ẽ)`-modules on `U(ẽ)` functorially into a
sheaf of the same kind that is acyclic for compactly supported sections.
Iterating on cokernels gives the acyclic resolutions of Lemma 2.2. These
compute compactly supported cohomology together with the smooth action of the
stabilizer `S(ẽ)`. Worker 13 read these passages in the original. This module
follows the same recipe: it takes the homology of the sections of an
equivariant Godement complex. The setting is the ordinary-topological transport
site of the published equivariant sheaf category, not the analytic étale site.

The equivariant Godement complex used here lifts the ordinary Godement
construction from all points of `X`. It is not Berkovich's `ν_* ν^*` (see the
Markdown of `Langlands.Sheaf.Equivariant.Godement.Complex`). This module proves
no exactness of the augmented Godement complex beyond degree zero, and no
flabbiness, softness or acyclicity of its terms. It makes no comparison with
the derived functors `EquivariantDerivedSections.globalDerived` and
`compactDerived`, nor with ordinary sheaf cohomology of the underlying sheaf.
It does not prove that the full `G`-action on Godement cohomology is smooth or
discrete. It also does not cover invariant (Berkovich `X(G)`) cohomology,
spectral sequences, analytic étale sites, Shimura level towers, Hecke or
Galois actions. These remain separate obligations.

The underlying-complex comparison is proved separately: Worker 149's
`Langlands.Cohomology.equivariantGodementUnderlying`, in
[`EquivariantGodement/UnderlyingProof.lean`](EquivariantGodement/UnderlyingProof.lean),
proves exactly `Langlands.Cohomology.EquivariantGodementUnderlyingStatement.{u}`.
For a commutative ring `R`, a group `G` and a topological space `X` in the same
arbitrary universe `u`, with `MulAction G X` and `ContinuousConstSMul G X`,
it gives a natural isomorphism from the equivariant Godement complex after
forgetting equivariance to the ordinary Godement complex of the underlying
sheaf, compatibly with the augmentations in degree zero.
Worker 3's `Langlands.Cohomology.EquivariantGodementComputesSectionsStatement`,
in [`EquivariantGodement/Statement.lean`](EquivariantGodement/Statement.lean),
remains a separate target for computing the right-derived global and compact
section representations in every degree. The underlying-complex comparison
does not establish that target. This module imports neither comparison module;
its own constructive and degree-zero scope is unchanged.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules are present in Library commit
`354dfade2c499262492d6db74cb58fd887ffed5f`.
