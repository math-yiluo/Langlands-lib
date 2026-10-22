# ℓ-divisible systems

Author: Worker 61. Built on Mathlib's short complexes, exact functors and
categories of homological complexes, on Worker 13's abelian category of smooth
equivariant sheaves `Langlands.Sheaf.Equivariant.SmoothAbelian`, and on the
abelian category of smooth representations
`Langlands.Representation.Category.Abelian`.

Harris (1999, section 2, printed p.304, equation (2.1)) defines an `ℓ`-divisible
system as a family `T_m`, `m ≥ 1`, of étale sheaves of smooth
`ℤ/ℓ^m ℤ[S(ẽ)]`-modules. It comes with maps `i = i_{m',m} : T_{m'} → T_m` and
`j = j_{m,m−m'} : T_m → T_{m−m'}` for all `m > m' ≥ 1`. Each `T_m` is free over
`ℤ/ℓ^m ℤ`, `i` identifies `T_{m'}` with the `ℓ^{m'}`-torsion of `T_m`, and
`0 → T_{m'} → T_m → T_{m−m'} → 0` is exact. This module defines such systems in
an arbitrary abelian category `C`, for a natural number `ℓ`. All names below
are in the namespace `Langlands.Cohomology`.

## Multiplication by `ℓ ^ m`

`powSMul ℓ m X` is the endomorphism `(ℓ ^ m) • 𝟙 X` of an object `X` of a
preadditive category, a natural-number multiple of the identity.
`comp_powSMul` says that every morphism commutes with it.
`powSMul_comp_powSMul` says that `ℓ ^ a` followed by `ℓ ^ b` is `ℓ ^ (a + b)`,
and `powSMul_zero` that `ℓ ^ 0` is the identity. `map_powSMul` says that an
additive functor carries `powSMul ℓ m X` to `powSMul ℓ m (F.obj X)`.
`shortComplex_exact_congr` transports exactness of a short complex along
equalities of its two maps.

## The structure

`DivisibleSystem C ℓ`, for an abelian category `C` and `ℓ : ℕ`, has the
following fields. Write `T m` for `T.obj m`.

- `tower : ℕᵒᵖ ⥤ C`. Its object at `m` is `T.obj m`. For `h : m' ≤ m`, its
  map is `T.projection h : T m ⟶ T m'`. Harris's map `j_{m,m−m'}` is
  `T.projection (Nat.sub_le m m') : T m ⟶ T (m - m')`.
- `inclusion h : T m' ⟶ T m` for `h : m' < m`. This is Harris's map
  `i_{m',m}`.
- `powSMul_eq_zero m`: `ℓ ^ m` is zero on `T m`.
- `inclusion_comp h`: `i` followed by `j` is zero.
- `shortExact h`: the short complex `T m' ⟶ T m ⟶ T (m - m')` given by `i`
  and `j` is short exact. This is (2.1).
- `torsion_exact h`: the short complex `T m' ⟶ T m ⟶ T m` given by `i` and
  `ℓ ^ m'` is exact.
- `flat a b`: the short complex `T (a + b) ⟶ T (a + b) ⟶ T (a + b)` given by
  `ℓ ^ a` and `ℓ ^ b` is exact. This renders freeness over `ℤ/ℓ^{a+b}`; see
  item 4 of the provenance section.

## Consequences

- `isZero_obj_zero`: `T 0` is a zero object. For `m = 0`, `powSMul_eq_zero`
  says that `𝟙 (T 0) = 0`.
- `mono_inclusion` (an instance): every `i` is a monomorphism, by
  `shortExact`.
- `epi_projection`: every transition map `T m ⟶ T m'` with `m' ≤ m` is an
  epimorphism. For `m' = 0` the target is a zero object. Otherwise the map
  is `j` for the pair `m - m' < m`, which is an epimorphism by `shortExact`.
- `inclusionIsKernel`: `i : T m' ⟶ T m` is a kernel of `ℓ ^ m'` on `T m`.
  So `i` identifies `T m'` with the `ℓ ^ m'`-torsion of `T m`. This combines
  `torsion_exact` with `mono_inclusion`.
- `projectionIsCokernel`: `j : T m ⟶ T (m - m')` is a cokernel of `i`.

## Morphisms

A morphism `DivisibleSystem.Hom T T'` is a natural transformation
`tower : T.tower ⟶ T'.tower` whose components commute with the maps `i`
(field `comm`). These are the morphisms of the category instance on
`DivisibleSystem C ℓ`. Identities and composition are those of natural
transformations (`id_tower`, `comp_tower`). `hom_ext` says that a morphism is
determined by its natural transformation. The functor
`forget C ℓ : DivisibleSystem C ℓ ⥤ (ℕᵒᵖ ⥤ C)` takes the underlying tower and
is faithful.

## Exact functors

Let `F : C ⥤ D` be an additive functor into an abelian category `D` that
preserves finite limits and finite colimits. `T.map F` is the system with
tower `T.tower ⋙ F` and maps `F.map (T.inclusion h)` (`map_tower`,
`map_inclusion`). The fields carry over because `F` preserves short exact
sequences and exact short complexes and commutes with `powSMul`
(`map_powSMul`). `mapFunctor C ℓ F : DivisibleSystem C ℓ ⥤ DivisibleSystem D ℓ`
is this construction as a functor. For two such functors `F` and `G` and a
natural transformation `α : F ⟶ G`, `T.mapNatTrans α : T.map F ⟶ T.map G` is
the morphism whose components are the components of `α` at the objects `T m`.

## Complexes

Let `T` be an `ℓ`-divisible system in the category `HomologicalComplex C c` of
complexes. Then `T.degree n` is the `ℓ`-divisible system of its degree-`n`
terms. It is the image of `T` under the evaluation functor
`HomologicalComplex.eval C c n`.

## Smooth sheaves and smooth representations

`SmoothSheafDivisibleSystem R G X ℓ` is
`DivisibleSystem (Sheaf.Equivariant.SmoothTopologicalSheaf R G X) ℓ`. As for
the published instance `smoothTopologicalSheaf_abelian`, `R`, `G` and `X` lie
in one universe, `G` is a topological group acting on `X` by continuous
translations, and `HasStableNeighbourhoods G X` holds.
`SmoothRepComplexDivisibleSystem R G ℓ` is
`DivisibleSystem (CochainComplex (SmoothRep R G) ℤ) ℓ`, using the published
instance `SmoothRep.abelian`. It has independent universe parameters for the
ring, the group and the representation spaces.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2. Worker 61 read printed
pp.304–306 in the scanned original. Printed p.304 reads: "By an ℓ-divisible
system of S(ẽ)-modules over U(ẽ) we mean a collection {T_m} of étale sheaves
in smooth ℤ/ℓ^mℤ[S(ẽ)]-modules over U(ẽ), m ≥ 1, with morphisms
i = i_{m',m} : T_{m'} → T_m and j = j_{m,m−m'} : T_m → T_{m−m'}, for all
m > m' ≥ 1 such that T_m is free over ℤ/ℓ^mℤ, i identifies T_{m'} with the
p^{m'}-torsion in T_m, and (2.1) 0 → T_{m'} → T_m → T_{m−m'} → 0 is exact."

Harris uses these systems in Fact 4 on p.304. There the Godement construction
`T ↦ F(T)` carries a system to a system, with the maps `F(i)` and `F(j)`. He
also uses them in Lemmas 2.2 and 2.2 bis (resolutions whose terms form
systems). On p.305 he uses systems of complexes "in the obvious sense", and on
p.306 the systems of complexes `C_m^•` of Lemma 2.8.

The Lean reads the printed text as follows.

1. Torsion. The printed "p^{m'}-torsion" is read as `ℓ^{m'}`-torsion. Here `p`
   is the residue characteristic, prime to `ℓ` (p.305: "Since p is prime to
   ℓ"). A `ℤ/ℓ^m`-module has no nonzero `p`-power torsion. So the printed
   condition would make every `T_{m'}` zero. If `T_m` is free of rank `r`, its
   `ℓ^{m'}`-torsion is `ℓ^{m−m'} T_m ≅ (ℤ/ℓ^{m'})^r`, which has the shape of
   `T_{m'}`. The fields are `torsion_exact` and, as a consequence,
   `inclusionIsKernel`.
2. Transitivity of `j`. Harris states no composition law for the maps `j`.
   Lemma 2.8 (p.306) takes the inverse limit over `m` of the complexes
   `C_m^•(U(ẽ)_F̄)` along the maps `j`. This presupposes that
   `j_{m',m''} ∘ j_{m,m'} = j_{m,m''}` for `m > m' > m''`. Likewise, the proof
   of Lemma 2.2 bis (p.305) checks surjectivity only for the projections
   from index `m` to `m − 1`. The Lean therefore makes the objects and the maps
   `j` a functor `ℕᵒᵖ ⥤ C`, with identity maps for `m' = m`. Nothing is
   imposed on composites of the maps `i`, and nothing relates `i` and `j`
   beyond (2.1); the source states no such condition.
3. Index 0. The Lean indexes by all of `ℕ`. Since `ℓ ^ 0 = 1`,
   `powSMul_eq_zero 0` forces `T 0` to be a zero object. The conditions with
   `m' = 0`, `a = 0` or `b = 0` then follow from the others. Conversely,
   Harris's data, with transitive `j`, extend by a zero object at index 0.
   The zero object does not change the inverse limit of the tower. These
   remarks are not formalized.
4. Freeness. "T_m is free over ℤ/ℓ^mℤ" is rendered by the field `flat`: on
   `T (a + b)`, the kernel of `ℓ ^ b` is the image of `ℓ ^ a`. For a
   `ℤ/ℓ^m`-module `M` with `ℓ` prime, this condition for all `a + b = m` is
   equivalent to freeness. The argument is elementary and not formalized.
   On `ℤ/ℓ^m` both sides are `ℓ^a ℤ/ℓ^m`, and the condition passes to direct
   sums, so free modules satisfy it. Conversely, let `B ⊆ M` lift a basis of
   `M/ℓM` over `𝔽_ℓ`. Then `M = span(B) + ℓM`, so by iteration
   `M = span(B) + ℓ^m M = span(B)`. Suppose that a relation `Σ c_β β = 0` has
   some `c_β ≠ 0`. Write `c_β = ℓ^a d_β` for all `β`, with `a < m` and some
   `d_β` prime to `ℓ`. Then `x = Σ d_β β` is killed by `ℓ^a`, so the
   condition for the pair `(m − a, a)` gives `x ∈ ℓ^{m−a} M ⊆ ℓM`. This
   contradicts the independence of the images of `B` in `M/ℓM`. The condition is the ideal criterion for
   flatness over `ℤ/ℓ^m`, whose ideals are the `ℓ^a ℤ/ℓ^m`. In a category of
   sheaves, `flat` is exactness of sheaves; it does not say that modules of
   sections are free.
5. Coefficients. The structure accepts any natural number `ℓ`. Harris's `ℓ`
   is a prime different from `p`, and item 4 uses that `ℓ` is prime. Each
   `T m` is an object of the one abelian category `C` killed by `ℓ ^ m`,
   rather than a module over `ℤ/ℓ^m`. With `R = ℤ` in
   `SmoothSheafDivisibleSystem` (so `G` and `X` lie in `Type`), a sheaf killed
   by `ℓ ^ m` is the same as a sheaf of `ℤ/ℓ^m`-modules.
6. Sheaves. `SmoothSheafDivisibleSystem` uses Worker 13's published smooth
   equivariant sheaves on a topological space. These transcribe Berkovich's
   discrete sheaves, which Harris uses (p.304), to the ordinary-topological
   transport site. They replace étale sheaves on Berkovich's analytic étale
   site. A group `G` acting on a space `X` replaces `S(ẽ)` acting on `U(ẽ)`,
   and `R`-modules replace abelian groups.
7. Complexes. On p.305, after (2.3), Harris uses `ℓ`-divisible systems of
   complexes "in the obvious sense". There the complexes
   `G_m^•(U(ẽ)_F̄)^H` from Lemma 2.2 bis form such a system of finite-length
   complexes of `ℤ/ℓ^m[S(ẽ)/H]`-modules. He then replaces each term by its
   canonical free resolution (2.4)–(2.5). That resolution is built by
   iterating a surjection and extends indefinitely to the left. On p.306 he
   takes the associated simple complexes `C_{m,H}^•` of free
   `ℤ/ℓ^m[S(ẽ)/H]`-modules. Their direct limit over `H` gives the system
   `C_m^•` of complexes of projective `ℤ/ℓ^m[S(ẽ)]`-modules. Finite length
   belongs to the `G_m^•`. The complexes `C_m^•` need not have finite length.
   Here systems of complexes are `ℓ`-divisible systems in an abelian category
   of complexes, whose conditions hold in each degree (`degree`). Neither
   finite length nor projectivity is part of the notion, and
   `SmoothRepComplexDivisibleSystem` imposes neither.

Morphisms, `map`, `mapFunctor`, `mapNatTrans` and `degree` are derived. Harris
uses morphisms of systems without naming them. His canonical embeddings
`b_m : T_m → F(T_m)` (p.304) commute with `i` and `j` by functoriality, and
their cokernels again form a system. `map` is the generic construction behind
Fact 4: an exact additive functor carries systems to systems. It is not
applied here to a Godement functor. Exactness of Harris's `T ↦ F(T)` is his
Fact 3, which this module does not prove.

## Scope

The module does not construct the cokernel system of a morphism (the
snake-lemma argument of p.304), Harris's resolutions (Lemmas 2.2 and
2.2 bis), inverse limits of systems, or the Mittag-Leffler argument of
Lemma 2.8. The published statements in
`Langlands.Cohomology.InverseLimit.Statement` concern towers
`ℕᵒᵖ ⥤ CochainComplex (ModuleCat R) ℤ`, and reindex Harris's exponent by adding
one. A system in that category of complexes has such a tower, with a zero
object at index 0 instead of the reindexing. No result relating them is
proved here.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are the modules named above, pinned to Lean 4.34.0 and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`.
