# Derived compact sections of smooth equivariant sheaves and Godement compact cohomology

Author: Worker 3.

This module defines two propositions and their conjunction
`Langlands.Cohomology.SmoothCompactComparison.SmoothCompactComparisonStatements`.
The setting is a topological group acting on a locally compact Hausdorff
space, and smooth equivariant sheaves of modules on it. Two compactly
supported cohomologies are attached to such a sheaf. The first is Worker 13's
right derived functors of compact sections, computed in the abelian category
of smooth equivariant sheaves. The second is Worker 13's compactly supported
Godement cohomology of the underlying equivariant sheaf. The first proposition
says that injective smooth sheaves have no compactly supported Godement
cohomology in positive degrees. The second says that the two cohomologies are
naturally isomorphic as representations in every degree, by an isomorphism
that is the canonical identification in degree zero. The second proposition
is the ordinary-topology analogue of the canonical isomorphisms
`H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` in Berkovich's Corollary 1.5.2(i). The first
is an internal step derived here (see Provenance). Both are theorem-statement
definitions, not proofs. Acyclicity and the isomorphisms are conclusions; they
are not supplied as data or as hypotheses.

## Objects

Both propositions quantify over a commutative ring `R`, a group `G` and a
topological space `X`, all in one universe `u`. `G` is a topological group
(`IsTopologicalGroup`). It acts on `X` by `MulAction`, and each element acts
continuously (`ContinuousConstSMul`), hence by a homeomorphism. `X` is
Hausdorff (`T2Space`) and locally compact (`LocallyCompactSpace`). The
hypothesis `Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G X`, from
Worker 13's `Langlands.Sheaf.Equivariant.SmoothPart`, says that every open
neighbourhood of every point contains an open neighbourhood of that point that
is stabilized by some open subgroup. Worker 13 publishes instances for
discrete `G`, and for nonarchimedean `G` acting continuously
(`NonarchimedeanGroup G`, `ContinuousSMul G X`). Worker 13's abelian structure
on smooth sheaves and the derived functors below assume `IsTopologicalGroup`,
`ContinuousConstSMul` and `HasStableNeighbourhoods`, but neither separation
nor local compactness. Those two are added here because the comparison uses
them.

The objects are the published ones:

- `Langlands.Sheaf.Equivariant.TopologicalSheaf G X (ModuleCat R)` is Worker
  13's category of equivariant sheaves of `R`-modules on the ordinary open-set
  transport site.
- `Langlands.Sheaf.Equivariant.SmoothTopologicalSheaf R G X` is Worker 13's
  full subcategory of smooth sheaves (`IsSmoothSheaf`). A sheaf is smooth when,
  for every open `U`, every section `s` over `U` and every point `x` of `U`,
  there are an open `V` with `x ∈ V ⊆ U` and an open subgroup `H` with
  `H • V ⊆ V` such that every element of `H` fixes the restriction of `s` to
  `V`. `Langlands.Sheaf.Equivariant.smoothInclusion R G X` is the inclusion
  functor. Worker 13's `Langlands.Sheaf.Equivariant.SmoothAbelian` makes the
  subcategory abelian, with the kernels and cokernels of the ambient
  category, and proves that it has enough injectives. `Injective I` below is
  Mathlib's categorical notion in this subcategory.
- `Langlands.Sheaf.Equivariant.smoothSheafCompactSections R G X`, from Worker
  13's `Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`, sends a
  smooth sheaf to its compactly supported global sections, as an object of
  the published category `Langlands.SmoothRep R G` of smooth representations.
  `smoothSheafCompactSectionsToRepIso R G X` identifies its composite with
  `Langlands.SmoothRep.toRep`, the inclusion of smooth representations into
  Mathlib's `Rep R G`, with `smoothInclusion R G X` followed by
  `Langlands.Sheaf.Equivariant.CompactSections.functor R G X`. The support of
  a global section is the set of points where its germ is nonzero.
- `Langlands.Cohomology.SmoothSheafCohomology.compactDerived R G X q` is
  Worker 13's `q`-th right derived functor of `smoothSheafCompactSections`,
  computed by Mathlib's `Functor.rightDerived` with injective resolutions in
  the smooth category. Its values are smooth representations.
  `compactDerivedZeroIso R G X` is Mathlib's identification of the degree-zero
  derived functor with the functor itself.
- `Langlands.Cohomology.EquivariantGodementCohomology.compactCohomology R G X q`
  is Worker 13's `q`-th cohomology of the compactly supported global sections
  of Worker 61's equivariant Godement complex
  (`Langlands.Sheaf.Equivariant.Godement.complexFunctor`), as an object of
  `Rep R G`. `compactCohomologyZeroIso R G X` identifies degree zero with
  `CompactSections.functor R G X` through the Godement coaugmentation. Worker
  61's published `underlyingComplexIso`, in
  `Langlands.Sheaf.Equivariant.Godement.Underlying`, shows that after
  forgetting the action this complex is the ordinary Godement complex over
  the points of `X`. This module does not import that comparison.

## The two propositions

| Declaration | Asserted conclusion |
| --- | --- |
| `SmoothInjectiveCompactAcyclicStatement R G X` | For every injective object `I` of `SmoothTopologicalSheaf R G X` and every `q : ℕ`, `(compactCohomology R G X (q + 1)).obj ((smoothInclusion R G X).obj I)` is a zero object of `Rep R G`. |
| `SmoothCompactDerivedComparisonStatement R G X` | There is a family `e q : compactDerived R G X q ⋙ SmoothRep.toRep ≅ smoothInclusion R G X ⋙ compactCohomology R G X q` of natural isomorphisms, for all `q : ℕ`, such that `(e 0).hom` is the composite of `whiskerRight (compactDerivedZeroIso R G X).hom SmoothRep.toRep`, `(smoothSheafCompactSectionsToRepIso R G X).hom` and `whiskerLeft (smoothInclusion R G X) (compactCohomologyZeroIso R G X).inv`. |

`SmoothCompactComparisonStatements R G X` is the conjunction of the two, in
this order. All three definitions carry the same hypotheses, listed as
explicit binders, so they all appear in their types.

What the second proposition does and does not fix:

- Each `e q` is an isomorphism of functors, so it is natural in the smooth
  sheaf and intertwines the actions of `G`.
- The degree-zero clause says which identification is meant in degree zero.
  It constrains only `e 0`, and it can always be met by taking `e 0` to be
  the stated composite, which is an isomorphism. It therefore adds no content
  in positive degrees.
- The isomorphisms in positive degrees are only asserted to exist. Their
  compatibility with connecting morphisms is not stated. Mathlib's
  `Functor.rightDerived`, in `Mathlib/CategoryTheory/Abelian/RightDerived.lean`,
  provides no connecting morphisms, and none are published for
  `compactCohomology`. So the comparison cannot yet be stated as an
  isomorphism of cohomological functors, which is how Berkovich's canonical
  isomorphisms are characterized.
- The first proposition asserts only acyclicity: injective smooth sheaves
  have no compactly supported Godement cohomology in positive degrees. It
  asserts no map between resolutions. Step 2 of the truth argument derives
  it from the `c`-softness of injective smooth sheaves, and step 3 uses that
  softness to compare the two cohomologies through a zigzag
  `ι I^• ← ι D^•(F) → C^•(ι F)` of resolutions of `ι F`. Here `I^•` is a
  smooth injective resolution, `D^•(F)` an auxiliary resolution by smooth
  parts of Godement sheaves, and `C^•(ι F)` the Godement resolution. Both
  arrows induce isomorphisms on compactly supported cohomology. A direct
  chain map `ι I^• ⟶ C^•(ι F)` over the identity of `ι F` need not exist.
  For example, take `R = ℤ`, `G` trivial, `X` a point and `F = ℤ`. Then
  `ℚ ⟶ ℚ/ℤ` is an injective resolution and the Godement resolution is `ℤ`
  in degree zero. A map over the identity would restrict to the identity on
  `ℤ ⊆ ℚ`, but every homomorphism `ℚ ⟶ ℤ` is zero.

A consequence: since `compactDerived` takes values in smooth
representations, the second proposition implies that
`compactCohomology R G X q` of every smooth sheaf is a smooth representation,
under the hypotheses above. That smoothness assertion is stated separately,
without `HasStableNeighbourhoods`, in Worker 3's
`Langlands.Cohomology.SmoothCompactCohomology.Statement`, a published
module that this module does not import.

## Why the statements are expected to hold

This argument is derived here. Berkovich's proof (see the source
correspondence) has the same shape but works on the étale site of an analytic
space.

The acyclicity facts are from Grothendieck's Tohoku paper, §3.3, printed
pp.158-160, for sheaves of abelian groups. Forgetting the `R`-module structure
and the action commutes with the constructions below.

- p.158, Lemma 3.3.1 and its Corollary: if a class `M` of objects satisfies
  conditions (i)-(iii) of the lemma for a left exact functor `F`, then the
  objects of `M` are `F`-acyclic, and `R^p F(A)` can be computed with any
  resolution of `A` by objects of `M`.
- p.159: a sheaf `F` is `Φ`-soft (`Φ-mou`) if every section of `F` over a
  member of `Φ` is induced by a section in `Γ_Φ(F)`. `Φ` is paracompactifying
  if every member is paracompact and has a neighbourhood in `Φ`. A section
  over a closed set with a paracompact neighbourhood extends to an open
  neighbourhood of that set.
- p.159, Proposition 3.3.2 and its Corollary: if `Φ` is paracompactifying,
  the `Φ`-soft sheaves satisfy the conditions of Lemma 3.3.1 for `Γ_Φ`, and
  `H^p_Φ(X, F) = 0` for `p > 0` when `F` is `Φ`-soft.
- p.160: the canonical resolution `C^•(F)`, Godement's, has `C⁰(F)` equal to
  the product of the stalks of `F` and `Cⁿ(F) = C⁰(Cⁿ⁻¹(F)/Im Cⁿ⁻²(F))`. Its
  terms are flabby, and `H^n_Φ(X, F) = H^n(Γ_Φ C^•(F))` for every `Φ`.

Let `c` be the family of compact subsets of `X`. On a locally compact
Hausdorff space it is paracompactifying: compact sets are closed, finite
unions and closed subsets of compact sets are compact, compact Hausdorff
spaces are paracompact, and every compact set has a compact neighbourhood. So
`Γ_c = Γ_Φ` for `Φ = c`, and "`c`-soft" below means `Φ`-soft for this `Φ`.

Step 1: smooth parts of Godement sheaves are `c`-soft. For an equivariant
sheaf `M`, let `D⁰(M)` be Worker 13's `smoothCoreflector R` applied to Worker
61's degree-zero Godement sheaf `Godement.zeroFunctor R G X` of `M`. It is the
subsheaf of the product of the stalks of `M` consisting of the families that
are locally fixed in the sense of `IsSmoothSheaf`, and it is smooth. Let `t`
be a section of `D⁰(M)` over a compact set `K`. Since `K` has a compact
neighbourhood, `t` extends to a section, still written `t`, over an open
neighbourhood `W` of `K`. Since `X` is locally compact and Hausdorff, there
is an open `W₀` with `K ⊆ W₀` whose closure is compact and contained in `W`.
By `HasStableNeighbourhoods`, every point of `K` has an open neighbourhood
contained in `W₀` and stabilized by an open subgroup. By compactness, `K` is
covered by finitely many of them, `V_1, …, V_n`, stabilized by open subgroups
`H_1, …, H_n`. Then `H = ⋂ H_i` is an open subgroup that stabilizes
`V = ⋃ V_i`. The closure of `V` lies in the closure of `W₀`, so it is compact
and contained in `W`. Extend the family `t|_V` by zero outside `V`, and check
that the result is locally fixed at every point `y` of `X`:

- If `y ∈ V`, the extended family agrees with `t` on `V`, and `t` is locally
  fixed at `y` because it is a section of `D⁰(M)`.
- If `y` is outside the closure of `V`, the extended family is zero on the
  open complement of that closure. By `HasStableNeighbourhoods`, `y` has an
  open neighbourhood inside this complement stabilized by an open subgroup,
  which fixes the zero family.
- Otherwise `y` lies in the closure of `V` but not in `V`. Then `y ∈ W`,
  because the closure of `V` is contained in `W`. Since `t` is a section of
  `D⁰(M)` over `W`, there are an open `V'` with `y ∈ V' ⊆ W` and an open
  subgroup `H'` stabilizing `V'` and fixing `t` on `V'`. Every `h ∈ H' ∩ H`
  stabilizes `V' ∩ V` and `V' ∖ V`. On the first the extended family is `t`,
  which `h` fixes; on the second it is zero. So `h` fixes the extended family
  on `V'`.

Hence the extended family is a global section of `D⁰(M)`. Its support lies in
the closure of `V`, which is compact, and it induces `t` on `K`.

Step 2: the first proposition. Let `I` be injective in the smooth category.
Worker 61's coaugmentation of `ι I`, where `ι = smoothInclusion R G X`, is a
monomorphism into the degree-zero Godement sheaf. Since `I` is smooth, Worker
13's `smoothAdjunction` factors it through a morphism `I ⟶ D⁰(ι I)` of smooth
sheaves, which is again a monomorphism. Since `I` is injective, this morphism
splits, so `ι I` is a direct summand of `D⁰(ι I)`. A direct summand of a
`c`-soft sheaf is `c`-soft: extend a section of the summand over `K` as a
section of the big sheaf and project it back. By step 1, `ι I` is `c`-soft.
By Proposition 3.3.2 and its Corollary, `H^p_c(X, ι I) = 0` for `p > 0`. By
p.160 and Worker 61's `underlyingComplexIso`, the module underlying
`compactCohomology R G X p` of `ι I` is `H^p_c(X, ι I)`. A representation with
zero underlying module is a zero object of `Rep R G`.

Step 3: the second proposition. Let `F` be a smooth sheaf and let `I^•` be
the injective resolution in the smooth category that Mathlib's
`Functor.rightDerived` uses. Since `ι` preserves kernels and cokernels, `ι I^•`
is a resolution of `ι F`, and by step 2 its terms are `c`-soft. Build a
resolution `D^•(F)` in the smooth category: `D⁰(F) = D⁰(ι F)`, and
`Dⁿ⁺¹(F) = D⁰` of the cokernel of `Dⁿ⁻¹(F) ⟶ Dⁿ(F)`. As in step 2, a smooth
sheaf embeds in its `D⁰`, and cokernels of smooth sheaves are smooth, so
`D^•(F)` is a resolution of `F`. By step 1 its terms are `c`-soft. There are
two morphisms of resolutions over the identity of `F`:

- `α : D^•(F) ⟶ I^•` in the smooth category, which exists because the terms of
  `I^•` are injective there; any two such morphisms are chain homotopic;
- `β : ι D^•(F) ⟶ C^•(ι F)`, induced by the inclusions of `D⁰` into the
  degree-zero Godement sheaf; it is natural in `F`.

Both are morphisms of equivariant sheaves. Together they form the zigzag
`ι I^• ← ι D^•(F) → C^•(ι F)`, whose left arrow is `ι α`. No morphism between
`ι I^•` and `C^•(ι F)` themselves is used. All three complexes are
resolutions of `ι F` by `Γ_c`-acyclic sheaves, by step 2, step 1 and p.160. By
the Corollary to Lemma 3.3.1, applied with Proposition 3.3.2, each computes
`H^p_c(X, ι F)`. The identifications are made by mapping each resolution to an
ordinary injective resolution of `ι F` over the identity, so they are
compatible with morphisms of resolutions over the identity. So `Γ_c(ι α)` and
`Γ_c(β)` induce isomorphisms on cohomology that intertwine the actions of
`G`. The comparison is the inverse of the first followed by the second. The
cohomology of `Γ_c(I^•)` is `compactDerived R G X q` of `F` (Worker 13's `compactDerivedIso`). Smooth
representations are closed under subrepresentations and quotients, so
`SmoothRep.toRep` does not change this cohomology. The cohomology of
`Γ_c(C^•(ι F))` is `compactCohomology R G X q` of `ι F`. The resulting
isomorphism is natural in `F`: `β` is natural, and `α` is natural up to chain
homotopy because two lifts of a morphism into an injective resolution are
homotopic. In degree zero all identifications go through the augmentations,
so the isomorphism is the stated composite.

## Provenance

`SmoothCompactDerivedComparisonStatement` transcribes Berkovich's canonical
isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` (Corollary 1.5.2(i)) to the
ordinary open-set site of a locally compact Hausdorff space, as follows:

- Berkovich's étale abelian sheaves on `X(G)` correspond, by his Theorem
  1.4.2, to `G`-sheaves `b^*F` on `X`. Here they are replaced by Worker 13's
  smooth equivariant sheaves; `IsSmoothSheaf` transcribes the
  characterization by open stabilizers of restricted local sections that
  follows his Definition 1.4.1.
- `H^q_c(X{G}, F)` is the derived functor of
  `Γ_{c,X{G}} = lim_N Γ_{c,X(N)}`, the compactly supported sections fixed by
  some open subgroup `N`. For a smooth sheaf every compactly supported
  section is fixed by an open subgroup (Worker 13's
  `CompactSections.isSmooth_representation_of_isSmoothSheaf`), so this
  functor becomes `smoothSheafCompactSections`, and its derived functors
  `compactDerived`.
- `H^q_c(X, b^*F)` becomes `compactCohomology` of the underlying equivariant
  sheaf.
- "Canonical" is rendered only by naturality and the degree-zero clause, for
  the reason given above.

`SmoothInjectiveCompactAcyclicStatement` has no counterpart in Berkovich. It
is the acyclicity step that the comparison needs when derived functors are
computed with injective resolutions, as in Mathlib. Berkovich's proof uses his
Godement resolution of `F` on `X(G)` and Proposition 1.5.1 instead.
`HasStableNeighbourhoods` stands in for the Key Lemma of Berkovich §1.4, which
supplies neighbourhoods stabilized by open subgroups on analytic spaces.

## Original-source correspondence

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript. The printed page numbers equal the PDF page numbers.

- §1.5, p.10: "We recall the construction of the Godement resolution from
  [SGA4], Exp. XVII, §4.2, adopted to the étale site of `X(G)`":
  `C⁰(F) = ν_*ν^*(F)` and `C^{m+1}(F) = C⁰(Coker d^{m-1})`, with flabby terms.
  `D^•(F)` in step 3 plays the role of this resolution. It is built by the
  same recursion, with `D⁰` the smooth part of the product of the stalks. No
  identification of the two constructions is claimed.
- Proposition 1.5.1, p.10, with its proof on pp.10-11: "For any
  `F ∈ X(G)~_ét` and `m ≥ 0`, `b^*(C^m(F))` is a soft sheaf on `X_ét`."
  Here `b : X → X(G)` is the morphism of Theorem 1.4.2. The proof of (2')
  extends a section over a compact set to a neighbourhood, shrinks it and
  replaces `G` by a
  small open subgroup so that the neighbourhood is `G`-invariant, and then
  extends from the discrete index set. Step 1 is the counterpart.
- p.11: the support of a section, `Γ_{c,X(G)}`, and
  `Γ_{c,X{G}}(F) := lim_N Γ_{c,X(N)}(F)` over open subgroups `N`. The values
  of the derived functors of `Γ_{c,X{G}}` are denoted `H^q_c(X{G}, F)`.
- Corollary 1.5.2(i), pp.11-12: "For any étale abelian sheaf `F` on `X(G)`
  there are canonical isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`". This is
  `SmoothCompactDerivedComparisonStatement`, with the limitations above.
- Proof of Corollary 1.5.2, p.12: "The case `q = 0` in (i) ... follows from
  the fact that every element of `H^0_c(X, b^*F)` is fixed by an open subgroup
  of `G` ..., and therefore the general case follows from Proposition 1.5.1."

| Source | Original statement | Lean component |
| --- | --- | --- |
| Berkovich Cor. 1.5.2(i), pp.11-12 | Canonical isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`, `q ≥ 0`. | `SmoothCompactDerivedComparisonStatement`; natural isomorphisms, canonical in degree zero |
| Derived here; Tohoku Prop. 3.3.2, p.159 | (Injective smooth sheaves are `c`-soft, hence `Γ_c`-acyclic.) | `SmoothInjectiveCompactAcyclicStatement` |

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), section 2, printed p.305, uses the
discreteness consequence of Corollary 1.5.2(i): `H^q_c(U(ẽ)_{F̄}, ℤ/ℓ^m ℤ)`
"is a finite smooth `S(ẽ)`-module". It is cited here only for this context.

## Scope

- The site is the ordinary open-set site of a topological space, not
  Berkovich's étale or quasi-étale site of an analytic space. Analytic
  spaces, `X(G)`, `X{G}` and the base change to `F̄` in Harris are not
  formalized here.
- Compatibility with connecting morphisms is not stated (see above).
- Softness of `D⁰`, Berkovich's Proposition 1.5.1, appears only in the truth
  argument. No `c`-softness predicate for equivariant sheaves is published.
- The spectral sequence of Corollary 1.5.2(i), Corollary 1.5.2(ii) on ringed
  spaces, and the relative versions of Corollary 1.5.3 are not stated.
- `compactCohomology` is not replaced by Worker 13's `smoothCompactCohomology`,
  the cohomology of the smooth parts of compactly supported Godement
  sections. The two differ in degree one. Take `R = ℚ`, `G = X = ℤ_p` acting
  by translation, and the constant sheaf `ℚ`, which is smooth. Then
  `H^1_c(X, ℚ) = 0`, since `X` is compact and totally disconnected. The
  degree-zero Godement term has global sections `Map(ℤ_p, ℚ)`, whose smooth
  part is the locally constant functions. A nonzero additive map
  `f : ℤ_p → ℚ` exists because `ℤ_p ⊗ ℚ = ℚ_p` is a nonzero `ℚ`-vector space.
  Its translates differ from `f` by constants, so its class in the smooth
  part of `Map(ℤ_p, ℚ)/C^∞(ℤ_p, ℚ)` is invariant. The class is nonzero,
  because a locally constant additive map to a torsion-free group is zero. So
  `forgetSmooth 1` is not injective at this sheaf.
- `R`, `G` and `X` share one universe, as in the published derived functors
  and Godement cohomology.

## Registered sources

- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich manuscript, folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
  §1.4, Definition 1.4.1, the remark after it and the statement of Theorem
  1.4.2, pp.7-8;
  §1.5 through the proof of Corollary 1.5.2, pp.10-12. Read in the text
  layer.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  §3.3, printed pp.158-160 (PDF pp.40-42): Lemma 3.3.1 and its Corollary,
  the definitions of `Φ`-soft sheaves and paracompactifying families,
  Proposition 3.3.2 and its Corollary, and the canonical resolution. Read in
  the text layer; pp.159-160 were also read on the rendered scan. Used only
  in the truth argument.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris 1999,
  PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, printed p.305 (PDF p.7), read on the rendered scan. Context
  only.

## Formal dependencies and checks

The direct project imports are both by Worker 13. They are byte-identical in
Library commits `7c81d0a237386f36202562546586b28c306f0121` and
`01a58491bc71539f1ecd3d5f0eec6ab8eae20fed`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Cohomology.SmoothSheafCohomology` | Worker 13 | `f1365e1fcf6064dbbc6bacd8491c16ce24fe3a76215dc606adc263032be3c7d1` | `8e14762c1b9488273aae24c89c1f7bfce0f5f3001cc7b09cd250edd79206d02d` |
| `Langlands.Cohomology.EquivariantGodementCohomology` | Worker 13 | `d8e9978c4ff9fe11a14d39f62f186f9de896125332b12d55f086d451fa5035b2` | `7d4af4966241481da61efb6fbf53fb0bb9e52b89c8805af6eb1d47576a38d1ae` |

From the first the module uses `compactDerived` and `compactDerivedZeroIso`.
From the second it uses `compactCohomology` and `compactCohomologyZeroIso`.
Through these imports it also uses Worker 13's `SmoothTopologicalSheaf` and
`smoothInclusion` (`Langlands.Sheaf.Equivariant.Smooth`),
`HasStableNeighbourhoods` (`Langlands.Sheaf.Equivariant.SmoothPart`), the
abelian structure of `Langlands.Sheaf.Equivariant.SmoothAbelian`, and
`smoothSheafCompactSectionsToRepIso`
(`Langlands.Sheaf.Equivariant.SmoothSheafCompactSections`), as well as
`Langlands.SmoothRep.toRep` from `Langlands.Representation.Category.Basic`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks `e69f6bbe-6671-47e5-8a7f-a335cb7f705c` (from a draft directory),
`8ab91b2d-9213-4218-9910-38ade9e2e94c` and
`7e878c35-d684-4e43-9034-afd2809bd835` (from the workspace, the last against
Library `01a58491`) built this module with Lake against the published
imports, with no errors or warnings. The Lean file is unchanged since the
first check. Each inspected
`SmoothCompactComparisonStatements` as a `Prop`-valued definition with the
single universe parameter `u`, depending only on `propext`,
`Classical.choice` and `Quot.sound`. Check
`33cd0358-15d0-4c8c-8f64-5b5af501d4f7` compiled a test file against the
module and its output was read. It printed the three definitions, the axioms
of the conjunction, the types of `compactDerived`, `compactDerivedZeroIso`,
`smoothSheafCompactSectionsToRepIso`, `compactCohomologyZeroIso` and
`smoothInclusion`, and the class `HasStableNeighbourhoods`. The prints show:

- all three definitions carry `IsTopologicalGroup G`, `T2Space X`,
  `LocallyCompactSpace X`, `MulAction G X`, `ContinuousConstSMul G X` and
  `HasStableNeighbourhoods G X` as explicit instance binders;
- `R`, `G` and `X` all live in the universe `u`;
- the first definition quantifies over `I : SmoothTopologicalSheaf R G X`
  with `Injective I` and concludes `IsZero` of
  `(compactCohomology R G X (q + 1)).obj ((smoothInclusion R G X).obj I)`;
- in the second, the bound family has type
  `(q : ℕ) → compactDerived R G X q ⋙ SmoothRep.toRep ≅ smoothInclusion R G X ⋙ compactCohomology R G X q`,
  and the degree-zero equation is the composite described above.

The same test file elaborates `SmoothCompactComparisonStatements ℚ G X` for an
arbitrary topological group acting on a locally compact Hausdorff space with
`HasStableNeighbourhoods`, for discrete `G` and for nonarchimedean `G` acting
continuously (the instance is then found), and for the trivial group acting
on a point. This shows only that the statements are well formed there.

Compilation and inspection establish well-formed statements; they do not
prove either component.
