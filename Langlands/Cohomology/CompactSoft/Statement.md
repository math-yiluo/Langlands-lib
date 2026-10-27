# Statements on `c`-soft module sheaves

Author: Worker 61.

This module defines three propositions about the published `c`-softness predicate
`Langlands.Sheaf.CompactSoft.IsCSoft`. The first two are the classical facts about
compactly supported sections of `c`-soft sheaves on a locally compact Hausdorff
space: Grothendieck's Proposition 3.3.2 and its Corollary (Tohoku, §3.3) for the
family of compact sets, in the form given by Kashiwara and Schapira (*Sheaves on
Manifolds*, §2.5). The third says that the sheaf underlying the degree-zero smooth
Godement sheaf of a smooth equivariant sheaf is `c`-soft. It is the ordinary-topology
counterpart of part (2') of Berkovich's proof of Proposition 1.5.1. A fourth
definition, `CSoftStatements`, is the conjunction of the three. All four are
theorem-statement definitions, not proofs. Exactness, softness and vanishing are
conclusions; none is supplied as data or as a hypothesis.

Composition `f ≫ g` is `f` followed by `g`.

## Objects

All declarations are in the namespace `Langlands.Cohomology`. Spaces, rings, groups
and module carriers live in one universe `u`. In the first two propositions,
`X : TopCat.{u}` is a topological space that is Hausdorff (`T2Space`) and locally
compact (`LocallyCompactSpace`), `R : Type u` is a commutative ring, and sheaves are
Mathlib's `TopCat.Sheaf (ModuleCat.{u} R) X`, an abelian category. The published
objects used are:

- `Langlands.Sheaf.CompactSoft.IsCSoft F` (Worker 61's `Langlands.Sheaf.CompactSoft`):
  for every compact `K ⊆ X`, every element of `setSections F K` is the germ along `K`
  of a global section with compact support. Here `setSections F K` is the colimit of
  the sections of `F` over the open neighbourhoods of `K`, and the support of a
  global section is the set of points where its germ is nonzero.
- `Langlands.Sheaf.CompactSupport.functor` (Worker 13's
  `Langlands.Sheaf.CompactSupport`): the additive functor from module sheaves to
  `ModuleCat R` sending a sheaf to its module of global sections with compact
  support, written `Γ_c` below.
- `Langlands.Cohomology.TopologicalDerivedSections.compactCohomology X R n` (Worker
  13's `Langlands.Cohomology.TopologicalDerivedSections`): Mathlib's `n`-th right
  derived functor (`Functor.rightDerived`) of `Γ_c`, computed with Mathlib's
  injective resolutions in the sheaf category. This is compactly supported
  cohomology `H^n_c(X, -)`.

In the third proposition, `R`, `G` and `X` are types in universe `u` with the same
hypotheses as Worker 3's published `Langlands.Cohomology.SmoothGodement` statements:
`G` is a topological group acting on the topological space `X` by `MulAction`,
each element acting continuously (`ContinuousConstSMul`), and
`Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G X` holds (every open
neighbourhood of a point contains an open neighbourhood of that point stabilized by
an open subgroup). In addition `X` is Hausdorff and locally compact. The published
objects used, from Worker 61's `Langlands.Sheaf.Equivariant.Godement.Smooth`, are:

- `Langlands.Sheaf.Equivariant.SmoothTopologicalSheaf R G X`, Worker 13's category
  of smooth equivariant sheaves of `R`-modules on `X`;
- `Langlands.Sheaf.Equivariant.Godement.smoothForget R G X`, the functor forgetting
  smoothness and the action, with values in
  `TopCat.Sheaf (ModuleCat.{u} R) (TopCat.of X)`;
- `Langlands.Sheaf.Equivariant.Godement.smoothZeroFunctor R G X`, the degree-zero
  smooth Godement functor: `smoothForget`, then the ordinary Godement sheaf of all
  stalks (the product over the points of `X` of the skyscraper sheaves of the
  stalks), then smooth coinduction (coinduction followed by the smooth part).

## The propositions

| Declaration | Asserted conclusion |
| --- | --- |
| `CSoftShortExactStatement` | For every locally compact Hausdorff `X : TopCat.{u}`, commutative ring `R : Type u` and short complex `S` of module sheaves on `X`: if `S` is short exact (`S.ShortExact`) and `S.X₁` is `c`-soft, then `S.map Γ_c` is short exact, and if moreover `S.X₂` is `c`-soft, then `S.X₃` is `c`-soft. |
| `CSoftAcyclicityStatement` | For every locally compact Hausdorff `X : TopCat.{u}`, commutative ring `R : Type u`, `c`-soft module sheaf `F` on `X` and `q : ℕ`, `(compactCohomology X R (q + 1)).obj F` is a zero object of `ModuleCat R`. |
| `SmoothGodementZeroCSoftStatement R G X` | For every smooth sheaf `M`, the module sheaf `(smoothForget R G X).obj ((smoothZeroFunctor R G X).obj M)` is `c`-soft. |
| `CSoftStatements` | `CSoftShortExactStatement`, `CSoftAcyclicityStatement`, and `SmoothGodementZeroCSoftStatement R G X` for all `R`, `G`, `X` in universe `u` with the instance hypotheses listed above. |

The first two are closed propositions: the space and the ring are quantified inside,
with the instance hypotheses `[T2Space X] [LocallyCompactSpace X] [CommRing R]` as
binders of the universal quantifier. The third takes `R`, `G`, `X` and their
instance hypotheses as explicit parameters, like Worker 3's statements. The
conjunction is closed: it quantifies the third over `R`, `G`, `X` and their
instance hypotheses. No component is assumed in defining it.

Remarks on what is asserted:

- In the first proposition only the first term is assumed `c`-soft for the
  exactness of `0 → Γ_c(S.X₁) → Γ_c(S.X₂) → Γ_c(S.X₃) → 0`. Since `Γ_c` is left
  exact, the content is the surjectivity of `Γ_c(S.X₂) → Γ_c(S.X₃)`. This is
  Kashiwara–Schapira's Proposition 2.5.8 (for the map to a point). Tohoku's
  condition (iii) of Lemma 3.3.1, verified in Proposition 3.3.2, assumes the first
  two terms in the class; it is the conjunction of both parts.
- The second proposition is stated for Mathlib's derived functors, not for a
  particular resolution. Its case `q + 1` covers all positive degrees.
- The terms of Worker 61's smooth Godement complex are, by definition,
  `(smoothComplex R G X F).X m = (smoothZeroFunctor R G X).obj ((residual _ _ m).obj F)`
  (checked by `rfl` in Worker 3's test file for `SmoothGodement.Statement`). So the
  third proposition, which quantifies over all smooth sheaves `M`, gives
  `c`-softness of the underlying sheaf of every term of the smooth Godement complex.
- None of the propositions is derived from another in Lean. The second, applied to
  the third, gives the vanishing of `H^q_c` of the underlying sheaves of the smooth
  Godement terms in positive degrees, the content of the published
  `SmoothGodementCompactAcyclicStatement` once Godement cohomology of the underlying
  equivariant sheaf is compared with `compactCohomology`. That comparison is not
  stated here.

## Why the statements are expected to hold

This section is a derived argument; the Lean module proves nothing.

Comparison of definitions. Kashiwara and Schapira (§2.5, p.104, Definition 2.5.5)
call a sheaf `F` on a locally compact space (Hausdorff by their convention, p.102)
`c`-soft if `Γ(X; F) → Γ(K; F)` is surjective for every compact `K`, where
`Γ(K; F)` is the module of sections of the restriction `F|_K`. By their
Proposition 2.5.1 (ii) (p.102), for compact `K` in a Hausdorff space the map from
the colimit of `F(U)` over open `U ⊇ K` to `Γ(K; F)` is an isomorphism; so
`Γ(K; F)` is `setSections F K`. By their Proposition 2.5.6 (p.105), applied to the
closed set `Z = K`, a `c`-soft sheaf has the stronger property that every section
over `K` is induced by a global section with compact support. Hence on a locally
compact Hausdorff space `IsCSoft F` is equivalent to Kashiwara–Schapira's
`c`-softness, and also to Grothendieck's `Φ`-softness for `Φ` the compact sets
(Tohoku, p.159; see the comparison in Worker 61's `CompactSoft.md`). The supports
agree: Kashiwara–Schapira's support is the set of points with nonzero germ, and
`Γ_c` takes global sections whose support is compact (and Hausdorff, automatic
here), as in their (2.5.2) on p.103.

Coefficients. Kashiwara–Schapira and Grothendieck state these results for sheaves of
abelian groups. For sheaves of `R`-modules, the forgetful functor to sheaves of
abelian groups is exact and faithful, so it preserves and reflects short exact
sequences; it commutes with `Γ_c`, with stalks and with the colimits defining
`setSections` (filtered colimits of modules are computed on underlying groups). So
`IsCSoft` and the exactness of `S.map Γ_c` can be checked on underlying sheaves of
abelian groups.

First proposition. Kashiwara–Schapira's Proposition 2.5.8 (p.105): if
`0 → F' → F → F'' → 0` is exact and `F'` is `c`-soft, then
`0 → Γ_c(X; F') → Γ_c(X; F) → Γ_c(X; F'') → 0` is exact. Their proof reduces to a
compact space by passing to a relatively compact open neighbourhood of the support
of a section of `F''`, covers it by finitely many compact sets over which the
section lifts, and glues two lifts at a time, correcting the difference on the
intersection by a global section of `F'`. Corollary 2.5.9 (p.105): if `F'` and `F`
are `c`-soft, so is `F''`. Together these are the first proposition. The case of
compact supports of Tohoku's Proposition 3.3.2 (p.159), whose proof Grothendieck
leaves to Godement's book, gives the same two conclusions when `F'` and `F` are both
`c`-soft.

Second proposition. Apply Tohoku's Lemma 3.3.1 (p.158) to the abelian category of
module sheaves on `X` (it has enough injectives), the functor `Γ_c` and the class
`M` of `c`-soft sheaves. The lemma gives `R^p Γ_c(A) = 0` for `p > 0` and `A ∈ M`,
computing `R^p Γ_c` with injective resolutions, as Mathlib's `Functor.rightDerived`
does. Its conditions:

- (i) Every sheaf embeds in a member of `M`. Every sheaf embeds in a flasque sheaf,
  for instance its Godement sheaf of all stalks (Tohoku, p.159), and flasque sheaves
  on a locally compact Hausdorff space are `c`-soft (Worker 61's published
  `isCSoft_of_isFlasque`; locally compact Hausdorff spaces are regular).
- (ii) A direct summand of a member is a member (published `IsCSoft.of_retract`,
  `IsCSoft.of_iso`).
- (iii) In a short exact sequence `0 → M' → M → M'' → 0` with `M'` and `M` in `M`,
  `M''` is in `M` and `Γ_c` of the sequence is exact: the first proposition.

Kashiwara–Schapira state the same conclusion as "the category of `c`-soft sheaves on
`X` is injective with respect to the functor `Γ_c(X; ·)`" (p.105, after Corollary
2.5.9). Their Remark 1.8.6 (p.51) then gives `R^k F(A) = 0` for `k ≠ 0` and `A` in
an `F`-injective subcategory.

Third proposition. This is Step 3 of the truth argument in Worker 3's published
`Langlands/Cohomology/SmoothGodement/Statement.md`, which this module turns into a
standalone statement. Briefly: by Worker 3's Step 0, a section of
`D(M) = smoothZeroFunctor M` over an open `U` is a family of stalk entries indexed by
the pairs `(g, y)` with `g • y ∈ U`, locally fixed at every point of `U`. A germ along
a compact `K` is represented by such a section `t` over an open `W ⊇ K`. Choose an
open `W₀ ⊇ K` with compact closure inside `W`. Using `HasStableNeighbourhoods` and
compactness, find finitely many opens `V_i ⊆ W₀` covering `K`, stabilized by open
subgroups `H_i` fixing `t` on `V_i`; then `H = ⋂ H_i` is an open subgroup stabilizing
`V = ⋃ V_i` and fixing `t` on `V`. The family `t'` equal to `t` at the indices over `V`
and zero elsewhere is locally fixed at every point of `X`: on `V` by `H`; outside the
closure of `V` because it is zero there; and at a point of the closure of `V` not in
`V` by the intersection of `H` with a subgroup witnessing local fixedness of `t`
there. So `t'` is a global section of `D(M)`, its support lies in the compact closure
of `V`, and its germ along `K` is that of `t`. Besides the description of sections in
Worker 3's Step 0, which comes from the right Kan extension defining coinduction and is
not constructed in Lean, only local compactness, the Hausdorff property and
`HasStableNeighbourhoods` are used; paracompactness of `X`, assumed by Berkovich, is
not needed for this form.

## Provenance

The three propositions are transcriptions to the published Lean objects, not
literal statements of one source:

- The first two specialize Tohoku Proposition 3.3.2 (case 2) and its Corollary to
  `Φ` the compact sets, which is a paracompactifying family on a locally compact
  Hausdorff space: compact Hausdorff spaces are paracompact, and every compact set
  has a compact neighbourhood. They are stated in the form of Kashiwara–Schapira
  Proposition 2.5.8, Corollary 2.5.9 and the injectivity remark after it, which
  concern exactly `c`-soft sheaves and `Γ_c`. The definition of `c`-softness used
  is the published colimit form `IsCSoft`, equivalent on these spaces as explained
  above; the equivalence is not formalized. The coefficients are sheaves of
  `R`-modules rather than abelian groups.
- The third is derived. Berkovich's Proposition 1.5.1 says that `b^*(C^m(F))` is a
  soft sheaf on `X_ét`, and part (2') of its proof shows that the restriction of
  `b^*(C^0(F))` to the usual topology is soft: for every compact `Σ ⊂ X` the map
  `F(X) → F(Σ)` is surjective. On the ordinary open-set site of a topological space
  with a smooth action, Worker 61's `smoothZeroFunctor` is the counterpart of
  `C^0 = ν_*ν^*` (see Worker 61's `Smooth.md` and Worker 3's
  `SmoothGodement/Statement.md`), and the conclusion is taken in the
  compact-support form `IsCSoft`. Harris (1999, section 2, p.304) uses Berkovich's
  construction `F(T)` and its `RΓ_c`-acyclicity; on the ordinary site that
  acyclicity is the second proposition applied to the third.

## Original-source correspondence

| Source | Original statement | Lean component |
| --- | --- | --- |
| Kashiwara–Schapira Prop. 2.5.8 and Cor. 2.5.9, p.105; Tohoku Prop. 3.3.2 case 2, p.159, for `Φ` = compact sets | `0 → Γ_c(X;F') → Γ_c(X;F) → Γ_c(X;F'') → 0` is exact if `F'` is `c`-soft; `F''` is `c`-soft if `F'` and `F` are. | `CSoftShortExactStatement` |
| Tohoku Cor. of Prop. 3.3.2, p.159; Kashiwara–Schapira p.105 (injectivity of `c`-soft sheaves for `Γ_c`) with Remark 1.8.6, p.51 | `H^p_Φ(X, F) = 0` for `p > 0` if `F` is `Φ`-soft and `Φ` paracompactifying. | `CSoftAcyclicityStatement` |
| Berkovich Prop. 1.5.1, p.10, proof of (2'), p.11; Worker 3's `SmoothGodement/Statement.md`, Step 3 | The restriction of `b^*(C^0(F))` to the usual topology is soft. | `SmoothGodementZeroCSoftStatement` |
| The three rows above | Their conjunction. | `CSoftStatements` |

## Scope

- Only compact supports are treated; general paracompactifying families, soft
  sheaves for closed sets and Tohoku's case 1 (flasque sheaves) are not stated.
- The identification of `setSections F K` with sections of the restricted sheaf,
  and of `IsCSoft` with Kashiwara–Schapira's and Grothendieck's definitions, is not
  stated.
- `c`-softness is stated for the degree-zero smooth Godement sheaf only; the higher
  terms are covered through the definitional equality recalled above. Softness for
  the étale site, Berkovich's fact (1') on Galois cohomology of stalks, and the
  comparison of `compactCohomology` with Worker 13's Godement-complex
  `EquivariantGodementCohomology.compactCohomology` are not stated.
- No statement concerns the smooth or equivariant derived functors
  (`SmoothSheafCohomology.compactDerived`); Worker 3's
  `SmoothGodementCompactDerivedAcyclicStatement` remains the statement for those.

## Registered sources

- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J. 9
  (1957), file
  `Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`.
  §3.3, printed p.158 (one-based PDF page 40): Lemma 3.3.1 and its Corollary;
  printed p.159 (one-based PDF page 41): flasque and `Φ`-soft sheaves,
  paracompactifying families, Proposition 3.3.2 and its Corollary. Read by Worker 61
  in the text layer.
- `provided-1a1e547af2f3cfc223f73a05ef9491bbf82f0d1976763c0d9c200813c4b8b658`:
  Kashiwara and Schapira, *Sheaves on Manifolds*, Grundlehren 292 (1990), file
  `Kashiwara, Schapira - Sheaves on Manifolds, Grundlehren 292 (1990).pdf`, SHA-256
  `27c80b305bf07611948cc4ebb154c9abae7454f1eed67cbe10cfb0318f0c2163`. §1.8, printed
  pp.50-51 (one-based PDF pages 60-61): Definition 1.8.2 and Remark 1.8.6; §2.5,
  printed pp.102-105 (one-based PDF pages 112-115): conventions, Proposition 2.5.1,
  the definition (2.5.2) of `Γ_c`, Definition 2.5.5, Propositions 2.5.6 and 2.5.8,
  Corollary 2.5.9 and the remark after it. Read by Worker 61 in the text layer.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
  manuscript (1995-1996), folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`. §1.5,
  printed pp.10-11 (one-based PDF pages 10-11): the Godement resolution,
  Proposition 1.5.1 and its proof, including (2'). Read by Worker 61 in the text
  layer.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris, *Galois
  properties of cohomological automorphic forms on GL(n)*, J. Math. Kyoto Univ.
  39-2 (1999), section 2, printed p.304 (one-based PDF page 6). Context only.

## Formal dependencies and checks

The module imports three published modules (Library commit
`89d348e1b4fafddacdfd1e8f7f291f234b066807`):

| Module | Author | Lean SHA-256 |
| --- | --- | --- |
| `Langlands.Sheaf.CompactSoft` | Worker 61 | `87dc2992215660890b9138f90ebcf073a1b2343766d9fe2fc3d1029ff69bf26c` |
| `Langlands.Cohomology.TopologicalDerivedSections` | Worker 13 | `f2c3e8f0d296eb10d666bb649c121362cf184069db96aa3c27d4b50f21b243c9` |
| `Langlands.Sheaf.Equivariant.Godement.Smooth` | Worker 61 | `c87bbf5eef53c9d4b6e1b2c9d30f834d14533f3e963b489a2fa96ccd7c1e37cc` |

Through them it uses Worker 13's `Langlands.Sheaf.CompactSupport.functor` (Lean
SHA-256 `65a924376d143fa231a58338848c323fcb3dad4f4f5a0be814b8a360684757b5`),
`SmoothTopologicalSheaf` and `HasStableNeighbourhoods`. The environment is
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Lean checks with Lake in the workspace (Library `89d348e1` plus this pair) built
the module with no errors or warnings. Each of the four declarations was inspected
(checks `f705bfe3-126e-4712-ba87-3a4d8d06c2bb` for `CSoftStatements`,
`a32dd067-b1ec-4db6-b953-a03a26f0c0e6` for `CSoftShortExactStatement`,
`de9feb6f-3ecc-4555-b09e-f82b53c7e0fa` for `CSoftAcyclicityStatement`,
`66c3476f-aa86-4206-84b3-9895b784d71b` for `SmoothGodementZeroCSoftStatement`): it
is a definition whose type is `Prop`, with the single universe parameter `u`,
depending only on `propext`, `Classical.choice` and `Quot.sound`. Compilation and
inspection establish well-formed statements; they do not prove any of them.
