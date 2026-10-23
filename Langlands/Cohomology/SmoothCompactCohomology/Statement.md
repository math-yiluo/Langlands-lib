# Smoothness of compactly supported cohomology of smooth equivariant sheaves

Author: Worker 3.

This module defines two propositions and their conjunction
`Langlands.Cohomology.SmoothCompactCohomology.SmoothCompactCohomologyStatements`.
The setting is a topological group acting on a topological space, with a
smooth equivariant sheaf of modules. The first proposition says that the
group acts smoothly on compactly supported global sections. The second says
that, on a locally compact Hausdorff space, it acts smoothly on every
compactly supported cohomology module. They are the ordinary-topology
analogue of the assertion in Berkovich's Corollary 1.5.2(i) that the action
of `G` on `H^q_c(X, b^*F)` is discrete. Harris 1999 uses that assertion on
printed p.305. The propositions are theorem-statement definitions, not
proofs. Smoothness is the conclusion in both; it is not supplied as data or
as a hypothesis.

## Objects

Both components quantify over a commutative ring `R`, a group `G` and a
topological space `X`, all in one universe `u`. `G` carries a topology that
makes it a topological group (`IsTopologicalGroup`). `G` acts on `X` by
`MulAction`, and each element acts continuously (`ContinuousConstSMul`), so
it acts by a homeomorphism. No continuity of the action map `G × X → X` is
assumed. The published Godement-route cohomology is stated with `G` in the
universe of `X` and `R`, so `G` shares the universe `u` here. The objects are
the published ones:

- `Langlands.Sheaf.Equivariant.TopologicalSheaf G X (ModuleCat R)` is the
  category of equivariant sheaves of `R`-modules on the ordinary open-set
  transport site.
- `Langlands.Sheaf.Equivariant.IsSmoothSheaf R G X F`, from Worker 13's
  `Langlands.Sheaf.Equivariant.Smooth`, says that `F` is smooth. For every
  open `U`, every section `s` of `F` over `U` and every point `x` of `U`,
  there are an open `V` with `x ∈ V ⊆ U` and an open subgroup `H` of `G` with
  `H • V ⊆ V`, such that every element of `H` fixes the restriction of `s` to
  `V`. The definition therefore also requires that every point have
  arbitrarily small neighbourhoods stabilized by open subgroups.
- `Langlands.Sheaf.Equivariant.CompactSections.functor R G X` sends `F` to
  its compactly supported global sections with their `G`-action, as an
  object of Mathlib's `Rep R G`. The support of a global section is the set
  of points where its germ is nonzero.
- `Langlands.Cohomology.EquivariantGodementCohomology.compactCohomology R G X q`
  is Worker 13's compactly supported cohomology in degree `q`, with its
  `G`-action. It is the `q`-th cohomology of the compactly supported global
  sections of Worker 61's equivariant Godement complex
  (`Langlands.Sheaf.Equivariant.Godement.complexFunctor`), as an object of
  `Rep R G`. Worker 61's published `underlyingComplexIso`, in
  `Langlands.Sheaf.Equivariant.Godement.Underlying`, shows that after
  forgetting the action, this complex is the ordinary Godement complex over
  the points of `X`. So the underlying module is the usual compactly
  supported sheaf cohomology. This module does not import that comparison.
- `Langlands.IsSmooth ρ` says that every vector is fixed by some open
  subgroup. This is the published Casselman convention of
  `Langlands.Representation.Smooth.Definitions`.

## The two propositions

| Declaration | Hypotheses on `X` | Asserted conclusion |
| --- | --- | --- |
| `CompactSectionsSmoothStatement R G X` | none beyond the objects above | For every smooth `F`, the representation `(CompactSections.functor R G X).obj F` is smooth. |
| `CompactCohomologySmoothStatement R G X` | `T2Space X`, `LocallyCompactSpace X` | For every smooth `F` and every `q : ℕ`, the representation `(compactCohomology R G X q).obj F` is smooth. |

`SmoothCompactCohomologyStatements R G X` is the conjunction of the two, in
this order, under the hypotheses of the second. In degree zero, the second
proposition and the published `compactCohomologyZeroIso` imply the first for
locally compact Hausdorff `X`. The first is stated separately because it
needs no separation or local compactness. It is also the step that
Berkovich's proof of Corollary 1.5.2 states explicitly.

Each definition lists its type-class hypotheses as explicit binders, so they
all appear in its type. The first proposition does not use
`IsTopologicalGroup G`. It is assumed in both for uniformity with Berkovich's
topological groups and with the published smooth-representation category.

## Why the statements are expected to hold

This argument is derived here; Berkovich's proof uses his analytic étale
setting instead.

Degree zero. Let `s` be a section with compact support `K`. Cover `K` by
finitely many neighbourhoods `V_i`, each stabilized by an open subgroup
`H_i` that fixes `s` on `V_i`. Then `H = ⋂ H_i` is an open subgroup that
stabilizes `V = ⋃ V_i` and fixes `s` on `V`. For `h ∈ H`, both `s` and `h • s`
vanish off `K ∪ h • K`, which is a closed subset of `V`. So they agree on the
open cover `{V, X ∖ (K ∪ h • K)}` of `X`, and `h • s = s`.

Higher degrees. The acyclicity facts used here are from Grothendieck's
Tohoku paper, §3.3, printed pp.158-160, and are stated there for sheaves of
abelian groups. Forgetting the `R`-module structure commutes with all the
constructions below.

- p.159: a sheaf is flabby (`flasque`) if every section over an open set
  extends to `X`. For a family `Φ` of closed sets as in §3.2, a sheaf `F` is
  `Φ`-soft (`Φ-mou`) if every section of `F` over a member of `Φ` is induced
  by a global section with support in `Φ`. `Φ` is paracompactifying if every
  member is paracompact and has a neighbourhood in `Φ`. Also, a section over
  a closed set with a paracompact neighbourhood extends to an open
  neighbourhood of that set.
- p.159, Proposition 3.3.2 and its Corollary: `H^p_Φ(X, F) = 0` for `p > 0`
  if `F` is flabby, or if `F` is `Φ`-soft and `Φ` is paracompactifying. By
  the Corollary to Lemma 3.3.1, p.158, a resolution of `F` by such sheaves
  computes `H^p_Φ(X, F)`.
- p.160: the canonical resolution `C^•(F)`, Godement's, has `C⁰(F)` equal to
  the product of the stalks of `F` and
  `Cⁿ(F) = C⁰(Cⁿ⁻¹(F)/Im Cⁿ⁻²(F))`. Its terms are flabby, and
  `H^n_Φ(X, F) = H^n(Γ_Φ C^•(F))` for every `Φ`.

Let `c` be the family of compact subsets of `X`. If `X` is locally compact
and Hausdorff, then `c` is paracompactifying. Compact sets are closed. Finite
unions of compact sets, and closed subsets of compact sets, are compact. A
compact Hausdorff space is paracompact. Every compact set has a compact
neighbourhood. So `Γ_c` is `Γ_Φ` for this paracompactifying `Φ = c`.

Let `D⁰(F)` be the subsheaf of the product of the stalks `∏_x F_x` consisting
of the families that are locally fixed in the sense of `IsSmoothSheaf`. It is
a smooth equivariant sheaf, and `F` embeds in it through its germs because
`F` is smooth. Its quotient by `F` is again smooth, because every section of
the quotient is locally the image of a section of `D⁰(F)`. `D⁰` is a functor,
so `Dⁿ = D⁰(Dⁿ⁻¹/Im Dⁿ⁻²)` defines a resolution `D^•` of `F` by smooth
sheaves. The inclusions `D⁰ ⊆ C⁰` induce a map of resolutions
`D^• → C^•(F)` over the identity of `F`, and this map commutes with the
action of `G`.

Each `D^m` is `c`-soft. Let `t` be a section of `D^m` over a compact set `K`.
`K` has a compact, hence paracompact, neighbourhood, so `t` extends to an
open neighbourhood `W` of `K`, which may be taken with compact closure. Cover
`K` by finitely many open `V_i ⊆ W`, each stabilized by an open subgroup
`H_i` that fixes `t` on `V_i`. Then `H = ⋂ H_i` is an open subgroup that
stabilizes `V = ⋃ V_i` and fixes `t` on `V`. Extend the family `t|_V` by zero
outside `V`. Since `H` stabilizes both `V` and its complement, `H` fixes the
extended family on all of `X`. Every point has a neighbourhood stabilized by
an open subgroup (see Objects), and the intersection of that subgroup with `H`
fixes the family there. So the family is locally fixed, and hence a global
section of `D^m`. Its support lies in the compact closure of `V`, and it
induces `t` on `K`.

By Proposition 3.3.2 and its Corollary, both `D^•` and `C^•(F)` are
resolutions of `F` by `Γ_c`-acyclic sheaves. So `Γ_c` of the map
`D^• → C^•(F)` induces an isomorphism on cohomology, which is compatible
with the action of `G`. Worker 61's published `underlyingComplexIso`, in
`Langlands.Sheaf.Equivariant.Godement.Underlying`, identifies the complex
underlying the equivariant Godement complex with `C^•(F)`. Hence
`compactCohomology q F` is the `q`-th cohomology of `Γ_c(D^•)`, with its
`G`-action. By degree zero, `Γ_c(D^•)` consists of smooth representations,
and subquotients of smooth representations are smooth.

## A false variant

Worker 13's `EquivariantGodementCohomology` also defines
`smoothCompactCohomology q`. It is the cohomology of the smooth parts of the
compactly supported Godement sections. `forgetSmooth q` maps it to
`compactCohomology q`. For smooth `F`, `forgetSmooth 0` at `F` is an
isomorphism by degree zero. In higher degrees it need not be. Take
`R = ℚ` and `G = X = ℤ_p`, acting by translation, and let `F` be the constant
sheaf `ℚ`, which is smooth. `X` is compact and totally disconnected, so
`H^1_c(X, F) = 0`. The degree-zero Godement term has global sections
`Map(ℤ_p, ℚ)`, and its smooth part consists of locally constant functions.
So the first cohomology of the smooth-part complex is the smooth part of
`Map(ℤ_p, ℚ)/C^∞(ℤ_p, ℚ)`. Choose a nonzero additive map `f : ℤ_p → ℚ`. It
exists because `ℤ_p ⊗ ℚ = ℚ_p` is a nonzero `ℚ`-vector space. Then
`f(x - h) - f(x) = -f(h)` is constant, so the class of `f` is `G`-invariant.
The class is nonzero, because a locally constant additive map into a
torsion-free group is zero. Hence `forgetSmooth 1` at `F` is not injective.
The smooth-part functor is left exact but not exact. This is why the second
proposition is stated as smoothness of `compactCohomology`.

## Original-source correspondence

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript. The printed page numbers equal the PDF page numbers.

- §1.1, pp.1-2: all analytic spaces are assumed Hausdorff, and a `G`-space
  is an analytic space with a continuous action of a topological group `G`.
  Here `T2Space X` and `LocallyCompactSpace X` take the place of these
  spaces. Local compactness of Berkovich's analytic spaces comes from his
  general theory, not from these pages.
- §1.4, pp.7-8: for a quasi-étale morphism `U → X` with compact `U`, the Key
  Lemma extends the action of `G` to a continuous action of an open subgroup
  `G_U` on `U`. Definition 1.4.1 calls a `G_d`-sheaf `F` a `G`-sheaf when
  `G_U` acts discretely on `F(U)` for every such `U`. The remark that follows
  characterizes étale `G`-sheaves: for every étale `U → X` and every
  `f ∈ F(U)`, each point of `U` has a distinguished open neighbourhood on
  which the stabilizer of the restriction of `f` is open. Worker 13's
  `IsSmoothSheaf` transcribes this characterization to the ordinary open-set
  site. The neighbourhoods stabilized by open subgroups, which the Key Lemma
  supplies on analytic spaces, are part of that hypothesis here.
- Corollary 1.5.2(i), pp.11-12: for an étale abelian sheaf `F` on `X(G)`,
  there are canonical isomorphisms `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)`. "In
  particular, the canonical action of `G` on the groups `H^q_c(X, b^*F)` is
  discrete." Here `b^*F` is the `G`-sheaf on `X` attached to `F` by Theorem
  1.4.2. This discreteness is `CompactCohomologySmoothStatement`.
- Proof of Corollary 1.5.2, p.12: "every element of `H^0_c(X, b^*F)` is
  fixed by an open subgroup of `G`". This is
  `CompactSectionsSmoothStatement`.

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), 299-318, section 2, printed p.305 (PDF
p.7). A compact open subgroup `S(ẽ)` stabilizes the analytic space `U(ẽ)`.
Harris states that `H^q_c(U(ẽ)_{F̄}, ℤ/ℓ^m ℤ)` "is a finite smooth
`S(ẽ)`-module". He then takes an open normal pro-`p` subgroup acting
trivially on these modules. The present module states only the smoothness,
in the ordinary-topology analogue.

| Source | Original statement | Lean component |
| --- | --- | --- |
| Berkovich, proof of Cor. 1.5.2, p.12 | Every element of `H^0_c(X, b^*F)` is fixed by an open subgroup. | `CompactSectionsSmoothStatement` |
| Berkovich Cor. 1.5.2(i), pp.11-12; Harris p.305 | The action of `G` on `H^q_c(X, b^*F)` is discrete (Berkovich); `H^q_c(U(ẽ)_{F̄}, ℤ/ℓ^m ℤ)` is a finite smooth `S(ẽ)`-module (Harris). | `CompactCohomologySmoothStatement`, smoothness only |

## Scope

- The site is the ordinary open-set site of a topological space, not
  Berkovich's étale or quasi-étale site of an analytic space. Analytic
  spaces, `X(G)`, the Drinfeld spaces and the base change to `F̄` in Harris
  are not formalized here.
- The ordinary-topology analogue of the comparison
  `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` of Corollary 1.5.2(i) uses derived
  functors on the category of smooth equivariant sheaves. Under the
  coefficient, topology, action and common-universe assumptions above,
  together with `HasStableNeighbourhoods G X`,
  `Langlands.Sheaf.Equivariant.SmoothAbelian` publishes
  `smoothTopologicalSheaf_abelian` and
  `smoothTopologicalSheaf_enoughInjectives` for `SmoothTopologicalSheaf R G X`.
  For locally compact Hausdorff `X`, with the same stable-neighbourhood
  hypothesis, `Langlands.Cohomology.SmoothCompactComparison.Statement`
  defines `SmoothInjectiveCompactAcyclicStatement`,
  `SmoothCompactDerivedComparisonStatement` and their conjunction
  `SmoothCompactComparisonStatements`. The comparison goal asks for natural
  isomorphisms in `Rep R G` in every degree, with the specified canonical
  identification through compact sections in degree zero. These are
  Prop-valued goals, not proofs of acyclicity or comparison. These companion
  modules are available in the Library but are not imported here. For a
  discrete group, `Langlands.Cohomology.OperatorSpace.Statement` also states
  `EquivariantCompactSectionsDerivedStatement`.
- The spectral sequence of Corollary 1.5.2(i) is not stated. The published
  `Langlands.Cohomology.OperatorSpace.Statement` explains why it fails for
  infinite discrete groups.
- Finiteness of the cohomology modules and Harris's choice of a pro-`p`
  subgroup acting trivially are not stated. The coefficient ring is
  arbitrary; no torsion hypothesis is made.
- Global sections without support conditions are excluded, because their
  action need not be smooth. Let `G = X = ℚ_p` act by translation, and let
  `F` be the constant sheaf `R`, which is smooth. Let `f` be the indicator
  function of the union of the disjoint compact open sets
  `p^(-n) + p^n ℤ_p` for `n ≥ 1`. This union is locally finite, so `f` is
  locally constant and is a global section. For `n > k`, the point
  `p^(-n) + p^k` has absolute value `p^n` but does not lie in
  `p^(-n) + p^n ℤ_p`, so `f(p^(-n) + p^k) = 0 ≠ 1 = f(p^(-n))`. Hence no
  `p^k ℤ_p`, and so no open subgroup, fixes `f`.

## Registered sources

- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich manuscript, folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
  §1.1, pp.1-2; §1.4 through Definition 1.4.1 and the remark after it,
  pp.7-8; §1.5 through the proof of Corollary 1.5.2, pp.10-12. Read in the
  text layer.
- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris 1999,
  PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, printed pp.304-305 (PDF pp.6-7). The sentence on p.305 was read
  visually on the rendered scan, which shows the support subscript in
  `H^q_c`.
- `provided-df60b2162f53c78d858f948959fe779f32064b9b99ef5345277dc18e8008a5f0`:
  Grothendieck, *Sur quelques points d'algèbre homologique*, Tôhoku Math. J.
  9 (1957), retained file
  `literature/Grothendieck 1957 Tohoku original- acyclic resolutions and derived comparison.pdf`,
  SHA-256 `7fb6ca3f5b860361dc75ff6456e25fc7b9e347acb0f08a78a1e032b9c2d330fe`;
  §3.3, printed pp.158-160 (PDF pp.40-42): Lemma 3.3.1 and its Corollary,
  the definitions of flabby and `Φ`-soft sheaves and of paracompactifying
  families, Proposition 3.3.2 and its Corollary, and the canonical
  resolution. Read in the text layer; pp.159-160 were also read on the
  rendered scan. These pages are used only in the truth argument for higher
  degrees.

## Formal dependencies and checks

The direct project imports are both by Worker 13 and are byte-identical to
Library commits `196ceda926c7cfe1fdbe5ae57c08133d83bbf940`,
`9a1bc5f8b8379aa4fe176f3af65ec4c9d96fc715`,
`9a0767626050f3346ad5f25e37cef39f38a5c0dc` and
`3afe6f3ba5efc4d00cccb18dba321ef341bbaf68`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Cohomology.EquivariantGodementCohomology` | Worker 13 | `d8e9978c4ff9fe11a14d39f62f186f9de896125332b12d55f086d451fa5035b2` | `7d4af4966241481da61efb6fbf53fb0bb9e52b89c8805af6eb1d47576a38d1ae` |
| `Langlands.Sheaf.Equivariant.Smooth` | Worker 13 | `efa99fe81a49bada1ae4e3f600c916293f224e19bbeb2e3ca2288f561e7bafc5` | `d0201fd9f4c461197409189fdcbee05ec5564993bf8f4d8264729ceb101b30af` |

From the first the module uses `compactCohomology`. From the second it uses
`IsSmoothSheaf`. Through these imports it also uses Worker 13's
`TopologicalSheaf` (`Langlands.Sheaf.Equivariant.Topological`) and
`CompactSections.functor` (`Langlands.Sheaf.Equivariant.CompactSupport`),
Worker 61's `Langlands.Sheaf.Equivariant.Godement.complexFunctor`, which
`compactCohomology` is built from, and `Langlands.IsSmooth` from
`Langlands.Representation.Smooth.Definitions`. The comparison in degree zero
mentioned above is Worker 13's `compactCohomologyZeroIso`; it is not used by
a proof in this module.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks `9060f031-ab99-403f-a09a-c037565dddc4`,
`9329ae0d-5220-4c58-912a-5d8eb3e8fdb1` and
`94f8bca0-f4b4-46b4-8337-86712c24d958` built this module with Lake
against the published imports, with no errors or warnings. Each inspected
`SmoothCompactCohomologyStatements` as a `Prop`-valued definition with the
single universe parameter `u`, depending only on `propext`,
`Classical.choice` and `Quot.sound`. Check
`154a10d2-6f29-4fc9-b09c-d40e74394a31` compiled a test file against the
module and its output was read. It printed the three definitions with
universe annotations, the axioms of the conjunction (`propext`,
`Classical.choice`, `Quot.sound`), the type of `compactCohomologyZeroIso`
and the definition of `Langlands.IsSmooth`. The prints show:

- all three definitions carry `IsTopologicalGroup G`, `MulAction G X` and
  `ContinuousConstSMul G X` as explicit instance binders; the second and the
  conjunction also carry `T2Space X` and `LocallyCompactSpace X`;
- `R`, `G` and `X` all live in the universe `u`, and the sheaves range over
  `TopologicalSheaf.{u, u, u + 1, u} G X (ModuleCat.{u, u} R)`;
- the first definition concludes `Langlands.IsSmooth` of the `ρ` of
  `(CompactSections.functor R G X).obj F`, and the second concludes it, for
  every `q : ℕ`, of the `ρ` of `(compactCohomology R G X q).obj F`; in both,
  `IsSmoothSheaf R G X F` is the only hypothesis on `F`;
- `Langlands.IsSmooth ρ` unfolds to `∀ v, Langlands.IsSmoothVector ρ v`.

The same test file elaborates `SmoothCompactCohomologyStatements ℚ G X` for
an arbitrary topological group `G` acting on a locally compact Hausdorff
space `X` in `Type`, and for the trivial group acting on a point. This shows
only that the statements are well formed there.

Compilation and inspection establish well-formed statements; they do not
prove either component.
