# Exactness and compact acyclicity of the smooth Godement construction

Author: Worker 3.

This module defines four propositions and their conjunction
`Langlands.Cohomology.SmoothGodement.SmoothGodementStatements`. They concern
Worker 61's published smooth equivariant Godement construction
(`Langlands.Sheaf.Equivariant.Godement.Smooth`). The setting is a topological
group acting on a topological space, and smooth equivariant sheaves of modules
on it. The first two propositions say that the degree-zero smooth Godement
functor and every term functor of the smooth Godement complex are additive
and exact. The last two assume that the space is locally compact and
Hausdorff. They say that every term of the smooth Godement complex of a smooth
sheaf has no compactly supported cohomology in positive degrees, in two
senses: Godement cohomology of the underlying equivariant sheaf, and the right
derived functors of compact sections in the smooth category. These are the
ordinary-topology analogues of Fact 3 and of the acyclicity of `F(T)` in
Harris 1999, section 2, printed p.304, and of property (ii) of §1.5 and
Proposition 1.5.1 in Berkovich's manuscript (see Provenance). All four are
theorem-statement definitions, not proofs. Exactness and acyclicity are
conclusions; they are not supplied as data or as hypotheses.

## Objects

All propositions quantify over a commutative ring `R`, a group `G` and a
topological space `X`, all in one universe `u`. `G` is a topological group
(`IsTopologicalGroup`). It acts on `X` by `MulAction`, and each element acts
continuously (`ContinuousConstSMul`), hence by a homeomorphism. The hypothesis
`Langlands.Sheaf.Equivariant.HasStableNeighbourhoods G X`, from Worker 13's
`Langlands.Sheaf.Equivariant.SmoothPart`, says that every open neighbourhood
of every point contains an open neighbourhood of that point that is
stabilized by some open subgroup. Worker 13 publishes instances for discrete
`G`, and for nonarchimedean `G` acting continuously (`NonarchimedeanGroup G`,
`ContinuousSMul G X`). Worker 61's construction and Worker 13's abelian
structure on smooth sheaves need exactly these hypotheses, and the two
exactness propositions assume nothing more. The two acyclicity propositions
and the conjunction also assume that `X` is Hausdorff (`T2Space`) and locally
compact (`LocallyCompactSpace`), which the truth argument uses.

The objects are the published ones:

- `Langlands.Sheaf.Equivariant.SmoothTopologicalSheaf R G X` is Worker 13's
  full subcategory of smooth sheaves (`IsSmoothSheaf`) inside the equivariant
  sheaves of `R`-modules `TopologicalSheaf G X (ModuleCat R)`. A sheaf is
  smooth when, for every open `U`, every section `s` over `U` and every point
  `x` of `U`, there are an open `V` with `x ∈ V ⊆ U` and an open subgroup `H`
  with `H • V ⊆ V` such that every element of `H` fixes the restriction of `s`
  to `V`. Call such a section locally fixed at `x`.
  `Langlands.Sheaf.Equivariant.smoothInclusion R G X` is the inclusion.
  Worker 13's `Langlands.Sheaf.Equivariant.SmoothAbelian` makes the
  subcategory abelian, with the kernels and cokernels of the ambient category,
  and proves that it has enough injectives.
- `Godement.smoothForget R G X` is `smoothInclusion` followed by `toSheaf`,
  which forgets the action. It lands in ordinary sheaves of `R`-modules on
  `X`. `Godement.smoothCoinduction R G X` is Worker 61's coinduction followed
  by Worker 13's smooth part `smoothCoreflector`, and
  `smoothCoinductionAdjunction` proves `smoothForget ⊣ smoothCoinduction`.
- `Godement.smoothZeroFunctor R G X` is the composite
  `smoothForget ⋙ Z ⋙ smoothCoinduction`, an endofunctor of smooth sheaves.
  Here `Z` is the published ordinary Godement degree-zero functor
  `Sheaf.Godement.zeroFunctor (Cohomology.Flasque.spacePoints (TopCat.of X)) (ModuleCat R)`,
  the product over all points of `X` of the skyscraper sheaves of the stalks.
  `Godement.smoothCoaugmentation R G X : 𝟭 ⟶ smoothZeroFunctor R G X` is
  Worker 61's coaugmentation, monic at every object
  (`mono_smoothCoaugmentation_app`).
- `Langlands.Cohomology.CokernelComplex.residual T η n` and
  `CokernelComplex.term T η n` are the published residual and term functors
  of the cokernel construction for a coaugmented endofunctor `η : 𝟭 ⟶ T`:
  `residual 0` is the identity, `residual (n + 1)` is the cokernel of `η`
  whiskered by `residual n`, and `term n = residual n ⋙ T`.
  `Godement.smoothComplex R G X F` is Worker 61's smooth Godement complex of a
  smooth sheaf `F`, the published cokernel complex for
  `T = smoothZeroFunctor R G X` and `η = smoothCoaugmentation R G X`. Its
  degree-`m` object is, by definition,
  `(smoothZeroFunctor R G X).obj ((residual _ _ m).obj F)`.
- `Langlands.Cohomology.EquivariantGodementCohomology.compactCohomology R G X q`
  is Worker 13's `q`-th cohomology of the compactly supported global sections
  of Worker 61's equivariant Godement complex
  (`Langlands.Sheaf.Equivariant.Godement.complexFunctor`), as an object of
  Mathlib's `Rep R G`. It is applied to equivariant sheaves, so the third
  proposition applies it to `smoothInclusion` of the terms. The equivariant
  Godement complex is a different construction from the smooth one: no
  smooth part is taken. Worker 61's published `underlyingComplexIso`, in
  `Langlands.Sheaf.Equivariant.Godement.Underlying`, shows that after
  forgetting the action it is the ordinary Godement complex over the points
  of `X`. This module does not import that comparison.
- `Langlands.Cohomology.SmoothSheafCohomology.compactDerived R G X q` is Worker
  13's `q`-th right derived functor, Mathlib's `Functor.rightDerived`, of
  `smoothSheafCompactSections R G X`. That functor sends a smooth sheaf to its
  compactly supported global sections, as an object of the published abelian
  category `Langlands.SmoothRep R G` of smooth representations. The support of
  a global section is the set of points where its germ is nonzero.

## The four propositions

| Declaration | Asserted conclusion |
| --- | --- |
| `SmoothGodementZeroExactStatement R G X` | `smoothZeroFunctor R G X` is additive (`Functor.Additive`), preserves finite limits and preserves finite colimits. |
| `SmoothGodementTermExactStatement R G X` | For every `m : ℕ`, the functor `CokernelComplex.term (smoothZeroFunctor R G X) (smoothCoaugmentation R G X) m` is additive, preserves finite limits and preserves finite colimits. |
| `SmoothGodementCompactAcyclicStatement R G X` | For every `F : SmoothTopologicalSheaf R G X` and all `m q : ℕ`, `(compactCohomology R G X (q + 1)).obj ((smoothInclusion R G X).obj ((smoothComplex R G X F).X m))` is a zero object of `Rep R G`. |
| `SmoothGodementCompactDerivedAcyclicStatement R G X` | For every `F : SmoothTopologicalSheaf R G X` and all `m q : ℕ`, `(compactDerived R G X (q + 1)).obj ((smoothComplex R G X F).X m)` is a zero object of `SmoothRep R G`. |

`SmoothGodementStatements R G X` is the conjunction of the four, in this
order. All hypotheses are explicit binders, so they appear in the types.

Remarks on what is asserted:

- Exactness of an additive functor between abelian categories is expressed by
  preservation of finite limits and finite colimits, as in the published
  `Langlands.Sheaf.Godement.ModuleZeroFunctorExactnessStatement`.
- No conjunct of the first proposition is supplied by instances. Worker 61
  publishes additivity of `smoothForget` and `smoothCoinduction`, but not of
  `Z` or of the composite, and no exactness. The print check below confirms
  that instance search finds none of `Additive`, `PreservesFiniteLimits` and
  `PreservesFiniteColimits` for `smoothZeroFunctor R G X`.
- `term _ _ 0` is `smoothZeroFunctor R G X` by definition, so the case
  `m = 0` of the second proposition is the first. The published
  `Langlands.Cohomology.CokernelResolutionFunctorExactnessStatement`, an
  unproved statement, would derive the second proposition from the first,
  because the coaugmentation is monic. Both are stated here so that the
  higher terms do not depend on that statement.
- The third proposition concerns the underlying equivariant sheaves of the
  terms. The fourth concerns derived functors computed in the smooth
  category. Neither is derived from the other in Lean.

## Why the statements are expected to hold

This argument is derived here. It follows the shape of Berkovich's proof (see
the source correspondence), on the ordinary open-set site. Fix a smooth sheaf
`M` and write `N = smoothForget M` and `N_y` for its stalk at `y`. Write
`D(M) = smoothZeroFunctor M`.

Step 0: sections of `D(M)`. The sections of `Z(N)` over an open `U` are the
families `(e_y)_{y ∈ U}` with `e_y ∈ N_y`. Worker 61's `Coinduction.md`
records that the sections of the coinduction of an ordinary sheaf `P` over
`U` are the product of the sections of `P` over the translates `g⁻¹ • U`,
`g ∈ G`; that description is not constructed in Lean. It comes from the right
Kan extension: the comma category over `U` splits into one component for each
`g`, consisting of the ordinary opens contained in `g⁻¹ • U`, and `g⁻¹ • U` is
terminal in it. So a section of the coinduction of `Z(N)` over `U` is a family
of entries `e_{g,y} ∈ N_y`, one for each pair `(g, y)` with `g • y ∈ U`.
Restriction to a smaller open drops entries. An element `h` of `G` carries
sections over `U` to sections over `h • U` by moving the entry at `(g, y)` to
`(h g, y)` without changing it. (With the opposite convention for transport
arrows, `h` is replaced by `h⁻¹`. The argument below uses only that `h` acts
on the index `g` by multiplication, hence freely, and does not change
entries.) Grouping the entries by the point `x = g • y`, the action moves the
entries at `x` to the point `h • x`. Worker 13's `smoothCoreflector` keeps the
sections that are locally fixed at every point. So the sections of `D(M)`
over `U` are the families of entries over `U` that are locally fixed at every
point of `U`.

Let `V` be an open stabilized by an open subgroup `H`, so `H • V = V`. A
section over `V` is fixed by `H` exactly when `e_{h g, y} = e_{g, y}` for all
`h ∈ H`. The index `(h g, y)` belongs to `V` exactly when `(g, y)` does,
because `h⁻¹ • V = V`. Choose one representative `g` in each coset `H g`.
Since `H` acts freely on the index `g`, the `H`-fixed sections over `V` are in
bijection with arbitrary families of entries at the indices `(g, y)` with `g`
a representative and `g • y ∈ V`. Every `H`-fixed section over `V` is locally
fixed at every point of `V`, with witnesses `V` and `H`, so it is a section of
`D(M)`.

Step 1: the first proposition.

- Additivity. `smoothForget` and `smoothCoinduction` are additive (Worker 61's
  instances). `Z` is a product of composites of stalk functors and skyscraper
  functors, which are additive. So the composite is additive.
- Finite limits. `smoothInclusion` preserves kernels, which are those of the
  ambient category, and finite biproducts, since it is additive. `toSheaf`
  preserves limits (the published
  `Langlands.Sheaf.Equivariant.toSheaf_preservesLimitsOfShape`). Stalk
  functors of sheaves of modules preserve finite limits, because filtered
  colimits of modules are exact. Skyscraper functors are right adjoints, and
  products preserve limits. So `Z` preserves finite limits.
  `smoothCoinduction` is a right adjoint. Hence `D` preserves finite limits.
- Epimorphisms. Let `f : M ⟶ M'` be an epimorphism of smooth sheaves.
  `smoothInclusion` preserves epimorphisms (Worker 13's
  `smoothInclusion_preservesEpimorphisms`), and `toSheaf` is a left adjoint
  (Worker 61's `coinductionAdjunction`). So `smoothForget f` is an
  epimorphism of sheaves of modules, and every stalk map
  `f_y : N_y ⟶ N'_y` is surjective. Let `s` be a section of `D(M')` over `U`
  and `x ∈ U`. Since `s` is locally fixed at `x`, there are an open `V` with
  `x ∈ V ⊆ U` and an open subgroup `H` stabilizing `V` and fixing `s` on `V`.
  By step 0, lift the entries of `s|_V` at the representative indices through
  the surjections `f_y`, and extend the lift so that it is `H`-fixed. The
  result is a section `t` of `D(M)` over `V`. `D(f)` acts on entries by the
  maps `f_y`, so it sends `t` to `s|_V`. Hence the underlying morphism of
  sheaves of `D(f)` is locally surjective, so it is an epimorphism. Faithful
  functors reflect epimorphisms, so `D(f)` is an epimorphism of smooth
  sheaves.
- An additive functor between abelian categories that preserves finite
  limits and epimorphisms sends short exact sequences to short exact
  sequences. It therefore preserves cokernels: factor a morphism through its
  image. It preserves finite coproducts, which are biproducts. So it
  preserves finite colimits.

Step 2: the second proposition. `residual 0` is the identity. Suppose
`residual n` is additive and exact. Then so is
`term n = residual n ⋙ D`, by step 1. At every object the sequence
`residual n ⟶ term n ⟶ residual (n + 1)` is short exact, because the
coaugmentation is monic and the second map is its cokernel. Apply the three
functors to a short exact sequence of smooth sheaves. The rows of the
resulting three-by-three diagram are short exact, and so are its first two
columns. By the nine lemma, the third column is short exact. So
`residual (n + 1)`, a cokernel of additive functors, is additive and exact,
and so is `term (n + 1)`. This is the induction in the proof of SGA 4 XVII
4.2.3(ii), as recorded for the published
`CokernelResolutionFunctorExactnessStatement`.

Step 3: `D(M)` is `c`-soft. The acyclicity facts are from Grothendieck's
Tohoku paper, §3.3, printed pp.158-160, for sheaves of abelian groups.
Forgetting the `R`-module structure and the action commutes with the
constructions used.

- p.158, Lemma 3.3.1 and its Corollary: let `F` be a functor from an abelian
  category with enough injectives. If a class `M` of objects satisfies
  conditions (i)-(iii) of the lemma, then `R^p F(A) = 0` for `p > 0` and
  `A ∈ M`. Condition (i): every object embeds in a member of `M`. Condition
  (ii): direct summands of members are members. Condition (iii): in a short
  exact sequence `0 → M' → M → M'' → 0` with `M'` and `M` in `M`, also `M''`
  is in `M` and `0 → F(M') → F(M) → F(M'') → 0` is exact.
- p.159: a sheaf `F` is `Φ`-soft (`Φ-mou`) if every section of `F` over a
  member of `Φ` is induced by a section in `Γ_Φ(F)`. `Φ` is paracompactifying
  if every member is paracompact and has a neighbourhood in `Φ`. A section
  over a closed set with a paracompact neighbourhood extends to an open
  neighbourhood of that set.
- p.159, Proposition 3.3.2 and its Corollary: if `Φ` is paracompactifying,
  the `Φ`-soft sheaves satisfy the conditions of Lemma 3.3.1 for `Γ_Φ`, and
  `H^p_Φ(X, F) = 0` for `p > 0` when `F` is `Φ`-soft.
- p.160: the canonical resolution `C^•(F)`, Godement's, has `C⁰(F)` equal to
  the product of the stalks of `F` and `Cⁿ(F) = C⁰(Cⁿ⁻¹(F)/Im Cⁿ⁻²(F))`, and
  `H^n_Φ(X, F) = H^n(Γ_Φ C^•(F))` for every `Φ`.

Let `c` be the family of compact subsets of `X`. On a locally compact
Hausdorff space it is paracompactifying: compact sets are closed, finite
unions and closed subsets of compact sets are compact, compact Hausdorff
spaces are paracompact, and every compact set has a compact neighbourhood.
So `Γ_c = Γ_Φ` for `Φ = c`, and "`c`-soft" means `Φ`-soft for this `Φ`.

Let `t` be a section of `D(M)` over a compact set `K`. Since `K` has a
compact neighbourhood, `t` extends to a section, still written `t`, over an
open neighbourhood `W` of `K`. Since `X` is locally compact and Hausdorff,
there is an open `W₀` with `K ⊆ W₀` whose closure is compact and contained in
`W`. Each point `x` of `K` has an open neighbourhood `V_x ⊆ W` and an open
subgroup `H_x` stabilizing `V_x` and fixing `t` on `V_x`. By
`HasStableNeighbourhoods`, `x` has an open neighbourhood inside `V_x ∩ W₀`
stabilized by an open subgroup. Its intersection with `H_x` stabilizes it and
fixes `t` on it. So every point of `K` has an open neighbourhood contained in
`W₀`, stabilized by an open subgroup that fixes `t` on it. By compactness,
finitely many of them, `V_1, …, V_n` with subgroups `H_1, …, H_n`, cover `K`.
Then `H = ⋂ H_i` is an open subgroup that stabilizes `V = ⋃ V_i` and fixes `t`
on each `V_i`, hence on `V`. The closure of `V` lies in the closure of `W₀`,
so it is compact and contained in `W`. Let `t'` be the global family of
entries that agrees with `t` at the points of `V` and is zero elsewhere.
Check that `t'` is locally fixed at every point `y` of `X`:

- If `y ∈ V`, then `t'` agrees with `t` on `V`, and `H` fixes `t` on `V`.
- If `y` is outside the closure of `V`, then `t'` is zero on the open
  complement of that closure. By `HasStableNeighbourhoods`, `y` has an open
  neighbourhood inside this complement stabilized by an open subgroup, which
  fixes the zero family.
- Otherwise `y` lies in the closure of `V` but not in `V`. Then `y ∈ W`.
  Since `t` is a section of `D(M)` over `W`, there are an open `V'` with
  `y ∈ V' ⊆ W` and an open subgroup `H'` stabilizing `V'` and fixing `t` on
  `V'`. Every `h ∈ H' ∩ H` stabilizes `V' ∩ V` and `V' ∖ V`, and moves the
  entries at a point `x` to the point `h • x`. On `V' ∩ V` the family `t'` is
  `t`, which `h` fixes. On `V' ∖ V` it is zero. So `h` fixes `t'` on `V'`.

Hence `t'` is a global section of `D(M)`. Its support lies in the closure of
`V`, which is compact, and it agrees with `t` near `K`. So `D(M)` is
`c`-soft. Only the shape of `Z(N)` was used, so this holds for every smooth
`M`.

Step 4: the third proposition. The degree-`m` term of the smooth Godement
complex of `F` is `D` of the smooth sheaf `(residual _ _ m).obj F`. By step 3
its underlying sheaf of abelian groups is `c`-soft. By Proposition 3.3.2 and
its Corollary, its compactly supported cohomology vanishes in positive
degrees. By p.160 and Worker 61's `underlyingComplexIso`, the module
underlying `compactCohomology R G X p` of an equivariant sheaf is the
compactly supported cohomology `H^p_c(X, -)` of its underlying sheaf. A
representation with zero underlying module is a zero object of `Rep R G`.

Step 5: the fourth proposition. Apply Lemma 3.3.1 to the abelian category of
smooth sheaves, which has enough injectives, the functor
`smoothSheafCompactSections R G X`, and the class `M` of smooth sheaves whose
underlying sheaf of abelian groups is `c`-soft. Smooth representations form
a full subcategory of `Rep R G` closed under subrepresentations and
quotients, so exactness in `SmoothRep R G` can be checked on underlying
modules. Through Worker 13's `smoothSheafCompactSectionsToRepIso`, the module
underlying the compact sections of a smooth sheaf is `Γ_c` of its underlying
sheaf.

- (i): every smooth sheaf embeds in `D` of itself by the monic
  coaugmentation, and `D` of it is in `M` by step 3.
- (ii): a direct summand of a `c`-soft sheaf is `c`-soft. Extend a section of
  the summand over `K` as a section of the big sheaf with compact support,
  and project it back; the projection does not enlarge supports.
- (iii): `smoothInclusion` preserves kernels and cokernels, and `toSheaf`
  preserves limits and, as a left adjoint, colimits. So a short exact
  sequence of smooth sheaves gives a short exact sequence of underlying
  sheaves of abelian groups. Proposition 3.3.2, case 2, gives (iii) for
  `Γ_c` there.

The lemma gives `R^p F(A) = 0` for `p > 0` and `A ∈ M`. Its proof computes
`R^p F` with injective resolutions, as Mathlib's `Functor.rightDerived` does.
Every term of the smooth Godement complex is in `M` by step 3, so
`compactDerived R G X (q + 1)` vanishes on it. This step does not use Worker
3's comparison candidate `Langlands.Cohomology.SmoothCompactComparison`,
which this module does not import.

## Provenance

Harris, *Galois properties of cohomological automorphic forms on GL(n)*, J.
Math. Kyoto Univ. 39-2 (1999), section 2, printed p.304, writes: "In
Proposition 1.4.1 of [B4], Berkovich shows how to construct an acyclic
resolution of a finite ℓ-torsion sheaf `T` on `U(ẽ)` by a complex of smooth
`S(ẽ)`-modules. Here "smooth" means that every element is stabilized by an
open subgroup of `S(ẽ)`." The construction "is a smooth `G`-equivariant
version of the Godement flasque resolution." Further down the page:

- "For any étale sheaf `T` in smooth `ℤ/ℓ^m ℤ[S(ẽ)]`-modules over `U(ẽ)`,
  Berkovich constructs an embedding `T → F(T)`, where `F(T)` is again an
  étale sheaf in smooth `ℤ/ℓ^m ℤ[S(ẽ)]`-modules over `U(ẽ)`, and which is
  acyclic for the functor `RΓ_c`: `H^q_c(U(ẽ)_F̄, F(T)) = 0` for `q > 0`. The
  construction is functorial in `T`."
- "Fact 3. The functor `T → F(T)` is exact."
- "The functor `F(T)` is expressed as the composition of two functors,
  denoted `𝒞⁰ = ν_*ν^*` and `b^*` by Berkovich, who verifies that both
  functors are exact. This gives another derivation of Fact 3."

In the registered Berkovich manuscript, 1.4.1 is a definition (of
quasi-étale and étale `G`-sheaves). The Godement resolution is in §1.5 and
the softness result is Proposition 1.5.1. So the numbering of the version
Harris cites ([B4]) differs from the registered one.

The four propositions transcribe these claims to the ordinary open-set site
of a topological space:

- Worker 61's `Smooth.md` explains why `smoothZeroFunctor` is the
  counterpart of `ν_*ν^*`: points of `X` replace geometric points, and the
  right adjoint of forgetting replaces `ν_*`. Smooth sheaves are modelled
  directly on `X`, so Berkovich's `b^*` is implicit. Harris's `F(T)`
  therefore corresponds to `D(T) = smoothZeroFunctor T`, and his embedding to
  `smoothCoaugmentation`.
- Fact 3 becomes `SmoothGodementZeroExactStatement`. Berkovich's property
  (ii), exactness of `F ↦ C^m(F)` for every `m`, becomes
  `SmoothGodementTermExactStatement`.
- Harris's `H^q_c(U(ẽ)_F̄, F(T)) = 0` is cohomology of the underlying sheaf,
  without invariants, so it becomes the case `m = 0` of
  `SmoothGodementCompactAcyclicStatement`, with `compactCohomology` of the
  underlying equivariant sheaf. Berkovich's Proposition 1.5.1 gives softness
  of `b^*C^m(F)` for every `m`, so the proposition is stated for every term.
- `SmoothGodementCompactDerivedAcyclicStatement` is the acyclicity of the
  terms for the derived functors of compact sections in the smooth category.
  Berkovich's proof of Corollary 1.5.2 uses it implicitly ("the general case
  follows from Proposition 1.5.1"). It is derived here; Worker 61 suggested
  stating it.
- `HasStableNeighbourhoods` stands in for the Key Lemma of Berkovich §1.4,
  which supplies neighbourhoods stabilized by open subgroups on analytic
  spaces. The coefficients are an arbitrary commutative ring, not
  `ℤ/ℓ^m ℤ`; no torsion hypothesis is needed for these statements.

## Original-source correspondence

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces*, unfinished
1995-1996 manuscript. The printed page numbers equal the PDF page numbers.

- §1.5, p.10: "We recall the construction of the Godement resolution from
  [SGA4], Exp. XVII, §4.2, adopted to the étale site of `X(G)`":
  `C⁰(F) = ν_*ν^*(F)` with the adjunction morphism `d⁻¹ : F → C⁰(F)`, and
  `C^{m+1}(F) = C⁰(Coker d^{m-1})`. "By loc. cit., 4.2.3, one has: (i)
  `C^m(F)` is a flabby sheaf; (ii) the functor `F ↦ C^m(F)` is exact; (iii)
  the fibre of the complex `C^•(F)` at a point `x ∈ X` is a canonically split
  resolution of `F_x`." Worker 61's `smoothComplex` is the counterpart of
  `C^•(F)`; the published cokernel complex has the same recursion.
- Proposition 1.5.1, p.10, with its proof on pp.10-11: "For any
  `F ∈ X(G)~_ét` and `m ≥ 0`, `b^*(C^m(F))` is a soft sheaf on `X_ét`." The
  proof reduces to `m = 0` and to two facts: (1') vanishing of Galois
  cohomology of the stalks, and (2') softness of the restriction to the usual
  topology. The proof of (2') extends a section over a compact set to a
  neighbourhood, shrinks it and replaces `G` by a small open subgroup so that
  the neighbourhood is `G`-invariant, and then extends from the discrete index
  set. Step 3 is the counterpart of (2'). Fact (1') has no counterpart on the
  ordinary site.
- Proof of Corollary 1.5.2, p.12: "The case `q = 0` in (i) ... follows from
  the fact that every element of `H^0_c(X, b^*F)` is fixed by an open
  subgroup of `G` ..., and therefore the general case follows from
  Proposition 1.5.1."

| Source | Original statement | Lean component |
| --- | --- | --- |
| Harris 1999, p.304, Fact 3; Berkovich §1.5 (ii), p.10, case `m = 0` | `T ↦ F(T)` is exact. | `SmoothGodementZeroExactStatement` |
| Berkovich §1.5 (ii), p.10 | `F ↦ C^m(F)` is exact. | `SmoothGodementTermExactStatement` |
| Harris 1999, p.304; Berkovich Prop. 1.5.1, p.10 | `H^q_c(U(ẽ)_F̄, F(T)) = 0` for `q > 0`; `b^*(C^m(F))` is soft. | `SmoothGodementCompactAcyclicStatement` |
| Derived here; used in Berkovich's proof of Cor. 1.5.2, p.12 | (The terms are acyclic for the derived functors of compactly supported smooth sections.) | `SmoothGodementCompactDerivedAcyclicStatement` |

## Scope

- Fact 4 of Harris, on `ℓ`-divisible systems, and his Lemma 2.2, which
  iterates the construction for `ℤ/ℓ^m ℤ`, are not stated.
- Acyclicity for Worker 13's invariant derived functors
  (`invariantCompactDerived`) is not stated; no consulted source states it.
- Berkovich's properties (i), flabbiness, and (iii), split fibres, are not
  stated.
- Exactness of the smooth Godement complex, that is, that the augmentation
  is a quasi-isomorphism, is not restated. It is an instance of the published
  `Langlands.Cohomology.CokernelResolutionStatement`, because the
  coaugmentation is monic.
- Softness appears only in the truth argument. No `c`-softness predicate for
  equivariant sheaves is published.
- The site is the ordinary open-set site of a topological space, not
  Berkovich's étale site of an analytic space. Analytic spaces, `X(G)`,
  `U(ẽ)` and the base change to `F̄` are not formalized here.
- `R`, `G` and `X` share one universe, as in the published construction and
  cohomology functors.

## Registered sources

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`: Harris 1999,
  PDF SHA-256
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`;
  section 2, printed p.304 (PDF p.6), read on the rendered scan.
- `provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`:
  Berkovich manuscript, folder SHA-256
  `e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`, member
  `Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
  SHA-256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`;
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

SGA 4 XVII 4.2.3 is cited by Berkovich for (i)-(iii). Its three-by-three
induction is cited here only through the published
`CokernelResolutionFunctorExactnessStatement` and its Markdown.

## Formal dependencies and checks

The direct project imports are byte-identical in Library commits
`01a58491bc71539f1ecd3d5f0eec6ab8eae20fed` and
`e3c2fa98be720f63c6981efbbdf15cd223329e76`:

| Module | Author | Lean SHA-256 | Markdown SHA-256 |
| --- | --- | --- | --- |
| `Langlands.Sheaf.Equivariant.Godement.Smooth` | Worker 61 | `c87bbf5eef53c9d4b6e1b2c9d30f834d14533f3e963b489a2fa96ccd7c1e37cc` | `a8303728c0bb25e91640fc14d1e29ca1301612d40414147d938f477710e26dda` |
| `Langlands.Cohomology.SmoothSheafCohomology` | Worker 13 | `f1365e1fcf6064dbbc6bacd8491c16ce24fe3a76215dc606adc263032be3c7d1` | `8e14762c1b9488273aae24c89c1f7bfce0f5f3001cc7b09cd250edd79206d02d` |
| `Langlands.Cohomology.EquivariantGodementCohomology` | Worker 13 | `d8e9978c4ff9fe11a14d39f62f186f9de896125332b12d55f086d451fa5035b2` | `7d4af4966241481da61efb6fbf53fb0bb9e52b89c8805af6eb1d47576a38d1ae` |

From the first the module uses `smoothZeroFunctor`, `smoothCoaugmentation`
and `smoothComplex`, and through it the published
`Langlands.Cohomology.CokernelComplex.term` (Lean SHA-256
`0f034f1d42a5f8d3c72f47635ad6bea750b94e1cf8c20f5b54e2d0514dac2f11`). From the
second it uses `compactDerived`, and from the third `compactCohomology`.
Through these imports it also uses Worker 13's `SmoothTopologicalSheaf`,
`smoothInclusion`, `HasStableNeighbourhoods` and the abelian structure of
`Langlands.Sheaf.Equivariant.SmoothAbelian`.

The environment is `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0,
Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`.

Checks `f04f0584-e6b8-4bf1-b563-5ee39d34c9b9` (from a draft directory) and
`9a21091f-8ae1-4209-be5a-6b9644ee9a97` (from the workspace, against Library
`e3c2fa98`) built this module with Lake against the published imports, with
no errors or warnings. The Lean file is unchanged since the first check. Each
inspected `SmoothGodementStatements` as a `Prop`-valued definition with the
single universe parameter `u`, depending only on `propext`,
`Classical.choice` and `Quot.sound`. Check
`79dd20f2-5636-4ead-a8ae-6ac0d61b2355` compiled a test file against the
module, with no errors or warnings, and its output was read. It printed the
five definitions with universes shown, the axioms of the conjunction, and the
types of `smoothZeroFunctor`, `smoothCoaugmentation`, `smoothComplex`,
`CokernelComplex.term`, `compactDerived` and `compactCohomology`. The prints
show:

- all five definitions carry `IsTopologicalGroup G`, `MulAction G X`,
  `ContinuousConstSMul G X` and `HasStableNeighbourhoods G X` as explicit
  instance binders;
- the two exactness propositions have no `T2Space X` or
  `LocallyCompactSpace X` binder, while the two acyclicity propositions and
  the conjunction carry both;
- `R`, `G` and `X` all live in the universe `u`;
- the bodies are exactly the conclusions listed in the table above.

The same test file checks by `rfl` that `(smoothComplex R G X F).X m` is
`smoothZeroFunctor R G X` applied to the `m`-th residual object of `F`, and
that `term _ _ 0` is `smoothZeroFunctor R G X`. Three `fail_if_success`
probes confirm that instance search finds none of `Additive`,
`PreservesFiniteLimits` and `PreservesFiniteColimits` for
`smoothZeroFunctor R G X`, so no conjunct of the first proposition is
supplied by an instance. The file also elaborates `SmoothGodementStatements
ℚ G X` for an arbitrary topological group acting on a locally compact
Hausdorff space with `HasStableNeighbourhoods`, for discrete `G`, for
nonarchimedean `G` acting continuously (the instance is then found), and for
the trivial group acting on a point. This shows only that the statements are
well formed there.

Compilation and inspection establish well-formed statements; they do not
prove any component.
