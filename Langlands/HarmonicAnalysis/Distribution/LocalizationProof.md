# Localization of equivariant algebraic distributions

`Langlands.HarmonicAnalysis.Distribution.equivariantLocalization.{uX, uY, uI}`
proves the published `EquivariantLocalizationStatement.{uX, uY, uI}`.
The theorem has exactly that proposition as its type.

## Scope and conventions

The source space `X` is an arbitrary topological space. The base `Y` is
Hausdorff, locally compact and totally disconnected, and `q : X → Y` is
continuous. The three universes of `X`, `Y` and the indexing type `ι` remain
independent. The homeomorphisms `h i` preserve the fibres of `q`; their associated
scalars `χ i : ℂ` are arbitrary. No group law on the family, invertibility of
the scalars, or surjectivity of `q` is needed.

The Library's `Distribution X` is the entire algebraic complex dual of
`SchwartzBruhat X`. Pushforward satisfies
`pushforward (h i) T f = T (f ∘ h i)`. The fibre hypothesis is used precisely
as published: a functional is supported on the fibre over `y` when it kills
every test function that vanishes pointwise on that fibre. The proof introduces
no restriction maps, sheaves, measure factors, or continuity requirement on
functionals.

## Implemented proof

The private linear map `cutoff q hq hV` multiplies a test function by the
characteristic function of `q ⁻¹' V`, for a clopen subset `V` of `Y`. The result
is locally constant and has compact support because the original function does.
The set `V` itself need not be compact. Its evaluation is the original function
where `q x ∈ V` and zero elsewhere.

Let `N` be the complex linear span of all relations
`pullback (h i) g - χ i • g`. Fibre preservation implies that cutoff commutes
with pullback along `h i`. Thus cutoff sends each generator to another generator,
and span induction proves that `N` is stable under every such cutoff.

Fix a test function `f` and a base point `y`. Let `I` be the submodule of test
functions vanishing on the fibre over `y`. The proof shows that `f ∈ N ⊔ I`.
Otherwise Mathlib's `Submodule.exists_dual_map_eq_bot_of_notMem` provides an
algebraic functional `T` nonzero on `f` and zero on `N ⊔ I`. Its vanishing on
`I` gives the exact support premise in the fibre hypothesis. Its vanishing on
the generators of `N` gives every required pushforward equivariance identity.
The fibre hypothesis forces `T = 0`, contradicting its value on `f`.

Write `f = n + e` with `n ∈ N` and `e ∈ I`. The support of a locally constant
test function is clopen and compact, even on the arbitrary space `X`, by the
Library's `Hecke.TestFunction.isClopen_support` and `isCompact_support`.
Consequently `q '' support e` is compact, hence closed in `Y`, and misses `y`.
Mathlib's `loc_compact_Haus_tot_disc_of_zero_dim` supplies a clopen neighbourhood
`V` of `y` disjoint from that image. Cutting off `e` gives zero; cutting off
`f` therefore equals the cutoff of `n` and belongs to `N`.

The private lemma `mem_of_local_cutoffs` combines these local memberships.
Compactness of `q '' support f` selects finitely many of the clopen
neighbourhoods. Finite induction shows that the cutoff of `f` by their union
belongs to `N`, using the pointwise identity

```text
cutoff (U ∪ V) f = cutoff U f + cutoff V f - cutoff U (cutoff V f).
```

The final term belongs to `N` by cutoff stability. This proves the finite-cover
step without choosing disjoint refinements. Since the union covers the image
of the support of `f`, its cutoff is `f` itself. Every test function thus
belongs to `N`.

Finally, the given equivariant distribution `D` kills each relation, so
`N ≤ LinearMap.ker D`. It therefore vanishes on every test function, and linear
map extensionality gives `D = 0`. Empty fibres, empty spaces, and empty index
families require no separate cases.

## Provenance

This is an internal direct proof of the variant stated in the paired
`LocalizationStatement` documentation. Its algebraic localization route was
provided by Worker 33 in the task context; Worker 121 implemented the Lean proof
and the finite-union argument.

The original is I. N. Bernshtein and A. V. Zelevinskii, *Representations of the
group GL(n,F), where F is a non-Archimedean local field (survey)*,
Russian Mathematical Surveys 31:3 (1976), 1–68, registered as
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The relevant passages are Proposition 1.8 and Corollary 1.9 (printed pp. 7–8),
Proposition 2.36 and Corollary 2.37 (pp. 25–26), and the regular case of
Theorem 6.9 (p. 54). These pages were read for this proof.

The source proves localization for group actions on l-sheaves over l-spaces.
The published target instead uses algebraic functionals supported on fibres
and an arbitrary family of homeomorphisms with scalar equivariance, allowing
`X` to be any topological space. The implemented argument proves that exact
variant directly; it does not claim a formalization of the source's sheaf
machinery or of the full constructive-action theorem.
