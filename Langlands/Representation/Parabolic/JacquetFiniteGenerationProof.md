# Finite generation of normalized standard Jacquet modules

Author: Worker 319. The proof reuses the published representative calculation
and adapts the single-vector cover argument by Worker 238, credited as coauthor.

The theorem `Langlands.Parabolic.normalizedJacquetFiniteGeneration` has the
complete unapplied type
`Langlands.Parabolic.NormalizedJacquetFiniteGenerationStatement.{uF,uV}`.
It proves finite generation over the actual complex Levi group algebra of
the normalized standard Jacquet module of every smooth representation that
is finitely generated over the ambient complex group algebra.

The statement quantifies every prime, actual p-adic field and compatible
topological realization, every natural rank and standard block shape, and
every complex carrier in the independent universe `uV`. The proof adds no
hypotheses. Rank zero and the zero representation are included.

## Implemented proof

Write `q = B.jacquetMk ρ`, `J = T.normalizedJacquet B ρ`, and let `P` and
`M` be the actual standard parabolic and block Levi.

The published lemma
`Langlands.CuspidalSupport.QuasicuspidalEmbedding.jacquetMk_parabolic`
gives, for `a ∈ P`,

```text
q(ρ(a)v) = δ_P(a)^(1/2) • J(leviProjection(a))(q(v)).
```

It factors `a` as its actual `unipotentPart` times its embedded Levi
projection. The radical acts trivially on coinvariant classes. Rewriting
`normalizedJacquet_mk_eq_inv_halfModulus` cancels the half-modulus unit
against its inverse. Thus the formula respects the published inverse
upper half-modulus normalization; it does not change the Jacquet action.

The helper `JacquetFiniteGeneration.finite_of_compactQuotient` assumes
compactness of `P \ G` for its ambient group topology. From
`Module.Finite.fg_top`, it extracts a finite generating set `s` over `ℂ[G]`.
For each vector `v`, smoothness gives an open subgroup `K_v` fixing `v`.
`Induction.exists_finset_doubleCoset_cover` supplies a finite set `t_v`
with `G = P t_v K_v`. For `g = a i k` in this cover,
`ρ(k)v = v`, and the representative formula shows that `q(ρ(g)v)` belongs
to every Levi subrepresentation containing all `q(ρ(i)v)` for `i ∈ t_v`.

Let `y` be the finite union, over `v ∈ s`, of the vectors `q(ρ(i)v)` for
`i ∈ t_v`. Let `N` be its `ℂ[M]`-span, and let `S` be the corresponding
Levi subrepresentation, obtained by `Subrepresentation.ofSubmodule'`.
The preceding cover argument puts every `q(ρ(g)v)` with `v ∈ s` in `S`.

To use the original group-algebra generators directly, the proof constructs
the ambient subrepresentation

```text
C = {v | for every g ∈ G, q(ρ(g)v) belongs to S}.
```

Its underlying complex submodule is the intersection of the inverse images
of `S` under the linear maps `q ∘ ρ(g)`. It is invariant because
`ρ(a)(ρ(g)v) = ρ(a g)v`. It contains `s`, so `C.asSubmodule` contains
the entire `ℂ[G]`-span of `s`, hence every vector of the ambient carrier.
Taking `g = 1` and using surjectivity of `q` proves `N = ⊤`. The finite set
`y` therefore witnesses the required `Module.Finite` conclusion.

The closing theorem installs `T.topology` and the published topological
group structure. It discharges compactness using
`Langlands.Parabolic.parabolicQuotientCompact F T B`, which covers every
rank including zero, and applies the helper. Neither the generator argument
nor the compactness specialization requires a nonzero vector or a nonempty
generating set. No separate rank-zero or zero-carrier argument is needed.

## Provenance and scope

The original source is W. Casselman, *Introduction to the theory of admissible
representations of p-adic reductive groups*, draft of 1 May 1995,
Theorem 3.3.1 and its finite-generation proof, printed/PDF page 35. The
quotient and unnormalized action are in §3.2, printed/PDF pages 33–34.
These pages were read for this proof. The registered source is
`casselman-1995-admissible-representations`, SHA256
`78b921fc6331ad2b75389f37d15bd5ac3399e6cfc2d7555e1a4d666e0d42612a`,
retained at
`/home/taskhub/central-library/Casselman--p-adic groups lecture notes/Introduction to representations of p-adic groups/Casselman--Introduction to the theory of admissible representations of p-adic reductive groups--1995.pdf`.
No source-specific errata file was found in the project notes or literature.

Casselman's argument chooses one compact open subgroup fixing a finite
generating set. The implementation instead takes an open stabilizer and a
finite double-coset cover for each generator, then forms their finite union.
Compactness of `P \ G` is all that the cover argument needs. The treatment
of the scalar normalization is the explicit derived calculation above.

The proof directly reuses
`Langlands.CuspidalSupport.QuasicuspidalEmbedding.jacquetMk_parabolic` and
adapts the single-vector cover step from `exists_finset_generating` in the published
`Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`, by
Worker 238. The present proof imports that module, the quotient construction,
actual quotient compactness, finite double-coset cover theorem, and Mathlib's
subrepresentation/group-algebra correspondence.
The intersection subrepresentation and finite-union construction extend the
cyclic argument to arbitrary finite generation.

This proves only finite generation of ambient standard GL Jacquet modules.
It supplies no admissibility, finite-length, refined-Levi Jacquet, or induced
finite-generation result, and uses neither `InducedFiniteTypeStatement` nor
`GLAdmissibleFiniteLengthStatement`. The target pair and its import closure
are unchanged.
