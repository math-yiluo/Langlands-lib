# Irreducible admissible components and Whittaker functionals at infinite places

Lean module: `Langlands.Automorphic.CuspidalArchimedeanPlaceComponent`.

This module states the two global facts about cuspidal automorphic representations of
`GL_n` over a number field `F` that produce, at each infinite place `v`, an irreducible
admissible generic `(𝔤_v, K_v)`-module inside an actual cuspidal realization:

1. the realization contains an irreducible admissible `(𝔤_v, K_v)`-submodule (its local
   component at `v`), and
2. every nonzero `(𝔤_v, K_v)`-stable subspace of a cuspidal realization carries a Whittaker
   functional for a nondegenerate character of the upper triangular nilpotent Lie algebra.

Both are stated as `Prop`-valued definitions and **neither is proved here**. The module
also defines the subspace predicates they use. Together with the fact that the place
actions restricted to a stable subspace satisfy the axioms of a `(𝔤, K)`-module, the two
statements give the global premise `CuspidalArchimedeanGenericComponentStatement` of the
reduction in `Langlands.Automorphic.ArchimedeanParameterReduction` (a separate candidate
of Task 5720, not imported here); that derivation is not part of this module either.

## Setting

For an actual operator realization `S : OperatorRealization F n` the Library defines, at a
real place `v` (`v : {v : NumberField.InfinitePlace F // v.IsReal}`):

* `S.realPlaceCompactRepresentation v : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) S.Space`,
  the action of `K_v = O(n)` by right translation in the `v`-component
  (`Langlands.Automorphic.PlaceCompactAction`);
* `S.realPlaceLieAction v : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ S.Space`,
  the complexified right-derivative action of `𝔤𝔩_n(F_v) = 𝔤𝔩_n(ℝ)`
  (`Langlands.Automorphic.PlaceLieAction`);

and at a complex place the analogues `complexPlaceCompactRepresentation` (for
`K_v = U(n)`) and `complexPlaceLieAction` (for `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`, `𝔤𝔩_n(ℂ)` regarded as a
real Lie algebra), with `F_v` identified with `ℂ` as in those modules. An actual cuspidal
realization `T : CuspidalOperatorRealization F r` is an operator realization of
`GL_{r+1}` that is irreducible for the full operator algebra and cuspidal
(`Langlands.Automorphic.CuspidalOperatorRealization`).

## Definitions (namespace `Langlands.Automorphic.PlaceComponent`)

Throughout, `K` is a group acting on a complex vector space `V` by `κ`, and `𝔤` is a complex
Lie algebra acting on `V` by `π`. These are abstract versions of the place actions above.

* `IsStable κ π W`: the subspace `W` is mapped into itself by every `κ k` and every `π X`,
  i.e. `W` is a `(𝔤, K)`-submodule.
* `IsIrreducible κ π W`: `W ≠ 0`, `W` is stable, and every stable subspace `W' ≤ W` is
  `0` or `W`. This is irreducibility of the `(𝔤, K)`-module `W` (Getz–Hahn 2024, p. 116).
* `intertwiners κ W d τ`: for a matrix representation `τ : K →* Matrix (Fin d) (Fin d) ℂ`,
  the complex subspace of linear maps `T : ℂ^d → V` with values in `W` such that
  `T (τ k x) = κ k (T x)` for all `k` and `x`, i.e. `Hom_K(τ, W)`. The lemma
  `mem_intertwiners` unfolds membership.
* `IsAdmissible κ W` (for a topological group `K`): for every continuous `d`-dimensional
  matrix representation `τ` of `K`, `Hom_K(τ, W)` is finite-dimensional. For a compact
  group, whose continuous finite-dimensional representations are sums of irreducible ones,
  this says that every irreducible continuous representation of `K` occurs in `W` with
  finite multiplicity, i.e. that every `K`-isotypic component of `W` is finite-dimensional:
  admissibility of a `(𝔤, K)`-module (Getz–Hahn, Definition 4.4.4 and p. 116). This is the
  same formulation as `Langlands.Archimedean.IsAdmissibleGKModule` in the companion
  candidate, applied to `W`.
* `IsRealWhittakerFunctional π W a ℓ` (`π` a Lie action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`,
  `a : Fin n → ℝ`, `ℓ : V →ₗ[ℂ] ℂ`): for every strictly upper triangular real matrix `X`
  (`X i j = 0` whenever `j ≤ i`) and every `x ∈ W`,
  `ℓ (π (1 ⊗ X) x) = (i · ∑_{i} a_i X_{i,i+1}) · ℓ x`.
  Here `X ↦ i ∑ a_i X_{i,i+1}` is the differential of the character
  `u ↦ exp(i ∑ a_i u_{i,i+1})` of the upper unipotent group `N_n(ℝ)`. The Lean sum runs over
  all pairs `(i, j)` with `j = i + 1`, so only `a_0, …, a_{n-2}` enter.
* `IsComplexWhittakerFunctional π W a ℓ` (`π` a Lie action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℂ)`,
  `a : Fin n → ℂ`): for every strictly upper triangular complex matrix `X`, used as the real
  direction `1 ⊗ X`, and every `x ∈ W`,
  `ℓ (π (1 ⊗ X) x) = (i · Re(∑_i a_i X_{i,i+1})) · ℓ x`, the differential of the unitary
  character `u ↦ exp(i Re(∑ a_i u_{i,i+1}))` of `N_n(ℂ)`. Every unitary character of `N_n(ℂ)`
  trivial on the commutator subgroup has this form, since every real-linear functional
  `ℂ → ℝ` is `z ↦ Re(a z)`.
* `IsRealGeneric π W` / `IsComplexGeneric π W`: there are coefficients `a` with
  `a_i ≠ 0` for every `i` with `i + 1 < n` (a nondegenerate, i.e. generic, character in the
  sense of Getz–Hahn, Definition 11.2.1 and Example 11.1) and a linear functional `ℓ` on all
  of `V` that is nonzero at some vector of `W` and is a Whittaker functional on `W` for `a`.
  Restricted to `W` this is a nonzero algebraic Whittaker functional on the
  `(𝔤, K)`-module `W`, the infinitesimal `K`-finite form of a `ψ`-Whittaker functional
  (Getz–Hahn, Definitions 11.3.2–11.3.3). The functional is only required to transform
  correctly on `W`; its values outside `W` play no role. The genericity condition is
  existential over all nondegenerate characters, as in the companion predicates
  `IsRealGenericGKModule` / `IsComplexGenericGKModule`, which use the same formulas.

## Statements

### `CuspidalArchimedeanIrreducibleAdmissibleComponentStatement.{u}`

For every number field `F : Type u` with compact adele quotient `AdeleQuotient F`, every
`r : ℕ` and every actual cuspidal realization `T : CuspidalOperatorRealization F r`:

* for every real place `v` there is a subspace `W` of `T.realization.Space` that is
  irreducible for the pair (`realPlaceCompactRepresentation v`, `realPlaceLieAction v`) and
  admissible for `realPlaceCompactRepresentation v`;
* for every complex place `v` there is a subspace `W` that is irreducible for
  (`complexPlaceCompactRepresentation v`, `complexPlaceLieAction v`) and admissible for
  `complexPlaceCompactRepresentation v`.

Source. A cuspidal automorphic representation is an irreducible admissible
`(𝔤, K_∞) × G(𝔸^∞)`-module and factors as a restricted tensor product
`⊗_v π_v` whose archimedean factors `π_v` are irreducible admissible `(𝔤_v, K_v)`-modules
(Getz–Hahn, Definition 6.3.5, Lemma 6.3.6 and Theorem 6.3.7, pp. 165–166, which rests on
Flath's theorem, Getz–Hahn Theorem 5.7.1). Fixing a nonzero vector `φ^v` of the tensor
product of the other factors, the image of `V_v ⊗ φ^v` is a subspace of the realization,
stable under the actions at `v` and isomorphic to `π_v`; this is the subspace `W` of the
statement. The hypothesis that the adele quotient is compact is the standing hypothesis of
the Library's constant terms and cuspidality.

### `CuspidalArchimedeanWhittakerFunctionalStatement.{u}`

For every number field `F : Type u` with compact adele quotient, every `r : ℕ` and every
actual operator realization `S : OperatorRealization F (r + 1)` with `S.IsCuspidal`:

* for every real place `v` and every nonzero subspace `W` of `S.Space` stable under
  (`realPlaceCompactRepresentation v`, `realPlaceLieAction v`), `IsRealGeneric
  (S.realPlaceLieAction v) W` holds;
* for every complex place `v` and every nonzero subspace `W` stable under
  (`complexPlaceCompactRepresentation v`, `complexPlaceLieAction v`),
  `IsComplexGeneric (S.complexPlaceLieAction v) W` holds.

Source. Every cusp form `φ ≠ 0` on `GL_n` has a nonvanishing global `ψ`-Whittaker function
`W_φ` (an integral of `n ↦ φ(n g)` against the character `ψ` over `[N]`, Getz–Hahn (11.6))
for a generic character `ψ` of `N(𝔸)` trivial on `N(F)`, because of the Whittaker expansion
`φ(g) = ∑_γ W_φ((γ, 1) g)`
(Getz–Hahn, (11.6) and Theorem 11.3.6, pp. 297–298), and the local components of a
globally generic representation are generic (Getz–Hahn, p. 297 and Exercise 11.3). In the
form used here: pick `φ ∈ W` nonzero and `g` with `W_φ(g) ≠ 0`; by the Iwasawa
decomposition `g_v = b k` with `b` upper triangular and `k ∈ K_v`, and since `W` is
`K_v`-stable one may replace `φ` by its right translate by `k` and assume `g_v = b`. Then
`ℓ(f) := W_f(g)` is a linear functional, nonzero at `φ`, and for `X ∈ 𝔫_v` the derivative
of `t ↦ W_f(g exp(tX))` gives `ℓ(π(X) f) = dψ_v(Ad(b) X) ℓ(f)`, the differential of a
nondegenerate character because conjugation by the torus part of `b` rescales the simple
root coordinates by nonzero factors.

## Provenance

Derived. The subspace predicates are the `(𝔤, K)`-module notions of Getz–Hahn
(Definitions 4.4.4, 4.4.6 and p. 116) and the infinitesimal form of the Whittaker
functionals of Definitions 11.2.1 and 11.3.2–11.3.3, phrased for subspaces of a realization
so that the two statements need no abstract module; the formulas agree with the companion
predicates in `Langlands.Representation.Archimedean.GKModule`. The two statements are the
archimedean parts of the factorization theorem (Theorem 6.3.7) and of global genericity of
cuspidal representations of `GL_n` (Theorem 11.3.6 with Exercise 11.3), restated for the
Library's actual realizations and place actions. They are split so that the irreducible
component (statement 1) and the Whittaker functional (statement 2, for an arbitrary stable
subspace) can be proved independently.
