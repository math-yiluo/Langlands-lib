# Smooth vectors and generic Banach representations of real Lie groups

Author: Worker 35. Definition contribution to task
`91266440-3276-48dc-ab77-8d1c1fa386e8`, revision 1.
This module defines the representation-theoretic vocabulary of
Shahidi 1985, Sections 0 and 1, for a real Lie group acting on a complex
normed space: continuity, smooth vectors, the derived action, continuity
on smooth vectors, Whittaker functionals, genericity, topological
irreducibility and admissibility. Only definitions and two elementary
facts about smooth vectors are proved (they are subspaces and are
`G`-invariant). No classification, multiplicity-one, Casselman–Wallach
or Gårding density result is stated or used.

The instances for `GL_n(ℝ)`, `GL_n(ℂ)` and the Levi subgroups
`GL_n(F) × GL_m(F)` are in the companion module
`Langlands.Representation.Archimedean.GeneralLinear`.

## Mathematical content

The namespace is `Langlands.Archimedean`. Throughout, `𝔤` is a real
normed space, `I : ModelWithCorners ℝ 𝔤 H` a model with corners and `G` a
group with a topology and a `ChartedSpace H G` structure. The facts that
need the group to be a Lie group assume `[LieGroup I ∞ G]`. The space `E`
is a complex normed space; the Banach condition `[CompleteSpace E]` is
added only in the final predicate. A representation is a group
homomorphism `π : G →* (E →L[ℂ] E)` into the bounded complex-linear
operators, so every `π(g)` is a bounded operator and `π(gh) = π(g)π(h)`.

Since the tangent space of the manifold `G` at `1` is, definitionally,
the model vector space `𝔤`, the space `𝔤` plays the role of the real Lie
algebra of `G`.

### Continuity and smooth vectors

- `IsContinuousRepresentation π`: the action map `G × E → E`,
  `(g, v) ↦ π(g)v`, is jointly continuous.
- `orbitMap π v : G → E` is `g ↦ π(g)v`.
- `IsSmoothVector I π v`: the orbit map of `v` is real `C^∞` as a map from
  the manifold `G` to the real normed space `E`
  (`ContMDiff I 𝓘(ℝ, E) ∞`).
- `smoothVectors I π : Submodule ℂ E` is the set of smooth vectors. Its
  closure under addition and complex scalar multiplication is proved
  (the orbit map of `c • v` is the composite of the orbit map of `v` with
  the real-linear bounded map `c • id`).
- `mem_smoothVectors_iff` unfolds membership.
- `isSmoothVector_apply` (for a Lie group): if `v` is smooth then so is
  `π(h)v`, because its orbit map is the orbit map of `v` composed with the
  smooth right translation `g ↦ g h`.
- `smoothRepresentation I π : G →* (smoothVectors I π →ₗ[ℂ] smoothVectors I π)`
  is the restriction of `π` to smooth vectors; `smoothRepresentation_apply`
  records that it acts by `π(g)`.

### The derived action and continuity on smooth vectors

- `lieDerivative I π X v` is `dπ(X)v`, the manifold derivative
  `mfderiv I 𝓘(ℝ, E) (orbitMap π v) 1 X` of the orbit map at the identity
  in the tangent direction `X : 𝔤`. For a smooth vector it is
  `d/dt π(γ(t))v` at `t = 0` for any smooth curve `γ` with `γ(0) = 1` and
  velocity `X`; in particular it is `d/dt π(exp tX)v` at `t = 0`. As
  usual for `mfderiv`, the value is `0` if the orbit map is not
  differentiable at `1`; the definition is only used on smooth vectors.
- `iteratedLieDerivative I π [X₁, …, Xₖ] v` is
  `dπ(X₁)(dπ(X₂)(⋯ dπ(Xₖ)v))`; the empty word gives `v`
  (`iteratedLieDerivative_nil`, `iteratedLieDerivative_cons`).
- `IsContinuousOnSmoothVectors I π ℓ`, for a complex-linear functional
  `ℓ` on `smoothVectors I π`: there are a finite set `S` of words in `𝔤`
  and a constant `C` such that
  `‖ℓ v‖ ≤ C · ∑_{[X₁,…,Xₖ] ∈ S} ‖dπ(X₁)⋯dπ(Xₖ)v‖` for every smooth `v`.
  This is continuity of `ℓ` for the locally convex topology on smooth
  vectors defined by the seminorms `v ↦ ‖dπ(X₁)⋯dπ(Xₖ)v‖`; see
  "Derived choices" for its agreement with Shahidi's topology.

### Irreducibility, admissibility and Whittaker functionals

- `IsTopologicallyIrreducible π`: `E` is nonzero and every closed complex
  subspace `W` with `π(g)W ⊆ W` for all `g` is `0` or `E`.
- `intertwiners π K d τ`, for a subgroup `K` and a homomorphism
  `τ : K →* Matrix (Fin d) (Fin d) ℂ` (a `d`-dimensional representation of
  `K` on column vectors), is the complex space of linear maps
  `T : ℂ^d → E` with `T(τ(k)x) = π(k)(T x)` for all `k ∈ K` and `x`, that
  is `Hom_K(τ, π|_K)`.
- `IsAdmissible π K`: for every `d` and every continuous `τ` as above,
  `Hom_K(τ, π|_K)` is finite-dimensional.
- `IsWhittakerFunctional I π N χ ℓ`, for a subgroup `N` and a character
  `χ : N →* ℂˣ`: `ℓ` is continuous on smooth vectors and
  `ℓ(π(u)v) = χ(u) ℓ(v)` for all `u ∈ N` and all smooth `v`.
- `IsGeneric I π N χ`: a nonzero `χ`-Whittaker functional exists.
- `IsIrreducibleAdmissibleGeneric I π K N χ`, for a Banach space `E`:
  `π` is a continuous representation, topologically irreducible,
  admissible for `K` and `χ`-generic.

## Instances, universes and scope

The declarations are universe-polymorphic in `𝔤`, `H`, `G` and `E`. The
generic definitions require only `ChartedSpace H G`; `[LieGroup I ∞ G]` is
assumed from `isSmoothVector_apply` on, and `[CompleteSpace E]` only for
`IsIrreducibleAdmissibleGeneric`. No hypothesis that `K` is compact or
maximal compact, or that `N` and `χ` come from a Borel subgroup and a
nondegenerate character, is built into the generic predicates; those
choices are made by the instances in `GeneralLinear`.

## Original source correspondence

F. Shahidi, *Local coefficients as Artin factors for real groups*, Duke
Math. J. 52 (1985), 973–1007 (literature id `shahidi-1985-real-artin`;
PDF page = printed page − 972).

- Printed p.973 (PDF 1), Introduction: `(σ, H(σ))` is "an irreducible
  admissible χ-generic Banach (in particular χ-generic unitary)
  representation of `M`"; the same phrase is repeated in §3, p.988
  (PDF 16), and in Theorem 3.1, p.990 (PDF 18). This is
  `IsIrreducibleAdmissibleGeneric`, for the Lie group in question. In
  Shahidi `M` is the Langlands factor `M_θ°` of the parabolic subgroup
  (p.973 `P = MAN`; p.984 `M = M_θ°`; p.988 `M_θ° = M`); the instance
  module `GeneralLinear` applies the predicate to the full Levi subgroup
  instead and explains the correspondence there.
- Printed p.976 (PDF 4), §0: induction starts from an irreducible
  admissible Banach representation `(σ, H(σ))`, and p.976–977 introduces
  `σ_∞`, "the corresponding differentiable representation on the subspace
  of smooth vectors". These are `smoothVectors` and
  `smoothRepresentation`.
- Printed p.977 (PDF 5), §0: for a continuous representation `π` on a
  Fréchet space `F`, the space `F_∞` "is equipped with the Schwartz
  topology of `C^∞(G, F)`", and `U(𝔤)` acts. The derived action is
  `lieDerivative` and `iteratedLieDerivative`; the topology is treated in
  "Derived choices" below.
- Printed p.977 (PDF 5), §1, relation (1.1): `π` is χ-nondegenerate if
  "there exists a continuous nonzero linear functional `λ` on `V_∞` such
  that `λ(π(u)v) = χ(u)λ(v)` (`u ∈ U`, `v ∈ V_∞`)"; such a `λ` is a
  χ-Whittaker functional. This is `IsWhittakerFunctional` and
  `IsGeneric`, with `N` in the role of `U` (Shahidi says "generic" for
  "nondegenerate" from §2 on).
- Printed p.984 (PDF 12), §2: for the Levi subgroup the genericity is
  "more precisely `χ|M_θ ∩ U`-generic". The instance module takes `N` to
  be `M_θ ∩ U` with the restricted character.

### Derived choices

These points are explanations of the formalization; none is proved in
Lean.

1. **Irreducibility and admissibility.** Shahidi does not define these
   words; the standard meanings for Banach representations are used.
   Irreducibility is topological irreducibility. Admissibility
   (Harish-Chandra) means that every irreducible continuous
   representation `δ` of the compact group `K` occurs in `π|_K` with
   finite multiplicity `dim Hom_K(δ, π|_K)`. The formal condition asks
   this for every continuous finite-dimensional `τ`; the two agree because
   a continuous finite-dimensional representation of a compact group is a
   finite direct sum of irreducible ones, and `Hom_K` is additive in the
   source. Linear maps out of `ℂ^d` are automatically bounded, so no
   continuity is asked of `T`.
2. **Continuity.** Joint continuity of `G × E → E` is used. For a locally
   compact group acting on a Banach space it is equivalent to strong
   continuity (`g ↦ π(g)v` continuous for each `v`) by the uniform
   boundedness principle, which gives local boundedness of `‖π(g)‖`.
3. **Topology on smooth vectors.** Shahidi topologizes `V_∞` as a subspace
   of `C^∞(G, V)` through `v ↦ (g ↦ π(g)v)`, with uniform convergence of
   all derivatives on compact sets. Writing `X̃` for the left-invariant
   vector field of `X`, one has
   `X̃₁⋯X̃ₖ(g ↦ π(g)v)(g) = π(g) dπ(X₁)⋯dπ(Xₖ)v`. Left-invariant vector
   fields frame the tangent bundle, so the `C^∞(G, V)` topology is given
   by the seminorms `sup_{g ∈ C} ‖π(g)dπ(X₁)⋯dπ(Xₖ)v‖` for compact `C`.
   Local boundedness of `‖π(g)‖` (point 2) and evaluation at `g = 1`
   show these are equivalent to the seminorms `‖dπ(X₁)⋯dπ(Xₖ)v‖` used
   here. A linear functional is continuous for a topology given by a
   family of seminorms closed under finite sums up to constants exactly
   when it is bounded by a constant times a finite sum of them, which is
   `IsContinuousOnSmoothVectors`.
4. **Complexified enveloping algebra.** Shahidi lets `U(𝔤)` of the
   complexified Lie algebra act. Every element of it is a complex linear
   combination of words in a real basis of `𝔤`, so finitely many words
   in `𝔤` give the same seminorm topology.
5. **Charts.** `lieDerivative` uses the chart of the fixed
   `ChartedSpace` structure at `1`. Another chart changes the
   identification of the tangent space at `1` with `𝔤` by a linear
   isomorphism, which only reparametrizes the words, so the family of
   seminorms, the derived action as a set of operators, and every
   predicate here are unchanged.
6. **Iterated derivatives of smooth vectors.** If `v` is smooth then so
   is `dπ(X)v`, with orbit map `X̃(g ↦ π(g)v)`, so the words are
   evaluated on smooth vectors only. This standard fact is not needed to
   state the definitions and is not proved.

## Relation to other Library units

The Library's `Langlands.Global.ArchimedeanSmoothTopology` (Worker 2) puts
an enveloping-derivative compact-open topology on smooth functions on the
infinite adelic `GL_n` of a number field. It concerns function spaces on
the global archimedean group, not Banach representations of a single real
group, and is not used here. The Library's `Langlands.IsSmoothVector`
(a vector fixed by an open subgroup, the notion for totally disconnected
groups) is a different notion with the same short name; the declarations
here live in the namespace `Langlands.Archimedean`.

This module is the first archimedean representation-theoretic unit for
Shahidi 1985 Theorem 3.1, which Henniart's global argument uses through
the comparison of archimedean local coefficients with Artin factors.
Induced representations, Jacquet and intertwining integrals and the local
coefficient are planned as later units.
