# Local trace factorization on an irreducible cuspidal summand, with an isotypic local factor (statement)

Module `Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement` contains
one proposition definition and no proof:

- `Langlands.TraceFormula.GroupSchemeCuspidalIsotypicTraceFactorizationStatement.{u}`.

It strengthens the Library's
`Langlands.TraceFormula.GroupSchemeCuspidalLocalTraceFactorizationStatement` (Task 7701, module
of the same name). That statement gives, for an irreducible closed invariant subspace `P` of the
group-scheme cuspidal `L²` space and a finite place `v`, an irreducible admissible
representation `ρ_v` of `G(F_v)` whose distribution character splits off the traces on `P`, in
an ordinary and a twisted form. It says nothing about how `ρ_v` is related to `P`, so its
conclusion holds for some `ρ_v` without telling which one. The present statement keeps all of its
conclusions for the same `ρ_v` and adds two:

- (realization) `ρ_v` occurs in `P`: there is a nonzero linear map `j₀ : V → S` with range in
  `P` that intertwines `ρ_v(y)` with right translation by `ofPlace F G (.inr v) y`;
- (isotypy) `P` is `ρ_v`-isotypic for `G(F_v)`: every smooth irreducible representation of
  `G(F_v)` with a nonzero such map into `P` is isomorphic to `ρ_v`.

Together the two clauses pin down the isomorphism class of `ρ_v` by `P`. If `(V₁, ρ₁)` and
`(V₂, ρ₂)` both satisfy them for the same `P`, then `ρ₁` is smooth (it is admissible),
irreducible and has a realization map into `P`, so the isotypy clause for `ρ₂` gives an
equivariant linear equivalence `V₁ ≃ V₂`. That is what is needed to identify `ρ_v` with a local
component defined by other means, for example the Library's local components of cuspidal
operator realizations of `GL_n` (see "Intended use").

## Setting and notation from the Library

All data, hypotheses and notation are those of `GroupSchemeCuspidalLocalTraceFactorizationStatement`;
its Markdown explains them in full. In brief:

- `F : Type u` is a number field and `G` an affine group scheme over `Spec F`, locally of finite
  type, with `hPD : ParabolicDynamicStatement.{u}`, `hG : IsConnectedReductive G`, a central map
  `i : T.toGrp ⟶ G` from a commutative group scheme `T` with injective character restriction
  `hi` of finite-index range, an isomorphism `e` of `T` with a split torus indexed by a finite
  type `I`, `hc : IsCentral i`, and right invariance of Haar measure on `normOneSubgroup F G`.
  These are the group data of the Library's
  `Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalDecompositionStatement`.
- `G(𝔸_F) = AdelicGroupPoints F G`. `S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc`
  is the closed cuspidal subspace of `L²` of the quotient of `G(𝔸_F)` by
  `positiveRationalSubgroup F G T i`, for the measure `positiveRationalQuotientHaarMeasure F G T i`
  (written `μ_Q`). `πc a := fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc a` is
  right translation by `a ∈ G(𝔸_F)` on `S`. `fullAEL2CuspidalIntegratedAction … ν f hf`
  (written `R_S(f)`) and `haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf` (written
  `R(f)`) are the integrated actions on `S` and on all of `L²([G], μ_Q)`.
- `v : Langlands.Global.FinitePlace F`, `G(F_v) = PlaceGroupPoints F G (.inr v)` with the
  instance binders `[MeasurableSpace] [BorelSpace] [LocallyCompactSpace]
  [TotallyDisconnectedSpace]`. `atPlace F G (.inr v) g = g_v` is the local component and
  `ofPlace F G (.inr v)` the insertion of a local point at `v` (identity elsewhere).
- `twistOperator (positiveRationalSubgroup F G T i) Θ hΘ μ_Q hΘμ` (written `I_Θ`) sends `φ` to
  `φ ∘ Θ⁻¹` on the quotient, for a topological automorphism `Θ` of `G(𝔸_F)` preserving the
  subgroup (`hΘ`) and the quotient measure (`hΘμ`).
- `Langlands.IsSmooth ρ` says that every vector is fixed by an open subgroup;
  `Langlands.IsAdmissible ρ` says that `ρ` is smooth and the fixed vectors of every open
  subgroup form a finitely generated (here finite-dimensional) space (module
  `Langlands.Representation.Smooth.Definitions`). `ρ.IsIrreducible` is Mathlib's
  `Representation.IsIrreducible`: the lattice of subrepresentations is `{⊥, ⊤}` with `⊥ ≠ ⊤`
  (purely algebraic). `Character.distribution μv ρ hρ fv` is the trace of the finite-rank
  operator `ρ(fv)`; `BaseChange.twistedDistribution μv ρ hρ A fv` is the trace of `ρ(fv) ∘ A`.
  `IsTraceClass` and `operatorTrace` are the Library's trace-class predicate and trace, and the
  compression of `X` to a complete subspace `P` is
  `P.orthogonalProjectionOnto ∘L X ∘L P.subtypeL`.

## Statement

For all data as above, every finite place `v` with the four instance binders, every Haar
measure `μv` on `G(F_v)` and every Haar measure `ν` on `G(𝔸_F)`, let `P : Submodule ℂ S` with
`[CompleteSpace P]`, `P ≠ ⊥`, `P` invariant under every `πc a`, and such that every closed
subspace `Q ≤ P` invariant under every `πc a` is `⊥` or `P`. Then there are `V : Type u` with
`AddCommGroup V` and `Module ℂ V`, a representation `ρ : Representation ℂ G(F_v) V` and
`hρ : IsAdmissible ρ` such that `ρ.IsIrreducible` and:

0. **Realization.** There is a linear map `j₀ : V →ₗ[ℂ] S` with `j₀ ≠ 0`,
   `LinearMap.range j₀ ≤ P`, and `j₀ (ρ y x) = πc (ofPlace F G (.inr v) y) (j₀ x)` for all
   `y ∈ G(F_v)` and `x ∈ V`.
0'. **Isotypy.** For every `V' : Type u` with `AddCommGroup V'` and `Module ℂ V'`, every
   representation `ρ' : Representation ℂ G(F_v) V'` with `IsSmooth ρ'` and `ρ'.IsIrreducible`,
   and every linear map `j : V' →ₗ[ℂ] S` with `j ≠ 0`, `LinearMap.range j ≤ P` and
   `j (ρ' y x) = πc (ofPlace F G (.inr v) y) (j x)` for all `y`, `x`, there is a linear
   equivalence `E : V' ≃ₗ[ℂ] V` with `E (ρ' y x) = ρ y (E x)` for all `y`, `x`.
1. **Ordinary trace factorization**, exactly part 1 of Task 7701: there is
   `C : (G(𝔸_F) → ℂ) → ℂ` such that for every `fv : SchwartzBruhat G(F_v)` and every
   `fw : G(𝔸_F) → ℂ` with `fw (g * ofPlace x) = fw g`, if `f g = fv (g_v) * fw g` is
   `ν`-integrable (`hf`) and the compression of `R_S(f)` to `P` is trace class, then its trace
   is `Character.distribution μv ρ hρ fv * C fw`.
2. **Twisted trace factorization**, exactly part 2 of Task 7701: for every `Θ`, `hΘ`, `hΘμ` and
   every topological automorphism `θv` of `G(F_v)` with `(Θ g)_v = θv (g_v)` and
   `Θ (ofPlace x) = ofPlace (θv x)`, if `I_Θ` maps `P` into `P`, then there are a bijective
   linear `Av : V → V` with `Av (ρ y w) = ρ (θv y) (Av w)` and `C : (G(𝔸_F) → ℂ) → ℂ` such that,
   for `fv`, `fw`, `f`, `hf` as in part 1, if the compression to `P` of the compression to `S`
   of `R(f) ∘ I_Θ` is trace class, then its trace is
   `BaseChange.twistedDistribution μv ρ hρ Av fv * C fw`.

The Lean text of parts 1 and 2 is copied verbatim from `GroupSchemeCuspidalLocalTraceFactorizationStatement`.
So the present statement implies that one: forget clauses 0 and 0'. The maps `j₀` and `j` are
only linear: `V` and `V'` carry no topology, and no continuity is asserted or assumed. The
carrier `V'` ranges over `Type u`, the universe of `F` and of `V`. That is the universe of the
Library's local realizations of `GL_n` (their spaces are subspaces of automorphic forms on
`GL_n(𝔸_F)` with `F : Type u`).

## Why the statement is true

The argument is the one written in the Markdown of
`GroupSchemeCuspidalLocalTraceFactorizationStatement`, plus a Schur-type step for clauses 0 and 0'.

1. **Tensor decomposition.** `(x, h) ↦ ofPlace(x) h` is an isomorphism of topological groups
   `G(F_v) × H ≅ G(𝔸_F)` with `H = ker (atPlace F G (.inr v))`. The right action on `P` is an
   irreducible unitary representation (the closed-subspace condition). `G(F_v)` is of type I
   (Getz–Hahn, Theorem 3.10.2; `F_v` has characteristic zero), so there is a unitary
   isomorphism `U : P ≅ H_v ⊗̂ H^v` with irreducible unitary representations `π_v` of
   `G(F_v)` and `π^v` of `H`, carrying `πc (ofPlace y)` to `π_v(y) ⊗ 1` (Folland,
   Theorem 7.17). The smooth vectors `V ⊆ H_v` of `π_v` (the vectors fixed by some compact
   open subgroup) carry an irreducible admissible representation `ρ` (Getz–Hahn,
   Proposition 5.3.8 and Theorem 5.3.9). Since every open subgroup of `G(F_v)` contains a
   compact open subgroup, these are also the vectors fixed by some open subgroup, as in
   `Langlands.IsSmooth`. Parts 1 and 2 hold for this `ρ` by the argument of Task 7701.
2. **Realization.** Fix a unit vector `ξ ∈ H^v` and put `j₀ x = U⁻¹ (x ⊗ ξ)`, viewed in `S`.
   This is linear, nonzero, has range in `P`, and intertwines `ρ(y)` with `πc (ofPlace y)`
   because `π_v(y) ⊗ 1` sends `x ⊗ ξ` to `π_v(y)x ⊗ ξ`.
3. **Isotypy.** Let `ρ'` and `j` be as in clause 0'. Pick `x₀` with `j x₀ ≠ 0`. For `e ∈ H^v`
   the map `λ_e = id ⊗ ⟨·, e⟩ : H_v ⊗̂ H^v → H_v` is bounded and satisfies
   `λ_e (π_v(y) ⊗ 1) = π_v(y) λ_e`. Since `⟨λ_e ζ, u⟩ = ⟨ζ, u ⊗ e⟩` and the elementary tensors
   span a dense subspace, some `e` has `λ_e (U (j x₀)) ≠ 0`. Put `T = λ_e ∘ U ∘ j : V' → H_v`.
   It is linear, nonzero and `G(F_v)`-equivariant. If an open subgroup `K` fixes `x ∈ V'`
   (smoothness of `ρ'`), then `πc (ofPlace K)` fixes `j x`, and `π_v(K)` fixes `T x`. So `T`
   takes values in `V` and intertwines `ρ'` with `ρ`. Its kernel is a subrepresentation of
   `ρ'` other than `⊤`, hence `⊥`. Its range is a nonzero subrepresentation of `ρ`, hence `⊤`.
   So `T` is a bijective intertwiner, and `E = LinearEquiv.ofBijective T` works.

Step 3 is the analytic form of Flath's observation that the restriction of an irreducible
`W_1 ⊗ W_2` to the first factor is `W_1`-isotypic (last sentence of the proof of Flath 1979,
Theorem 1, printed p. 180).

## Use and provenance

This is derived content, formulated for this project. It packages the local part of the
factorization of a cuspidal automorphic representation with the trace identities of Task 7701:

- J. R. Getz and H. Hahn, *An introduction to automorphic representations*, GTM 300 (2024),
  registered `getz-hahn-2024-automorphic-representations`: Theorem 3.10.2 (printed p. 97,
  PDF p. 113; the points of an affine algebraic group over a characteristic-zero local field
  form a type I group); Proposition 5.3.8 and Theorem 5.3.9 (printed p. 141, PDF p. 156; for a
  reductive group over a nonarchimedean local field, a unitary representation is irreducible
  if and only if its smooth vectors are, and irreducible unitary representations are
  admissible); Theorem 5.7.1 (Flath) and Theorem 5.7.2 (printed p. 152, PDF p. 167; the
  algebraic factorization over a product of td-groups, with uniquely determined factor
  classes).
- D. Flath, *Decomposition of representations into tensor products*, Proc. Sympos. Pure Math.
  33, part 1 (1979), registered `flath-1979-tensor-products` (registered file: Corvallis
  Part I, PDF pp. 175–176; the separate offprint in the central library has these as PDF
  pp. 1–2). Theorem 1 (printed p. 179): for locally compact totally disconnected `G_1`, `G_2`,
  an admissible irreducible representation of `G_1 × G_2` is `W_1 ⊗ W_2` with admissible
  irreducible `W_i`, and the classes of the `W_i` are determined. The last sentence of its
  proof (printed p. 180) gives the reason: the restriction to `G_i` is `W_i`-isotypic. Flath's
  setting is algebraic (admissible modules); clause 0' is the analogue for the Hilbert space
  `P`, with the first factor replaced by the smooth vectors of `π_v`.
- G. B. Folland, *A course in abstract harmonic analysis*, 2nd ed. (2015), registered
  `folland-2015-abstract-harmonic-analysis-second`, Theorem 7.17 (printed p. 237, PDF p. 250):
  if `G_1` or `G_2` is of type I, every irreducible unitary representation of `G_1 × G_2` is
  equivalent to an outer tensor product `π_1 ⊗ π_2`.
- Henniart–Lemaire 2011, Proposition of II.6.5 (printed pp. 121–122), uses this factorization
  for the global intertwining operator in cyclic base change (as cited by Task 7701).

Differences from the sources, all of which keep the content: one place `v` is split off; the
local factor is realized on algebraic (smooth) vectors and maps into `P` are only linear; the
irreducibility in clause 0' is Mathlib's algebraic irreducibility; trace class is a hypothesis
in parts 1 and 2, as in Task 7701.

## Intended use

Task 7340 uses clause 0' to identify the local factor `ρ` with the Library's local component of
a cuspidal operator realization of `GL_{r+1}`. This identification is the content of
`Langlands.TraceFormula.GeneralLinearCuspidalLocalComponentTraceStatement` (Task 7819). The
local component embeds into `P` through the form-to-`L²` map `Φ`, clause 0' gives an
equivariant linear equivalence with `ρ`, and the Library lemma
`Langlands.Character.distribution_eq_of_equivariant` (module
`Langlands.Representation.Character.Basic`) transports the character. The twisted part with
the identified local factor (the twisted local statement of Task 7851) uses clause 0' in the
same way, transporting `Av` along `E`. The statement is generic over group schemes and
automorphisms, so the Jacquet–Langlands and automorphic induction comparisons can use it the
same way.
