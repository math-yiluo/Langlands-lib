# Renard VII.3.4–VII.3.5 (i): the integral normalization of `J_{Q|P}(σ)` and its composition law

Author: Worker 1222. Module
`Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameters `u, v`. The module contains
one auxiliary `Prop`-valued predicate and two **statements**, all `Prop`-valued definitions:

- `IsIntegralIntertwiner`: Renard's integral formula `J(f)(1) = ∫_{N̄∩U} f(u) du` for an
  intertwining operator `J`;
- `PQIntegralIntertwiningOperatorStatement`: the explicit form of VII.3.4;
- `PQIntertwiningCompositionStatement`: part (i) of the Proposition of VII.3.5.

It proves nothing.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

- VII.3.4, printed pp.235–236 / PDF pp.241–242: construction of `K_{Q|P}(σ)` and
  `J_{Q|P}(σ)`; the paragraph "Il est utile de donner une forme plus explicite de
  l'opérateur `K_{Q|P}`", which says that the natural isomorphism
  `F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(E) ≃ E` is obtained by passing to the quotient from
  `F̃^{<1̄}_{PQ} → E`, `f ↦ ∫_{(U∩N)\U} f(u) dν(u) = ∫_{U∩N̄} f(u) du` (the quotient is by `U ∩ N`, the
  integral is over the complementary factor `U ∩ N̄`), a special case of
  (VI.5.1.12) (printed p.172 / PDF p.178), with convergent integrals; and the Proposition:
  for `P = MN`, `Q = MU` semi-standard and `σ` `PQ`-regular, `J_{Q|P}(σ)` is the unique
  element of `Hom_G(i_P^G(σ), i_Q^G(σ))` with `J_{Q|P}(σ)(f)(1_G) = ∫_{N̄∩U} f(u) du` for all
  `f ∈ F̃^{<1̄}_{PQ}(E)`.
- VII.3.5, printed pp.236–240 / PDF pp.242–246: the definition
  `d(P, Q) = |Σ(P) ∩ Σ(Q̄)|` for semi-standard `P`, `Q` with the same Levi factor `M`, and
  part (i) of the Proposition: if `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)` and `d(P₁, P₂) = 1`, and
  `σ` is `P₁P₃`-regular, then `σ` is `P₂P₃`-regular and `P₁P₂`-regular, and
  `J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ) = J_{P₃|P₁}(σ)`. Its proof translates the hypothesis on `d`
  into `N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)` and computes
  `J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ)(f)(1_G) = ∫_{N̄₂∩N₃} ∫_{N̄₁∩N₂} f(vu) dv du = ∫_{N̄₁∩N₃} f(u) du`.
- V.3.4, printed p.110 / PDF p.116: `Σ′(A)` is the set of roots of `A` in `Lie(G)`, `Σ(A)` the
  reduced roots (`α ∈ Σ′(A)` with `α/n ∉ Σ′(A)` for `n ≥ 2`), `Σ′(P)` the roots of `A` in
  `N`, and `Σ(P)` the reduced positive roots.

## Published objects used

From the published VII.3.4 statement
[PQIntertwiningOperatorStatement](PQIntertwiningOperatorStatement.md) and, through it,
[PQRegularity](PQRegularity.md), with the meanings described in those Markdown files:

- `leviInductionFunctor p l r hp hr hl hmul`, Renard's normalized `i_P^G` on smooth
  representations of `M(F)`, and `leviJacquetInductionFunctor`, Renard's `r_Q^G ∘ i_P^G`;
- `identityParabolicDoubleCoset p q` (Renard's `1̄`), `boundaryVanishingSubfunctor …`
  (Renard's `F̃^{<1̄}_{PQ}`), `boundarySupportImage …` and `closureSupportImage …` (Renard's
  `F^{<1̄}_{PQ}` and `F^{≤1̄}_{PQ}`), and the quotient `quotientObj` with its projection
  `quotientProjection`;
- `IsPQRegular … a σ`, condition (i) of the VII.3.3 Lemma, `I_σ + I^{PQ}_σ = ℂ[A_M]`;
- `Induction.eval (pointImage p) (inducingRepresentation …) f x`, the value `f(x) ∈ E` of an
  induced function, and `Jacquet.Localization.mk … (pointImage (rQ ≫ q)) 1 f`, the image `f̄` of
  `f` in `r_Q^G ∘ i_P^G(σ)`; these appear in exactly the same form in the published statement;
- `pointImage f`, the image of `X(F)` in `G(F)` under a represented subgroup `f : X ⟶ G`, and
  `IsSplitComponent a` (`A` is the split component `A_M` of `M`).

From `Langlands.GroupScheme.Rational.SubgroupRelativeRoots`:
`RelativeRoot.subgroupRelativeRoots i F`, the nonzero characters `χ` of `A` (embedded in `G` by
`i`) such that some nonzero tangent vector of `G` in the `χ`-weight space for conjugation lies
in the subgroup functor `F`, that is, the roots of `A` in `Lie(F)`. `SubgroupFunctor.range f` is
the subgroup functor of points of `G` factoring through `f`.

From `Langlands.GroupScheme.Rational.RootProductStatement`: `RelativeRoot.indivisibleRoots i`,
the roots `a` of `A` in `Lie(G)` (`relativeRoots i`) such that `m • b ≠ a` for every root `b`
and every natural `m > 1`. The character lattice is torsion free, so this is Renard's reduced
roots `Σ(A)`.

From Mathlib: `MeasureTheory.Measure`, `Measure.IsHaarMeasure`, `BorelSpace`, `Integrable`, the
Bochner integral `∫ x, φ x ∂μ`, `Module.Dual`, `Continuous`, `HasCompactSupport`, `Set.ncard`,
and `Representation.IntertwiningMap`, `Representation.Equiv`, `Representation.IntertwiningMap.comp`.

## Common setting

All statements quantify over a nonarchimedean local field `k : Type u` and a connected
reductive `G` over `Spec k`, with the canonical topology on `G(F)`,
`[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]`,
exactly as the published VII.3.4 statement. A represented parabolic `P = MN` is given by
`p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `hp : IsParabolicSubgroup p`,
`hl : IsRationalLeviSubgroup l`, `hr : LeviSubgroup.IsGeometricUnipotentRadical r` and
`hmul : IsIso (subgroupMultiplication l r)`; all parabolics share the Levi scheme `M`, and their
embeddings of `M` in `G` agree (`l ≫ p = lQ ≫ q`, and so on). The topology on `M(F)` is
`leviPointTopology l hl` (for VII.3.5, `leviPointTopology l₁ hl₁`).

**Opposite parabolics.** Renard's `N̄` is the unipotent radical of the parabolic `P̄` opposite
to `P` with respect to `M`. A represented parabolic `P̄ = MN̄` (`pb`, `lb`, `rb` with the same
four hypotheses) is taken with the same embedded Levi subgroup (`lb ≫ pb = l ≫ p`) and with
`P(F) ∩ P̄(F) = M(F)`, written `pointImage p ⊓ pointImage pb = pointImage (l ≫ p)`. This
characterizes the opposite parabolic among parabolics with Levi `M`: for such a `P′`,
`P ∩ P′ = M (N ∩ N′)`, and `N ∩ N′` is a split unipotent group (the product of the root
groups for `Σ′(P) ∩ Σ′(P′)`), so its `F`-points are trivial only when `Σ′(P) ∩ Σ′(P′)` is
empty, that is, when `P′ = P̄`. The subgroup `N̄(F) ∩ U(F)` of `G(F)` is
`pointImage (rb ≫ pb) ⊓ pointImage (rQ ≫ q)`, with the subspace topology from `G(F)`.

## `IsIntegralIntertwiner`

Arguments: represented parabolics `P = MN` and `Q = MU` (no compatibility of the embeddings is
needed to state the formula), a subgroup `V` of `G(F)` with a measurable structure and a measure
`haar` on `V`, a smooth representation `σ` of `M(F)`, and an intertwining map
`J : i_P^G(σ) → i_Q^G(σ)`. The predicate holds when, for every `f ∈ F̃^{<1̄}_{PQ}(σ)` and every
linear form `ℓ` on the space `E` of `σ`:

- `x ↦ ℓ(f(x))` is `haar`-integrable on `V`, and
- `ℓ(J(f)(1)) = ∫_V ℓ(f(x)) d haar(x)`.

Renard's `∫_{N̄∩U} f(u) du` is an `E`-valued integral; `E` carries no topology. For
`f ∈ F̃^{<1̄}_{PQ}(E)`, the restriction of `f` to `N̄ ∩ U` is locally constant (`f` is smooth)
with compact support (Renard's remark before the Proposition of VII.3.4), so it is a finite sum
of vectors times indicator functions of compact open sets, and its integral is the
corresponding finite sum. A vector of `E` is determined by its values under all linear forms,
so the weak formulation against every `ℓ` expresses exactly Renard's equality, and its
integrability clause is Renard's convergence remark.

## `PQIntegralIntertwiningOperatorStatement` (VII.3.4, explicit form)

Additional binders: represented parabolics `P = MN`, `Q = MU`, `P̄ = MN̄` as above with
`l ≫ p = lQ ≫ q`, `lb ≫ pb = l ≫ p` and `P(F) ∩ P̄(F) = M(F)`; `V = N̄(F) ∩ U(F)` with a
measurable structure, `[BorelSpace V]`, and a Haar measure `haar` on `V`. The statement asserts
two things.

1. **The identification is induced by the integral.** For every smooth representation `σ` of
   `M(F)` there is an `M(F)`-equivariant linear equivalence
   `e : F^{<1̄}_{PQ}/F^{≤1̄}_{PQ}(σ) ≃ σ` (the same quotient object as in the published
   statement) such that, for every `f ∈ F̃^{<1̄}_{PQ}(σ)`, every `y` with membership proof
   `hy : y ∈ F^{<1̄}_{PQ}(σ)` equal to the image `f̄` of `f`, and every linear form `ℓ`:
   `x ↦ ℓ(f(x))` is integrable on `V` and `ℓ(e([y])) = ∫_V ℓ(f(x)) d haar(x)`. The `y`, `hy`
   device is the one of the published statement; it adds no condition.
2. **Characterization of `J_{Q|P}(σ)`.** For every split component `a : A → M` and every
   `PQ`-regular `σ`, there is exactly one intertwining map `J : i_P^G(σ) → i_Q^G(σ)` with
   `IsIntegralIntertwiner … V haar σ J`.

Clause 2 is Renard's Proposition. Clause 1 is the paragraph preceding it. The published
`PQIntertwiningOperatorStatement` (proved in the Library as `pqIntertwiningOperator`) gives
existence and uniqueness of `J` for an arbitrary identification `e`; applied to an `e` from
clause 1 it gives clause 2. Clause 2 is stated separately so that the normalized operator can
be used directly in VII.3.5.

## `PQIntertwiningCompositionStatement` (VII.3.5 (i))

Additional binders: represented parabolics `P₁ = MN₁`, `P₂ = MN₂`, `P₃ = MN₃` and opposites
`P̄₁ = MN̄₁`, `P̄₂ = MN̄₂`, `P̄₃ = MN̄₃`, all with the same embedded Levi subgroup
(`lᵢ ≫ pᵢ = l₁ ≫ p₁`, `lbᵢ ≫ pbᵢ = l₁ ≫ p₁`) and with `Pᵢ(F) ∩ P̄ᵢ(F) = M(F)`; a split
component `a : A → M`.

**The distance `d`.** For a subgroup functor `F` of `G`, `rootsIn F` is
`subgroupRelativeRoots (a ≫ l₁ ≫ p₁) F ∩ indivisibleRoots (a ≫ l₁ ≫ p₁)`, the reduced roots of
`A` in `Lie(F)`. For `F = range (rᵢ ≫ pᵢ)` this is Renard's `Σ(Pᵢ)`, and for
`F = range (rbⱼ ≫ pbⱼ)` it is `Σ(P̄ⱼ)`. The statement sets
`d(F, F′) = (rootsIn F ∩ rootsIn F′).ncard` and assumes

- `d(N₁, N̄₂) + d(N₂, N̄₃) = d(N₁, N̄₃)`, Renard's `d(P₁, P₂) + d(P₂, P₃) = d(P₁, P₃)`;
- `d(N₁, N̄₂) = 1`, Renard's `d(P₁, P₂) = 1`.

The sets are finite (there are finitely many roots), so `ncard` is their cardinality.

**Measures.** `V₁₂ = N̄₁(F) ∩ N₂(F)`, `V₂₃ = N̄₂(F) ∩ N₃(F)`, `V₁₃ = N̄₁(F) ∩ N₃(F)`, each with
a measurable structure and `[BorelSpace]`. Measures `haar₁₂`, `haar₂₃`, `haar₁₃` are
*compatible* when, for every continuous compactly supported `φ : G(F) → ℂ`,

`∫_{V₁₃} φ(x) d haar₁₃(x) = ∫_{V₂₃} ∫_{V₁₂} φ(w u) d haar₁₂(w) d haar₂₃(u)`.

This is the change of variables in the last display of Renard's proof of (i),
`∫_{N̄₂∩N₃} ∫_{N̄₁∩N₂} f(vu) dv du = ∫_{N̄₁∩N₃} f(u) du`, read on test functions. Since `V₁₃`
is closed in `G(F)`, every continuous compactly supported function on `V₁₃` extends to one on
`G(F)`, so compatibility determines `haar₁₃` from `haar₁₂` and `haar₂₃`.

**Conclusion.** The statement asserts:

1. for all Haar measures `haar₁₂` on `V₁₂` and `haar₂₃` on `V₂₃` there is a Haar measure
   `haar₁₃` on `V₁₃` compatible with them. This is the measure-theoretic content of Renard's
   `N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)`;
2. for every smooth representation `σ` of `M(F)` that is `P₁P₃`-regular:
   - `σ` is `P₂P₃`-regular and `P₁P₂`-regular;
   - for all compatible Haar measures `haar₁₂`, `haar₂₃`, `haar₁₃` and all intertwining maps
     `J₁₂ : i_{P₁}^G(σ) → i_{P₂}^G(σ)`, `J₂₃ : i_{P₂}^G(σ) → i_{P₃}^G(σ)`,
     `J₁₃ : i_{P₁}^G(σ) → i_{P₃}^G(σ)` that satisfy `IsIntegralIntertwiner` for `(V₁₂, haar₁₂)`,
     `(V₂₃, haar₂₃)` and `(V₁₃, haar₁₃)` respectively, `J₂₃ ∘ J₁₂ = J₁₃`.

By clause 2 of `PQIntegralIntertwiningOperatorStatement` and the regularity conclusions, the
three operators exist and are unique, and they are Renard's `J_{P₂|P₁}(σ)`, `J_{P₃|P₂}(σ)` and
`J_{P₃|P₁}(σ)` for these measures. So the last item is Renard's
`J_{P₃|P₂}(σ) ∘ J_{P₂|P₁}(σ) = J_{P₃|P₁}(σ)`.

## Provenance and departures from the source

The provenance is source: Renard's Proposition of VII.3.4, the identification paragraph
preceding it, and part (i) of the Proposition of VII.3.5. Formal choices and departures:

- **Measures.** Renard leaves the Haar measures on `N̄ ∩ U` implicit. `J_{Q|P}(σ)` depends on
  this choice by a positive scalar, so the statements quantify over Haar measures. Renard's
  composition law needs the three measures to be related; the compatibility condition is the
  relation used in his proof, and its existence clause is the content of
  `N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)`. The product decomposition itself, as an equality of
  subgroups, is not stated.
- **Weak integrals.** The `E`-valued integrals are read against every linear form on `E`;
  see the section on `IsIntegralIntertwiner`.
- **Semi-standard parabolics.** Renard takes all parabolics semi-standard. The statements do
  not assume this. Since all the parabolics share the Levi subgroup `M`, they are all
  semi-standard with respect to any maximal split torus of `M`, so nothing is lost.
- **`PQ`-regularity** is `IsPQRegular`, condition (i) of the VII.3.3 Lemma, as in the published
  VII.3.4 statement. Renard's proof of (i) works with exactly this condition.
- **Double cosets and quotient.** `1̄`, `F̃^{<1̄}_{PQ}`, `F^{<1̄}_{PQ}`, `F^{≤1̄}_{PQ}` and the
  quotient are those of the published VII.3.4 statement; its Markdown explains the use of actual
  double cosets and of the quotient by `F^{≤1̄}_{PQ} ∩ F^{<1̄}_{PQ}`.
- **Composition as a universal statement.** The VII.3.5 conclusion is stated for all
  operators satisfying the integral formulas rather than for chosen ones; with the existence
  and uniqueness of clause 2 of the VII.3.4 statement it is equivalent to Renard's equality.
- **Not stated here.** The remark "il est bien connu que `d(P, Q)` est la longueur de
  l'élément `w` du groupe de Weyl `W(A_M)` tel que `w · P = Q`" is not stated: for
  non-minimal `M` the book defines no length function on `W(A_M)`, which need not be a Coxeter
  group, and the remark is not used in the proof. Parts (ii) and (iii) of the VII.3.5
  Proposition, which need the identification `i_P^G ≅ i_Q^G ∘ i_{P∩L}^L` of induction in
  stages, are left for a separate unit.

## Remaining obligations

The proofs of both statements are separate obligations. For VII.3.4 the source argument is: the
explicit form (VI.5.1.12) of the geometric lemma gives clause 1; clause 2 then follows from
clause 1 and the proved `pqIntertwiningOperator` (Frobenius reciprocity and the retraction
given by `ε_σ ∈ I^{PQ}_σ`). For VII.3.5 (i): the regularity assertions via the
inclusions of double cosets `P₁ w P₃ ⊂ P₁ P₃` and the Levi `L` generated by `M`, `N_α`, `N_{-α}`
(Bruhat decomposition of `L`); the composition law via the characterization
`F̃^{<1̄}_{P₁P₃}(E) = {f | Supp f ∩ (N̄₁ ∩ N₃) compact}`, the integral formula and uniqueness in
VII.3.4.

## Imports

| Module | Used for |
| --- | --- |
| `Langlands.Representation.Intertwining.PQIntertwiningOperatorStatement` | the VII.3.4 objects listed above, through `PQRegularity` |
| `Langlands.GroupScheme.Rational.SubgroupRelativeRoots` | `RelativeRoot.subgroupRelativeRoots`, `SubgroupFunctor.range` |
| `Langlands.GroupScheme.Rational.RootProductStatement` | `RelativeRoot.indivisibleRoots` |
| `Mathlib.MeasureTheory.Measure.Haar.Basic` | `Measure.IsHaarMeasure` |
| `Mathlib.MeasureTheory.Integral.Bochner.Basic` | `Integrable`, the Bochner integral |
