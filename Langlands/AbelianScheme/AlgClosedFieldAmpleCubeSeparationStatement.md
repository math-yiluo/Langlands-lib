# Lefschetz's theorem over an algebraically closed field: the cube of an ample bundle separates points and tangent vectors

`Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationStatement` is a
universe-polymorphic `Prop`-valued definition. It states, over an
algebraically closed field, the content of Mumford's proof of Lefschetz's
theorem: the complete linear system of the tensor cube of an ample line
bundle on an abelian variety has no base point and separates points and
tangent vectors. The module states the proposition only. It supplies no
proof and adds no axiom.

## Statement

For every universe `u`, every field `K : Type u` with `IsAlgClosed K`, every
`A : AbelianScheme (Spec (CommRingCat.of K))` and every actual line bundle
`L : LineBundle A.X.left`, the proposition says

```text
L.IsAmple →
  SeparatesPointsAndTangents A.X.hom
    ⟨tensorPow L.obj 3, tensorPow_isLocallyFreeRankOne _ L 3⟩
```

The source declaration is

```lean
def AlgClosedFieldAmpleCubeSeparationStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K))) (L : LineBundle A.X.left),
    L.IsAmple →
      SeparatesPointsAndTangents A.X.hom
        ⟨tensorPow L.obj 3, tensorPow_isLocallyFreeRankOne _ L 3⟩
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules`. The
module imports `Langlands.AbelianScheme.Basic`,
`Langlands.AlgebraicGeometry.Picard.Ample`,
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`,
`Langlands.AlgebraicGeometry.Picard.TensorRankOneProof` and
`Mathlib.FieldTheory.IsAlgClosed.Basic`. In the Lean environment in which it
was checked the definition compiles with no
errors or warnings, its type is `Prop`, it has the single universe
parameter `u`, and it depends only on `propext`, `Classical.choice` and
`Quot.sound`.

## Library objects used

The statement uses only published definitions. It introduces no new data,
structure, certificate or axiom.

- `A : AbelianScheme S` is the published bundle: a commutative group scheme
  over `S` whose structure morphism `A.X.hom : A.X.left ⟶ S` is smooth,
  proper and geometrically connected. Here `S = Spec K`.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf; `L.obj` is the module sheaf.
- `L.IsAmple` is the published ampleness predicate of `Picard.Ample`
  (Stacks Project Definition 28.27.1, tag 01PS, identified there with
  EGA II Definition 4.5.3; see `Picard/Ample.md`): `A.X.left` is
  quasi-compact and every point lies in an affine generation locus
  `L.sectionOpen s` of a global section `s` of some positive tensor power.
- `tensorPow L.obj 3` is the published right-associated tensor power
  `L ⊗ (L ⊗ (L ⊗ 𝒪))` of `Langlands.Scheme.Modules`, and
  `tensorPow_isLocallyFreeRankOne _ L 3` is the published proof that it is
  again a line bundle. The anonymous constructor packages the two as a
  `LineBundle A.X.left`. This is the same expression as the published
  `Langlands.AbelianScheme.PolarizedFiniteLevel.Datum.cubicBundle`, which is
  `⟨tensorPow a.canonicalBundle.obj 3, tensorPow_isLocallyFreeRankOne _ a.canonicalBundle 3⟩`;
  for a datum `a` over an algebraically closed field the conclusion for
  `L = a.canonicalBundle` is therefore literally
  `SeparatesPointsAndTangents a.abelian.X.hom a.cubicBundle`.
- `SeparatesPointsAndTangents` is imported unchanged from
  `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`, where it is
  documented. For `p = A.X.hom` and a line bundle `M` it is the conjunction
  of three clauses about all global sections
  `s : Langlands.SchemeModule.GlobalSections M.obj`; a section vanishes
  along a morphism `f` (`VanishesAlong M f s`) when its pullback
  `Langlands.SchemeModule.pullbackSection f M.obj s` is zero:
  0. base-point freeness: for every rational point `x : Spec K ⟶ A.X.left`
     (`x ≫ p = 𝟙`) some section does not vanish along `x`;
  1. separation of points: for distinct rational points `x ≠ y` some section
     vanishes along `x` but not along `y`;
  2. separation of tangent vectors: for every rational point `x` and every
     nonzero rational tangent vector `t : Spec K[ε] ⟶ A.X.left` at `x`
     (`K[ε] = DualNumber K`; `t` lies over `Spec K`, restricts to `x` at
     `ε = 0` and differs from the constant vector), some section vanishes
     along `x` but not along `t`.

No base change, projective embedding, theorem of the square, finiteness of
`K(L)`, quotient or dimension count is supplied as a hypothesis.

## Original source

The original is D. Mumford, *Abelian Varieties*, Tata Institute of
Fundamental Research Studies in Mathematics 5, Oxford University Press,
1970, registered as `mumford-abelian-varieties-full-scan`, SHA256
`9541a2e454c78920d4a41b4a78cac36544cd83e99bd1a221e55f25e3f247dcc3`, file
`literature/David Mumford - Abelian Varieties (full scan).pdf`. The scan
has two printed pages per PDF page and no text layer; the pages cited were
read from renderings.

- §4, printed p.39 / PDF p.24: "We now turn to the study of abelian
  varieties over an arbitrary algebraically closed field `k`." An abelian
  variety is "a complete algebraic variety over `k` with a group law
  `m : X × X → X` such that `m` and the inverse map are both morphisms of
  varieties"; a footnote says that this includes irreducibility.
- §17 "Very ample line bundles", printed p.163 / PDF p.86 (right half):
  "THEOREM. For any ample line bundle `L` on an abelian variety `X`, `Lⁿ` is
  very ample, if `n ≥ 3`." The proof begins: "For simplicity, we shall
  prove `L³` is very ample." It writes `L ≅ 𝒪_X(D)` with `D` effective and
  without multiple components, notes that
  `T_x^*(D) + T_y^*(D) + T_{-x-y}^*(D) ∈ |3D|` for all `x, y ∈ X` (theorem
  of the square), and reduces very ampleness to:
  (1) "Given `x₀, x₁ ∈ X` with `x₀ ≠ x₁`, there is a `D' ∈ |3D|` such that
  `x₀ ∈ Supp D'`, `x₁ ∉ Supp D'`."
  (2) "Given any tangent vector `t` to `X` at `x₀`, there is a
  `D' ∈ |3D|` such that `x₀ ∈ Supp D'` and `t` is not tangential to `D'`
  (i.e. if `φ = 0` is a local equation of `D'` at `x₀`, `⟨t, dφ⟩ ≠ 0`)."
- Printed pp.163–165 / PDF pp.86–87 prove (1) and (2); see the proof
  obligations below. In the proof of (2) the tangent vector is "a non-zero
  tangent vector `t` at 0".

### Correspondence with the Lean clauses

These comparisons explain the formulation; they are not proved in Lean.

- Mumford's `Lⁿ` is the `n`-th tensor power; for `n = 3` it is the published
  `tensorPow L.obj 3`. Only the exponent `3` is stated here; Mumford's
  `n > 3` cases are not.
- Members of `|3D|` are the zero divisors of the nonzero global sections of
  `L³ ≅ 𝒪_X(3D)`, so the clauses quantify over the complete linear system
  `Γ(A, L³)`.
- Over the algebraically closed `K`, and for `A.X.left` of finite type over
  `K`, the closed points are exactly the rational points
  `x : Spec K ⟶ A.X.left`. A point `x₀` lies on the zero divisor of `s`
  exactly when `s` vanishes in the fibre of `L³` at `x₀`, which is the
  vanishing of `pullbackSection x s`. This gives clause 1 from (1).
- A tangent vector at `x₀` is a `K[ε]`-point over `K` restricting to `x₀`;
  the zero vector is the constant one. If `s(x₀) = 0` and `φ` is a local
  equation of `div s` at `x₀`, then the pullback of `s` along `t` is
  `ε · ⟨t, dφ⟩` times a local generator, so `t` is not tangential to
  `div s` exactly when `s` does not vanish along `t`. Mumford's (2) is for
  nonzero `t`, as in his proof. This gives clause 2 from (2).
- Clause 0 is part of very ampleness: a very ample bundle is generated by
  its global sections. It also follows from the displayed members of
  `|3D|`: for a point `x₀`, the translates through `x₀` are avoided for `x`,
  `y` outside proper closed subsets. When `A` has dimension zero, `A.X.left`
  is `Spec K`, every line bundle is trivial and clause 0 is given by a
  nonvanishing section; clauses 1–2 are then vacuous.

The formulation through `K`-points, `K[ε]`-points and the base-point clause
is therefore derived (internal) provenance from Mumford's statement and
proof. The statement claims the separation conditions only; it does not
claim that the morphism to projective space defined by `|3D|` is a closed
immersion, which over an algebraically closed field follows from these
conditions by a separate very-ampleness criterion.

## Comparison of source hypotheses with the Library interfaces

- *Algebraically closed field.* Mumford works over an algebraically closed
  field throughout; the binder `IsAlgClosed K` is exactly that convention.
- *Abelian variety.* Over `Spec K`, the published `AbelianScheme` is smooth,
  proper and geometrically connected, with a rational identity section.
  Properness gives a complete, separated scheme of finite type. Smoothness
  over the algebraically closed `K` gives regularity; a connected
  noetherian regular scheme is integral. So `A.X.left` is a complete
  variety with a group law in Mumford's sense, and every abelian variety in
  Mumford's sense, being commutative (§4), underlies such an
  `AbelianScheme`. The published
  `Langlands/AbelianScheme/Basic.md` and
  `Langlands/AbelianScheme/AmpleLineBundleHigherCohomologyVanishingStatement.md`
  record the same comparison.
- *Ample.* For a complete variety over a field, ampleness in the sense of
  EGA II 4.5.3, which `L.IsAmple` formalizes, is equivalent to some positive
  tensor power being very ample (EGA II 4.5.10; Hartshorne,
  *Algebraic Geometry*, II.7.6). This equivalence is standard mathematics
  recorded for orientation; neither EGA nor Hartshorne is a registered
  source of this pair, and the equivalence is not formalized or used here.

No genuine mismatch was found: the Lean hypotheses are Mumford's, and the
Lean conclusion is the conjunction of base-point freeness and Mumford's
(1)–(2) for `L³`.

## Errata

No source-specific errata note for Mumford's *Abelian Varieties* was found
in the project, Library or `notes/errata/` locations on 2026-11-19. The
scanned first edition is the registered text; later editions were not
compared. This records the locations checked; it does not assert that no
errata exist.

## Proof obligations

A proof must have this entire named proposition as its type, with no extra
outer hypotheses; the Library's proof is
`Langlands.AbelianScheme.algClosedFieldAmpleCubeSeparation`, in the module
`Langlands.AbelianScheme.AlgClosedFieldAmpleCubeSeparationProof`.
Mumford's argument uses, none of it proved here:

1. `dim H⁰(X, L) = χ(L) > 0` for ample `L` (§16), to choose an effective `D`
   with `L ≅ 𝒪_X(D)`, and the reduction to `D` without multiple components.
2. The theorem of the square, giving
   `T_x^*(D) + T_y^*(D) + T_{-x-y}^*(D) ∈ |3D|`. The Library has the
   published theorem `Langlands.GroupScheme.fieldTheoremOfTheSquare`
   (statement `Langlands.GroupScheme.FieldTheoremOfTheSquareStatement`).
3. Reduction to `x₀ = 0` by translating `L`.
4. For (1): if it failed, `Supp D` would be invariant under translation by
   `x₁`, so `x₁ ∈ K(L)` has finite order; for the finite group `F` it
   generates, the étale quotient `π : X → X/F` gives `D = π^*(D₁)` and
   `dim H⁰(X, L) = (ord F) · dim H⁰(X/F, 𝒪(D₁)) > dim H⁰(X/F, 𝒪(D₁))`. As
   the `D₁` fall into finitely many linear equivalence classes, every
   section of `L` would define a multiple divisor or lie in one of finitely
   many proper subspaces, a contradiction. The Library has the published
   theorem `Langlands.AbelianScheme.algClosedFieldAmpleTranslationStabilizerFinite`:
   only finitely many rational points `x` satisfy `t_x^* L ≅ L` for an ample
   `L`.
5. For (2): if it failed, `D` would be invariant under the `K[ε]`-valued
   translation defined by `t`, so `t` lies in the subgroup scheme `K(L)`.
   In characteristic `0` group schemes are reduced, so `t = 0`. In
   characteristic `p`, the smallest subgroup scheme `H ⊂ K(L)` containing
   `t` is infinitesimal (`H ⊂ X^(p)`), `D` is `H`-invariant, `X → X/H` is
   flat and surjective (§12) and `D` descends to a divisor `D'` on `X/H`
   (§12, Theorem 1, Part (B)); the same dimension count gives the
   contradiction.

A proof must therefore supply, for the published interfaces,
the positivity of `H⁰` of ample bundles, quotients of abelian varieties by
finite étale subgroups and by infinitesimal subgroup schemes with the
corresponding descent of divisors and multiplicativity of `χ`, or another
unconditional route. A conditional assembly is not a proof of this
proposition.

## Scope

The statement covers every universe `u`, every algebraically closed field
of every characteristic, every dimension and every actual ample line
bundle. No polarization, finite-level datum, projectivity, dual, `H⁰`
positivity, separating divisor or chosen basis is added as a premise.
Separation is stated for the complete linear system `Γ(A, L³)`.

## Role

This is a focused prerequisite of the published
`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingStatement`
over an arbitrary field, which
`Langlands.AbelianScheme.PolarizedFiniteLevel.cubicFieldEmbedding_of_cubeSeparation`
(module `Langlands.AbelianScheme.PolarizedFiniteLevel.CubicFieldEmbeddingReduction`)
derives from the present statement. That reduction applies the present statement to the
canonical bundle `a.canonicalBundle` of a datum base-changed to an
algebraic closure, whose ampleness is the first component of the published
theorem `Langlands.AbelianScheme.PolarizedFiniteLevel.canonicalCubicBundleAmple`,
and descends the resulting closed immersion. `CubicFieldEmbeddingStatement` is not used to justify this statement.
