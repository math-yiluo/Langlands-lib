# Separation of rational points and tangent vectors by global sections

This module defines when the global sections of a line bundle separate rational
points and rational tangent vectors. These are the hypotheses of the
very-ampleness criterion that Milne quotes from Hartshorne (II, 7.8.2) in the
proof of Theorem 7.1 ("Every abelian variety is projective"), Milne,
*Abelian Varieties*, author revision of 2022, pp.10–11. Here the conditions are
stated through `K`-points and `K[ε]`-points of a scheme over a field. This
formulation is derived (internal) provenance, explained below. It uses the
complete linear system `Γ(X, L)` of all global sections of `L`.

All declarations live in the namespace `Langlands.AlgebraicGeometry.Picard`.
Throughout, `K : Type u` is a field, `X : Scheme.{u}` is a scheme, and
`p : X ⟶ Spec (CommRingCat.of K)` is a morphism. `L : LineBundle X` is the
published locally free rank-one actual `X.Modules`; its module is `L.obj`. No
other hypothesis is imposed. There is no algebraic closedness, properness,
finiteness of type, finite dimensionality of `Γ(X, L)`, chosen subspace or
family of sections, ampleness or morphism to projective space. The universe,
the characteristic of `K` and the scheme `X` are arbitrary; `X` may be empty.

## Definitions

- `IsRationalPoint p x`, for `x : Spec (CommRingCat.of K) ⟶ X`, is
  `x ≫ p = 𝟙 _`. So `x` is a section of the structure morphism, a `K`-point of
  `X` over `K`.
- `VanishesAlong L f s`, for any scheme `Y`, any morphism `f : Y ⟶ X` and a
  global section `s : Langlands.SchemeModule.GlobalSections L.obj`, is
  `Langlands.SchemeModule.pullbackSection f L.obj s = 0`. This uses the
  published pullback of a global section to a global section of
  `(Scheme.Modules.pullback f).obj L.obj`, from module
  `Langlands.AlgebraicGeometry.Modules.SectionResidue`.
- `dualNumberProjection K : Spec K[ε] ⟶ Spec K` is
  `Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))`. It is the
  structure morphism `π` of the dual numbers. `K[ε]` is Mathlib's
  `DualNumber K`.
- `dualNumberAugmentation K : Spec K ⟶ Spec K[ε]` is
  `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)`. It is
  the spectrum `ι` of the augmentation `a + bε ↦ a`, the closed point of
  `Spec K[ε]`.
- `IsTangentVectorAt p x t`, for `t : Spec (CommRingCat.of (DualNumber K)) ⟶ X`,
  is `t ≫ p = dualNumberProjection K ∧ dualNumberAugmentation K ≫ t = x`. So
  `t` is a `K[ε]`-point of `X` over `K` whose closed point is `x`.
- `IsNonzeroTangentVectorAt p x t` is
  `IsTangentVectorAt p x t ∧ t ≠ dualNumberProjection K ≫ x`. The excluded
  `K[ε]`-point `π ≫ x` is the zero tangent vector at `x`.

`SeparatesPointsAndTangents p L` is the conjunction `C₀ ∧ C₁ ∧ C₂`, nested to
the right, so `C₀` is `.1`, `C₁` is `.2.1` and `C₂` is `.2.2`. Every `s` below
ranges over `Langlands.SchemeModule.GlobalSections L.obj`, the global sections
`Γ(X, L)`.

- `C₀` (no rational base point): for every `x` with `IsRationalPoint p x` there
  is `s` with `¬ VanishesAlong L x s`.
- `C₁` (separation of rational points): for all `x` and `y` with
  `IsRationalPoint p x`, `IsRationalPoint p y` and `x ≠ y`, there is `s` with
  `VanishesAlong L x s` and `¬ VanishesAlong L y s`.
- `C₂` (separation of rational tangent vectors): for every `x` with
  `IsRationalPoint p x` and every `t` with `IsNonzeroTangentVectorAt p x t`,
  there is `s` with `VanishesAlong L x s` and `¬ VanishesAlong L t s`. The
  last condition is, by definition, `pullbackSection t L.obj s ≠ 0`.

In `C₁` and `C₂` the chosen section does not vanish along `y` or `t`, so it is
nonzero.

## Lemmas

Three small lemmas record facts about the dual-number maps. They are proved
without extra hypotheses.

- `dualNumberAugmentation_comp_dualNumberProjection`:
  `dualNumberAugmentation K ≫ dualNumberProjection K = 𝟙 _`. The proof rewrites
  the composite as `Spec.map` of the composite ring map `K → K[ε] → K`, and
  `Spec.map_id`, and closes the goal by `rfl`. The composite ring map is the
  identity by definition, since the first coordinate of `algebraMap K K[ε] a` is `a`.
- `IsTangentVectorAt.isRationalPoint`: if `IsTangentVectorAt p x t`, then
  `IsRationalPoint p x`. The proof is
  `x ≫ p = ι ≫ t ≫ p = ι ≫ π = 𝟙`. So the hypothesis `IsRationalPoint p x` in
  `C₂` is implied by the tangent-vector hypothesis; it is kept to match the
  wording of the task.
- `isTangentVectorAt_dualNumberProjection_comp`: if `IsRationalPoint p x`, then
  `IsTangentVectorAt p x (dualNumberProjection K ≫ x)`. The proof uses
  `x ≫ p = 𝟙` for the first component and the first lemma for the second. So
  the vector excluded in `IsNonzeroTangentVectorAt` is indeed a tangent vector
  at `x`.

## Correspondence with the source

Milne (p.10, last lines, and p.11, items (a) and (b)) recalls the criterion as
follows. A variety is projective if it has a very ample linear system, and a
linear system `d` is very ample if

- (a) it separates points: for every pair `a, b` of distinct closed points
  there is `D` in `d` with `a ∈ D` but `b ∉ D`; and
- (b) it separates tangent vectors: for every closed point `a` and tangent
  vector `t` to the variety at `a` there is `D ∈ d` with `a ∈ D` but
  `t ∉ T_a(D)`.

In Milne's second step, `d` is the complete linear system `|3D|`. This module
uses the complete linear system of `L`: every `s` in `Γ(X, L)` is allowed, and
no subspace is chosen. A divisor `D` of `d` corresponds to a nonzero section
`s` with `D` the zero divisor of `s`. Then `a ∈ D` means that `s` vanishes at
`a`, which `VanishesAlong L x s` expresses for the `K`-point `x` at `a`.

The following comparison is informal background, not formalized here. Let `K`
be algebraically closed and let `X` be locally of finite type over `K`. Then
the closed points of `X` are its points with residue field `K`, that is, the
rational points `x`. A `K[ε]`-point `t` over `K` with closed point `x`
corresponds to a `K`-linear functional `v` on `m_x/m_x²`, and `π ≫ x` gives
`v = 0`. Suppose `s` vanishes at `x`, and let `f ∈ m_x` be a local equation of
`s` in a trivialization of `L` near `x`. Then the pullback `t*s` corresponds
to `v(f mod m_x²) · ε`. So `t*s ≠ 0` says that `v` does not vanish on the class
of `f`, which is Hartshorne's `t ∉ T_x(D)` for the zero divisor `D` of `s`.
Hence `C₂`, for all nonzero `t` at `x`, says that no nonzero functional on
`m_x/m_x²` annihilates the classes of the sections vanishing at `x`. That is,
these sections span `m_x L_x / m_x² L_x`. In the same setting, `C₁` is Milne's
item (a). Item (b) concerns nonzero tangent vectors, since the zero vector lies
in every `T_a(D)`, and `C₂` quantifies over those.

No equivalence between these predicates and the classical conditions, or with
very ampleness, is proved or assumed here. The module also does not compare
`VanishesAlong` along a rational point with the published residue-field
predicate `Langlands.SchemeModule.NonvanishingAt`.

## Provenance

The formulation is derived (internal) provenance. Neither Milne nor the
criterion he cites states the conditions through `K`-points `x` with
`x ≫ p = 𝟙`, through `K[ε]`-points, or through pullbacks of sections. This
formulation is chosen so that it makes sense for every scheme over every
field and uses only the published `LineBundle`, `GlobalSections` and
`pullbackSection`. It agrees with the classical notions only under the
informal comparison above.

Clause `C₀` (base-point freeness) does not appear in Milne's two-item
paraphrase. It is part of this predicate for two reasons. First, a linear
system defines a morphism to projective space only away from its base points.
Second, `C₁` and `C₂` alone give no information when `X` has at most one
rational point and no nonzero rational tangent vector, as for `X = Spec K`.

Hartshorne's *Algebraic Geometry* is not registered in the project
literature. It is cited only through Milne's statement of the criterion on
pp.10–11. Milne's errata page (snapshot of 2026-10-25) lists no correction to
Section 7.
