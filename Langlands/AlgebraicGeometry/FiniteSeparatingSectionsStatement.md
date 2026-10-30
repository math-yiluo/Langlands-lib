# Finitely many sections already separate points and tangent vectors

This module states an intermediate step of the very-ampleness criterion that
Milne uses in the proof of Theorem 7.1 ("Every abelian variety is
projective"), Milne, *Abelian Varieties*, author revision of 2022, pp.10–11.
Milne recalls the criterion from Hartshorne's *Algebraic Geometry* (II, 7.8.2).
The step says that, for a line bundle whose complete linear system separates
rational points and nonzero rational tangent vectors, a finite family of
global sections already does so. The module contains only the proposition; it
proves nothing.

## The statement

`Langlands.AlgebraicGeometry.FiniteSeparatingSectionsStatement` is a
universe-polymorphic `Prop`. For a universe `u` it says:

for every `K : Type u` with `[Field K]` and `[IsAlgClosed K]`, every
`X : Scheme.{u}`, every morphism `p : X ⟶ Spec (CommRingCat.of K)` and every
`L : Langlands.AlgebraicGeometry.Picard.LineBundle X`, if `IsProper p` and
`Langlands.AlgebraicGeometry.Picard.SeparatesPointsAndTangents p L`, then there
are `n : ℕ` and a family
`s : Fin (n + 1) → Langlands.SchemeModule.GlobalSections L.obj` such that,
writing

```text
σ c := ∑ i, Langlands.Scheme.Modules.scalarsFromBase p (c i) • s i
```

for `c : Fin (n + 1) → K`, the following three clauses hold.

1. For every point `x : X` there is `i` with
   `x ∈ Langlands.SchemeModule.nonvanishingLocus L.obj (s i)`.
2. For all `x y : Spec (CommRingCat.of K) ⟶ X` with `IsRationalPoint p x`,
   `IsRationalPoint p y` and `x ≠ y`, there is `c : Fin (n + 1) → K` with
   `VanishesAlong L x (σ c)` and `¬ VanishesAlong L y (σ c)`.
3. For every `x : Spec (CommRingCat.of K) ⟶ X` with `IsRationalPoint p x` and
   every `t : Spec (CommRingCat.of (DualNumber K)) ⟶ X` with
   `IsNonzeroTangentVectorAt p x t`, there is `c : Fin (n + 1) → K` with
   `VanishesAlong L x (σ c)` and `¬ VanishesAlong L t (σ c)`.

In the Lean text `σ c` is written out in full each time it occurs; there is no
auxiliary definition. `IsRationalPoint`, `VanishesAlong` and
`IsNonzeroTangentVectorAt` are those of the namespace
`Langlands.AlgebraicGeometry.Picard`.

## The ingredients

- `IsProper p` is Mathlib's `AlgebraicGeometry.IsProper`: `p` is separated,
  universally closed and locally of finite type.
- `L` is an actual line bundle: an object of the published full subcategory of
  locally free rank-one `X.Modules`, with module `L.obj`.
  `Langlands.SchemeModule.GlobalSections L.obj` is `Γ(L.obj, ⊤)`, the global
  sections of `L`. It is a module over the global functions `Γ(X, ⊤)`.
- `SeparatesPointsAndTangents p L`, `IsRationalPoint`, `VanishesAlong` and
  `IsNonzeroTangentVectorAt` are the published declarations of module
  `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`, used unchanged.
  A rational point is `x : Spec (CommRingCat.of K) ⟶ X` with `x ≫ p = 𝟙 _`. A
  section `s` vanishes along `f : Y ⟶ X` when
  `Langlands.SchemeModule.pullbackSection f L.obj s = 0`. A nonzero rational
  tangent vector at `x` is `t : Spec (CommRingCat.of (DualNumber K)) ⟶ X` with
  `t ≫ p = π`, `ι ≫ t = x` and `t ≠ π ≫ x`, where `π : Spec K[ε] ⟶ Spec K` is
  the structure morphism and `ι : Spec K ⟶ Spec K[ε]` is the closed point.
  `SeparatesPointsAndTangents p L` is the conjunction of three clauses on the
  complete linear system, that is, on all global sections `s`:
  - (C₀) for every rational point `x` some `s` does not vanish along `x`;
  - (C₁) for rational points `x ≠ y` some `s` vanishes along `x` and not
    along `y`;
  - (C₂) for every rational point `x` and every nonzero rational tangent
    vector `t` at `x`, some `s` vanishes along `x` and not along `t`.
- `Langlands.SchemeModule.nonvanishingLocus L.obj s` is the published set of
  points `x : X` at which the value of `s` in the fibre of `L` over the
  residue field `κ(x)` is nonzero (module
  `Langlands.AlgebraicGeometry.Modules.SectionResidue`). Precisely, `x` lies
  in it when `residueSection L.obj s x`, the pullback of `s` along
  `X.fromSpecResidueField x`, is nonzero.
- `Langlands.Scheme.Modules.scalarsFromBase p : K →+* Γ(X, ⊤)` is the
  published ring map of module `Langlands.AlgebraicGeometry.ModuleLinear`: the
  inverse of `Scheme.ΓSpecIso` followed by `p.appTop`. It is how `K` acts on
  global sections here: `scalarsFromBase p a • s` uses the `Γ(X, ⊤)`-module
  structure of `Γ(L.obj, ⊤)`. No `K`-module instance on global sections is
  assumed or introduced.

## Reading the clauses

- The span. As `c` ranges over all of `Fin (n + 1) → K`, `σ c` ranges over
  the `K`-span of `s 0, …, s n` in `Γ(X, L)`, for the `K`-action through
  `scalarsFromBase p`. The family has `n + 1 ≥ 1` members, matching the
  homogeneous coordinates of an `n`-dimensional projective space. It need not
  be linearly independent; repeated or zero members are allowed. The integer
  `n` is part of the conclusion, not fixed in advance.
- Separation clauses. Clauses 2 and 3 are the clauses C₁ and C₂ of
  `SeparatesPointsAndTangents p L` with the separating section required to
  lie in this span rather than in all of `Γ(X, L)`. They are word for word
  the same conditions on `VanishesAlong`, with `s` replaced by `σ c`.
- Base points. Clause 1 is base-point freeness of the family at every point
  of `X`, closed or not, rational or not, and not only along rational points
  as in C₀. It is stated for the members `s i` themselves. Informally, at a
  rational point `x` with image point `x₀`, the field map `κ(x₀) → K` is an
  isomorphism, so `s` does not vanish along `x` exactly when `x₀` lies in the
  nonvanishing locus of `s`; clause 1 therefore implies C₀ for the span. This
  identification is an explanation; the statement does not assert it.

## Excluded and retained generality

No other hypothesis is present. The statement covers every universe and every
characteristic of `K`, the empty scheme, schemes of dimension zero, and
non-reduced, reducible or disconnected `X`. It has no hypothesis of finite
dimensionality of `Γ(X, L)`, reducedness, finite type beyond properness, a
chosen family or subspace of sections, a morphism to projective space,
ampleness or any certificate. If `X` is empty, clauses 1–3 are vacuous and any
one-member family works.

## Relation to the source

Milne (p.10, last two lines, and p.11, items (a) and (b)) writes: "Recall
(Hartshorne 1977, II, 7.8.2) that a variety is projective if it has a very
ample linear system, and that a linear system d is very ample if:
(a) it separates points (for every pair a, b of distinct closed points on the
variety, there is a D in d such that a ∈ D but b ∉ D); and (b) it separates
tangent vectors (for every closed point a and tangent vector t to the variety
at a, there exists a D ∈ d such that a ∈ D but t ∉ T_a(D))." He then applies
this to the complete linear system `|3D|`. The published
`SeparatingLineBundleHProjectivityStatement` (module
`Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityStatement`)
states that criterion for the complete linear system of an actual line bundle;
its Markdown explains how C₀–C₂ correspond to Milne's items (a) and (b). The
present statement isolates one step of its proof.

The task contract places this step in Hartshorne's proof of the criterion
(II.7.3 with Remark II.7.8.2, behind Milne's citation), where the finite family
is a basis of `Γ(X, L)`. This works because, for a proper `X` over a field,
`Γ(X, L)` is a finite-dimensional `K`-vector space. A basis then gives a family
as in the statement: its span is all of `Γ(X, L)`, so clauses 2 and 3 are C₁
and C₂. For clause 1, the common zero locus of the basis is closed. If it were
nonempty it would contain a closed point of `X`. Such a point is rational
because `X` is of finite type over the algebraically closed `K` (Hilbert's
Nullstellensatz), and C₀ excludes it. When `X` is nonempty, C₀ also forces
`Γ(X, L) ≠ 0`, so the basis is nonempty.

The statement asserts only that some finite family exists. Its proof can
therefore avoid the finite dimensionality of `Γ(X, L)`. That coherence theorem
for proper morphisms is not available in the pinned Mathlib or in the Library
at the time of writing.

## Why the statement holds without finite dimensionality

This is the expected proof, not part of the statement. Let `K` be
algebraically closed and `p` proper. Then `X` is quasi-compact and of finite
type over `K`, hence a Noetherian scheme. Every nonempty closed subset of `X`
contains a closed point, and closed points are rational.

0. A finite base-point-free family `S₀`. The nonvanishing loci of sections
   are open. By C₀ they contain every closed point, so their union is an open
   set containing all closed points, hence all of `X`. Quasi-compactness gives
   finitely many sections whose nonvanishing loci cover `X`.
1. Every rational point `x` is good for some finite family `S ⊇ S₀`: the span
   of `S` separates `x` from every other rational point and detects every
   nonzero tangent vector at `x`. For point separation, consider the open sets
   `⋃ {X_σ : σ ∈ span S, σ vanishes at x}`, where `X_σ` is the nonvanishing
   locus. They grow with `S`, and a maximal one exists because `X` is a
   Noetherian topological space. For a maximal `S`, the nonvanishing locus of
   every section vanishing at `x` lies in this union, so C₁ shows that it
   contains every other rational point. For tangent separation, choose an
   affine open `U ∋ x` on which some `s₀ ∈ S₀` does not vanish, and consider
   the ideals of the Noetherian ring `Γ(U, O_X)` generated by the ratios
   `σ / s₀` with `σ ∈ span S` vanishing at `x`. A maximal one contains the
   ratio of every section vanishing at `x`, so C₂ shows that some member of
   `span S` does not vanish along a given nonzero tangent vector at `x`.
   Both maximality conditions persist when `S` is enlarged, so one finite `S`
   serves for both.
2. Goodness is open. If `x` is good for `S`, the morphism to projective space
   given by `S` separates `x` from the other rational points and is unramified
   at `x`. As it is proper, a local closed-immersion criterion makes it a
   closed immersion over a neighbourhood `V` of the image of `x`. Linear forms
   on projective space separate its rational points and tangent vectors, so
   every rational point in the preimage of `V` is good for `S`.
3. These preimages contain all closed points, so they cover `X`, and
   quasi-compactness gives finitely many. The union of the corresponding
   finite families is the required family `s 0, …, s n`. It contains `S₀`,
   which gives clause 1; goodness of every rational point gives clauses 2
   and 3.

Nothing in this argument uses reducedness, irreducibility or connectedness of
`X`.

## Provenance

The formulation is derived (internal) provenance. Milne quotes the
very-ampleness criterion on pp.10–11 but does not state this finite-family
step. The step was isolated as an intermediate result of the proof of that
criterion, so that the proof of the published
`SeparatingLineBundleHProjectivityStatement` can avoid the finite
dimensionality of `Γ(X, L)`. The exact Lean form was fixed by the task
contract for the parent proof task of that statement. It is phrased through an
actual scheme proper over `K`, an actual line bundle, `K`-points and
`K[ε]`-points, pullbacks of sections, residue-field nonvanishing loci and the
`K`-action through `scalarsFromBase p`. It agrees with Milne's sentences only
through the informal identifications above.

Hartshorne's *Algebraic Geometry* is not registered in the project literature,
so it is cited only through Milne's sentence on p.10. Milne's errata page
(snapshot of 2026-10-25) lists no correction to Section 7: its entries skip
from printed p.104 (Section 1) to p.119 (Section 11), and Section 7 lies
between them. The page states that the xnotes version used here incorporates
all listed corrections.
