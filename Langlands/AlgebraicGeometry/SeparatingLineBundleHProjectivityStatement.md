# Separating line bundles on proper schemes over algebraically closed fields

This module states the very-ampleness criterion that Milne uses in the proof
of Theorem 7.1 ("Every abelian variety is projective"), Milne, *Abelian
Varieties*, author revision of 2022, pp.10–11. Milne recalls it from
Hartshorne's *Algebraic Geometry* (II, 7.8.2). The module contains only the
proposition; it proves nothing.

## The statement

`Langlands.AlgebraicGeometry.SeparatingLineBundleHProjectivityStatement` is a
universe-polymorphic `Prop`. For a universe `u` it says:

for every `K : Type u` with `[Field K]` and `[IsAlgClosed K]`, every
`X : Scheme.{u}`, every morphism `p : X ⟶ Spec (CommRingCat.of K)` and every
`L : Langlands.AlgebraicGeometry.Picard.LineBundle X`,

```text
IsProper p → Langlands.AlgebraicGeometry.Picard.SeparatesPointsAndTangents p L →
  Langlands.AlgebraicGeometry.IsHProjective p
```

The ingredients are the following.

- `IsProper p` is Mathlib's `AlgebraicGeometry.IsProper`: `p` is separated,
  universally closed and locally of finite type.
- `L` is an actual line bundle: an object of the published full subcategory of
  locally free rank-one `X.Modules`, with module `L.obj`.
- `SeparatesPointsAndTangents p L` is the published predicate of module
  `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`. It is the
  conjunction of three clauses on the complete linear system, that is, on all
  global sections `s : Langlands.SchemeModule.GlobalSections L.obj`. A section
  `s` vanishes along a morphism `f : Y ⟶ X` when
  `Langlands.SchemeModule.pullbackSection f L.obj s = 0`. A rational point is
  `x : Spec (CommRingCat.of K) ⟶ X` with `x ≫ p = 𝟙 _`. A nonzero rational
  tangent vector at `x` is `t : Spec (CommRingCat.of (DualNumber K)) ⟶ X`
  with `t ≫ p = π`, `ι ≫ t = x` and `t ≠ π ≫ x`. Here `π : Spec K[ε] ⟶ Spec K`
  is the structure morphism and `ι : Spec K ⟶ Spec K[ε]` is the closed point.
  The clauses are:
  - (C₀) for every rational point `x` some `s` does not vanish along `x`;
  - (C₁) for rational points `x ≠ y` some `s` vanishes along `x` and not
    along `y`;
  - (C₂) for every rational point `x` and every nonzero rational tangent
    vector `t` at `x`, some `s` vanishes along `x` and does not vanish
    along `t`.
- `IsHProjective p` is the published predicate of module
  `Langlands.AlgebraicGeometry.ProjectiveSpace`: there are `n : ℕ` and an
  actual morphism `i : X ⟶ ProjectiveSpace K n` with `IsClosedImmersion i`
  and `i ≫ projectiveSpaceToSpec K n = p`. Here `ProjectiveSpace K n` is the
  Proj of the polynomial ring `MvPolynomial (Fin (n + 1)) K` with its
  total-degree grading.

No other hypothesis is present. In particular the statement covers every
characteristic of `K`, every universe, the empty scheme, schemes of dimension
zero, and non-reduced, reducible or disconnected `X`. It has no hypothesis of
finite dimensionality of `Γ(X, L)`, ampleness, a chosen finite family or
subspace of sections, a given morphism to projective space, an existing
embedding or a comparison certificate. The integer `n` is part of the
conclusion; it is not fixed in advance.

## Correspondence with the source

Milne (p.10, last two lines, and p.11, items (a) and (b)) writes: "Recall
(Hartshorne 1977, II, 7.8.2) that a variety is projective if it has a very
ample linear system, and that a linear system d is very ample if:
(a) it separates points (for every pair a, b of distinct closed points on the
variety, there is a D in d such that a ∈ D but b ∉ D); and (b) it separates
tangent vectors (for every closed point a and tangent vector t to the variety
at a, there exists a D ∈ d such that a ∈ D but t ∉ T_a(D))." In his second
step he applies this to the complete linear system `|3D|`. The task contract
also names Hartshorne II.7.3, the closed-immersion criterion for a morphism to
projective space given by global sections, behind this citation. The present
statement relates to Milne's sentence as follows.

- Linear system. The linear system is the complete one, `Γ(X, L)`: every
  global section of `L` may be used, as for Milne's `|3D|`. A divisor `D` of
  the system corresponds to a nonzero section `s` through its zero subscheme
  `Z(s)`, the largest closed subscheme on which `s` vanishes. `Z(s)` is an
  effective Cartier divisor exactly when `s` is a regular section (Stacks
  Project, Lemma 31.15.9, Tag 02OR). This holds for every nonzero `s` when `X`
  is integral, as Milne's varieties are, but not on every proper `X`. For
  example, `X = Spec K[ε]` with `ε² = 0` is finite, hence proper, over `K`,
  and the section `ε` of `O_X` is a zero divisor whose zero subscheme is not
  an effective Cartier divisor. In every case `a ∈ Z(s)` means that `s`
  vanishes at `a`.
- Closed points. `X` is proper, hence of finite type, over the algebraically
  closed field `K`. So the residue field of every closed point is `K` (Hilbert's
  Nullstellensatz), and the closed points are exactly the images of the
  rational points `x` with `x ≫ p = 𝟙 _`. Distinct closed points give distinct
  rational points. Clause C₁ therefore says that for distinct closed points
  `a` and `b` some section `s` has `a ∈ Z(s)` and `b ∉ Z(s)`. This is the
  zero-subscheme analogue of Milne's item (a). It is item (a) itself, for the
  complete linear system `Γ(X, L)`, when the separating sections are regular,
  so that each `Z(s)` used is an effective Cartier divisor. This holds when `X`
  is integral. Without such a hypothesis the two conditions differ. For
  example, `X = Spec (K × K)` is finite, hence proper, over `K`. For
  `L = O_X`, the sections `(0, 1)` and `(1, 0)` separate its two rational
  points in either order, so C₁ holds. But every regular element of `K × K` is
  a unit, so every effective Cartier divisor on `X` is empty, and no divisor
  separates the two points.
- Tangent vectors. A `K[ε]`-point `t` of `X` over `K` with `ι ≫ t = x` is the
  same as a `K`-linear functional `v` on the Zariski cotangent space
  `m_x/m_x²`, that is, a tangent vector at `x`. The point `π ≫ x` gives `v = 0`.
  If `s` vanishes at `x` with local equation `f ∈ m_x` in a trivialization of
  `L` near `x`, the pullback of `s` along `t` is `v(f mod m_x²) · ε`. So
  "`s` does not vanish along `t`" says `t ∉ T_a(Z(s))` for the zero subscheme
  `Z(s)` of `s`, which is Milne's `t ∉ T_a(D)` when `Z(s)` is the divisor
  `D`. Clause C₂ is therefore the zero-subscheme analogue of Milne's item (b)
  for nonzero tangent vectors; the zero vector lies in every `T_a(D)`, so
  item (b) concerns only those. Equivalently, the sections vanishing at `x`
  span `m_x L_x / m_x² L_x`. It is item (b) itself when the separating
  sections are regular, for example when `X` is integral. On
  `X = Spec K[ε]` with `L = O_X`, the section `ε` vanishes at the only
  rational point and not along any nonzero tangent vector there, so C₂ holds,
  although every effective Cartier divisor on `X` is empty.
- Base points. Clause C₀ is the base-point freeness that a linear system
  needs to define a morphism to projective space. For `X` with at least two
  rational points it follows from C₁; it is required separately so that
  `X = Spec K` and other schemes with a single closed point are covered.
- Conclusion. Milne's "projective" is replaced by `IsHProjective p`, an actual
  closed immersion into some `ProjectiveSpace K n` over `Spec K`. Milne's
  "variety" is replaced by an arbitrary scheme proper over `K`.

These identifications are informal explanations. The statement itself does
not assert them, and it does not assert that `L` is very ample in any formal
sense.

## Why the statement holds in this generality

This is the expected proof, not part of the statement. Let `K` be
algebraically closed and let `p` be proper.

1. Since `X` is proper over a field, `Γ(X, L)` is a finite-dimensional
   `K`-vector space. Choose a basis `s_0, …, s_n`. If `X` is empty, the empty
   morphism into `ProjectiveSpace K 0` is a closed immersion over `Spec K`. If
   `X` is nonempty, it has a closed point, hence a rational point, and C₀
   shows `Γ(X, L) ≠ 0`.
2. The base locus of the sections is closed. If it were nonempty it would
   contain a closed point, which is rational, contradicting C₀. So the basis
   defines a morphism `φ : X ⟶ ProjectiveSpace K n` over `Spec K`, with
   `φ*O(1) ≅ L`.
3. `φ` is proper, since `X` is proper and projective space is separated.
   A section vanishes at a rational point `x` exactly when the corresponding
   linear form vanishes at `φ(x)`. So C₁ makes `φ` injective on closed points.
   Its fibres over closed points therefore have at most one closed point, so
   they are finite; by upper semicontinuity of fibre dimension for proper
   morphisms all fibres are finite. A proper quasi-finite morphism is finite.
4. At a closed point `x` with `φ(x) = P`, the ring map
   `O_{P^n, P} → O_{X, x}` is local, the residue fields are both `K`, and
   C₂ makes `m_P → m_x/m_x²` surjective: otherwise a nonzero functional on
   `m_x/m_x²` vanishing on the image would give a nonzero tangent vector at
   `x` along which every section vanishing at `x` vanishes.
5. Since `φ` is finite and injective on closed points, `(φ_* O_X)_P = O_{X, x}`
   is a finite `O_{P^n, P}`-module. Nakayama's lemma then makes
   `O_{P^n, P} → O_{X, x}` surjective. The cokernel of
   `O_{P^n} → φ_* O_X` is coherent with closed support containing no closed
   point, so it is zero, and `φ` is a closed immersion.

Nothing in this argument uses reducedness, irreducibility or connectedness
of `X`, which is why the statement keeps arbitrary proper `X`.

## Provenance

The formulation is derived (internal) provenance. Milne states the criterion
for varieties and linear systems of divisors and concludes projectivity; the
statement here is phrased through an actual scheme proper over `K`, an actual
line bundle, `K`-points and `K[ε]`-points, pullbacks of sections and the
published `IsHProjective`. It agrees with Milne's sentence only through the
informal identifications above. Base-point freeness on rational points
(C₀) is an explicit hypothesis that Milne's two-item paraphrase leaves
implicit.

Hartshorne's *Algebraic Geometry* is not registered in the project
literature, so it is cited only through Milne's sentence on pp.10–11.
Milne's errata page (snapshot of 2026-10-25) lists no correction to the
pages containing Section 7.

The facts about the zero subscheme `Z(s)` are from the Stacks Project,
Lemma 31.15.9 (Tag 02OR), registered as
`stacks-zero-scheme-cartier-02OR-2026-10-29`. They enter only the informal
identifications, not the Lean statement.
