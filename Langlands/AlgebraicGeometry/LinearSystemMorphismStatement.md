# The morphism to projective space defined by finitely many sections

This module states one intermediate step of the very-ampleness criterion
that Milne uses in the proof of Theorem 7.1 ("Every abelian variety is
projective"), Milne, *Abelian Varieties*, author revision of 2022, pp.10–11.
Finitely many global sections of a line bundle without common zero define a
morphism to projective space, and this morphism is described on rational
points and rational tangent vectors by the vanishing of linear combinations of
the sections. The module contains only the proposition; it proves nothing.

## The statement

`Langlands.AlgebraicGeometry.LinearSystemMorphismStatement` is a
universe-polymorphic `Prop`. For a universe `u` it says:

for every `K : Type u` with `[Field K]`, every `X : Scheme.{u}`, every morphism
`p : X ⟶ Spec (CommRingCat.of K)`, every
`L : Langlands.AlgebraicGeometry.Picard.LineBundle X`, every `n : ℕ` and every
family `s : Fin (n + 1) → Langlands.SchemeModule.GlobalSections L.obj`, if

```text
∀ x : X, ∃ i, x ∈ Langlands.SchemeModule.nonvanishingLocus L.obj (s i)
```

then there is `φ : X ⟶ ProjectiveSpace K n` with
`φ ≫ projectiveSpaceToSpec K n = p` such that, writing

```text
σ c := ∑ i, Langlands.Scheme.Modules.scalarsFromBase p (c i) • s i
```

for `c : Fin (n + 1) → K` (in Lean the sum is written out in full each time):

1. for all `x y : Spec (CommRingCat.of K) ⟶ X` with
   `Picard.IsRationalPoint p x` and `Picard.IsRationalPoint p y`,

   ```text
   x ≫ φ = y ≫ φ ↔
     ∀ c, Picard.VanishesAlong L x (σ c) → Picard.VanishesAlong L y (σ c)
   ```

2. for all `x : Spec (CommRingCat.of K) ⟶ X` and
   `t : Spec (CommRingCat.of (DualNumber K)) ⟶ X` with
   `Picard.IsRationalPoint p x` and `Picard.IsTangentVectorAt p x t`,

   ```text
   t ≫ φ = (Picard.dualNumberProjection K ≫ x) ≫ φ ↔
     ∀ c, Picard.VanishesAlong L x (σ c) → Picard.VanishesAlong L t (σ c)
   ```

Inside the existential, the conclusion is the conjunction of the equation over
`Spec K` and the two clauses, nested to the right: `φ ≫ projectiveSpaceToSpec K n = p` is `.1`,
clause 1 is `.2.1` and clause 2 is `.2.2`.

## The ingredients

All names below are published Library declarations, used unchanged.

- `Picard.LineBundle X` is the published full subcategory of locally free
  rank-one actual `X.Modules`; `L.obj` is the module.
  `SchemeModule.GlobalSections L.obj` is `Γ(L.obj, ⊤)`, the global sections.
- `SchemeModule.nonvanishingLocus L.obj (s i)` (module
  `Langlands.AlgebraicGeometry.Modules.SectionResidue`) is the set of points
  `x : X` at which the value of `s i` in the residue-field fibre is nonzero.
  The hypothesis says that the `s i` have no common zero at any point of `X`,
  closed or not. By the published `lineBundleSectionResidueComparison` this
  locus is the open set where `s i` generates `L`, so the hypothesis says
  that the `s i` generate `L`.
- `ProjectiveSpace K n` is the Proj of `MvPolynomial (Fin (n + 1)) K` with its
  total-degree grading, and `projectiveSpaceToSpec K n` is its structure
  morphism to `Spec K` (module `Langlands.AlgebraicGeometry.ProjectiveSpace`).
  So `φ` is a morphism over `Spec K`.
- `Scheme.Modules.scalarsFromBase p : K →+* Γ(X, ⊤)` (module
  `Langlands.AlgebraicGeometry.ModuleLinear`) is the ring map induced by `p`
  on global functions. Global sections of `L.obj` are a module over
  `Γ(X, ⊤)`, so `K` acts on them through `scalarsFromBase p`. Thus `σ c` is
  the `K`-linear combination `∑ c_i s_i`, and the `σ c` form the linear
  system spanned by the `s i`.
- From module `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`:
  `IsRationalPoint p x` is `x ≫ p = 𝟙 _`; `VanishesAlong L f s` is
  `SchemeModule.pullbackSection f L.obj s = 0`, the vanishing of the pulled-back
  section; `dualNumberProjection K : Spec K[ε] ⟶ Spec K` is `Spec.map` of the
  algebra map `K → K[ε]`, where `K[ε]` is Mathlib's `DualNumber K`; and
  `IsTangentVectorAt p x t` is
  `t ≫ p = dualNumberProjection K ∧ dualNumberAugmentation K ≫ t = x`, where
  `dualNumberAugmentation K : Spec K ⟶ Spec K[ε]` is `Spec.map` of the
  augmentation `a + bε ↦ a`. So `t` is a `K[ε]`-point of `X` over `K` whose
  closed point is `x`, and `dualNumberProjection K ≫ x` is the constant
  `K[ε]`-point at `x`.

No other hypothesis is present. The field is arbitrary, not necessarily
algebraically closed, of any characteristic. The scheme `X` is arbitrary:
there is no finite type, properness, separatedness or reducedness hypothesis,
and `X` may be empty. The case `n = 0` is included; then `ProjectiveSpace K 0`
is the Proj of a polynomial ring in one variable, and the single section
`s 0` generates `L`. No morphism, certificate or comparison data is given as
a premise; the morphism `φ` is part of the conclusion.

`IsTangentVectorAt` allows the zero tangent vector
`t = dualNumberProjection K ≫ x`. For it both sides of clause 2 hold, because
`ι ≫ π = 𝟙` (with `ι = dualNumberAugmentation K`, `π = dualNumberProjection K`),
so vanishing along `x` gives vanishing along `π ≫ x`. The hypothesis
`IsRationalPoint p x` in clause 2 already follows from
`IsTangentVectorAt p x t` (published lemma `IsTangentVectorAt.isRationalPoint`);
it is kept to make the clause easy to read.

## Meaning

The intended witness `φ` is the morphism of the linear system: on the open set
`X_{s_j}` where `s j` does not vanish, `s i = r_ij · s j` for a unique
`r_ij ∈ Γ(X_{s_j}, O_X)`, and `φ` maps `X_{s_j}` to the standard chart
`D₊(X_j) = Spec K[X_0/X_j, …, X_n/X_j]` by `X_i/X_j ↦ r_ij`. On overlaps these
chart maps agree, since the ratios change by the unit `r_jk`, so they glue.
In homogeneous coordinates, `φ` is `[s 0 : … : s n]`.

Clause 1 says that two `K`-points `x` and `y` of `X` have the same image in
`ProjectiveSpace K n` exactly when every section in the linear system spanned
by the `s i` that vanishes at `x` also vanishes at `y`. Clause 2 makes the same
comparison for a `K[ε]`-point `t` over `x` and the constant `K[ε]`-point at
`x`: `t ≫ φ` is the constant `K[ε]`-point at `φ ∘ x` exactly when every such
section vanishing at `x` also vanishes along `t`. In tangent-space terms
(informally): `φ` kills the tangent vector `t` exactly when it is tangent to
the zero locus of every section of the system through `x`.

The right-hand implications are equivalent to the corresponding
bi-implications.

- In clause 2, vanishing along `t` always implies vanishing along `x`. Indeed
  `x = ι ≫ t`, and the pullback of a section along a composite agrees with the
  iterated pullback up to the canonical isomorphism, which preserves zero.
  So the implication "vanishing along `x` gives vanishing along `t`" is the same
  as "vanishing along `x` iff vanishing along `t`".
- In clause 1, for a rational point `x` the set of `c ∈ K^{n+1}` with
  `σ c` vanishing along `x` is a hyperplane: choosing a basis of the
  one-dimensional `K`-space of sections of the pullback of `L` along `x`,
  this set is `{c | ∑ c_i a_i = 0}`, where `a_i` is the coordinate of the
  pullback of `s i`, and not all `a_i` vanish because the `s i` have no common
  zero. A hyperplane contained in another hyperplane equals it, so the
  implication is the same as the bi-implication.

These equivalences are explanation only; the Lean statement uses the
implications as written.

The statement asserts only the existence of some `φ` over `Spec K` with the two
properties. It does not say that `φ` is unique, that `φ` pulls `D₊(X_j)` back
to `X_{s_j}`, or that `φ` pulls `O(1)` back to `L`; consumers can use only the
equation over `Spec K` and clauses 1 and 2.

## Why the statement holds (proof sketch, not formalized here)

Construction. Let `ψ : K[X_0, …, X_n] → ⊕_d Γ(X, L^{⊗d})` be the graded ring
map with `X_i ↦ s i`, with `K` acting through `scalarsFromBase p`. The union of
the loci `X_{s_i}` is all of `X` by hypothesis. Stacks Lemma 27.14.1 (Tag
01NJ) then gives a morphism `φ : X ⟶ Proj K[X_0, …, X_n] = ProjectiveSpace K n`
with `φ⁻¹ D₊(X_j) = X_{s_j}`, whose restriction to `X_{s_j}` is given on rings
by `X_i/X_j ↦ r_ij` as described above. Its proof constructs the morphism
locally by these chart maps and glues them by uniqueness. Constants map through `scalarsFromBase p` on every
chart, so `φ ≫ projectiveSpaceToSpec K n = p`.

Dictionary. A `T`-point `g` of `X` landing in `X_{s_j}`, for `T = Spec K` or
`Spec K[ε]` over `K`, has `g ≫ φ` determined by the pulled-back ratios
`g^* r_ij`, since `D₊(X_j)` is affine over `K` with coordinates `X_i/X_j`.

- Let `x` be a rational point in `X_{s_j}` and let `α_i ∈ K` be the value of
  `r_ij` at `x`, so `α_j = 1`. The pullback of `s j` along `x` is a basis
  vector, the pullback of `s i` is `α_i` times it, and `x^*(p^* c) = c`
  because `x ≫ p = 𝟙`. Hence `σ c` vanishes along `x` iff `∑ c_i α_i = 0`.
- Clause 1. If `y ≫ φ = x ≫ φ`, then `y` lands in `φ⁻¹ D₊(X_j) = X_{s_j}` with
  the same values `α_i`, so the vanishing conditions agree. Conversely, test
  `c = e_i − α_i e_j`, which vanishes at `x`. If `y` were outside `X_{s_j}`,
  then `s j` would vanish at `y`, so every `s i` would vanish at `y`,
  contradicting the hypothesis. So `y` lies in `X_{s_j}`, its values `β_i` of
  `r_ij` satisfy `β_i = α_i`, and `y ≫ φ = x ≫ φ`.
- Clause 2. `Spec K[ε]` has one point, so `t` lands in `X_{s_j}`; write
  `t^* r_ij = α_i + β_i ε` (the constant point gives `α_i`). Then
  `t ≫ φ = (π ≫ x) ≫ φ` iff every `β_i = 0`, and `σ c` vanishes along `t` iff
  `∑ c_i α_i = 0` and `∑ c_i β_i = 0`. Testing `c = e_i − α_i e_j`, with
  `β_j = 0`, gives `β_i = 0` from the right side; the converse is immediate.

The sketch uses no property of `K` beyond being a field and no property of
`X` beyond the hypothesis on the `s i`. That is why the statement is posed in
this generality. Formalizing the gluing of chart maps and the dictionary is
the job of a separate proof task.

## Correspondence with the sources

The morphism defined by finitely many generating sections is Stacks Project,
Lemma 27.13.1 and Definition 27.13.2 (Tag 01ND): a pair
`(L, (s_0, …, s_n))` with the `s_i` generating `L` defines
`φ_{(L, (s_0, …, s_n))} : Y ⟶ P^n_S`, characterized by `φ^* O(1) = L` and
`φ^* T_i = s_i`. The construction directly into the Proj of a graded ring,
with `φ⁻¹ D₊(f) = T_{ψ(f)}` and the affine-chart gluing used above, is
Lemma 27.14.1 (Tag 01NJ). Stacks defines `P^n_S` by base change from `P^n_Z`;
the Library's `ProjectiveSpace K n` is the Proj of the polynomial ring over
`K` itself, as its own module records.

Milne uses morphisms defined by linear systems: his proof of Theorem 7.1 shows
that the complete linear system `|3D|` is very ample, and p.11 refers to "the
map `A_k̄ ↪ P^n` defined by `|D_k̄|`". The two clauses are the dictionary that
turns the separation hypotheses of Hartshorne's criterion, as quoted by Milne
on pp.10–11, for the span of the `s i`, into two properties of `φ`: `φ` is
injective on rational points, and no `K[ε]`-point `t` at a rational point `x`
other than the constant one satisfies `t ≫ φ = (π ≫ x) ≫ φ`. Hartshorne's *Algebraic Geometry* (Proposition II.7.1 and the proof
of Proposition II.7.3, which the task names) is not registered in the project
literature, and no claim is made here about its text.

## Provenance

The construction of `φ` follows the registered Stacks sources. The formulation
of clauses 1 and 2 through `K`-points with `x ≫ p = 𝟙`, `K[ε]`-points over
`K`, pullbacks of sections and linear combinations through `scalarsFromBase p`
is derived (internal) provenance. Neither Stacks nor Milne states it in this
form. It is chosen so that it makes sense for every scheme over every field,
uses only published Library declarations, and supplies exactly the two
hypotheses needed by the closed-immersion step of the very-ampleness
argument.

Sources:

- Stacks Project, Section 27.13 (Tag 01ND), registered as
  `stacks-projective-space-twists-morphisms-2026-10-26`
  (file `01ND.html`).
- Stacks Project, Section 27.14 (Tag 01NJ), registered as
  `stacks-very-ampleness-support-2026-10-29` (file `01NJ.html`; no page
  comments).
- J. S. Milne, *Abelian Varieties*, author revision of 2022, pp.10–11,
  registered as `milne-abelian-varieties-1986-author-2022`. Milne's errata
  page (snapshot of 2026-10-25) lists no correction to Section 7.
