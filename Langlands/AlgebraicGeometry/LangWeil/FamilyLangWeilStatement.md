# The Lang–Weil estimate, uniformly in families over the integers

Author: Worker 69.

This module states the uniform Lang–Weil estimate for families of geometrically irreducible
varieties over the integers. It is the common generalization through which the Library's route
proves Conrad's Lemma 4.6 (`Langlands.AlgebraicGeometry.UniformLangWeilStatement`) and its
algebraic-space form. The module contains no proof.

## The statements

`FamilyLangWeilInDimension d` (for `d : ℕ`) says: let `S` and `X` be schemes in a universe `u`
and `f : X ⟶ S` a morphism such that

- `S` is of finite type over `ℤ`: the unique map `specULiftZIsTerminal.from S` to
  `Spec (ULift ℤ)` is locally of finite type, and `S` is quasi-compact (`CompactSpace S`);
- `f` is locally of finite type and quasi-compact;
- `f` is geometrically irreducible (Mathlib's `GeometricallyIrreducible f`: every base change of
  `f` to the spectrum of a field is irreducible, equivalently every fibre is geometrically
  irreducible over its residue field);
- every fibre `f.fiber s` has pure dimension `d`
  (`SchemeFiberGeometry.HasPureDimension`: every irreducible component has topological Krull
  dimension `d`; as the fibres are irreducible, this says each fibre has dimension `d`).

Then there is a real number `C > 0` such that for every finite field `κ` (a type in universe
`u`) and every morphism `s : Spec κ ⟶ S`, the number `N_s` of morphisms
`x : Spec κ ⟶ X` with `x ≫ f = s` satisfies

`|N_s − (#κ) ^ d| ≤ C · (#κ) ^ (d − 1/2)`

in `ℝ`, with `(#κ) ^ (d − 1/2)` the real power. Here `N_s` is `Nat.card` of the subtype of such
`x`, the number of `κ`-points of the fibre `X ×_S Spec κ`, and `#κ = Nat.card κ`.

`FamilyLangWeilStatement` is `∀ d : ℕ, FamilyLangWeilInDimension d`.

## Relation to the sources

- Brian Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
  Lemma 4.6, printed p.12 (registered source `conrad-2011-weil-grothendieck-adelic-points`):
  "Let `f : Y → B` be a smooth separated surjective map between finite type `Z`-schemes such
  that the fibers are geometrically connected of dimension `d`. There is a constant `C > 0` such
  that for all closed points `b ∈ B`, `|#Y_b(k(b)) − q_b^d| ≤ C q_b^{d−1/2}`, where
  `q_b = #k(b)`."
- Serge Lang and André Weil, *Number of points of varieties in finite fields*, Amer. J. Math.
  76 (1954), 819–827 (registered source `lang-weil-1954-number-of-points`; PDF page = printed
  page − 817), Theorem 1, printed p.819 (PDF p.2): "There exists a constant `A(n, d, r)`
  depending only on `n, d, r` such that for any variety `V = V_{n,d,r}` defined over a finite
  field `k` we have `|N − q^r| ≤ δ q^{r−1/2} + A(n, d, r) q^{r−1}`, where `δ = (d − 1)(d − 2)`."
  Here `V` is an (absolutely irreducible) variety of dimension `r` and degree `d` in projective
  `n`-space, `q = #k`, and `N` is the number of points of `V` rational over `k`.
- Terence Tao, *The Lang–Weil bound* (blog post, 31 August 2012; registered source
  `tao-2012-lang-weil-bound`), Theorem 2: for a variety `V` of complexity at most `M`, defined
  over the finite field `F` and geometrically irreducible,
  `|V(F)| = (1 + O_M(|F|^{−1/2})) |F|^{dim V}`. The implied constant depends only on the
  complexity bound `M`. This is the affine, complexity form of Lang and Weil's Theorem 1.

Provenance: derived. The statement generalizes Conrad's Lemma 4.6 in three ways, and
specializes the uniform Lang–Weil estimate (constants depending only on `n, d, r` in Lang–Weil,
only on the complexity in Tao) to a family:

1. smoothness and separatedness are dropped, and geometric connectedness is replaced by
   geometric irreducibility (for smooth fibres the two agree; see below);
2. the base points are all `κ`-points `s : Spec κ ⟶ S` for all finite fields `κ`, not only the
   closed points `b` with their residue fields `k(b)`; the closed-point form is the case
   `κ = k(b)` and `s = Spec k(b) ⟶ S`, the canonical morphism;
3. surjectivity is not assumed separately: geometric irreducibility makes every fibre
   nonempty.

Uniformity in the family is the content shared with Lang–Weil's Theorem 1 and Tao's Theorem 2:
a morphism of finite type over a base of finite type over `ℤ` is covered by finitely many affine
charts, whose fibres are cut out by polynomials of bounded number and degree, so their embedding
dimension, degree and complexity are bounded. Lang–Weil's error term
`δ q^{r−1/2} + A q^{r−1}` is at most `(δ + A) q^{r−1/2}`, the form used here. Points over `s` are
`Spec κ`-valued points of `X` lying over `s`, the standard meaning of `X_s(κ)`.

## Use in the Library's route

Conrad proves Lemma 4.6 with Deligne's Weil II [Del1, Cor. 3.3.3]. The Library follows the
Lang–Weil route instead, through the following statements in
`Langlands/AlgebraicGeometry/LangWeil/`:

- `FamilyPointUpperBoundStatement`: the uniform upper bound `C (#κ) ^ e` for point counts over
  `κ`-points whose fibre has dimension at most `e` (Lang–Weil's Lemma 1, printed p.820; Tao's
  Lemma 1);
- `PlaneCurveHasseWeilStatement`: Schmidt's elementary Hasse–Weil bound for absolutely
  irreducible plane curves;
- `BertiniGenericHyperplaneStatement`: geometric irreducibility of the generic hyperplane section
  (Stacks Project, Lemma 37.32.3);
- `FamilyLangWeilZeroStatement` (the case `d = 0`), `FamilyLangWeilCurveStatement` (the case
  `d = 1` from the plane-curve bound) and `FamilyLangWeilSlicingStatement` (the step from
  `d + 1` to `d + 2` by hyperplane slicing, as in Lang–Weil's proof, printed pp.822–823, and
  Tao's Section 2).

Together they give `FamilyLangWeilStatement` by induction on `d`.
`SpaceUniformLangWeilOfFamilyStatement` reduces the algebraic-space form of Lemma 4.6
(`Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceUniformLangWeilStatement`) to
`FamilyLangWeilStatement` and `FamilyPointUpperBoundStatement`.
`UniformLangWeilOfFamilyStatement` reduces Conrad's Lemma 4.6 to it: a smooth morphism whose
fibres are geometrically connected has geometrically irreducible fibres, because smooth schemes
over a field have domain stalks and a connected locally Noetherian scheme with domain stalks is
integral.

## Status

Open. None of these statements is proved here; each is to be proved through its own focused
proof task.
