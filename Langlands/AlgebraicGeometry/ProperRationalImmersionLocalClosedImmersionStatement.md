# A local closed-immersion criterion at a rational point for proper morphisms

`Langlands.AlgebraicGeometry.ProperRationalImmersionLocalClosedImmersionStatement`
is a universe-polymorphic proposition with level `u`. It is a statement target
only. This module proves none of its content.

## Exact statement

Write `Spec K` for `Spec (CommRingCat.of K)` and `K[ε]` for Mathlib's
`DualNumber K`. The proposition is

```text
∀ (K : Type u) [Field K] [IsAlgClosed K] (X Y : Scheme.{u})
  (p : X ⟶ Spec K) (q : Y ⟶ Spec K)
  [LocallyOfFiniteType p] [LocallyOfFiniteType q]
  (f : X ⟶ Y) [IsProper f],
  f ≫ q = p →
  ∀ (x : Spec K ⟶ X), Picard.IsRationalPoint p x →
    (∀ (y : Spec K ⟶ X), Picard.IsRationalPoint p y →
      y ≫ f = x ≫ f → y = x) →                                   -- (P)
    (∀ (t : Spec K[ε] ⟶ X), Picard.IsTangentVectorAt p x t →
      t ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f →
      t = Picard.dualNumberProjection K ≫ x) →                   -- (T)
    ∃ V : Y.Opens,
      f.base (x.base (IsLocalRing.closedPoint K)) ∈ V ∧
      IsClosedImmersion (f ∣_ V)
```

The Lean body is the interface given in the task objective, unchanged. The
predicates `Picard.IsRationalPoint`, `Picard.IsTangentVectorAt` and the map
`Picard.dualNumberProjection` are imported unchanged from the published module
`Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`. Everything else is
Mathlib.

## Hypotheses

- `K : Type u` is an algebraically closed field of arbitrary characteristic.
  `X` and `Y` are schemes in the same universe `u`.
- `p : X ⟶ Spec K` and `q : Y ⟶ Spec K` are structure morphisms, both locally
  of finite type. The equation `f ≫ q = p` says that `f : X ⟶ Y` is a morphism
  over `K`.
- `f` is proper in Mathlib's sense `IsProper`: separated, universally closed and
  locally of finite type.
- The instance `[LocallyOfFiniteType p]` follows from the others, since
  `p = f ≫ q` is a composite of morphisms locally of finite type. It is kept to
  match the suggested interface and adds no restriction.
- `x : Spec K ⟶ X` is a rational point: `Picard.IsRationalPoint p x` is
  `x ≫ p = 𝟙 _`. The scheme `Spec K` has exactly one point,
  `IsLocalRing.closedPoint K`. Write `x₀ = x.base (IsLocalRing.closedPoint K)`
  for the point of `X` that `x` picks out, and `y₀ = f.base x₀` for its image
  in `Y`.
- (P), the rational fibre hypothesis: every rational point `y` of `X` with
  `y ≫ f = x ≫ f` equals `x`. Here `x ≫ f` is a rational point of `Y` for `q`,
  because `(x ≫ f) ≫ q = x ≫ p = 𝟙 _`. So (P) says that `x` is the only
  rational point of `X` over this rational point of `Y`.
- (T), the tangent kernel hypothesis: every rational tangent vector `t` at `x`
  with `t ≫ f = (Picard.dualNumberProjection K ≫ x) ≫ f` equals
  `Picard.dualNumberProjection K ≫ x`. By definition,
  `Picard.IsTangentVectorAt p x t` says `t ≫ p = dualNumberProjection K` and
  `dualNumberAugmentation K ≫ t = x`. So `t` is a `K[ε]`-point of `X` over `K`
  whose closed point is `x`. Its image `t ≫ f` is a `K[ε]`-point of `Y` over
  `K` at `x ≫ f`. The morphism
  `(dualNumberProjection K ≫ x) ≫ f = dualNumberProjection K ≫ (x ≫ f)` is the
  constant `K[ε]`-point, the zero tangent vector at `x ≫ f`. So (T) says that
  the only tangent vector at `x` that `f` sends to zero is the zero tangent
  vector `dualNumberProjection K ≫ x`: the rational tangent kernel of `f` at `x`
  is trivial.

Both (P) and (T) concern only the specified point `x`. Nothing is assumed at
other rational points of `X`, at non-rational points, or over other points of
`Y`.

## Conclusion: local on the target

The conclusion asks for an open `V : Y.Opens` of the target containing the
image point `y₀ = f.base (x.base (IsLocalRing.closedPoint K))` such that
`f ∣_ V` is a closed immersion. Here `f ∣_ V` is Mathlib's `morphismRestrict f V
: f ⁻¹ᵁ V ⟶ V`, the restriction of `f` to the entire preimage of `V`. Mathlib's
`IsClosedImmersion` asks that the underlying continuous map is a closed embedding
and that the morphism is surjective on stalks.

So the conclusion says that `f` is a closed immersion over a neighbourhood of
`y₀` in `Y`. It is not a statement about a neighbourhood of `x₀` in `X`. A
source-side conclusion, such as `f` being a closed immersion on some open
`U ∋ x₀`, would ignore the other points of `X` over `V`, and would not be this
proposition. Over `V`, every point of `X` is accounted for. Informally, the
fibre of `f` over `y₀` is then a closed subscheme of `Spec κ(y₀) = Spec K`
containing `x₀`, so it is the single reduced point `x₀`.

The global companion criterion is the separate statement task
`ff70fb1d-235d-4247-8160-22c713da74a4`
(`ProperRationalImmersionClosedImmersionStatement`). It assumes the point and
tangent hypotheses at every rational point and concludes `IsClosedImmersion f`.
The present local proposition neither assumes nor concludes anything at other
points. Informally, the global criterion follows from the local one as follows.
Closed immersions are local on the target. The image `f(X)` is closed since `f`
is proper, and over its open complement the preimage is empty. Every closed
point of `Y` in `f(X)` is the image of a closed point of its nonempty fibre,
which is a rational point of `X`; the local criterion gives an open `V` around
it. These opens and the complement of `f(X)` contain every closed point of `Y`,
so they cover the Jacobson scheme `Y`. This is why neither statement needs `Y`
to be proper. This derivation is an informal explanation, not part of this
statement.

## The rational and dual-number formulation

The statement uses the project's formulation through `K`-points and
`K[ε]`-points from `Langlands.AlgebraicGeometry.Picard.PointTangentSeparation`,
not closed points, residue fields or Zariski tangent spaces. The following
comparison with the classical notions is informal background. It is neither
stated nor assumed in Lean.

Let `K` be algebraically closed and `X` locally of finite type over `K`. Then
the rational points of `X` correspond to its closed points (Mathlib's
`AlgebraicGeometry.pointEquivClosedPoint`, which sends `x` to
`x.base (IsLocalRing.closedPoint K)`). Two rational points of `Y` with the same
image point are equal (Mathlib's `AlgebraicGeometry.ext_of_apply_closedPoint_eq`).
So (P) says that `x₀` is the only closed point of `X` lying over `y₀`. Since
`X` is a Jacobson scheme and the fibre over `y₀` is closed in `X`, (P) then
forces this fibre to be the single point `x₀`. Indeed, a fibre point `z ≠ x₀`
would not be closed. An affine open neighbourhood of `z` then meets the closure
of `z` in an irreducible `K`-scheme of finite type and positive dimension. That
scheme has infinitely many closed points, which are closed points of `X` over
`y₀`, contradicting (P).

A `K[ε]`-point `t` of `X` over `K` with closed point `x₀` corresponds to a local
`K`-algebra homomorphism `𝒪_{X,x₀} → K[ε]` lifting the residue map, hence to a
`K`-linear functional on `𝔪_{x₀}/𝔪_{x₀}²`. The published
`Langlands.AlgebraicGeometry.cotangentDualNumberLift` constructs the algebra map
from a functional. The constant point `dualNumberProjection K ≫ x` corresponds
to the zero functional, and composing with `f` corresponds to precomposing the
functional with the cotangent map `𝔪_{y₀}/𝔪_{y₀}² → 𝔪_{x₀}/𝔪_{x₀}²`. So (T)
says that the tangent map `T_{x₀}X → T_{y₀}Y` is injective. Over a field this
is equivalent to surjectivity of the cotangent map, since a nonzero functional
vanishing on a proper image would lie in the kernel.

## Scope and edge cases

- The universe `u` and the characteristic of `K` are arbitrary.
- `X` may be empty; then there is no rational point and the proposition is
  vacuous at that instance. If `Y` is empty, so is `X`.
- Dimension zero is included: `X` and `Y` may be spectra of finite-dimensional
  `K`-algebras.
- `X` and `Y` may be non-reduced. The conclusion is then a genuine
  scheme-theoretic condition: it includes surjectivity on stalks, not just
  injectivity or a closed embedding of underlying spaces.
- `Y` is only assumed locally of finite type over `K`. It need not be proper,
  separated, quasi-compact or of finite type over `K`. `X` need not be proper
  over `K`; only `f` is proper.
- There is no finite, quasi-finite, monomorphism, unramifiedness,
  stalk-surjectivity, reducedness, smoothness or Noetherian premise beyond
  local finite type, and no supplied certificate of any part of the conclusion.

## Why each hypothesis is needed

These examples are informal and not formalized.

- Without (P): the fold map `Spec K ⊔ Spec K → Spec K` is finite, hence proper,
  and both tangent spaces are zero, so (T) holds at either point. The only open
  containing the image point is all of `Spec K`, and the fold map is not
  injective, so the conclusion fails.
- Without (T): take `X = Spec K[ε]`, `Y = Spec K`, `q = 𝟙`,
  `f = p = dualNumberProjection K` and `x = dualNumberAugmentation K`. Then (P)
  holds, since `x` is the only rational point of `X`: a `K`-algebra map
  `K[ε] → K` must send the nilpotent `ε` to `0`. The vector `t = 𝟙` is a
  tangent vector at `x` with `t ≫ f = (dualNumberProjection K ≫ x) ≫ f`, but
  `𝟙 ≠ dualNumberProjection K ≫ x`, because this composite is the spectrum of
  the ring endomorphism `a + bε ↦ a` of `K[ε]`. The conclusion fails, as
  `K → K[ε]` is not surjective. Here `f` is a homeomorphism, so topological
  injectivity alone does not suffice.
- Without properness: let `Y = 𝔸¹_K` and `X = Spec K ⊔ (𝔸¹_K ∖ {0})`, mapping
  the point to the origin and the second piece by the open inclusion. Then `f`
  is locally of finite type and separated, (P) and (T) hold at the point over
  the origin, and `f` is not proper. For any open `V` containing the origin,
  the preimage of `V` contains the open and closed piece `V ∖ {0}`, whose image
  is not closed in `V`. So `f ∣_ V` is not a closed map, and not a closed
  immersion.

## Source correspondence and derived provenance

The source is the registered original `stacks-very-ampleness-support-2026-10-29`
(content SHA256
`51a2acde9eaa6c049ffffdb45977818fe541190390edede792ebfff339eed121`), file
`0E8R.html`: Stacks Project, Section 33.23 (tag 0E8R), Lemma 33.23.1 and its
proof. The lemma takes a proper `k`-scheme `X` over an algebraically closed
field `k`, an invertible module `ℒ` and a subspace `V ⊂ H⁰(X, ℒ)` that
separates closed points (1) and nonzero tangent vectors (2), and concludes that
`ℒ` is very ample and `φ_{ℒ,V} : X → 𝐏(V)` is a closed immersion. Its proof
runs as follows. `φ` is proper. By (1) it is injective on closed points, so its
fibres over closed points are singletons, and it is finite (Cohomology of
Schemes, Lemma 30.21.2). It suffices that `𝒪_{𝐏(V)} → φ_*𝒪_X` is surjective,
which may be checked on stalks at closed points. For a closed point `x` with
image `p`, `φ⁻¹({p}) = {x}` and properness make the stalk of `φ♯` at `p` the
local ring map `𝒪_{𝐏(V),p} → 𝒪_{X,x}`, so `𝒪_{X,x}` is a finite module.
Both residue fields are `k` by the Nullstellensatz. Condition (2) makes the
tangent map `T_{X/k,x} → T_{𝐏(V)/k,p}` injective, hence the cotangent map
`𝔪_p/𝔪_p² → 𝔪_x/𝔪_x²` surjective (Lemma 33.16.5). Algebra, Lemma 10.20.3
finishes.

This proposition is a derived formulation, not a verbatim theorem of the
source. It extracts the finite-morphism and Nakayama steps of that proof at a
single point, and makes the following changes.

- The particular target `𝐏(V)` and morphism `φ_{ℒ,V}` are replaced by an
  arbitrary proper `K`-morphism `f` into an arbitrary scheme `Y` locally of
  finite type over `K`. There is no line bundle and no space of sections. `X`
  need not be proper over `K`.
- The source's hypotheses (1) and (2) on sections are replaced by the two
  consequences that the proof uses at one point: (P), injectivity on rational
  points over `y₀`, and (T), injectivity of the tangent map at `x`. Both are
  stated through the project's `K`-points and `K[ε]`-points.
- The source proves finiteness of `φ` globally, from singleton fibres over all
  closed points. Here only the fibre over `y₀` is controlled, so finiteness is
  available only near `y₀`. The conclusion is correspondingly local: `f` is a
  closed immersion over a neighbourhood of `y₀`.
- The registered README notes that the source's "fibre over any closed point is
  a singleton" fails for closed points outside the image, whose fibre is empty,
  and that point injectivity gives at most one closed point in each closed
  fibre. Here `y₀` is in the image, so its fibre contains `x₀`, and (P) makes
  `x₀` its only closed point. The README's base-point caveat concerns the
  section hypotheses of Lemma 33.23.1 and does not arise here.

The page's comment thread was read. Comment #7149 reports the misprint "there
exist" for "there exists" in condition (2), fixed per comment #7299. It does
not change the mathematics.

## Expected proof route

This is guidance for the proof task, not part of the statement; a different
valid route is allowed.

1. Use rational points as closed points and Jacobsonness to show that the
   fibre of `f` over `y₀` is `{x₀}`.
2. Apply Mathlib's
   `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton`
   (in `Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`, carrying Mathlib's
   Stacks tag attribute 02UP) to get an open `V₀ ∋ y₀` with `f ∣_ V₀` finite.
3. Turn (T) into surjectivity of the cotangent map of the stalk map at `x₀`.
   The published modules `Langlands.AlgebraicGeometry.CotangentDualNumber`,
   `Langlands.AlgebraicGeometry.Picard.StalkTangent` and
   `Langlands.AlgebraicGeometry.Picard.StalkTangentNaturality` give the
   relevant dual-number algebra maps and stalk algebras. The sibling statement
   task `0331bf1a-f24e-41dc-a296-9bbd055c9e98` states this step.
4. Apply Nakayama to the finite local map `𝒪_{Y,y₀} → 𝒪_{X,x₀}` to get its
   surjectivity. The sibling statement task
   `e4fa5987-8bef-436d-9702-80bbe4536255` states this algebraic step.
5. Over an affine open inside `V₀`, the preimage is affine since `f ∣_ V₀` is
   finite, and the cokernel of `𝒪_Y → f_*𝒪_X` is a finite module whose
   localization at `y₀` vanishes. So it vanishes after shrinking to a smaller
   affine neighbourhood. A morphism of affine schemes that is surjective on
   global sections is a closed immersion (Mathlib's
   `IsClosedImmersion.of_surjective_of_isAffine`).

## What is not claimed

- No proof of the proposition.
- Not the global criterion, the very-ampleness criterion of Lemma 33.23.1, or
  any statement about line bundles or projective space.
- No formal equivalence between the rational and dual-number hypotheses and the
  classical closed-point and Zariski-tangent-space conditions.
