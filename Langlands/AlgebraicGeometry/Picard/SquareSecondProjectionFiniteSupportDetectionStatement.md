# Finite-support cohomology detection for the second abelian-square projection

`Langlands.AbelianScheme.AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement`
is a universe-polymorphic `Prop`-valued definition. It states the geometric
consequence used in the second Leray calculation of Edixhoven, van der Geer
and Moonen, Proposition (7.21), printed p.106 / one-based PDF p.110. This
module supplies a statement target, with no proof or new axiom.

## Exact statement

Fix any field `K : Type u` with `[Field K] [IsAlgClosed K]`, an actual
`A : AbelianScheme (Spec (CommRingCat.of K))`, and write

```text
S  = Spec (CommRingCat.of K)
a  = A.X.hom : A.X.left ⟶ S
Z  = pullback a a
p1 = pullback.fst a a
p2 = pullback.snd a a
sZ = p1 ≫ a : Z ⟶ S.
```

For every actual line bundle `Q : LineBundle Z` and every
`F : Set (Over.mk (𝟙 S) ⟶ A.X)`, the statement says:

1. If `F.Finite`;
2. if for every rational point `x ∉ F` and every `n : ℕ`,
   `Hⁿ(A, i2(x)⁎Q)` is zero;
3. and if for every `n : ℕ`, `Hⁿ(Z, Q)` is zero;
4. then for every rational point `x` and every `n : ℕ`,
   `Hⁿ(A, i2(x)⁎Q)` is zero.

Every displayed `Hⁿ` denotes the actual `DerivedSections.relativeCohomology`
functor below. In particular, all degrees include zero. `F` is a finite
set of actual rational points, with no chosen enumeration and no
scheme-theoretic support condition in its definition.

Inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory CategoryTheory.Limits AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.AlgebraicGeometry.Modules`,
the complete defining expression is:

```lean
def AlgClosedFieldSquareSecondProjectionFiniteSupportDetectionStatement : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (A : AbelianScheme (Spec (CommRingCat.of K)))
    (Q : LineBundle (pullback A.X.hom A.X.hom))
    (F : Set (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X)),
    let sZ := pullback.fst A.X.hom A.X.hom ≫ A.X.hom
    let i2 : (Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X) →
        (A.X.left ⟶ pullback A.X.hom A.X.hom) :=
      fun x ↦ pullback.lift (𝟙 A.X.left) (A.X.hom ≫ x.left) (by
        have hx : x.left ≫ A.X.hom = 𝟙 _ := x.w
        simp [Category.assoc, hx])
    F.Finite →
      (∀ x, x ∉ F → ∀ n : ℕ,
        IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj
          ((LineBundle.pullback (i2 x)).obj Q).obj)) →
      (∀ n : ℕ, IsZero ((DerivedSections.relativeCohomology sZ n).obj Q.obj)) →
      ∀ x (n : ℕ),
        IsZero ((DerivedSections.relativeCohomology A.X.hom n).obj
          ((LineBundle.pullback (i2 x)).obj Q).obj)
```

There are no additional outer parameters or hypotheses.

## Actual fibre embedding and cohomology

A rational point `x : Over.mk (𝟙 S) ⟶ A.X` has underlying scheme morphism
`x.left : S ⟶ A.X.left`. Its over-morphism equation `x.w` gives
`x.left ≫ a = 𝟙 S`. The local definition

```text
i2(x) = pullback.lift (𝟙 A.X.left) (a ≫ x.left) (section equation)
```

therefore has
`i2(x) ≫ p1 = 𝟙 A.X.left` and `i2(x) ≫ p2 = a ≫ x.left`.
It parametrizes `A × {x}` in the actual square and identifies `A` with
the fibre of `p2` at `x`. The square with arrows `i2(x)`, `a`, `p2`,
and `x.left` is a pullback by the same universal property. The first
projection supplies the inverse identification with `A`. No fibre
object or embedding is supplied as data.

`Q` is an object of the published full subcategory of actual scheme
modules that are locally free of rank one. Its restriction is the actual
line bundle `(LineBundle.pullback (i2 x)).obj Q`, whose underlying module
is `((LineBundle.pullback (i2 x)).obj Q).obj`.

For any morphism `f : X ⟶ Spec R`, the published
`Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology f n`
is `(relativeGlobalSections f).rightDerived n : X.Modules ⥤ ModuleCat R`,
where `relativeGlobalSections f` is actual scheme-module pushforward
followed by `moduleSpecΓFunctor`. Thus all the fibre groups use `a`,
all the total groups use exactly `sZ = p1 ≫ a`, and `IsZero` refers to
zero objects in `ModuleCat K`. The pullback identity gives `p1 ≫ a = p2 ≫ a`.
No abstract cohomology operation replaces these functors.

## Original and derived provenance

The registered original is B. Edixhoven, G. van der Geer and B. Moonen,
*Abelian Varieties*, preliminary version of the first chapters:

- Literature ID: `edixhoven-vandergeer-moonen-abelian-varieties-draft`.
- SHA256: `81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
- File: `literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
- Locator: Fact (7.20), printed p.105 / PDF p.109, and the second Leray
  calculation in the proof of Proposition (7.21), printed p.106 / PDF p.110.
  The surrounding Lemmas (7.15), (7.16) and (7.19) on PDF pp.108–109 were
  also read.

The source proof uses `𝒦 = Λ(L) ⊗ p2⁎M⁻¹`. It first obtains vanishing
of all total cohomology. It then uses vanishing of the second-projection
fibre cohomology away from the finite stabilizer to put the higher direct
images on finitely many closed points. Finite-support acyclicity collapses
the second Leray sequence, total vanishing forces all higher direct
images to be zero, and base change gives vanishing on every fibre.
The present target isolates this consequence for an arbitrary actual
line bundle `Q` and an arbitrary finite set `F` of rational points. The
Mumford-bundle identity, ampleness and stabilizer finiteness belong to
the source's application, rather than to this geometric implication.

This is derived content, not a verbatim numbered proposition. The proof
of (7.21) cites Lemma (7.15) at the support step. In context this appears
to be a cross-reference slip: the fibrewise vanishing there uses Lemma
(7.19) together with Fact (7.20), as in the first Leray calculation.

On 2026-10-29 no source-specific errata note was found at
`notes/errata/edixhoven-vandergeer-moonen-abelian-varieties-draft.md` in
the published Library. An author-site errata recheck found no correction
identified for this passage. This bounded search does not assert that
the draft is free of errors.

## Why the geometric specialization has sufficient hypotheses

The printed Fact (7.20) is stated for a proper morphism of noetherian
schemes with reduced connected base and a coherent module. In that
generality it omits flat-family hypotheses needed for the stated
cohomology-and-base-change assertions. The present statement uses the
following stronger geometric situation, all obtained mathematically
from the quantified `A` and `Q`.

The structure morphism `a` is smooth and proper by the definition of
`AbelianScheme`. It is of finite type, and its base changes `p1` and `p2`
are smooth, proper and of finite type. Smoothness makes them flat.
Since `K` is a field, `A` and `Z` are noetherian schemes of finite type;
the base of `p2` is reduced by smoothness over `K` and is connected by
the abelian-scheme geometric connectedness condition. A line bundle is
coherent here and locally free over `𝒪_Z`; flatness of `p2` then makes
it flat over the projection base.

Moreover, a finite-type scheme over an algebraically closed field has
its closed points represented by exactly the `K`-rational points.
Consequently the outside-`F` premise supplies the required information
at every closed point away from the finite set. It does not silently
quantify only over some chosen subset of closed points. The proof
must derive the corresponding support statement for the actual higher
direct images.

These observations explain why proper flat-family base change can be
used for this specialization. They are obligations for its later proof,
not extra hypotheses or assertions established by this statement module.
In particular, one must not assume that each higher direct image
commutes with arbitrary base change without proving the needed
comparison; the joint vanishing in all degrees is the relevant input.

## Later proof obligations and scope

An unconditional exact-target proof must establish, using the actual
scheme-module functors:

1. Coherence of every `R^q p2,* Q` and, from the outside-`F` hypothesis
   and proper flat-family base change, support on the finitely many
   closed points represented by `F`.
2. Vanishing of positive-degree cohomology of those coherent modules
   with finite support, and detection of their zero objects by global
   sections.
3. The actual Leray comparison for `sZ = p2 ≫ a`. The preceding
   acyclicity then identifies total cohomology in degree `n` with
   global sections of `R^n p2,* Q`.
4. Vanishing of all higher direct images from total vanishing and
   detection, and vanishing of all fibre cohomology by the applicable
   flat-family base-change result.

The `DerivedSections` foundation supplies the functors but proves none
of these geometric inputs. This statement assumes none of them as
certificates. The later proof must reuse the arbitrary-base
perfect-pushforward and base-change work owned by Worker 606 and split
any substantial missing constructions and inputs into focused units.

The universe `u`, characteristic and dimension are unrestricted,
including dimension zero. No tensor-preservation premise, cube theorem,
ample bundle, projectivity assumption, dual or Picard scheme, or
unproved comparison or vanishing premise is added. No first-projection
variant is included. Publication of this statement will not prove it.

Worker 360 implemented the pair from Worker 516's focused task
specification.
