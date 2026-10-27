# Translation-invariant line bundles as translation differences over an algebraically closed field

`Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement`
is a universe-polymorphic `Prop`-valued definition. It states the
Library form of Edixhoven, van der Geer and Moonen, *Abelian Varieties*,
Proposition (7.21), for actual line bundles on an abelian scheme over an
algebraically closed field. The module supplies no proof and adds no axiom.

## Statement

For every `preservation : pullbackTensorComparisonIsIsoStatement.{u}`,
every field `K : Type u` with `IsAlgClosed K`, every
`A : AbelianScheme (Spec (CommRingCat.of K))`, every actual line bundle
`L` on `A.X.left`, every actual line bundle `N` on `A.X.left` with a
supplied evaluation `tensorObj L.obj N.obj ≅ structureSheaf A.X.left`, and
every actual line bundle `P` on `A.X.left`,

```text
L.IsAmple → Langlands.GroupScheme.IsTranslationInvariant A.toGrp P →
  ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
    Nonempty (LineBundle.tensor preservation
      ((LineBundle.pullback (Langlands.GroupScheme.translation A.toGrp x).left).obj L)
      N ≅ P).
```

In words: if `L` is ample and `P` is invariant under translation by every
`K`-point, then `P ≅ t_x^*L ⊗ N` for some `K`-point `x`, where `N` is the
chosen tensor inverse of `L`.

## Complete checked type

The source declaration is

```lean
def AlgClosedFieldTranslationDifferenceLiftingStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L N : LineBundle A.X.left)
    (_evaluation : tensorObj L.obj N.obj ≅ structureSheaf A.X.left)
    (P : LineBundle A.X.left),
    L.IsAmple → GroupScheme.IsTranslationInvariant A.toGrp P →
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ A.X,
        Nonempty (LineBundle.tensor preservation
          ((LineBundle.pullback (GroupScheme.translation A.toGrp x).left).obj L) N ≅ P)
```

inside `namespace Langlands.AbelianScheme`, with
`open CategoryTheory AlgebraicGeometry` and
`open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules`.
With `pp.fieldNotation false`, `pp.proofs true` and `pp.funBinderTypes true`,
`#print` in the approved environment reports:

```text
def Langlands.AbelianScheme.AlgClosedFieldTranslationDifferenceLiftingStatement.{u} : Prop :=
∀ (preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement) (K : Type u) [inst : Field K]
  [IsAlgClosed K] (A : Langlands.AbelianScheme (AlgebraicGeometry.Spec ↧K))
  (L N :
    Langlands.AlgebraicGeometry.Picard.LineBundle
      (CategoryTheory.Over.left
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)))))
  (_evaluation :
    Langlands.Scheme.Modules.tensorObj (CategoryTheory.ObjectProperty.FullSubcategory.obj L)
        (CategoryTheory.ObjectProperty.FullSubcategory.obj N) ≅
      Langlands.Scheme.Modules.structureSheaf
        (CategoryTheory.Over.left
          (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)))))
  (P :
    Langlands.AlgebraicGeometry.Picard.LineBundle
      (CategoryTheory.Over.left
        (CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))))),
  Langlands.AlgebraicGeometry.Picard.LineBundle.IsAmple L →
    Langlands.GroupScheme.IsTranslationInvariant
        (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) P →
      ∃ (x :
        CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id (AlgebraicGeometry.Spec ↧K)) ⟶
          CategoryTheory.Grp.X (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A))),
        Nonempty
          (Langlands.AlgebraicGeometry.Picard.LineBundle.tensor (fun {X Y : AlgebraicGeometry.Scheme} => preservation)
              (CategoryTheory.Functor.obj
                (Langlands.AlgebraicGeometry.Picard.LineBundle.pullback
                  (CategoryTheory.Over.Hom.left
                    (Langlands.GroupScheme.translation
                      (Langlands.CommGroupScheme.toGrp (Langlands.AbelianScheme.toCommGroupScheme A)) x)))
                L)
              N ≅
            P)
```

and `#check` reports type `Prop`. Here `↧K` is `CommRingCat.of K`, and
`A.X` abbreviates `Grp.X (CommGroupScheme.toGrp (toCommGroupScheme A))`.
The argument `fun {X Y} => preservation` is the binder's eta-expanded
form, not a separate hypothesis.

## Library objects used

The statement uses only published definitions, without new structures,
certificates or axioms.

- `A : AbelianScheme S` is the published bundle: a commutative group scheme
  over `S` whose structure morphism `A.X.hom` is smooth, proper and
  geometrically connected. Here `S = Spec K`.
- `LineBundle X` is the full subcategory of actual `X.Modules` that are
  locally isomorphic to the structure sheaf. An isomorphism of line bundles
  is an isomorphism of the underlying sheaves of modules.
- `LineBundle.pullback f` is the actual sheaf pullback restricted to line
  bundles, and `LineBundle.tensor preservation L M` has underlying sheaf
  the actual sheafified tensor product `tensorObj L.obj M.obj`.
- The hypothesis `preservation` is the published statement
  `Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement`: for
  every morphism of schemes `f`, the canonical comparison
  `pullbackTensorComparison f` is an isomorphism. `LineBundle.tensor` uses
  it only to show that the tensor product is again locally free of rank
  one. Pullback of modules commuting with tensor products is a standard
  fact, but this Library statement currently has no published proof, so it
  is an explicit premise here, as in the other actual-tensor statements.
- A section `x : Over.mk (𝟙 (Spec K)) ⟶ A.X` is a `K`-rational point of
  `A`. `GroupScheme.translation A.toGrp x` is
  `(Over.mkIdTerminal.from A.X ≫ x) * 𝟙 A.X`, the translation built from
  the actual group law. On `T`-points it sends `y` to `x_T * y`.
- `GroupScheme.IsTranslationInvariant A.toGrp P` means that for every
  section `x`, `(LineBundle.pullback (translation A.toGrp x).left).obj P ≅ P`.
- `L.IsAmple` is the published ampleness predicate described below.

## Original source

The original is B. Edixhoven, G. van der Geer and B. Moonen, *Abelian
Varieties*, preliminary version of the first chapters, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`,
retained as
`literature/Edixhoven, van der Geer, Moonen - Abelian Varieties (preliminary version of the first chapters).pdf`.
Printed page numbers are PDF page numbers minus four. On 2026-10-27 UTC
the [author's PDF](https://van-der-geer.nl/~gerard/AV.pdf) was fetched and
is byte-identical to the registered file (same SHA256). The author's page
links only this PDF and lists no errata, and the Library has no errata note
for this source.

Proposition (7.21), printed p.105 (PDF p.109), reads: "Let `X` be an
abelian variety over an algebraically closed field `k`. Let `L` be an ample
line bundle on `X` and `M` a line bundle with `φ_M = 0`. Then there exists
a point `x ∈ X(k)` with `M ≅ t_x^*L ⊗ L^{-1}`." The statement here is this
proposition with the source's `X`, `k`, `L`, `M` and `L^{-1}` replaced by
`A.X.left`, `K`, `L`, `P` and the chosen `N`. The orientation of the
isomorphism is the same.

The surrounding definitions were also read. Paragraph (6.2), printed p.88
(PDF p.92), introduces line bundles rigidified along a section and the
functor of their isomorphism classes, under assumptions `(*)` that hold for
a complete variety over a field with a rational point. Chapter VI §3,
printed p.95 (PDF p.99), defines for a line bundle `L` on an abelian
variety the morphism `φ_L : X → Pic_{X/k}`. It is the unique morphism with
`(id × φ_L)^*𝒫 ≅ Λ(L)`, and on points it is `x ↦ [t_x^*L ⊗ L^{-1}]`.
Here `Λ(L) = m^*L ⊗ p_1^*L^{-1} ⊗ p_2^*L^{-1}` is the Mumford bundle of
Definition (2.15), printed p.22 (PDF p.26). Printed p.104 (PDF p.108)
assembles these morphisms into the homomorphism
`φ : Pic_{X/k} → Hom(X, X^t)`. Lemma (7.15) there gives
`Pic^0_{X/k} ⊂ Ker(φ)`.

The statement concerns ordinary, non-rigidified line bundles only. It
makes no claim about the Library's rigidified families, the chosen dual
parameter scheme or their comparison with the source's Picard scheme. Those
comparisons belong to the separate rigidified point-formula statement task
`d0494538-ad40-4cf9-b030-5d538865f064` and to Worker 420's parent proof
`012915dc-316e-4c87-a08e-16730ad96609`.

The provenance is derived. The algebraically closed Proposition (7.21) is
stated for actual Library line bundles. The source condition `φ_M = 0` is
expressed as translation invariance, and the inverse `L^{-1}` as a chosen
tensor inverse with evaluation. The next two sections explain these
translations. The source notion of an ample line bundle is matched with the
Library predicate in the section after them.

## The condition `φ_P = 0` as translation invariance

The source works on the abelian variety `X` over the algebraically closed
field `k`, so `X(k)` is the set of sections of `X → Spec k`. In the
Library these are the sections `x` quantified in `IsTranslationInvariant`.
The source's `t_x` is translation `y ↦ y + x`, and the Library translation
is `y ↦ x * y`. The Library group law is commutative, so these agree.

Mathematically, for a line bundle `M` on `X`, `φ_M = 0` if and only if
`t_x^*M ≅ M` for every `x ∈ X(k)`.

- If `φ_M = 0`, then for each `x ∈ X(k)` the class `[t_x^*M ⊗ M^{-1}]`
  is zero in `Pic_{X/k}(k)`. The map `Pic(X) → Pic_{X/k}(k)` has kernel
  `Pic(Spec k) = 0` by sequence (1) of (6.2), so `t_x^*M ⊗ M^{-1}` is
  trivial and `t_x^*M ≅ M`.
- Conversely, if `t_x^*M ≅ M` for every `x ∈ X(k)`, then `φ_M` and the
  zero morphism agree at every `k`-point. `X` is smooth, hence reduced, and
  of finite type over the algebraically closed `k`. Its `k`-points are
  therefore its closed points, and they are dense in every closed subset.
  The source admits on p.95 that `Pic_{X/k}` is a group scheme over `k`
  with projective connected components; in particular it is separated.
  So the locus where `φ_M` agrees with the zero morphism is a
  closed subscheme of the reduced scheme `X` containing every closed point.
  This locus is all of `X`, so `φ_M = 0`.

Thus over an algebraically closed field the source hypothesis `φ_P = 0` is
exactly `IsTranslationInvariant A.toGrp P`. This explanation does not depend
on the Library having a Picard scheme. The Lean statement takes the
translation-invariance form as its hypothesis and makes no claim about
`φ`. `TranslationBaseChange.isTranslationInvariant_of_isGeometricallyPicardZero`
derives this hypothesis from the Library's geometric-fibre Picard-zero
condition over an algebraically closed field. It is not a lifting theorem.

## The chosen inverse `N`

The source's `L^{-1}` is a tensor inverse defined only up to isomorphism.
The statement takes an actual line bundle `N` together with an
evaluation isomorphism `tensorObj L.obj N.obj ≅ structureSheaf A.X.left`.
This premise can always be satisfied: the published theorem
`LineBundle.exists_tensorObj_iso_structureSheaf`, in
`LineBundleDualEvaluation`, provides such an `N` and evaluation for every
line bundle, namely the dual.

The evaluation is not a lifting certificate. It only identifies `N` as an
inverse of `L`, and any two such inverses are isomorphic. The conclusion
`t_x^*L ⊗ N ≅ P` therefore does not depend on the choice of `N` up to
isomorphism. The variable is named `_evaluation` because the proposition
needs the premise but does not mention it later.

## Ampleness

EvdGM uses "ample" without its own definition. It is read as the standard
notion of EGA II, Definition 4.5.3. The registered original
`stacks-invertible-picard-ampleness-2026-10-21`, directory SHA256
`2a0bbd01484fc7cef97110a88cf4b3e472574fbbb9469d037170744a1462f835`,
retained in
`literature/Stacks Project - Invertible sheaves, Picard groups and ampleness (HTML snapshot 2026-10-21)`,
was read in `01PS.html` and `01CY.html`.
[Definition 28.27.1, tag 01PS](https://stacks.math.columbia.edu/tag/01PS),
which the page attributes to EGA II Definition 4.5.3, calls an invertible
sheaf `ℒ` ample if `X` is quasi-compact and every `x ∈ X` lies in some
affine `X_s` with `s ∈ Γ(X, ℒ^{⊗ n})` and `n ≥ 1`.

The Library predicate `L.IsAmple` is used unchanged. For `X = A.X.left` it is

```text
CompactSpace X ∧ ∀ x : X, ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
  x ∈ L.sectionOpen s ∧ IsAffineOpen (L.sectionOpen s).
```

Here `L.powSections n` is the set of global sections of the actual tensor
power `Langlands.Scheme.Modules.tensorPow L.obj n`. `L.sectionOpen s` is
`trivializationOpen (tensorPow L.obj n) s`, the supremum of the opens on
which the map from the structure sheaf sending `1` to `s` is an
isomorphism. The whole generation open must be affine. An affine
neighbourhood of `x` inside it does not suffice, and the statement does not
weaken this condition.

[Lemma 17.25.10, tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
shows that on `X_s` the map given by `s` is an isomorphism, so `X_s` lies
in the generation open. Conversely, at any point where `s` generates, its
image is not in `𝔪_x ℒ_x`. Hence the generation open is exactly `X_s`, and
`L.IsAmple` is the source notion with `ℒ^{⊗ n}` read as `tensorPow L.obj n`.
In Lean, the published `LineBundle.isAmple_iff_nonvanishingLocus` records
this equivalence under two hypotheses. The first,
`LineBundleResidueOpenComparison`, is available as the theorem
`Langlands.SchemeModule.lineBundleResidueOpenComparison`. The second is
local rank one of every actual tensor power `tensorPow L.obj n`, the
separate statement
`Langlands.AlgebraicGeometry.Picard.TensorPowLocallyFreeRankOneStatement`.

As used in a proof of this statement, `L.IsAmple` is a hypothesis. A proof
along the source route must derive from it whatever ampleness consequences
Mumford's argument needs. Those obligations are listed in the next section.
They are not established here.

## Proof obligations for the later exact proof

After independent acceptance and publication, a separate exact-target proof
must have this entire named proposition as its type, with no extra outer
hypotheses. The source proof, which the source attributes to Mumford, uses
`𝒦 = Λ(L) ⊗ p_2^*M^{-1}` on `X × X` and computes `H^n(X × X, 𝒦)` with the
Leray spectral sequences of both projections. If no `x` works, both
computations combine to make every `R^n p_{2,*}𝒦` vanish. This contradicts
the triviality of `𝒦|_{X × {0}}`. Read as a Library proof, it leaves these
obligations.

1. The Mumford-bundle restrictions
   `𝒦|_{{x} × X} ≅ t_x^*L ⊗ L^{-1} ⊗ P^{-1}` and
   `𝒦|_{X × {x}} ≅ t_x^*L ⊗ L^{-1}`, for actual pullbacks, tensors and
   the chosen inverses. The published `Langlands.AbelianScheme.mumfordBundle`
   is a parameter-first rigidified version with a supplied inverse and
   evaluation.
2. The fact that `t_x^*L ⊗ N` is translation invariant. The source cites
   `φ_L(x) ∈ Pic^0 ⊂ Ker(φ)`. In the Library,
   `Langlands.AbelianScheme.MumfordPicardZero.isTranslationInvariant_square`
   proves this translation invariance from `preservation`,
   `Langlands.GroupScheme.FieldCubePullbackStatement` and
   `Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityStatement`.
   The last is proved in the Library as `fieldLineBundleTriviality`; the
   cube pullback statement has no published proof yet.
3. Lemma (7.19), printed p.105: a translation-invariant line bundle that is
   not trivial has vanishing cohomology in every degree. The source proof
   uses `(-1)^*M ≅ M^{-1}`, `m^*M ≅ p_1^*M ⊗ p_2^*M` and the Künneth formula.
   In the Library these must be derived from `IsTranslationInvariant` itself.
4. Fact (7.20), printed p.105: cohomology and base change for proper
   morphisms. The source cites `[MAV]`, §5, for it. It also needs sheaf cohomology of the Library's `X.Modules` and the Leray
   spectral sequences.
5. Finiteness of the set of `x ∈ X(k)` with `t_x^*L ≅ L`, or of the
   subgroup scheme `K(L)` of Definition (2.16), for ample `L`. This is
   Lemma (2.19), printed p.23 (PDF p.27). Its proof uses that the
   restriction of an ample bundle to an abelian subvariety, its pullback by
   `-1`, and tensor products of ample bundles are ample. It also uses that a
   proper scheme over a field carrying a trivial ample bundle is finite. The
   published statements `ClosedImmersionPullbackAmpleStatement`,
   `AmpleTensorStatement`, `AmpleTrivialQuasiAffineStatement` and
   `ProperAmpleTrivialFiniteStatement` in
   `Langlands.AlgebraicGeometry.Picard` cover several of these steps as
   statements. Using finiteness of a set of closed points instead of the
   subgroup scheme is acceptable, since the argument only needs vanishing
   outside finitely many points.

The proof of (7.21) cites "Lemma (7.15)" for
`supp(R^q p_{2,*}𝒦) ⊂ K(L)`. The argument that follows, "again" as in the
first spectral sequence, actually uses Lemma (7.19) together with
Fact (7.20). This appears to be a cross-reference slip in the draft. It
does not affect the mathematics.

Any genuinely missing substantial construction must be split into
definition, statement and proof units, in that order. Existing ampleness,
Mumford-bundle, square-theorem, tensor and pullback work should be reused,
not duplicated. This module discharges none of these obligations.

## Scope

The statement covers every universe `u`, every algebraically closed field
in every characteristic, and dimension zero. Mathematically, in dimension
zero `A.X.left` is isomorphic to `Spec K`, every line bundle is trivial, and the conclusion holds with
`x` the unit section. Algebraic closedness is the only condition on `K`;
no perfectness is assumed beyond it. The statement adds no projectivity,
existing dual, isogeny, cohomology-vanishing, point-lift, geometric
Picard-zero presentation, source Picard identification or
scheme-surjectivity premise. It introduces no Picard group, dual-existence
axiom or abstract lifting certificate.

## Role and authorship

This is a focused prerequisite of Worker 420's exact chosen-dual surjection
proof `012915dc-316e-4c87-a08e-16730ad96609`. The parent keeps the final
chosen-universal-family classification and the passage from geometric
points to scheme surjectivity. This ordinary lifting statement does not
prove the parent statement, and the parent is not used to justify it.

Worker 299 implemented this pair. Worker 420 supplied the focused
specification, including the binders and the conclusion.
