/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale

/-!
# Split presentations of a pro-etale constant trivialization

Source: Stacks Project, Tags 098Z, 03P5, 03YW and 0AP6; blueprint proof of
`lemma-lattices-lisse-e-sheaves`, part (2)
(blueprint: lem-sfb-proetale-constant-split-descent).

The overlap isomorphism is stated explicitly. Its cocycle is expressed using the
recorded scheme descent datum, whose transport is required to preserve the same
sections. Thus its overlap isomorphism is the unique one already specified.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The codiagonal of the coproduct of copies of a scheme.
Source: Stacks Project, Tag 03YW
(blueprint: lem-sfb-proetale-constant-split-descent). -/
noncomputable def proetaleSplitCodiagonal (V : Scheme.{u}) (S : Type w)
    [Small.{u} S] : (∐ fun _ : S ↦ V) ⟶ V :=
  Sigma.desc (fun _ : S ↦ 𝟙 V)

/-- Forget a localized pro-etale object to its underlying scheme over the cover.
Source: Stacks Project, Tag 098Z, localized site
(blueprint: lem-sfb-proetale-constant-split-descent). -/
def proetaleSliceToOver {X V : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p] :
    Over (Scheme.ProEt.mk p) ⥤ Over V :=
  Over.post (Scheme.ProEt.forget X) ⋙ Over.iteratedSliceForward (Over.mk p)

/-- The first overlap projection as a morphism in the small pro-etale site.
Source: Stacks Project, Tag 023V, and blueprint proof (2)
(blueprint: lem-sfb-proetale-constant-split-descent). -/
noncomputable def proetaleSplitOverlapFirst {X V : Scheme.{u}} (p : V ⟶ X)
    [WeaklyEtale p] :
    Scheme.ProEt.mk (pullback.fst p p ≫ p) ⟶ Scheme.ProEt.mk p :=
  MorphismProperty.Over.homMk (pullback.fst p p) rfl

/-- The second overlap projection as a morphism in the small pro-etale site.
Source: Stacks Project, Tag 023V, and blueprint proof (2)
(blueprint: lem-sfb-proetale-constant-split-descent). -/
noncomputable def proetaleSplitOverlapSecond {X V : Scheme.{u}} (p : V ⟶ X)
    [WeaklyEtale p] :
    Scheme.ProEt.mk (pullback.fst p p ≫ p) ⟶ Scheme.ProEt.mk p :=
  MorphismProperty.Over.homMk (pullback.snd p p) (pullback.condition (f := p) (g := p)).symm

/-- The point in the labelled component of a split presentation.
Source: Stacks Project, Tag 03YW
(blueprint: lem-sfb-proetale-constant-split-descent). -/
noncomputable def proetaleSplitLabel {X V : Scheme.{u}} (p : V ⟶ X) [WeaklyEtale p]
    (S : Type w) [Small.{u} S] (W : Over (Scheme.ProEt.mk p)) (s : S) :
    (proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S) :=
  Over.homMk (((proetaleSliceToOver p).obj W).hom ≫ Sigma.ι (fun _ : S ↦ V) s)
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k : V ⟶ V ↦ ((proetaleSliceToOver p).obj W).hom ≫ k)
        (Sigma.ι_comp_desc (fun _ : S ↦ 𝟙 V) s)).trans (Category.comp_id _)))

/-- The representability and overlap/descent-data part of the split presentation: natural
bijections `rho` from maps over `V` into the labelled coproduct to the sections of `F`,
normalized on labels by `e`, the unique overlap isomorphism matching the two `rho`, and a
transport-form scheme descent datum preserving `rho`.
Source: Stacks Project, Tags 098Z, 03P5, 03YW and 001P
(blueprint: lem-sfb-proetale-constant-split-descent;
split blueprint: lem-sfb-proetale-constant-split-descent-data). -/
def proetaleConstantSplitDescentData {X V : Scheme.{u}} (p : V ⟶ X)
    [QuasiCompact p] [Surjective p] [WeaklyEtale p] [IsAffine V]
    (S : Type w) [Small.{u} S] [UnivLE.{u + 1, w}]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (e : F.over (Scheme.ProEt.mk p) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
        (Type w)).obj S) : Prop :=
  ∃ rho : ∀ W : Over (Scheme.ProEt.mk p),
      ((proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)) ≃
        F.obj.obj (op W.left),
    (∀ (W W' : Over (Scheme.ProEt.mk p)) (g : W' ⟶ W)
        (f : (proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)),
      rho W' ((proetaleSliceToOver p).map g ≫ f) =
        F.obj.map g.left.op (rho W f)) ∧
    (∀ (W : Over (Scheme.ProEt.mk p)) (s : S),
      rho W (proetaleSplitLabel p S W s) =
        e.inv.hom.app (op W)
          ((toSheafify ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
            ((Functor.const (Over (Scheme.ProEt.mk p))ᵒᵖ).obj S)).app (op W) s)) ∧
    (∃! alpha :
        (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S)) ≅
          (Over.pullback (pullback.snd p p)).obj
            (Over.mk (proetaleSplitCodiagonal V S)),
      ∀ (W : Over (Scheme.ProEt.mk (pullback.fst p p ≫ p)))
        (f : (proetaleSliceToOver (pullback.fst p p ≫ p)).obj W ⟶
          (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S))),
        rho ((Over.map (proetaleSplitOverlapFirst p)).obj W)
          (((Over.mapPullbackAdj (pullback.fst p p)).homEquiv _ _).symm f) =
        rho ((Over.map (proetaleSplitOverlapSecond p)).obj W)
          (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv _ _).symm
            (f ≫ alpha.hom))) ∧
    (∃ D : Over.DescentDatum p (Over.mk (proetaleSplitCodiagonal V S)),
      ∀ (W : X.ProEt) (a b : W ⟶ Scheme.ProEt.mk p)
        (f : Over.mk a.left ⟶ Over.mk (proetaleSplitCodiagonal V S)),
        rho (Over.mk b)
          (D.transport a.left b.left
            ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
        rho (Over.mk a) f)

/-- The representability and overlap/descent-data part of the split presentation.
Source: Tags 098Z, 03P5, 03YW and 001P
(blueprint: lem-sfb-proetale-constant-split-descent;
split blueprint: lem-sfb-proetale-constant-split-descent-data).

Proof: representable fpqc descent makes the presheaf of maps over `V` into the labelled
coproduct a sheaf. The clopen-component description gives local surjectivity and local
injectivity, including the empty-label and empty-test-scheme cases. The local-bijection
criterion identifies its sheafification with the given constant sheaf and supplies the
natural equivalences `rho`, normalized on each labelled component. On the double overlap,
fully faithful Yoneda gives the unique comparison `alpha` matching the two rho sections.
On the triple overlap both composites correspond to the same first-to-third transport,
so Yoneda faithfulness proves the cocycle. The comparison is then packaged as the recorded
transport-form scheme descent datum; transport preserves the rho sections by construction. -/
theorem proetaleConstantSplitDescentData_proof {X V : Scheme.{u}} (p : V ⟶ X)
    [QuasiCompact p] [Surjective p] [WeaklyEtale p] [IsAffine V]
    (S : Type w) [Small.{u} S] [UnivLE.{u + 1, w}]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (e : F.over (Scheme.ProEt.mk p) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
        (Type w)).obj S) : proetaleConstantSplitDescentData p S F e := by
  sorry

/-- The geometric properties of the split codiagonal.
Source: Tags 03YW and 0AP6
(blueprint: lem-sfb-proetale-constant-split-descent;
split blueprint: lem-sfb-proetale-constant-split-descent-geometry).

Proof: the clopen-coproduct calculation identifies the pullback with components indexed by
pairs of labels; the diagonal is the closed union of the equal-label components, proving
separatedness. Each component chart is the identity of `V`, so the codiagonal is flat and
locally of finite presentation and hence etale. A chosen label gives a section, proving
surjectivity for nonempty `S`. Finally, a quasi-compact open above an affine open meets
only finitely many components. It is open in that finite subcoproduct, which is affine by
the finite affine-coproduct spectrum lemma, and is therefore quasi-affine; the empty open
is handled by the empty subunion. In Lean, etaleness is
`IsZariskiLocalAtSource.sigmaDesc (fun _ ↦ inferInstance)`, and surjectivity follows from
`Sigma.ι_comp_desc` (a labelled component is a section). -/
theorem proetaleConstantSplitDescentGeometry {V : Scheme.{u}} (S : Type w)
    [Small.{u} S] [IsAffine V] :
    IsSeparated (proetaleSplitCodiagonal V S) ∧
      Etale (proetaleSplitCodiagonal V S) ∧
      (Nonempty S → Surjective (proetaleSplitCodiagonal V S)) ∧
      (∀ (B : V.Opens), IsAffineOpen B →
        ∀ (U : ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme.Opens),
          IsCompact (U : Set ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme) →
            U.toScheme.IsQuasiAffine) := by
  sorry

/-- A constant trivialization gives natural split scheme presentations, a unique
matching overlap isomorphism and its scheme descent cocycle. The codiagonal is
separated, etale, surjective for nonempty labels, and ind-quasi-affine.

Source: Stacks Project, Tags 098Z, 03P5, 03YW, 001P, 023V and 0AP6;
blueprint `lemma-lattices-lisse-e-sheaves`, proof (2)
(blueprint: lem-sfb-proetale-constant-split-descent).

Proof: the conjunction of `proetaleConstantSplitDescentData_proof`
(`lem-sfb-proetale-constant-split-descent-data`, steps 2-6 below) and
`proetaleConstantSplitDescentGeometry` (`lem-sfb-proetale-constant-split-descent-geometry`,
steps 1, 2 and 7 below). The argument of the two parts:
1. By `lem-galois-coproduct-copies-morphisms-clopen` the coproduct represents
labelled clopen decompositions. Its square over the base has components indexed
by pairs of labels; the diagonal is the clopen union of equal-label components.
It is therefore a closed immersion, proving separatedness. The same component
calculation identifies every base change with the coproduct over the new base.
2. Each component chart of the codiagonal is an identity, hence flat and locally
of finite presentation. The diagonal is an open immersion, so the codiagonal is
etale and weakly etale. `lemma-stability` puts the overlaps and
split schemes in the localized sites.
3. The presheaf of morphisms over V into the coproduct is a sheaf by
`lem-weil-pbc-fpqc-representable-descent`. Send each constant label to its
component morphism; composition makes this a natural transformation.
4. The clopen component preimages give local surjectivity. Disjoint components
give local injectivity on nonempty objects; the empty covering treats empty
objects and the empty label set. The criterion in
`lem-cbc-set-presheaf-sheafification-local-bijection` identifies its sheafification
with the constant sheaf. Composing its inverse with e inverse gives rho and the
normalization on labels.
5. On the overlap, the two pullbacks represent the same restricted sheaf. By
`lem-galois-yoneda-fully-faithful`, their comparison gives the unique alpha
matching sections; reversing the comparison gives its inverse.
6. On a triple overlap both composites correspond to rho third inverse followed
by rho first: the middle pair cancels. Yoneda faithfulness proves the cocycle.
This gives `proposition-jacobian-over-ground-field--1` in its recorded transport form; its transport
preserves rho and therefore induces precisely the unique alpha of step 5.
7. A label gives a section of the codiagonal, proving surjectivity when labels
are nonempty. A quasi-compact open above an affine open meets only finitely many
components. It is open in their finite union, which is affine by
`lem-weil-pbc-finite-affine-coproduct-spectrum`, hence is quasi-affine. For the
empty open use the empty union and the zero ring. No effectiveness is asserted.

Sizes (`prose-01-10`): the labels are `u`-small, so the coproduct exists in
`Scheme.{u}`; sheaves of sets take values in any universe `w` containing the `u + 1`-sized
site (`UnivLE.{u + 1, w}`), where sheafification and the constant sheaf exist.
-/
theorem proetaleConstantSplitDescent {X V : Scheme.{u}} (p : V ⟶ X)
    [QuasiCompact p] [Surjective p] [WeaklyEtale p] [IsAffine V]
    (S : Type w) [Small.{u} S] [UnivLE.{u + 1, w}]
    (F : Sheaf (Scheme.ProEt.topology X) (Type w))
    (e : F.over (Scheme.ProEt.mk p) ≅
      (constantSheaf ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
        (Type w)).obj S) :
    (∃ rho : ∀ W : Over (Scheme.ProEt.mk p),
        ((proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)) ≃
          F.obj.obj (op W.left),
      (∀ (W W' : Over (Scheme.ProEt.mk p)) (g : W' ⟶ W)
          (f : (proetaleSliceToOver p).obj W ⟶ Over.mk (proetaleSplitCodiagonal V S)),
        rho W' ((proetaleSliceToOver p).map g ≫ f) =
          F.obj.map g.left.op (rho W f)) ∧
      (∀ (W : Over (Scheme.ProEt.mk p)) (s : S),
        rho W (proetaleSplitLabel p S W s) =
          e.inv.hom.app (op W)
            ((toSheafify ((Scheme.ProEt.topology X).over (Scheme.ProEt.mk p))
              ((Functor.const (Over (Scheme.ProEt.mk p))ᵒᵖ).obj S)).app (op W) s)) ∧
      (∃! alpha :
          (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S)) ≅
            (Over.pullback (pullback.snd p p)).obj
              (Over.mk (proetaleSplitCodiagonal V S)),
        ∀ (W : Over (Scheme.ProEt.mk (pullback.fst p p ≫ p)))
          (f : (proetaleSliceToOver (pullback.fst p p ≫ p)).obj W ⟶
            (Over.pullback (pullback.fst p p)).obj (Over.mk (proetaleSplitCodiagonal V S))),
          rho ((Over.map (proetaleSplitOverlapFirst p)).obj W)
            (((Over.mapPullbackAdj (pullback.fst p p)).homEquiv _ _).symm f) =
          rho ((Over.map (proetaleSplitOverlapSecond p)).obj W)
            (((Over.mapPullbackAdj (pullback.snd p p)).homEquiv _ _).symm
              (f ≫ alpha.hom))) ∧
      (∃ D : Over.DescentDatum p (Over.mk (proetaleSplitCodiagonal V S)),
        ∀ (W : X.ProEt) (a b : W ⟶ Scheme.ProEt.mk p)
          (f : Over.mk a.left ⟶ Over.mk (proetaleSplitCodiagonal V S)),
          rho (Over.mk b)
            (D.transport a.left b.left
              ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) f) =
          rho (Over.mk a) f)) ∧
    IsSeparated (proetaleSplitCodiagonal V S) ∧
    Etale (proetaleSplitCodiagonal V S) ∧
    (Nonempty S → Surjective (proetaleSplitCodiagonal V S)) ∧
    (∀ (B : V.Opens), IsAffineOpen B →
      ∀ (U : ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme.Opens),
        IsCompact (U : Set ((proetaleSplitCodiagonal V S) ⁻¹ᵁ B).toScheme) →
          U.toScheme.IsQuasiAffine) := by
  classical
  exact ⟨by simpa [proetaleConstantSplitDescentData] using
      proetaleConstantSplitDescentData_proof p S F e,
    proetaleConstantSplitDescentGeometry S⟩

end AlgebraicGeometry
