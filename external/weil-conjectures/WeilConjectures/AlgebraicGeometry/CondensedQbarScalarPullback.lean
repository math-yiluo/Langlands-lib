/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction

import all WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality

/-! # Compatibility of bounded coefficient constructions
Source: RefactorInstruction, Section 4, coefficient realization and geometric fibers.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

namespace CondensedQbarScalarConstruction

/- The following private constructions realize steps 1 and 3 of the node's plan.
Precompose bounded functions with the base-change projection, then extend to the
abelian sheafifications by their adjunction. No existence witness is chosen. -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def boundedPrecompose (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    boundedP ℓ Y ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op ⋙ boundedP ℓ Z where
  app U := AddCommGrpCat.ofHom
    { toFun := fun s ↦ ULift.up (boundedComp ℓ
        (pullback.fst U.unop.hom g).base.hom s.down)
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    ext x
    have h : ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).map f.unop).left ≫
        pullback.fst U.unop.hom g = pullback.fst V.unop.hom g ≫ f.unop.left :=
      pullback.lift_fst _ _ _
    exact congrArg (fun k : pullback V.unop.hom g ⟶ U.unop.left ↦ s.down.1 (k x)) h.symm

private noncomputable def boundedPushforwardPresheaf (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    boundedP ℓ Y ⟶ ((lowerStar Ab.{u + 1} g).obj (padicAlgClSheaf Z ℓ)).obj :=
  boundedPrecompose ℓ g ≫ Functor.whiskerLeft (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op
    (toSheafify (Scheme.ProEt.topology Z) (boundedP ℓ Z))

private noncomputable def boundedPushforward (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    padicAlgClSheaf Y ℓ ⟶ (lowerStar Ab.{u + 1} g).obj (padicAlgClSheaf Z ℓ) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _).symm
    (boundedPushforwardPresheaf ℓ g)

private lemma boundedPushforward_unit (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    toSheafify (Scheme.ProEt.topology Y) (boundedP ℓ Y) ≫
      (boundedPushforward ℓ g).hom = boundedPushforwardPresheaf ℓ g :=
  (Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _) _)

private lemma boundedPrecompose_mul (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    boundedMul ℓ Y a ≫ boundedPrecompose ℓ g =
      boundedPrecompose ℓ g ≫ Functor.whiskerLeft
        (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g).op
        (boundedMul ℓ Z (boundedComp ℓ g.base.hom a)) := by
  ext U s
  apply ULift.ext
  apply Subtype.ext
  ext x
  change s.down.1 (pullback.fst U.unop.hom g x) *
      a.1 (U.unop.hom (pullback.fst U.unop.hom g x)) =
    s.down.1 (pullback.fst U.unop.hom g x) *
      a.1 (g (pullback.snd U.unop.hom g x))
  congr 1
  exact congrArg (fun k : pullback U.unop.hom g ⟶ Y ↦ a.1 (k x))
    (pullback.condition (f := U.unop.hom) (g := g))

set_option backward.isDefEq.respectTransparency false in
private lemma boundedPushforward_scalar (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    (sheafScalar ℓ Y a).asHom.hom ≫ boundedPushforward ℓ g =
      boundedPushforward ℓ g ≫ (lowerStar Ab.{u + 1} g).map
        (sheafScalar ℓ Z (boundedComp ℓ g.base.hom a)).asHom.hom := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) Ab.{u + 1}).homEquiv _ _).injective
  change toSheafify _ _ ≫ (sheafifyMap _ (boundedMul ℓ Y a)) ≫
      (boundedPushforward ℓ g).hom =
    toSheafify _ _ ≫ (boundedPushforward ℓ g).hom ≫ _
  rw [← toSheafify_naturality_assoc, boundedPushforward_unit]
  rw [← Category.assoc, boundedPushforward_unit]
  unfold boundedPushforwardPresheaf
  rw [← Category.assoc, boundedPrecompose_mul]
  simp only [Category.assoc, ← Functor.whiskerLeft_comp]
  congr 1
  change Functor.whiskerLeft _ _ = Functor.whiskerLeft _ (toSheafify _ _) ≫
    Functor.whiskerLeft _ (sheafifyMap _ (boundedMul ℓ Z (boundedComp ℓ g.base.hom a)))
  rw [← Functor.whiskerLeft_comp, toSheafify_naturality]

end CondensedQbarScalarConstruction

/- Step 2: normalization on profinite test functions identifies the two realization
maps. Naturality of the sheafification unit reduces the comparison to pullback pasting. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma boundedCoefficient_scheme_naturality (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y) :
    condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) g ≫
      (lowerStar Ab.{u + 1} g).map
        (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Z).hom.hom =
    (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y).hom.hom ≫
      CondensedQbarScalarConstruction.boundedPushforward ℓ g := by
  let adjY := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))
  have hleft := CondensedRing.chartMate_homEquiv g (toSpecZ Y) (toSpecZ Z) (comp_toSpecZ g)
    (pointUpperStar.obj (Profinite.padicAlgClRingObj ℓ)) (padicAlgClSheaf Z ℓ)
    (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Z).hom.hom
  rw [← condensedPullbackHom_eq (Profinite.padicAlgClRingObj ℓ) g] at hleft
  apply (adjY.homEquiv _ _).injective
  conv_rhs => rw [adjY.homEquiv_naturality_right]
  simp only [adjY, Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  simp only [← unitAlgHom_comp_map_condensedPullbackHom, Category.assoc]
  erw [hleft, pointUpperStarLowerStarAdjunction.homEquiv_naturality_right]
  ext S a
  cases a with
  | up a =>
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ConcreteCategory.comp_apply]
    change ((((lowerStarFactor Ab.{u + 1} (comp_toSpecZ g)).inv.app
        (padicAlgClSheaf Z ℓ)).hom.app (op (profiniteToProEt.obj S.unop)))
      ((((pointUpperStarLowerStarAdjunction.comp
        (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Z))).homEquiv _ _
          (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Z).hom.hom).hom.app S)
        (ULift.up a))) =
      (((CondensedQbarScalarConstruction.boundedPushforward ℓ g).hom.app
        (op ((profiniteToProEtOf Y).obj S.unop)))
        ((((pointUpperStarLowerStarAdjunction.comp
          (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ Y))).homEquiv _ _
          (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y).hom.hom).hom.app S)
          (ULift.up a)))
    rw [CondensedQbarCoefficientRealization.globalCoefficientIso_test,
      CondensedQbarCoefficientRealization.globalCoefficientIso_test,
      lowerStarFactor_inv_app_hom_app]
    have hu := ConcreteCategory.congr_hom (congr_app
      (CondensedQbarScalarConstruction.boundedPushforward_unit ℓ g)
        (op ((profiniteToProEtOf Y).obj S.unop)))
      (ULift.up (CondensedQbarScalarConstruction.boundedComp ℓ
        (profiniteTestProjection Y S.unop) a))
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hu
    rw [hu]
    unfold CondensedQbarScalarConstruction.boundedPushforwardPresheaf
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, ConcreteCategory.comp_apply]
    let e := (MorphismProperty.Over.pullbackComp g (toSpecZ Y) (toSpecZ Z)
      (comp_toSpecZ g).symm).inv.app (profiniteToProEt.obj S.unop)
    have hn := ConcreteCategory.congr_hom
      ((toSheafify (Scheme.ProEt.topology Z)
        (CondensedQbarScalarConstruction.boundedP ℓ Z)).naturality e.op)
      (ULift.up (CondensedQbarScalarConstruction.boundedComp ℓ
        (profiniteTestProjection Z S.unop) a))
    simp only [ConcreteCategory.comp_apply] at hn
    erw [← hn]
    congr 1
    apply ULift.ext
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    have hp : e.left ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Z) =
        pullback.fst (((profiniteToProEtOf Y).obj S.unop).hom) g ≫
          pullback.fst (toSpecZ (profiniteToScheme.obj S.unop)) (toSpecZ Y) := by
      dsimp only [e]
      simp only [MorphismProperty.Over.pullbackComp_inv_app_left]
      dsimp only [pullback.map]
      erw [Category.assoc, pullback.lift_fst]
      simp only [Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
      rfl
    have hp' := congrArg (fun k ↦ k.base.hom) hp
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp] at hp'
    change ((a.1.comp (profiniteTestProjection Z S.unop)).comp e.left.base.hom) x =
      ((a.1.comp (profiniteTestProjection Y S.unop)).comp
        (pullback.fst (((profiniteToProEtOf Y).obj S.unop).hom) g).base.hom) x
    simp only [profiniteTestProjection, ContinuousMap.comp_assoc]
    rw [hp']
    rfl

private theorem conjugate_extend (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (P : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      ((g)^*[Ab.{u + 1}].obj
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)))
    (p : P ⟶ P) :
    let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) g
    let E := Mod.extendScalarsIsoComapInv α
    (E.app P).inv ≫ (Mod.extendScalars α).map p ≫ (E.app P).hom =
      (Mod.comap (asIso α).inv).map p := by
  let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) g
  dsimp only [α]
  change (Mod.extendScalarsIsoComapInv α).inv.app P ≫
    ((Mod.extendScalars α).map p ≫ (Mod.extendScalarsIsoComapInv α).hom.app P) = _
  rw [(Mod.extendScalarsIsoComapInv α).hom.naturality]
  simp [α]

private theorem regular_pullback_hom (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (p : Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y) ⟶
      Mod.regular (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)) :
    ((condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map p ≫
        (condensedQbarRegularPullbackIso ℓ g).hom).hom =
      inv (condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) g) ≫
        (upperStar Ab.{u + 1} g).map p.hom ≫
          condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) g := by
  let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) g
  let P := (upperStar Ab.{u + 1} g).mapMod
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y)
  let d := Mod.regularIsoOfIsIso α
  have h := congrArg (fun k ↦ d.inv ≫ k ≫ d.hom)
    (conjugate_extend ℓ g _ (P.map p))
  have hh := congrArg Mod.Hom.hom h
  have hr : (d.inv ≫ (Mod.comap (asIso α).inv).map (P.map p) ≫ d.hom).hom =
      inv α ≫ (upperStar Ab.{u + 1} g).map p.hom ≫ α := by rfl
  rw [hr] at hh
  simpa only [condensedQbarRegularPullbackIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, P, d, α, CondensedRing.upperStar, Functor.comp_map] using hh

private theorem scalar_hom (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    (condensedQbarScalar ℓ Y a).asHom.hom =
      (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y).hom.hom ≫
        (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom.hom ≫
          (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y).inv.hom := by
  unfold condensedQbarScalar CondensedQbarScalarConstruction.transportedScalar
  change inv (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y).inv.hom ≫
    (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom.hom ≫ _ = _
  let e := (Mon.forget _).mapIso
    (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y)
  change inv e.inv ≫ (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom.hom ≫ e.inv =
    e.hom ≫ (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom.hom ≫ e.inv
  rw [IsIso.inv_eq_of_hom_inv_id e.inv_hom_id]

private theorem conjugate_square
    {C : Type (u + 2)} [Category.{u + 1} C] {D : Type (u + 2)} [Category.{u + 1} D]
    (G : D ⥤ C) {A B : C} {R S : D} (e : A ≅ B) (d : R ≅ S)
    (η : A ⟶ G.obj R) (δ : B ⟶ G.obj S) (p : B ⟶ B) (q : S ⟶ S)
    (hs : η ≫ G.map d.hom = e.hom ≫ δ) (hp : p ≫ δ = δ ≫ G.map q) :
    (e.hom ≫ p ≫ e.inv) ≫ η = η ≫ G.map (d.hom ≫ q ≫ d.inv) := by
  apply (cancel_mono (G.map d.hom)).1
  simp only [Functor.map_comp, Category.assoc]
  calc
    e.hom ≫ p ≫ e.inv ≫ η ≫ G.map d.hom =
        e.hom ≫ p ≫ e.inv ≫ e.hom ≫ δ := by rw [hs]
    _ = e.hom ≫ p ≫ δ := by simp
    _ = e.hom ≫ δ ≫ G.map q := by rw [hp]
    _ = η ≫ G.map d.hom ≫ G.map q := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ G.map q) hs.symm
    _ = η ≫ G.map d.hom ≫ G.map q ≫ G.map d.inv ≫ G.map d.hom := by
      have hcancel : G.map d.inv ≫ G.map d.hom = 𝟙 _ := by
        rw [← G.map_comp, d.inv_hom_id, G.map_id]
      rw [hcancel, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Bounded scalar multiplication commutes with arbitrary scheme inverse image.

Source: RefactorInstruction, Section 4, finite-matrix refinement, coefficient
realization and geometric-fiber comparison, steps 1--3
(auxiliary; not a blueprint node).

Proof in words: base change of small pro-etale objects sends a bounded function to
its composite with the first projection. This defines a morphism from the bounded
presheaf on Y to the direct image of the bounded presheaf on Z. Compose with the
sheafification unit and use the sheafification adjunction to obtain the corresponding
morphism of abelian sheaves. Its adjoint is a ring morphism from the inverse image
of the bounded coefficient sheaf on Y to the bounded coefficient sheaf on Z.
The square with the two globalCoefficientIso maps and condensedPullbackHom commutes:
under the point adjunction, evaluate both sides on a profinite test space S and a
bounded function on S. The normalization globalCoefficientIso_test identifies both
with that function pulled back through Z[S] to S. The canonical base-change
isomorphism Y[S] times_Y Z = Z[S] makes these projections equal. Equality follows
from the adjunction bijection and extensionality on profinite spaces and sections.
Multiplication by a pulls back to multiplication by a composed with g, as is checked
on bounded presheaf sections using associativity of function composition.
Naturality of the monoidal sheafification unit transports this equation to the
bounded sheaves. Conjugate the commuting square by the global coefficient
isomorphisms. Naturality of extendScalarsIsoComapInv cancels its two components;
the remaining regular-module comparisons have underlying maps alpha and alpha^-1,
where alpha is condensedPullbackHom. This is precisely the asserted equality.
The finite-extension bound survives every precomposition. If Z is empty both
endomorphisms are the unique endomorphism of the zero coefficient object.
-/
theorem condensedQbar_scalar_pullback (ℓ : ℕ) [Fact ℓ.Prime]
    {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (a : PadicAlgCl.finiteIntermediateFieldValued ℓ Y) :
    (condensedQbarRegularPullbackIso ℓ g).inv ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj ℓ) g).map
        (condensedQbarScalar ℓ Y a).asHom ≫ (condensedQbarRegularPullbackIso ℓ g).hom =
      (condensedQbarScalar ℓ Z
        (CondensedQbarScalarConstruction.boundedComp ℓ g.base.hom a)).asHom := by
  apply Mod.hom_ext
  rw [regular_pullback_hom]
  let α := condensedPullbackHom (Profinite.padicAlgClRingObj ℓ) g
  let G := lowerStar Ab.{u + 1} g
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} g
  let eY := (Mon.forget _).mapIso (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Y)
  let eZ := (Mon.forget _).mapIso (CondensedQbarCoefficientRealization.globalCoefficientIso ℓ Z)
  have hn := conjugate_square G eY eZ
    (condensedPushforwardHom (Profinite.padicAlgClRingObj ℓ) g)
    (CondensedQbarScalarConstruction.boundedPushforward ℓ g)
    (CondensedQbarScalarConstruction.sheafScalar ℓ Y a).asHom.hom
    (CondensedQbarScalarConstruction.sheafScalar ℓ Z
      (CondensedQbarScalarConstruction.boundedComp ℓ g.base.hom a)).asHom.hom
    (boundedCoefficient_scheme_naturality ℓ g)
    (CondensedQbarScalarConstruction.boundedPushforward_scalar ℓ g a)
  rw [scalar_hom, scalar_hom]
  apply (cancel_epi α).1
  simp only [α, IsIso.hom_inv_id_assoc]
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  rw [← unitAlgHom_comp_map_condensedPullbackHom] at hn
  exact hn

end AlgebraicGeometry.ProEtale
