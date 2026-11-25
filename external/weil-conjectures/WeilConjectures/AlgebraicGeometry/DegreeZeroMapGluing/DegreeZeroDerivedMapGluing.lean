/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.GoodTruncationNormalization
import WeilConjectures.CategoryTheory.Exact.ExactDerivedCohomologyCoherence
import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Conservative
import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.SheafGluing
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Unique gluing of derived maps locally concentrated in degree zero

Source: Stacks Project, Derived Categories, Tag 06XS; Modules on Sites, Tag 03EM;
Sites, Tag 04TQ; Homology, Tag 0118 (blueprint: lem-pur-degree-zero-derived-map-gluing).

The auxiliary predicates only spell out the conclusion, using the actual exact inverse
images and their canonical composition isomorphisms. They assume no descent property.
Both small sites use fixed-ring module sheaves. For finite coefficients the canonical
coefficient realization identifies this with modules over the constant ring sheaf, as in
`definition-small-pro-etale-site--1`. No new derived category or restriction is constructed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u uB vB wB wI

open CategoryTheory CategoryTheory.Limits Opposite
open ZeroObject

namespace AlgebraicGeometry.DegreeZeroMapGluing

section Formulas

variable (B : Scheme.{u} → Type uB) [∀ X, Category.{vB} (B X)]
  [∀ X, Abelian (B X)] [∀ X, HasDerivedCategory.{wB} (B X)]
  (r : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → B Y ⥤ B X)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (r f).Additive]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (r f)]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (r f)]
  (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), r (f ≫ g) ≅ r g ⋙ r f)

/-- The canonical comparison for two restrictions, including the equality of the
composite open immersion with the smaller open's immersion. Source: Stacks 04IX and
05RU (blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def openComp (T : Scheme.{u}) {U V : T.Opens} (h : U ≤ V) :
    (r V.ι).mapDerivedCategory ⋙ (r (T.homOfLE h)).mapDerivedCategory ≅
      (r U.ι).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso (r V.ι) (r (T.homOfLE h)) ≪≫
    Functor.mapDerivedCategoryNatIso
      ((c (T.homOfLE h) V.ι).symm ≪≫
        eqToIso (congrArg (fun f ↦ r f) (Scheme.homOfLE_ι T h)))

/-- Restrict a local map to a smaller open and identify its endpoints with the
restrictions of the global endpoints. Source: Stacks 04IX, 05RU
(blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def onSmallerOpen (T : Scheme.{u}) (M N : DerivedCategory (B T))
    {U V : T.Opens} (h : U ≤ V)
    (a : (r V.ι).mapDerivedCategory.obj M ⟶ (r V.ι).mapDerivedCategory.obj N) :
    (r U.ι).mapDerivedCategory.obj M ⟶ (r U.ι).mapDerivedCategory.obj N :=
  (openComp B r c T h).inv.app M ≫
    (r (T.homOfLE h)).mapDerivedCategory.map a ≫ (openComp B r c T h).hom.app N

/-- The good-truncation identifications on open subschemes of `T`, including `T` itself
via its identity immersion. Their normalization is the explicit roof through `truncLE 0`;
its degree-zero map is cycles modulo boundaries. Naturality and restriction use the
existing single and homology comparisons. Source: Stacks 0118, 05RU and 06XS
(blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def HasCanonicalIdentifications (T : Scheme.{u}) : Prop :=
  ∃ e : ∀ (X : Scheme.{u}) (j : X ⟶ T), IsOpenImmersion j →
      ∀ K : DerivedCategory (B X), DerivedCategory.homologyConcentratedIn 0 0 K →
        (K ≅ (DerivedCategory.singleFunctor (B X) 0).obj
          ((DerivedCategory.homologyFunctor (B X) 0).obj K)),
    (∀ (X : Scheme.{u}) (j : X ⟶ T) (hj : IsOpenImmersion j)
      (K L : DerivedCategory (B X))
      (hK : DerivedCategory.homologyConcentratedIn 0 0 K)
      (hL : DerivedCategory.homologyConcentratedIn 0 0 L) (a : K ⟶ L),
      a ≫ (e X j hj L hL).hom = (e X j hj K hK).hom ≫
        (DerivedCategory.singleFunctor (B X) 0).map
          ((DerivedCategory.homologyFunctor (B X) 0).map a)) ∧
    (∀ (X : Scheme.{u}) (j : X ⟶ T) (hj : IsOpenImmersion j)
      (Y : Scheme.{u}) (f : Y ⟶ X) (_hf : IsOpenImmersion f)
      (hfj : IsOpenImmersion (f ≫ j)) (K : DerivedCategory (B X))
      (hK : DerivedCategory.homologyConcentratedIn 0 0 K)
      (hRK : DerivedCategory.homologyConcentratedIn 0 0 ((r f).mapDerivedCategory.obj K)),
      (r f).mapDerivedCategory.map (e X j hj K hK).hom ≫
        ((r f).mapDerivedCategorySingleFunctor 0).hom.app
          ((DerivedCategory.homologyFunctor (B X) 0).obj K) ≫
        (DerivedCategory.singleFunctor (B Y) 0).map
          (((r f).mapDerivedCategoryHomologyFunctorIso 0).hom.app K) =
      (e Y (f ≫ j) hfj ((r f).mapDerivedCategory.obj K) hRK).hom) ∧
    (∀ (X : Scheme.{u}) (j : X ⟶ T) (hj : IsOpenImmersion j)
      (K : CochainComplex (B X) ℤ)
      (hK : DerivedCategory.homologyConcentratedIn 0 0 (DerivedCategory.Q.obj K)),
      ∃ p : K.truncLE 0 ⟶ (CochainComplex.singleFunctor (B X) 0).obj (K.homology 0),
        (p.f 0 ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom =
          (K.truncLEXIsoCycles 0).hom ≫ K.homologyπ 0) ∧
        (∀ a : ℤ, a ≠ 0 → p.f a = 0) ∧
        IsIso (DerivedCategory.Q.map (K.ιTruncLE 0)) ∧ IsIso (DerivedCategory.Q.map p) ∧
        DerivedCategory.Q.map (K.ιTruncLE 0) ≫
            (e X j hj (DerivedCategory.Q.obj K) hK).hom =
          DerivedCategory.Q.map p ≫ (DerivedCategory.singleFunctor (B X) 0).map
            ((DerivedCategory.homologyFunctorFactors (B X) 0).inv.app K))

/-- The full conclusion of degree-zero derived-map gluing, with the restriction bijection
written as compatibility iff a unique preimage exists. Thus no choice of a compatibility
proof is needed to define a map into a subtype. The last two clauses identify this with
sheaf-map gluing through `H⁰` and state the equality test explicitly. Source: Stacks 06XS,
03EM and 04TQ (blueprint: lem-pur-degree-zero-derived-map-gluing). -/
def Conclusion (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens) : Prop :=
  HasCanonicalIdentifications B r T ∧
  ∀ M N : DerivedCategory (B T),
    (∀ i : I, DerivedCategory.homologyConcentratedIn 0 0
      ((r (U i).ι).mapDerivedCategory.obj M) ∧
      DerivedCategory.homologyConcentratedIn 0 0 ((r (U i).ι).mapDerivedCategory.obj N)) →
    DerivedCategory.homologyConcentratedIn 0 0 M ∧
    DerivedCategory.homologyConcentratedIn 0 0 N ∧
    (∀ a : ∀ i : I, (r (U i).ι).mapDerivedCategory.obj M ⟶
        (r (U i).ι).mapDerivedCategory.obj N,
      (∀ i j : I,
        onSmallerOpen B r c T M N (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
          onSmallerOpen B r c T M N (inf_le_right : U i ⊓ U j ≤ U j) (a j)) ↔
      ∃! b : M ⟶ N, ∀ i : I, (r (U i).ι).mapDerivedCategory.map b = a i) ∧
    Function.Bijective (fun a : M ⟶ N ↦ (DerivedCategory.homologyFunctor (B T) 0).map a) ∧
    (∀ (a : M ⟶ N) (i : I),
      (r (U i).ι).map ((DerivedCategory.homologyFunctor (B T) 0).map a) ≫
          ((r (U i).ι).mapDerivedCategoryHomologyFunctorIso 0).hom.app N =
        ((r (U i).ι).mapDerivedCategoryHomologyFunctorIso 0).hom.app M ≫
          (DerivedCategory.homologyFunctor (B (U i).toScheme) 0).map
            ((r (U i).ι).mapDerivedCategory.map a)) ∧
    (∀ a b : M ⟶ N,
      (∀ i : I, (r (U i).ι).mapDerivedCategory.map a =
        (r (U i).ι).mapDerivedCategory.map b) ↔ a = b)

end Formulas

private theorem concentrated_iff {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C) :
    DerivedCategory.homologyConcentratedIn 0 0 K ↔
      ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C n).obj K) := by
  constructor
  · intro h n hn
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact (DerivedCategory.isGE_iff K 0).1 h.1 n hn
    · exact (DerivedCategory.isLE_iff K 0).1 h.2 n hn
  · intro h
    exact ⟨(DerivedCategory.isGE_iff K 0).2 (fun n hn ↦ h n (ne_of_lt hn)),
      (DerivedCategory.isLE_iff K 0).2 (fun n hn ↦ h n (ne_of_gt hn))⟩

section Canonical
variable (B : Scheme.{u} → Type uB) [∀ X, Category.{vB} (B X)]
  [∀ X, Abelian (B X)] [∀ X, HasDerivedCategory.{wB} (B X)]
  (r : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → B Y ⥤ B X)
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (r f).Additive]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (r f)]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (r f)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
private theorem canonical_identifications (T : Scheme.{u}) :
    HasCanonicalIdentifications B r T := by
  let e := fun (X : Scheme.{u}) (_j : X ⟶ T) (_hj : IsOpenImmersion _j)
    (K : DerivedCategory (B X)) (hK : DerivedCategory.homologyConcentratedIn 0 0 K) ↦
      DerivedCategory.goodTruncationNormalization K ((concentrated_iff K).1 hK)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro X j hj K L hK hL a
    exact (DerivedCategory.goodTruncationNormalization_naturality_hom K L
      ((concentrated_iff K).1 hK) ((concentrated_iff L).1 hL) a).1
  · intro X j hj Y f hf hfj K hK hRK
    exact (DerivedCategory.goodTruncationNormalization_exact (r f) K K
      ((concentrated_iff K).1 hK) ((concentrated_iff K).1 hK) (𝟙 K)).1.symm
  · intro X j hj K hK
    have h := DerivedCategory.goodTruncationNormalization_roof (DerivedCategory.Q.obj K)
      ((concentrated_iff _).1 hK) K (Iso.refl _)
    have hc := h.1
    have hp := h.2.1
    refine ⟨DerivedCategory.goodTruncationProjection K, ?_, ?_,
      inferInstance, inferInstance, ?_⟩
    · simp [DerivedCategory.goodTruncationProjection]
    · intro a ha
      exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ ha).eq_of_tgt _ _
    · have hh := h.2.2
      simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_inv, NatTrans.id_app,
        Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp] at hh
      erw [Category.id_comp, Category.comp_id] at hh
      exact hh

variable
  (c : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z), r (f ≫ g) ≅ r g ⋙ r f)

private def sheafComp (T : Scheme.{u}) {U V : T.Opens} (h : U ≤ V) :
    r V.ι ⋙ r (T.homOfLE h) ≅ r U.ι :=
  (c (T.homOfLE h) V.ι).symm ≪≫
    eqToIso (congrArg (fun f ↦ r f) (Scheme.homOfLE_ι T h))

private def onSmallerSheaf (T : Scheme.{u}) (F G : B T)
    {U V : T.Opens} (h : U ≤ V) (a : (r V.ι).obj F ⟶ (r V.ι).obj G) :
    (r U.ι).obj F ⟶ (r U.ι).obj G :=
  (sheafComp B r c T h).inv.app F ≫ (r (T.homOfLE h)).map a ≫
    (sheafComp B r c T h).hom.app G

omit [∀ X, Abelian (B X)] [∀ X, HasDerivedCategory.{wB} (B X)]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (r f).Additive]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (r f)]
  [∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (r f)] in
private theorem onSmallerSheaf_eq (T : Scheme.{u}) (F G : B T)
    {U V : T.Opens} (h : U ≤ V) (a : (r V.ι).obj F ⟶ (r V.ι).obj G)
    (e : r U.ι ≅ r V.ι ⋙ r (T.homOfLE h))
    (he : sheafComp B r c T h = e.symm) :
    onSmallerSheaf B r c T F G h a =
      e.hom.app F ≫ (r (T.homOfLE h)).map a ≫ e.inv.app G := by
  exact congrArg (fun q : r V.ι ⋙ r (T.homOfLE h) ≅ r U.ι ↦
    q.inv.app F ≫ (r (T.homOfLE h)).map a ≫ q.hom.app G) he

private def localH (T : Scheme.{u}) (M N : DerivedCategory (B T)) (U : T.Opens)
    (a : (r U.ι).mapDerivedCategory.obj M ⟶ (r U.ι).mapDerivedCategory.obj N) :
    (r U.ι).obj ((DerivedCategory.homologyFunctor (B T) 0).obj M) ⟶
      (r U.ι).obj ((DerivedCategory.homologyFunctor (B T) 0).obj N) :=
  ((r U.ι).mapDerivedCategoryHomologyFunctorIso 0).hom.app M ≫
    (DerivedCategory.homologyFunctor (B U.toScheme) 0).map a ≫
    ((r U.ι).mapDerivedCategoryHomologyFunctorIso 0).inv.app N

private theorem localH_map (T : Scheme.{u}) (M N : DerivedCategory (B T))
    (U : T.Opens) (a : M ⟶ N) :
    localH B r T M N U ((r U.ι).mapDerivedCategory.map a) =
      (r U.ι).map ((DerivedCategory.homologyFunctor (B T) 0).map a) := by
  dsimp only [localH]
  have hn := ((r U.ι).mapDerivedCategoryHomologyFunctorIso 0).hom.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem localH_bijective (T : Scheme.{u}) (M N : DerivedCategory (B T))
    (U : T.Opens)
    (hM : DerivedCategory.homologyConcentratedIn 0 0
      ((r U.ι).mapDerivedCategory.obj M))
    (hN : DerivedCategory.homologyConcentratedIn 0 0
      ((r U.ι).mapDerivedCategory.obj N)) :
    Function.Bijective (localH B r T M N U) := by
  have hb := (DerivedCategory.goodTruncationNormalization_naturality_hom _ _
    ((concentrated_iff _).1 hM) ((concentrated_iff _).1 hN) (0 :
      (r U.ι).mapDerivedCategory.obj M ⟶ (r U.ι).mapDerivedCategory.obj N)).2.1
  exact (((((r U.ι).mapDerivedCategoryHomologyFunctorIso 0).app M).symm.homCongr
    (((r U.ι).mapDerivedCategoryHomologyFunctorIso 0).app N).symm).bijective).comp hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem localH_smaller (T : Scheme.{u}) (M N : DerivedCategory (B T))
    {U V : T.Opens} (h : U ≤ V)
    (a : (r V.ι).mapDerivedCategory.obj M ⟶ (r V.ι).mapDerivedCategory.obj N) :
    localH B r T M N U (onSmallerOpen B r c T M N h a) =
      onSmallerSheaf B r c T
        ((DerivedCategory.homologyFunctor (B T) 0).obj M)
        ((DerivedCategory.homologyFunctor (B T) 0).obj N) h
        (localH B r T M N V a) := by
  let F := r V.ι
  let G := r (T.homOfLE h)
  let L := r U.ι
  let eta := sheafComp B r c T h
  let d := openComp B r c T h
  let H := DerivedCategory.homologyFunctor (B U.toScheme) 0
  have hc (K : DerivedCategory (B T)) :=
    (Functor.exactDerivedCohomologyCoherence F G 0).2 L eta K
  have hi (K : DerivedCategory (B T)) :
      (L.mapDerivedCategoryHomologyFunctorIso 0).hom.app K ≫ H.map (d.inv.app K) =
        eta.inv.app ((DerivedCategory.homologyFunctor (B T) 0).obj K) ≫
          G.map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app K) ≫
          (G.mapDerivedCategoryHomologyFunctorIso 0).hom.app
            (F.mapDerivedCategory.obj K) := by
    apply (cancel_epi (eta.hom.app _)).1
    apply (cancel_mono (H.map (d.hom.app K))).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← H.map_comp,
      Iso.inv_hom_id_app]
    erw [H.map_id, Category.comp_id]
    exact (hc K).symm
  dsimp only [localH, onSmallerOpen, onSmallerSheaf]
  change _ = eta.inv.app _ ≫ G.map (_ ≫ _ ≫ _) ≫ eta.hom.app _
  rw [H.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (hi M)]
  simp only [Category.assoc, G.map_comp]
  have hnat := (G.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality a
  dsimp only [Functor.comp_map] at hnat
  rw [← reassoc_of% hnat]
  have hn := hc N
  change G.map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app N) ≫
      (G.mapDerivedCategoryHomologyFunctorIso 0).hom.app _ ≫ H.map (d.hom.app N) =
        eta.hom.app _ ≫ (L.mapDerivedCategoryHomologyFunctorIso 0).hom.app N at hn
  have hn' :
      (G.mapDerivedCategoryHomologyFunctorIso 0).hom.app _ ≫ H.map (d.hom.app N) ≫
          (L.mapDerivedCategoryHomologyFunctorIso 0).inv.app N =
        G.map ((F.mapDerivedCategoryHomologyFunctorIso 0).inv.app N) ≫ eta.hom.app _ := by
    apply (cancel_epi (G.map ((F.mapDerivedCategoryHomologyFunctorIso 0).hom.app N))).1
    simp only [← G.map_comp_assoc, Iso.hom_inv_id_app,
      G.map_id, Category.id_comp]
    rw [reassoc_of% hn, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [hn']

private theorem assemble (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hzero : ∀ F : B T, (∀ i, IsZero ((r (U i).ι).obj F)) → IsZero F)
    (hglue : ∀ (F G : B T)
      (a : ∀ i, (r (U i).ι).obj F ⟶ (r (U i).ι).obj G),
      (∀ i j, onSmallerSheaf B r c T F G
        (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
        onSmallerSheaf B r c T F G (inf_le_right : U i ⊓ U j ≤ U j) (a j)) →
      ∃! b : F ⟶ G, ∀ i, (r (U i).ι).map b = a i) :
    Conclusion B r c T U := by
  have hext (F G : B T) (a b : F ⟶ G)
      (h : ∀ i, (r (U i).ι).map a = (r (U i).ι).map b) : a = b := by
    have hc (i j : I) :
        onSmallerSheaf B r c T F G (inf_le_left : U i ⊓ U j ≤ U i)
          ((r (U i).ι).map a) =
        onSmallerSheaf B r c T F G (inf_le_right : U i ⊓ U j ≤ U j)
          ((r (U j).ι).map a) := by
      have side {V W : T.Opens} (h : W ≤ V) :
          onSmallerSheaf B r c T F G h ((r V.ι).map a) = (r W.ι).map a := by
        have hn := (sheafComp B r c T h).hom.naturality a
        dsimp only [Functor.comp_map] at hn
        dsimp only [onSmallerSheaf]
        rw [hn]
        simp
      rw [side, side]
    obtain ⟨x, hx, hu⟩ := hglue F G (fun i ↦ (r (U i).ι).map a) hc
    exact (hu a (fun _ ↦ rfl)).trans (hu b (fun i ↦ (h i).symm)).symm
  refine ⟨canonical_identifications B r T, ?_⟩
  intro M N hMN
  have hconc (K : DerivedCategory (B T))
      (hK : ∀ i, DerivedCategory.homologyConcentratedIn 0 0
        ((r (U i).ι).mapDerivedCategory.obj K)) :
      DerivedCategory.homologyConcentratedIn 0 0 K := by
    apply (concentrated_iff K).2
    intro n hn
    apply hzero _
    intro i
    exact ((concentrated_iff _).1 (hK i) n hn).of_iso
      (((r (U i).ι).mapDerivedCategoryHomologyFunctorIso n).app K)
  have hM := hconc M (fun i ↦ (hMN i).1)
  have hN := hconc N (fun i ↦ (hMN i).2)
  have hb := (DerivedCategory.goodTruncationNormalization_naturality_hom M N
    ((concentrated_iff M).1 hM) ((concentrated_iff N).1 hN) (0 : M ⟶ N)).2.1
  have hdext (a b : M ⟶ N)
      (h : ∀ i, (r (U i).ι).mapDerivedCategory.map a =
        (r (U i).ι).mapDerivedCategory.map b) : a = b := by
    apply hb.1
    apply hext
    intro i
    simpa only [← localH_map B r T M N (U i)] using
      congrArg (localH B r T M N (U i)) (h i)
  refine ⟨hM, hN, ?_, hb, ?_, ?_⟩
  · intro a
    constructor
    · intro ha
      let aa := fun i ↦ localH B r T M N (U i) (a i)
      obtain ⟨b, hba, hbu⟩ := hglue _ _ aa (by
        intro i j
        rw [← localH_smaller, ← localH_smaller]
        exact congrArg (localH B r T M N (U i ⊓ U j)) (ha i j))
      obtain ⟨f, hf⟩ := hb.2 b
      have hfa (i : I) : (r (U i).ι).mapDerivedCategory.map f = a i := by
        apply (localH_bijective B r T M N (U i) (hMN i).1 (hMN i).2).1
        rw [localH_map]
        change (DerivedCategory.homologyFunctor (B T) 0).map f = b at hf
        rw [hf]
        exact hba i
      exact ⟨f, hfa, fun g hg ↦ hdext g f (fun i ↦ (hg i).trans (hfa i).symm)⟩
    · rintro ⟨b, hab, _⟩ i j
      rw [← hab i, ← hab j]
      have side {V W : T.Opens} (h : W ≤ V) :
          onSmallerOpen B r c T M N h ((r V.ι).mapDerivedCategory.map b) =
            (r W.ι).mapDerivedCategory.map b := by
        have hn := (openComp B r c T h).hom.naturality b
        dsimp only [Functor.comp_map] at hn
        dsimp only [onSmallerOpen]
        rw [hn]
        simp
      rw [side, side]
  · intro a i
    exact ((r (U i).ι).mapDerivedCategoryHomologyFunctorIso 0).hom.naturality a
  · intro a b
    exact ⟨hdext a b, fun h i ↦ congrArg ((r (U i).ι).mapDerivedCategory.map) h⟩

private theorem assemble_of_reflects (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hreflect : JointlyReflectIsomorphisms (fun i ↦ r (U i).ι))
    (hglue : ∀ (F G : B T)
      (a : ∀ i, (r (U i).ι).obj F ⟶ (r (U i).ι).obj G),
      (∀ i j, onSmallerSheaf B r c T F G
        (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
        onSmallerSheaf B r c T F G (inf_le_right : U i ⊓ U j ≤ U j) (a j)) →
      ∃ b : F ⟶ G, ∀ i, (r (U i).ι).map b = a i) :
    Conclusion B r c T U := by
  apply assemble B r c T U
  · intro F hF
    have hh (i : I) : IsIso ((r (U i).ι).map (0 : F ⟶ 0)) :=
      isIso_of_source_target_iso_zero _ (hF i).isoZero
        ((r (U i).ι).map_isZero (isZero_zero _)).isoZero
    have := hreflect.isIso (0 : F ⟶ 0)
    exact (isZero_zero _).of_iso (asIso (0 : F ⟶ 0))
  · intro F G a ha
    obtain ⟨b, hb⟩ := hglue F G a ha
    exact ⟨b, hb, fun b' hb' ↦ hreflect.jointlyFaithful.map_injective
      (fun i ↦ (hb' i).trans (hb i).symm)⟩

end Canonical

-- Keep categorical associativity abstract when the morphisms come from adjunctions.
private theorem reassociate_five {C : Type*} [Category C]
    {A B D E F G : C} {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {d : E ⟶ F} {e : F ⟶ G} {z : A ⟶ G}
    (h : a ≫ b ≫ c ≫ d ≫ e = z) : a ≫ (b ≫ c ≫ d) ≫ e = z := by
  simpa only [Category.assoc] using h

private theorem map_eq_of_conjugate {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} (b : X ⟶ Y)
    (a : F.obj X ⟶ F.obj Y)
    (h : G.map b = e.inv.app X ≫ a ≫ e.hom.app Y) : F.map b = a := by
  have hn := e.hom.naturality b
  rw [h] at hn
  apply (cancel_mono (e.hom.app Y)).1
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc] using hn

private theorem transport_local_map {C D E : Type*} [Category C] [Category D]
    [Category E] (F G : Cᵒᵖ ⥤ E) (m : D ⥤ C)
    (a : m.op ⋙ F ⟶ m.op ⋙ G) {X Y : D} {W Z : C}
    (b : X ≅ Y) (c : W ≅ m.obj X) (e : W ≅ Z) (q : m.obj Y ≅ Z)
    (hc : c.inv ≫ e.hom = m.map b.hom ≫ q.hom)
    (hc' : e.inv ≫ c.hom = q.inv ≫ m.map b.inv) :
    F.map e.hom.op ≫ (F.map c.inv.op ≫ a.app (op X) ≫ G.map c.hom.op) ≫
      G.map e.inv.op = F.map q.hom.op ≫ a.app (op Y) ≫ G.map q.inv.op := by
  have hn := a.naturality b.hom.op
  change F.map (m.map b.hom).op ≫ a.app (op X) =
    a.app (op Y) ≫ G.map (m.map b.hom).op at hn
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp]
  rw [hc, hc']
  simp only [op_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← op_comp, ← m.map_comp,
    Iso.inv_hom_id, m.map_id, op_id]
  erw [G.map_id, Category.id_comp]

attribute [local irreducible] Etale.upperStarIsoLocalizationRestriction
  ProEtale.upperStarIsoLocalizationRestriction

private noncomputable def etale_overMapIso {X Y : Scheme.{u}} (e : Y ⟶ X)
    (he : Etale e) (Z : X.Etale) (t : Z.left ⟶ Y) (h : t ≫ e = Z.hom) :
    (MorphismProperty.Over.map ⊤ he).obj (MorphismProperty.Over.mk ⊤ t
      (MorphismProperty.of_postcomp _ _ _ he (h ▸ Z.prop))) ≅ Z :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by simp [h])

-- The source proof works for a covering sieve indexed in any universe.
private theorem etale_local_glue (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    {X : Scheme.{u}} {ι : Type wI} {V : ι → Scheme.{u}} (e : ∀ j, V j ⟶ X)
    (he : ∀ j, Etale (e j))
    (hcov : Sieve.ofArrows (fun j ↦ MorphismProperty.Over.mk ⊤ (e j) (he j))
      (fun j ↦ (MorphismProperty.Over.homMk (e j) (Category.comp_id _) :
        MorphismProperty.Over.mk ⊤ (e j) (he j) ⟶ Scheme.Etale.mk (𝟙 X))) ∈
        X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)))
    (F G : Sheaf X.smallEtaleTopology E)
    (ψ : ∀ j, (Etale.localizationRestriction E (e j) (he j)).obj F ⟶
      (Etale.localizationRestriction E (e j) (he j)).obj G)
    (hψ : ∀ j k (T : X.Etale) (tj : T.left ⟶ V j) (tk : T.left ⟶ V k) (hj : tj ≫ e j = T.hom)
      (hk : tk ≫ e k = T.hom),
      F.obj.map (etale_overMapIso (e j) (he j) T tj hj).hom.op ≫ (ψ j).hom.app (op _) ≫
          G.obj.map (etale_overMapIso (e j) (he j) T tj hj).inv.op =
        F.obj.map (etale_overMapIso (e k) (he k) T tk hk).hom.op ≫ (ψ k).hom.app (op _) ≫
          G.obj.map (etale_overMapIso (e k) (he k) T tk hk).inv.op) :
    ∃ φ : F ⟶ G,
      ∀ j, (Etale.localizationRestriction E (e j) (he j)).map φ = ψ j := by
  let P := presheafHom F.obj G.obj
  let V' : ι → X.Etale := fun j ↦ MorphismProperty.Over.mk ⊤ (e j) (he j)
  let top : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let π : ∀ j, V' j ⟶ top := fun j ↦ MorphismProperty.Over.homMk (e j) (Category.comp_id _) trivial
  have hw : ∀ j (T : Over (V' j)), T.hom.left ≫ e j = T.left.hom := fun j T ↦ by
    simpa [V'] using MorphismProperty.Over.w T.hom
  -- the transport of `ψ j` to the localized site at `V' j`
  let Φ : ∀ j, Over (V' j) ⥤ (V j).Etale := fun j ↦
    { obj T := MorphismProperty.Over.mk ⊤ T.hom.left
        (MorphismProperty.of_postcomp _ _ _ (he j) (by
          rw [hw j T]; exact T.left.prop))
      map g := MorphismProperty.Over.homMk g.left.left
        (congrArg (fun f ↦ f.left) (Over.w g)) trivial }
  let κ : ∀ j, Φ j ⋙ MorphismProperty.Over.map ⊤ (he j) ≅ Over.forget (V' j) := fun j ↦
    NatIso.ofComponents (fun T ↦ etale_overMapIso (e j) (he j) T.left T.hom.left
      (hw j T)) (fun g ↦ by ext; simp [etale_overMapIso, Φ])
  let x : ∀ j, P.obj (op (V' j)) := fun j ↦
    (Functor.isoWhiskerRight (NatIso.op (κ j)) F.obj).hom ≫
      Functor.whiskerLeft (Φ j).op (ψ j).hom ≫
        (Functor.isoWhiskerRight (NatIso.op (κ j)) G.obj).inv
  have hx : Presieve.Arrows.Compatible P π x := by
    intro i k Z gi gk h
    refine NatTrans.ext (funext fun T ↦ ?_)
    exact hψ i k T.unop.left _ _ (hw i ((Over.map gi).obj T.unop)) (hw k ((Over.map gk).obj T.unop))
  have hP : Presheaf.IsSheaf X.smallEtaleTopology P := Presheaf.IsSheaf.hom F.obj G.obj G.property
  have hsf : (Presieve.ofArrows V' π).IsSheafFor P := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp hP
    rw [Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf x hx
  let toTop : ∀ U : X.Etale, U ⟶ top := fun U ↦
    MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial
  have htop : ∀ {U : X.Etale} (f : U ⟶ top), f = toTop U := fun f ↦ by
    exact MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let s : P.sections := ⟨fun U ↦ P.map (toTop U.unop).op t, fun {U U'} f ↦ by
    simp only [← Functor.map_comp_apply]
    rw [show (toTop U.unop).op ≫ f = (f.unop ≫ toTop U.unop).op from rfl,
      htop (f.unop ≫ toTop U.unop)]⟩
  refine ⟨⟨presheafHomSectionsEquiv _ _ s⟩, fun j ↦ ?_⟩
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  let g₀ : (MorphismProperty.Over.map ⊤ (he j)).obj W.unop ⟶ V' j :=
    MorphismProperty.Over.homMk W.unop.hom rfl trivial
  have h := congrArg (fun α ↦ α.app (op (Over.mk g₀))) (ht j)
  have hκ : etale_overMapIso (e j) (he j) _ g₀.left (hw j (Over.mk g₀)) = Iso.refl _ := by
    ext; rfl
  dsimp only [x] at h
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.op_hom, NatIso.op_inv,
    NatTrans.op_app] at h
  have h₁ : (κ j).hom.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.hom hκ
  have h₂ : (κ j).inv.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.inv hκ
  rw [h₁, h₂] at h
  erw [op_id, F.obj.map_id, G.obj.map_id, Category.id_comp, Category.comp_id] at h
  refine Eq.trans ?_ h
  change t.app (op (Over.mk (𝟙 _ ≫ toTop _))) = t.app (op (Over.mk (g₀ ≫ π j)))
  rw [htop (𝟙 _ ≫ toTop _), htop (g₀ ≫ π j)]

-- Use the same sheaf-Hom argument for a family of pro-etale cover arrows.
private theorem proetale_local_glue (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    {X : Scheme.{u}} {ι : Type wI} {V : ι → Scheme.{u}} (e : ∀ j, V j ⟶ X)
    (he : ∀ j, WeaklyEtale (e j))
    (hcov : Sieve.ofArrows (fun j ↦ MorphismProperty.Over.mk ⊤ (e j) (he j))
      (fun j ↦ (MorphismProperty.Over.homMk (e j) (Category.comp_id _) :
        MorphismProperty.Over.mk ⊤ (e j) (he j) ⟶ Scheme.ProEt.mk (𝟙 X))) ∈
        (Scheme.ProEt.topology X) (Scheme.ProEt.mk (𝟙 X)))
    (F G : Sheaf (Scheme.ProEt.topology X) E)
    (ψ : ∀ j, (ProEtale.localizationRestriction E (e j) (he j)).obj F ⟶
      (ProEtale.localizationRestriction E (e j) (he j)).obj G)
    (hψ : ∀ j k (T : X.ProEt) (tj : T.left ⟶ V j) (tk : T.left ⟶ V k) (hj : tj ≫ e j = T.hom)
      (hk : tk ≫ e k = T.hom),
      F.obj.map (ProEtale.overMapIso (e j) (he j) T tj hj).hom.op ≫ (ψ j).hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso (e j) (he j) T tj hj).inv.op =
        F.obj.map (ProEtale.overMapIso (e k) (he k) T tk hk).hom.op ≫ (ψ k).hom.app (op _) ≫
          G.obj.map (ProEtale.overMapIso (e k) (he k) T tk hk).inv.op) :
    ∃ φ : F ⟶ G,
      ∀ j, (ProEtale.localizationRestriction E (e j) (he j)).map φ = ψ j := by
  let P := presheafHom F.obj G.obj
  let V' : ι → X.ProEt := fun j ↦ MorphismProperty.Over.mk ⊤ (e j) (he j)
  let top : X.ProEt := MorphismProperty.Over.mk ⊤ (𝟙 X) inferInstance
  let π : ∀ j, V' j ⟶ top := fun j ↦ MorphismProperty.Over.homMk (e j) (Category.comp_id _) trivial
  have hw : ∀ j (T : Over (V' j)), T.hom.left ≫ e j = T.left.hom := fun j T ↦ by
    simpa [V'] using MorphismProperty.Over.w T.hom
  -- the transport of `ψ j` to the localized site at `V' j`
  let Φ : ∀ j, Over (V' j) ⥤ (V j).ProEt := fun j ↦
    { obj T := MorphismProperty.Over.mk ⊤ T.hom.left
        (MorphismProperty.of_postcomp _ _ _ (he j) (by
          rw [hw j T]; exact T.left.prop))
      map g := MorphismProperty.Over.homMk g.left.left
        (congrArg (fun f ↦ f.left) (Over.w g)) trivial }
  let κ : ∀ j, Φ j ⋙ MorphismProperty.Over.map ⊤ (he j) ≅ Over.forget (V' j) := fun j ↦
    NatIso.ofComponents (fun T ↦ ProEtale.overMapIso (e j) (he j) T.left T.hom.left
      (hw j T)) (fun g ↦ by ext; simp [ProEtale.overMapIso, Φ])
  let x : ∀ j, P.obj (op (V' j)) := fun j ↦
    (Functor.isoWhiskerRight (NatIso.op (κ j)) F.obj).hom ≫
      Functor.whiskerLeft (Φ j).op (ψ j).hom ≫
        (Functor.isoWhiskerRight (NatIso.op (κ j)) G.obj).inv
  have hx : Presieve.Arrows.Compatible P π x := by
    intro i k Z gi gk h
    refine NatTrans.ext (funext fun T ↦ ?_)
    exact hψ i k T.unop.left _ _ (hw i ((Over.map gi).obj T.unop)) (hw k ((Over.map gk).obj T.unop))
  have hP : Presheaf.IsSheaf (Scheme.ProEt.topology X) P :=
    Presheaf.IsSheaf.hom F.obj G.obj G.property
  have hsf : (Presieve.ofArrows V' π).IsSheafFor P := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp hP
    rw [Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1 hsf x hx
  let toTop : ∀ U : X.ProEt, U ⟶ top := fun U ↦
    MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial
  have htop : ∀ {U : X.ProEt} (f : U ⟶ top), f = toTop U := fun f ↦ by
    exact MorphismProperty.Over.Hom.ext
      ((Category.comp_id _).symm.trans (MorphismProperty.Over.w f))
  let s : P.sections := ⟨fun U ↦ P.map (toTop U.unop).op t, fun {U U'} f ↦ by
    simp only [← Functor.map_comp_apply]
    rw [show (toTop U.unop).op ≫ f = (f.unop ≫ toTop U.unop).op from rfl,
      htop (f.unop ≫ toTop U.unop)]⟩
  refine ⟨⟨presheafHomSectionsEquiv _ _ s⟩, fun j ↦ ?_⟩
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun W ↦ ?_)
  let g₀ : (MorphismProperty.Over.map ⊤ (he j)).obj W.unop ⟶ V' j :=
    MorphismProperty.Over.homMk W.unop.hom rfl trivial
  have h := congrArg (fun α ↦ α.app (op (Over.mk g₀))) (ht j)
  have hκ : ProEtale.overMapIso (e j) (he j) _ g₀.left (hw j (Over.mk g₀)) = Iso.refl _ := by
    ext; rfl
  dsimp only [x] at h
  simp only [NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.op_hom, NatIso.op_inv,
    NatTrans.op_app] at h
  have h₁ : (κ j).hom.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.hom hκ
  have h₂ : (κ j).inv.app (Over.mk g₀) = 𝟙 _ := congrArg Iso.inv hκ
  rw [h₁, h₂] at h
  erw [op_id, F.obj.map_id, G.obj.map_id, Category.id_comp, Category.comp_id] at h
  refine Eq.trans ?_ h
  change t.app (op (Over.mk (𝟙 _ ≫ toTop _))) = t.app (op (Over.mk (g₀ ≫ π j)))
  rw [htop (𝟙 _ ≫ toTop _), htop (g₀ ≫ π j)]

private theorem open_jointly_surjective (T : Scheme.{u}) {I : Type wI}
    (U : I → T.Opens) (hU : ∀ x : T, ∃ i, x ∈ U i) :
    ⋃ i, Set.range (U i).ι.base = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  obtain ⟨i, hi⟩ := hU x
  exact ⟨i, ⟨x, hi⟩, rfl⟩

private theorem open_proetale_cover (T : Scheme.{u}) {I : Type wI}
    (U : I → T.Opens) (hU : ∀ x : T, ∃ i, x ∈ U i) :
    Presieve.ofArrows (fun i ↦ (U i).toScheme) (fun i ↦ (U i).ι) ∈
      Scheme.proetalePrecoverage T :=
  Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ by obtain ⟨i, hi⟩ := hU x; exact ⟨i, by simpa using hi⟩,
        fun i ↦ inferInstanceAs (IsOpenImmersion (U i).ι)⟩)

private theorem etale_reflects (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i) :
    JointlyReflectIsomorphisms
      (fun i ↦ Etale.upperStar E (U i).ι) := by
  constructor
  intro F G f hf
  apply Etale.isIso_of_isIso_localizationRestriction E f
    (fun i ↦ (U i).ι)
  · exact open_jointly_surjective T U hU
  · intro i
    exact (NatIso.isIso_map_iff (Etale.upperStarIsoLocalizationRestriction
      E (U i).ι inferInstance) f).1 (hf i)

private theorem proetale_reflects (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i) :
    JointlyReflectIsomorphisms
      (fun i ↦ ProEtale.upperStar E (U i).ι) := by
  constructor
  intro F G f hf
  apply ProEtale.isIso_of_isIso_localizationRestriction E f
    (fun i ↦ (U i).ι)
  · exact open_proetale_cover T U hU
  · intro i
    exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction
      E (U i).ι inferInstance) f).1 (hf i)

private theorem etale_sheafComp (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {U V : T.Opens} (h : U ≤ V) :
    sheafComp (fun X ↦ Sheaf X.smallEtaleTopology E)
      (fun {_ _} f ↦ Etale.upperStar E f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp E f g) T h =
        (Etale.upperStarComp E (T.homOfLE h) V.ι U.ι
          (Scheme.homOfLE_ι T h).symm).symm := by
  have aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
      (e : f ≫ g = k) :
      (Etale.upperStarComp E f g).symm ≪≫
          eqToIso (congrArg (Etale.upperStar E) e) =
        (Etale.upperStarComp E f g k e.symm).symm := by
    subst k
    simp only [eqToIso_refl, Iso.trans_refl]
  exact aux (T.homOfLE h) V.ι U.ι (Scheme.homOfLE_ι T h)

private theorem proetale_sheafComp (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {U V : T.Opens} (h : U ≤ V) :
    sheafComp (fun X ↦ Sheaf (Scheme.ProEt.topology X) E)
      (fun {_ _} f ↦ ProEtale.upperStar E f)
      (fun {_ _ _} f g ↦ ProEtale.upperStarComp E f g) T h =
        (ProEtale.upperStarComp' E (T.homOfLE h) V.ι U.ι
          (Scheme.homOfLE_ι T h).symm).symm := by
  have aux {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
      (e : f ≫ g = k) :
      (ProEtale.upperStarComp E f g).symm ≪≫
          eqToIso (congrArg (ProEtale.upperStar E) e) =
        (ProEtale.upperStarComp' E f g k e.symm).symm := by
    subst k
    simp [ProEtale.upperStarComp', ProEtale.upperStarCongr]
  exact aux (T.homOfLE h) V.ι U.ι (Scheme.homOfLE_ι T h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in

private theorem etale_restriction_glue (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i)
    (F G : Sheaf T.smallEtaleTopology E)
    (ψ : ∀ i, (Etale.localizationRestriction E
      (U i).ι inferInstance).obj F ⟶
      (Etale.localizationRestriction E
        (U i).ι inferInstance).obj G)
    (hψ : ∀ i j,
      (Etale.localizationRestrictionComp E
        (T.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (U i).ι inferInstance inferInstance
        (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).hom.app F ≫
        (Etale.localizationRestriction E
          (T.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) inferInstance).map (ψ i) ≫
        (Etale.localizationRestrictionComp E
          (T.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (U i).ι inferInstance inferInstance
          (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).inv.app G =
      (Etale.localizationRestrictionComp E
        (T.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (U j).ι inferInstance inferInstance
        (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).hom.app F ≫
        (Etale.localizationRestriction E
          (T.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) inferInstance).map (ψ j) ≫
        (Etale.localizationRestrictionComp E
          (T.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (U j).ι inferInstance inferInstance
          (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).inv.app G) :
    ∃ b : F ⟶ G, ∀ i, (Etale.localizationRestriction E
      (U i).ι inferInstance).map b = ψ i := by
  exact etale_local_glue E (fun i ↦ (U i).ι) (fun _ ↦ inferInstance)
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff _).2
      (open_jointly_surjective T U hU)) F G ψ (by
      intro i j Z ti tj hi hj
      obtain ⟨t, hti, htj⟩ := (isPullback_opens_inf (U i) (U j)).exists_lift
        ti tj (hi.trans hj.symm)
      have ht : t ≫ (U i ⊓ U j).ι = Z.hom := by
        rw [← Scheme.homOfLE_ι T (inf_le_left : U i ⊓ U j ≤ U i),
          ← Category.assoc, hti]
        exact hi
      let V : (U i ⊓ U j).toScheme.Etale := MorphismProperty.Over.mk ⊤ t
        (MorphismProperty.of_postcomp _ _ _ (inferInstance : Etale (U i ⊓ U j).ι)
          (ht ▸ Z.prop))
      have hh' := hψ i j
      let e := etale_overMapIso (U i ⊓ U j).ι
        (inferInstance : Etale (U i ⊓ U j).ι) Z t ht
      have hv := congrArg (fun f ↦ F.obj.map e.hom.op ≫ f.hom.app (op V) ≫
        G.obj.map e.inv.op) hh'
      have side (k : I) (h : U i ⊓ U j ≤ U k) (tk : Z.left ⟶ (U k).toScheme)
          (hk : tk ≫ (U k).ι = Z.hom) (htk : t ≫ T.homOfLE h = tk) :
          F.obj.map e.hom.op ≫
            (F.obj.map ((MorphismProperty.Over.mapComp ⊤
                (inferInstance : Etale (T.homOfLE h))
                (inferInstance : Etale (U k).ι) (U i ⊓ U j).ι
                (Scheme.homOfLE_ι T h).symm).inv.app V).op ≫
              (ψ k).hom.app (op ((MorphismProperty.Over.map ⊤
                (inferInstance : Etale (T.homOfLE h))).obj V)) ≫
              G.obj.map ((MorphismProperty.Over.mapComp ⊤
                (inferInstance : Etale (T.homOfLE h))
                (inferInstance : Etale (U k).ι) (U i ⊓ U j).ι
                (Scheme.homOfLE_ι T h).symm).hom.app V).op) ≫ G.obj.map e.inv.op =
            F.obj.map (etale_overMapIso (U k).ι inferInstance Z tk hk).hom.op ≫
              (ψ k).hom.app (op (MorphismProperty.Over.mk ⊤ tk
                (MorphismProperty.of_postcomp _ _ _
                  (inferInstance : Etale (U k).ι) (hk ▸ Z.prop)))) ≫
              G.obj.map (etale_overMapIso (U k).ι inferInstance Z tk hk).inv.op := by
        let b := MorphismProperty.Over.isoMk (P := @Etale) (Q := ⊤)
          (A := (MorphismProperty.Over.map ⊤
            (inferInstance : Etale (T.homOfLE h))).obj V)
          (B := MorphismProperty.Over.mk ⊤ tk
            (MorphismProperty.of_postcomp _ _ _
              (inferInstance : Etale (U k).ι) (hk ▸ Z.prop)))
          (Iso.refl Z.left) (by simpa [V] using htk.symm)
        let m := MorphismProperty.Over.map ⊤ (inferInstance : Etale (U k).ι)
        let c := (MorphismProperty.Over.mapComp ⊤
          (inferInstance : Etale (T.homOfLE h))
          (inferInstance : Etale (U k).ι) (U i ⊓ U j).ι
          (Scheme.homOfLE_ι T h).symm).app V
        let q := etale_overMapIso (U k).ι (inferInstance : Etale (U k).ι) Z tk hk
        have hc : c.inv ≫ e.hom = m.map b.hom ≫ q.hom := by
          apply MorphismProperty.Over.Hom.ext
          change (𝟙 Z.left) ≫ (𝟙 Z.left) = (𝟙 Z.left) ≫ (𝟙 Z.left)
          rfl
        have hc' : e.inv ≫ c.hom = q.inv ≫ m.map b.inv := by
          apply MorphismProperty.Over.Hom.ext
          change (𝟙 Z.left) ≫ (𝟙 Z.left) = (𝟙 Z.left) ≫ (𝟙 Z.left)
          rfl
        exact transport_local_map F.obj G.obj m (ψ k).hom b c e q hc hc'
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hv
      simp only [Etale.localizationRestriction_map_hom_app,
        Etale.localizationRestrictionComp, Iso.symm_hom, Iso.symm_inv,
        Functor.sheafPushforwardContinuousComp'_inv_app_hom_app,
        Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hv
      exact (side i inf_le_left ti hi hti).symm.trans
        (hv.trans (side j inf_le_right tj hj htj)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in

private theorem etale_sheaf_glue (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i)
    (F G : Sheaf T.smallEtaleTopology E)
    (a : ∀ i, (Etale.upperStar E (U i).ι).obj F ⟶
      (Etale.upperStar E (U i).ι).obj G)
    (ha : ∀ i j, onSmallerSheaf
      (fun X ↦ Sheaf X.smallEtaleTopology E)
      (fun {_ _} f ↦ Etale.upperStar E f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp E f g) T F G
      (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      onSmallerSheaf (fun X ↦ Sheaf X.smallEtaleTopology E)
      (fun {_ _} f ↦ Etale.upperStar E f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp E f g) T F G
      (inf_le_right : U i ⊓ U j ≤ U j) (a j)) :
    ∃ b : F ⟶ G, ∀ i, (Etale.upperStar E (U i).ι).map b = a i := by
  let θ := fun i ↦ Etale.upperStarIsoLocalizationRestriction
    E (U i).ι inferInstance
  let ψ := fun i ↦ (θ i).inv.app F ≫ a i ≫ (θ i).hom.app G
  obtain ⟨b, hb⟩ := etale_restriction_glue E T U hU F G ψ (by
      intro i j
      have side {V W : T.Opens} (h : W ≤ V)
          (a : (Etale.upperStar E V.ι).obj F ⟶ (Etale.upperStar E V.ι).obj G) :=
        (congrArg (fun f ↦
          (Etale.upperStarIsoLocalizationRestriction E W.ι inferInstance).inv.app F ≫
            f ≫ (Etale.upperStarIsoLocalizationRestriction E W.ι inferInstance).hom.app G)
          (onSmallerSheaf_eq (fun X ↦ Sheaf X.smallEtaleTopology E)
            (fun {_ _} f ↦ Etale.upperStar E f)
            (fun {_ _ _} f g ↦ Etale.upperStarComp E f g) T F G h a
            (Etale.upperStarComp E (T.homOfLE h) V.ι W.ι
              (Scheme.homOfLE_ι T h).symm) (etale_sheafComp E T h))).trans
          (reassociate_five (Etale.upperStarComp_conj (T.homOfLE h) V.ι
            inferInstance inferInstance W.ι (Scheme.homOfLE_ι T h).symm inferInstance a))
      exact (side (inf_le_left : U i ⊓ U j ≤ U i) (a i)).symm.trans
        ((congrArg (fun f ↦
          (Etale.upperStarIsoLocalizationRestriction E (U i ⊓ U j).ι
            inferInstance).inv.app F ≫ f ≫
            (Etale.upperStarIsoLocalizationRestriction E (U i ⊓ U j).ι
              inferInstance).hom.app G) (ha i j)).trans
          (side (inf_le_right : U i ⊓ U j ≤ U j) (a j))))
  exact ⟨b, fun i ↦ map_eq_of_conjugate (θ i) b (a i) (hb i)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem proetale_restriction_glue (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i)
    (F G : Sheaf (Scheme.ProEt.topology T) E)
    (ψ : ∀ i, (ProEtale.localizationRestriction E
      (U i).ι inferInstance).obj F ⟶
      (ProEtale.localizationRestriction E
        (U i).ι inferInstance).obj G)
    (hψ : ∀ i j,
      (ProEtale.localizationRestrictionComp E
        (T.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (U i).ι inferInstance inferInstance
        (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).hom.app F ≫
        (ProEtale.localizationRestriction E
          (T.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) inferInstance).map (ψ i) ≫
        (ProEtale.localizationRestrictionComp E
          (T.homOfLE (inf_le_left : U i ⊓ U j ≤ U i)) (U i).ι inferInstance inferInstance
          (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).inv.app G =
      (ProEtale.localizationRestrictionComp E
        (T.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (U j).ι inferInstance inferInstance
        (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).hom.app F ≫
        (ProEtale.localizationRestriction E
          (T.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) inferInstance).map (ψ j) ≫
        (ProEtale.localizationRestrictionComp E
          (T.homOfLE (inf_le_right : U i ⊓ U j ≤ U j)) (U j).ι inferInstance inferInstance
          (U i ⊓ U j).ι (Scheme.homOfLE_ι T _).symm inferInstance).inv.app G) :
    ∃ b : F ⟶ G, ∀ i, (ProEtale.localizationRestriction E
      (U i).ι inferInstance).map b = ψ i := by
  exact proetale_local_glue E (fun i ↦ (U i).ι) (fun _ ↦ inferInstance)
    (by
      rw [Scheme.ProEt.mem_topology_iff]
      refine ⟨_, ?_, Sieve.le_generate _⟩
      rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
      exact open_proetale_cover T U hU) F G ψ (by
      intro i j Z ti tj hi hj
      obtain ⟨t, hti, htj⟩ := (isPullback_opens_inf (U i) (U j)).exists_lift
        ti tj (hi.trans hj.symm)
      have ht : t ≫ (U i ⊓ U j).ι = Z.hom := by
        rw [← Scheme.homOfLE_ι T (inf_le_left : U i ⊓ U j ≤ U i),
          ← Category.assoc, hti]
        exact hi
      let V : (U i ⊓ U j).toScheme.ProEt := MorphismProperty.Over.mk ⊤ t
        (MorphismProperty.of_postcomp _ _ _ (inferInstance : WeaklyEtale (U i ⊓ U j).ι)
          (ht ▸ Z.prop))
      have hh' := hψ i j
      let e := ProEtale.overMapIso (U i ⊓ U j).ι
        (inferInstance : WeaklyEtale (U i ⊓ U j).ι) Z t ht
      have hv := congrArg (fun f ↦ F.obj.map e.hom.op ≫ f.hom.app (op V) ≫
        G.obj.map e.inv.op) hh'
      have side (k : I) (h : U i ⊓ U j ≤ U k) (tk : Z.left ⟶ (U k).toScheme)
          (hk : tk ≫ (U k).ι = Z.hom) (htk : t ≫ T.homOfLE h = tk) :
          F.obj.map e.hom.op ≫
            (F.obj.map ((MorphismProperty.Over.mapComp ⊤
                (inferInstance : WeaklyEtale (T.homOfLE h))
                (inferInstance : WeaklyEtale (U k).ι) (U i ⊓ U j).ι
                (Scheme.homOfLE_ι T h).symm).inv.app V).op ≫
              (ψ k).hom.app (op ((MorphismProperty.Over.map ⊤
                (inferInstance : WeaklyEtale (T.homOfLE h))).obj V)) ≫
              G.obj.map ((MorphismProperty.Over.mapComp ⊤
                (inferInstance : WeaklyEtale (T.homOfLE h))
                (inferInstance : WeaklyEtale (U k).ι) (U i ⊓ U j).ι
                (Scheme.homOfLE_ι T h).symm).hom.app V).op) ≫ G.obj.map e.inv.op =
            F.obj.map (ProEtale.overMapIso (U k).ι inferInstance Z tk hk).hom.op ≫
              (ψ k).hom.app (op (MorphismProperty.Over.mk ⊤ tk
                (MorphismProperty.of_postcomp _ _ _
                  (inferInstance : WeaklyEtale (U k).ι) (hk ▸ Z.prop)))) ≫
              G.obj.map (ProEtale.overMapIso (U k).ι inferInstance Z tk hk).inv.op := by
        let b := MorphismProperty.Over.isoMk (P := @WeaklyEtale) (Q := ⊤)
          (A := (MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale (T.homOfLE h))).obj V)
          (B := MorphismProperty.Over.mk ⊤ tk
            (MorphismProperty.of_postcomp _ _ _
              (inferInstance : WeaklyEtale (U k).ι) (hk ▸ Z.prop)))
          (Iso.refl Z.left) (by simpa [V] using htk.symm)
        let m := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (U k).ι)
        let c := (MorphismProperty.Over.mapComp ⊤
          (inferInstance : WeaklyEtale (T.homOfLE h))
          (inferInstance : WeaklyEtale (U k).ι) (U i ⊓ U j).ι
          (Scheme.homOfLE_ι T h).symm).app V
        let q := ProEtale.overMapIso (U k).ι (inferInstance : WeaklyEtale (U k).ι) Z tk hk
        have hc : c.inv ≫ e.hom = m.map b.hom ≫ q.hom := by
          apply MorphismProperty.Over.Hom.ext
          change (𝟙 Z.left) ≫ (𝟙 Z.left) = (𝟙 Z.left) ≫ (𝟙 Z.left)
          rfl
        have hc' : e.inv ≫ c.hom = q.inv ≫ m.map b.inv := by
          apply MorphismProperty.Over.Hom.ext
          change (𝟙 Z.left) ≫ (𝟙 Z.left) = (𝟙 Z.left) ≫ (𝟙 Z.left)
          rfl
        exact transport_local_map F.obj G.obj m (ψ k).hom b c e q hc hc'
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hv
      simp only [ProEtale.localizationRestriction_map_hom_app,
        ProEtale.localizationRestrictionComp, Iso.symm_hom, Iso.symm_inv,
        Functor.sheafPushforwardContinuousComp'_inv_app_hom_app,
        Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at hv
      exact (side i inf_le_left ti hi hti).symm.trans
        (hv.trans (side j inf_le_right tj hj htj)))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem proetale_sheaf_glue (E : Type (u + 2)) [Category.{u + 1} E]
    [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens)
    (hU : ∀ x : T, ∃ i, x ∈ U i)
    (F G : Sheaf (Scheme.ProEt.topology T) E)
    (a : ∀ i, (ProEtale.upperStar E (U i).ι).obj F ⟶
      (ProEtale.upperStar E (U i).ι).obj G)
    (ha : ∀ i j, onSmallerSheaf
      (fun X ↦ Sheaf (Scheme.ProEt.topology X) E)
      (fun {_ _} f ↦ ProEtale.upperStar E f)
      (fun {_ _ _} f g ↦ ProEtale.upperStarComp E f g) T F G
      (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      onSmallerSheaf (fun X ↦ Sheaf (Scheme.ProEt.topology X) E)
      (fun {_ _} f ↦ ProEtale.upperStar E f)
      (fun {_ _ _} f g ↦ ProEtale.upperStarComp E f g) T F G
      (inf_le_right : U i ⊓ U j ≤ U j) (a j)) :
    ∃ b : F ⟶ G, ∀ i, (ProEtale.upperStar E (U i).ι).map b = a i := by
  let θ := fun i ↦ ProEtale.upperStarIsoLocalizationRestriction
    E (U i).ι inferInstance
  let ψ := fun i ↦ (θ i).inv.app F ≫ a i ≫ (θ i).hom.app G
  obtain ⟨b, hb⟩ := proetale_restriction_glue E T U hU F G ψ (by
      intro i j
      have side {V W : T.Opens} (h : W ≤ V)
          (a : (ProEtale.upperStar E V.ι).obj F ⟶ (ProEtale.upperStar E V.ι).obj G) :=
        (congrArg (fun f ↦
          (ProEtale.upperStarIsoLocalizationRestriction E W.ι inferInstance).inv.app F ≫
            f ≫ (ProEtale.upperStarIsoLocalizationRestriction E W.ι inferInstance).hom.app G)
          (onSmallerSheaf_eq (fun X ↦ Sheaf (Scheme.ProEt.topology X) E)
            (fun {_ _} f ↦ ProEtale.upperStar E f)
            (fun {_ _ _} f g ↦ ProEtale.upperStarComp E f g) T F G h a
            (ProEtale.upperStarComp' E (T.homOfLE h) V.ι W.ι
              (Scheme.homOfLE_ι T h).symm) (proetale_sheafComp E T h))).trans
          (reassociate_five (ProEtale.upperStarComp'_conj E (T.homOfLE h) V.ι
            inferInstance inferInstance W.ι (Scheme.homOfLE_ι T h).symm inferInstance a))
      exact (side (inf_le_left : U i ⊓ U j ≤ U i) (a i)).symm.trans
        ((congrArg (fun f ↦
          (ProEtale.upperStarIsoLocalizationRestriction E (U i ⊓ U j).ι
            inferInstance).inv.app F ≫ f ≫
            (ProEtale.upperStarIsoLocalizationRestriction E (U i ⊓ U j).ι
              inferInstance).hom.app G) (ha i j)).trans
          (side (inf_le_right : U i ⊓ U j ≤ U j) (a j))))
  exact ⟨b, fun i ↦ map_eq_of_conjugate (θ i) b (a i) (hb i)⟩

/-- Unique gluing on both small sites for finite commutative coefficients.
Source: Stacks 06XS, 03EM, 04TQ, 0118
(blueprint: lem-pur-degree-zero-derived-map-gluing).

Proof:
1. The etale localization equivalence (lem-weil-pbc-etale-site-localization-open) and
   the pro-etale localization equivalence (lem-weil-proetale-weakly-etale-localization)
   identify open restriction with localized-site restriction. Constant coefficients
   restrict to the same coefficients (lem-weil-pbc-site-constant-restriction). The given
   Zariski cover is a cover on either site; for pro-etale covers refine affine opens by
   affine opens and take finite subcovers (lem-weil-pbc-affine-opens-basis and
   lem-weil-pbc-affine-scheme-qcqs).
2. Restriction is exact (lem-pur-site-restriction-module-adjunction-exact), so it
   induces the termwise derived functor (situation-conventions).
   Kernels, images and quotients commute with it. Hence so do all cohomology sheaves,
   naturally for maps and inverses of quasi-isomorphisms.
3. A cohomology sheaf vanishing on the cover is zero: its sections over any site
   object inject into the product of its sections on the pulled-back cover. This is
   the sheaf equalizer axiom (def-weil-pbc-sites-and-cohomology), also for an empty cover.
4. For a representing complex K use c : truncLE K 0 → K and p to H⁰(K)[0], with
   p in degree zero the quotient of cycles by boundaries and zero elsewhere. Both
   are quasi-isomorphisms by concentration; the identification is Q(c)⁻¹ Q(p).
5. Kernels and quotient maps are natural; their natural transformations descend
   through localization (theorem-pbc-injective-acyclicity and
   lem-weil-pbc-localization-universal-property). This proves independence of the
   representative, naturality and compatibility with restriction, including iteration.
6. The single functor is fully faithful (lem-weil-pbc-derived-single-fully-faithful).
   Conjugation by the normalized identifications identifies every derived map with
   its H⁰ sheaf map. The single and homology comparisons give the restriction square.
7. Compatible local sheaf maps glue uniquely (lem-pur-sheaf-hom-cover-gluing).
   Transport through step 6 proves the restriction bijection and the equality test.
   For the empty scheme the empty-cover sheaf axiom makes all sheaves zero, and all
   derived objects are zero; both sides of the bijection are singleton sets. -/
theorem degreeZeroDerivedMapGluing (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) {I : Type wI} (U : I → T.Opens) (hU : iSup U = ⊤) :
    Conclusion (fun X : Scheme.{u} ↦ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (fun {_ _} f ↦ Etale.upperStar (ModuleCat.{u + 1} A) f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp (ModuleCat.{u + 1} A) f g) T U ∧
    Conclusion (fun X : Scheme.{u} ↦ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (fun {_ _} f ↦ ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (fun {_ _ _} f g ↦ ProEtale.upperStarComp (ModuleCat.{u + 1} A) f g) T U := by
  have hcover : ∀ x : T, ∃ i, x ∈ U i := by
    intro x
    have hx : x ∈ iSup U := by rw [hU]; trivial
    simpa using hx
  constructor
  · exact assemble_of_reflects
      (fun X ↦ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
      (fun {_ _} f ↦ Etale.upperStar (ModuleCat.{u + 1} A) f)
      (fun {_ _ _} f g ↦ Etale.upperStarComp (ModuleCat.{u + 1} A) f g) T U
      (etale_reflects (ModuleCat.{u + 1} A) T U hcover)
      (etale_sheaf_glue (ModuleCat.{u + 1} A) T U hcover)
  · exact assemble_of_reflects
      (fun X ↦ Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
      (fun {_ _} f ↦ ProEtale.upperStar (ModuleCat.{u + 1} A) f)
      (fun {_ _ _} f g ↦ ProEtale.upperStarComp (ModuleCat.{u + 1} A) f g) T U
      (proetale_reflects (ModuleCat.{u + 1} A) T U hcover)
      (proetale_sheaf_glue (ModuleCat.{u + 1} A) T U hcover)

end AlgebraicGeometry.DegreeZeroMapGluing
