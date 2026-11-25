/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The map of tuple open subschemes to the pullback of the source tuple open.
It uses the actual inclusions of opens, not a choice of a comparison map.
Source: Stacks Project, Tag 01FD, tuple restriction maps.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map) -/
noncomputable def additiveCechTuplePullback
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (p : ℕ) (y : Fin (p + 1) → ι) :
    (additiveCechOpenInclusion Y).obj (∏ᶜ fun l ↦ V (y l)) ⟶
      (MorphismProperty.Over.pullback @Etale ⊤ g).obj
        ((additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l))) :=
  (additiveCechOpenInclusion Y).map (homOfLE
    ((TopCat.Presheaf.piObj_le_iInf V y).trans
      ((hinter p y).trans (g.preimage_mono (TopCat.Presheaf.iInf_le_piObj U y))))) ≫
    Etale.openSectionPullback g (∏ᶜ fun l ↦ U (y l))

/-- Explicit product of tuple section transfers in bidegree (p,q).
Source: Stacks Project, Tag 01FD, map of double complexes.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map) -/
noncomputable def additiveCechPullbackBidegree
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) (p q : ℕ) :
    ((etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).X p).X q ⟶
      ((etaleOpenCechResolutionDoubleComplex Y (additiveCechOpenInclusion Y) V J).X p).X q :=
  Pi.lift (fun y : Fin (p + 1) → ι ↦ Pi.π _ y ≫
    (Etale.resolutionSectionTransfer g I.cocomplex J.cocomplex α _ _
      (additiveCechTuplePullback g U V hinter p y)).f q)

/-- Specification on all total summands; it determines the total map uniquely.
Source: Stacks Project, Tag 01FD; the coproduct universal property.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map) -/
def IsAdditiveCechPullbackTotalMap
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex)
    (t : additiveCechTotal U I ⟶ additiveCechTotal V J) : Prop :=
  ∀ p q n (h : p + q = n),
    (etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I).ιTotal
        (.up ℕ) p q n h ≫ t.f n =
      additiveCechPullbackBidegree g U V hinter I J α p q ≫
        (etaleOpenCechResolutionDoubleComplex Y (additiveCechOpenInclusion Y) V J).ιTotal
          (.up ℕ) p q n h

private lemma bidegree_pi
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) (p q : ℕ) (y : Fin (p + 1) → ι) :
    additiveCechPullbackBidegree g U V hinter I J α p q ≫
      TopCat.Presheaf.cechComplexFunctorπ V
        ((additiveCechOpenInclusion Y).op ⋙ (J.cocomplex.X q).obj) p y =
    TopCat.Presheaf.cechComplexFunctorπ U
        ((additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X q).obj) p y ≫
      (Etale.resolutionSectionTransfer g I.cocomplex J.cocomplex α _ _
        (additiveCechTuplePullback g U V hinter p y)).f q := by
  exact Pi.lift_comp_π _ y

private lemma tuple_square
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (p r : ℕ) (f : Fin (p + 1) → Fin (r + 1)) (y : Fin (r + 1) → ι) :
    (additiveCechOpenInclusion Y).map (Pi.lift (fun l ↦ Pi.π _ (f l))) ≫
        additiveCechTuplePullback g U V hinter p (y ∘ f) =
      additiveCechTuplePullback g U V hinter r y ≫
        (MorphismProperty.Over.pullback @Etale ⊤ g).map
          ((additiveCechOpenInclusion X).map (Pi.lift (fun l ↦ Pi.π _ (f l)))) := by
  unfold additiveCechTuplePullback
  rw [← Category.assoc, ← Functor.map_comp]
  have h : (∏ᶜ fun l ↦ U (y l)) ≤ (∏ᶜ fun l ↦ U ((y ∘ f) l)) :=
    leOfHom (Pi.lift (fun l ↦ Pi.π _ (f l)))
  have hs := Etale.openSectionPullback_naturality g h
  have he :
      (additiveCechOpenInclusion X).map (Pi.lift (fun l ↦ Pi.π _ (f l))) =
        MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h) := by
    rfl
  rw [he]
  rw [Category.assoc, ← hs, ← Category.assoc]
  congr 1
  have heY : (MorphismProperty.Over.homMk (Y.homOfLE (g.preimage_mono h))
      (Y.homOfLE_ι _) : Scheme.Etale.mk (g ⁻¹ᵁ (∏ᶜ fun l ↦ U (y l))).ι ⟶
        Scheme.Etale.mk (g ⁻¹ᵁ (∏ᶜ fun l ↦ U ((y ∘ f) l))).ι) =
      (additiveCechOpenInclusion Y).map (homOfLE (g.preimage_mono h)) := rfl
  rw [heY, ← Functor.map_comp]
  congr 1

private lemma tuple_terminal_square
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (p : ℕ) (y : Fin (p + 1) → ι) :
    (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ V (y l)).ι (Category.comp_id _) :
      (additiveCechOpenInclusion Y).obj (∏ᶜ fun l ↦ V (y l)) ⟶
        Scheme.Etale.mk (𝟙 Y)) ≫ Etale.terminalSectionPullback g =
    additiveCechTuplePullback g U V hinter p y ≫
      (MorphismProperty.Over.pullback @Etale ⊤ g).map
        (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι (Category.comp_id _) :
          (additiveCechOpenInclusion X).obj (∏ᶜ fun l ↦ U (y l)) ⟶
            Scheme.Etale.mk (𝟙 X)) := by
  unfold additiveCechTuplePullback
  rw [Category.assoc, ← Etale.terminalSectionPullback_naturality]
  rw [← Category.assoc]
  congr 1
  apply MorphismProperty.Over.Hom.ext
  exact (Y.homOfLE_ι
    ((TopCat.Presheaf.piObj_le_iInf V y).trans
      ((hinter p y).trans (g.preimage_mono
        (TopCat.Presheaf.iInf_le_piObj U y))))).symm

private noncomputable def pullbackDoubleMap
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) :
    etaleOpenCechResolutionDoubleComplex X (additiveCechOpenInclusion X) U I ⟶
      etaleOpenCechResolutionDoubleComplex Y (additiveCechOpenInclusion Y) V J :=
  HomologicalComplex₂.homMk
    (fun b ↦ additiveCechPullbackBidegree g U V hinter I J α b.1 b.2)
    (by
      intro p p' q hp
      obtain rfl : p + 1 = p' := hp
      let P := (additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X q).obj
      let Q := (additiveCechOpenInclusion Y).op ⋙ (J.cocomplex.X q).obj
      apply TopCat.Presheaf.cechComplexFunctor_hom_ext V Q
      intro y
      change additiveCechPullbackBidegree g U V hinter I J α p q ≫
          ((cechComplexFunctor V).obj Q).d p (p + 1) ≫
            TopCat.Presheaf.cechComplexFunctorπ V Q (p + 1) y =
        ((cechComplexFunctor U).obj P).d p (p + 1) ≫
          additiveCechPullbackBidegree g U V hinter I J α (p + 1) q ≫
            TopCat.Presheaf.cechComplexFunctorπ V Q (p + 1) y
      rw [TopCat.Presheaf.cechComplexFunctor_d_π]
      rw [bidegree_pi, ← Category.assoc,
        TopCat.Presheaf.cechComplexFunctor_d_π U P p y]
      simp only [Preadditive.comp_sum, Preadditive.sum_comp,
        Preadditive.comp_zsmul, Preadditive.zsmul_comp, Category.assoc]
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      rw [← Category.assoc, bidegree_pi, Category.assoc]
      have h := Etale.resolutionSectionTransfer_naturality g I.cocomplex J.cocomplex α
        ((additiveCechOpenInclusion X).map
          (Pi.lift (fun l ↦ Pi.π (fun l ↦ U (y l)) (i.succAbove l))))
        ((additiveCechOpenInclusion Y).map
          (Pi.lift (fun l ↦ Pi.π (fun l ↦ V (y l)) (i.succAbove l))))
        (additiveCechTuplePullback g U V hinter (p + 1) y)
        (additiveCechTuplePullback g U V hinter p (y ∘ i.succAbove))
        (tuple_square g U V hinter p (p + 1) i.succAbove y)
      exact congrArg (fun t ↦ TopCat.Presheaf.cechComplexFunctorπ U P p
        (y ∘ i.succAbove) ≫ t.f q) h.symm)
    (by
      intro p q q' hq
      let P := (additiveCechOpenInclusion X).op ⋙ (I.cocomplex.X q).obj
      let Q := (additiveCechOpenInclusion Y).op ⋙ (J.cocomplex.X q').obj
      apply TopCat.Presheaf.cechComplexFunctor_hom_ext V Q
      intro y
      change additiveCechPullbackBidegree g U V hinter I J α p q ≫
          ((cechComplexFunctor V).map
            (Functor.whiskerLeft (additiveCechOpenInclusion Y).op
              (J.cocomplex.d q q').hom)).f p ≫
          TopCat.Presheaf.cechComplexFunctorπ V Q p y =
        ((cechComplexFunctor U).map
          (Functor.whiskerLeft (additiveCechOpenInclusion X).op
            (I.cocomplex.d q q').hom)).f p ≫
          additiveCechPullbackBidegree g U V hinter I J α p q' ≫
          TopCat.Presheaf.cechComplexFunctorπ V Q p y
      rw [TopCat.Presheaf.cechComplexFunctor_map_f_π]
      rw [← Category.assoc, bidegree_pi, Category.assoc]
      rw [bidegree_pi]
      simp only [← Category.assoc]
      rw [TopCat.Presheaf.cechComplexFunctor_map_f_π]
      simp only [Category.assoc]
      exact congrArg (fun t ↦ TopCat.Presheaf.cechComplexFunctorπ U P p y ≫ t)
        ((Etale.resolutionSectionTransfer g I.cocomplex J.cocomplex α _ _
          (additiveCechTuplePullback g U V hinter p y)).comm q q'))

/-- Tuplewise restriction maps assemble to a total cochain map satisfying the alpha square.
Source: Stacks Project, Tag 01FD, Lemma 20.15.1, double-complex construction.
(blueprint: lem-pbc-etale-additive-cech-pullback-total-map)
Proof: Use additiveCechPullbackBidegree in each bidegree. For every tuple deletion,
the square of additiveCechTuplePullback maps commutes: composing with the two
pullback projections gives respectively the same inclusion followed by g, and
the same target open inclusion. The naturality of resolutionSectionTransfer
then makes these maps commute with each face restriction, hence with their
alternating sum. The vertical equation is the chain-map equation of
resolutionSectionTransfer. These equations define a morphism of double
complexes. Totalize it; total inclusion naturality gives the stated summand
specification, with unchanged bidegree and therefore unchanged signs.
For alpha, the analogous square with the terminal etale objects commutes by
the same two pullback projections. Section-transfer naturality, product
extensionality in Cech degree zero, and total inclusion naturality give the
alpha square. No augmentation equation is used. Empty tuple families give
zero products and degree zero uses the same identities without any negative
index. The specification on all total summands determines t uniquely. -/
theorem exists_additiveCech_pullback_total_map
    {X Y : Scheme.{u}} (g : Y ⟶ X)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (V : ι → Y.Opens)
    (hinter : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      (⨅ l, V (y l)) ≤ g ⁻¹ᵁ (⨅ l, U (y l)))
    (I : InjectiveResolution X.etaleAdditiveSheaf)
    (J : InjectiveResolution Y.etaleAdditiveSheaf)
    (α : I.cocomplex ⟶
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).mapHomologicalComplex
        (.up ℕ)).obj J.cocomplex) (n : ℕ) :
    ∃ t : additiveCechTotal U I ⟶ additiveCechTotal V J,
      IsAdditiveCechPullbackTotalMap g U V hinter I J α t ∧
      (additiveCechAlpha U I n ≫ t.f n =
        (Etale.globalResolutionSectionTransfer g I.cocomplex J.cocomplex α).f n ≫
          additiveCechAlpha V J n) := by
  let φ := pullbackDoubleMap g U V hinter I J α
  refine ⟨HomologicalComplex₂.total.map φ (.up ℕ), ?_, ?_⟩
  · intro p q k h
    exact HomologicalComplex₂.ιTotal_map _ _ φ (.up ℕ) p q k h
  · unfold additiveCechAlpha
    rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
    rw [← Category.assoc, ← Category.assoc]
    apply congrArg (fun f ↦ f ≫
      (etaleOpenCechResolutionDoubleComplex Y (additiveCechOpenInclusion Y) V J).ιTotal
        (.up ℕ) 0 n n (by simp))
    apply Pi.hom_ext
    intro y
    change (Pi.lift _) ≫ additiveCechPullbackBidegree g U V hinter I J α 0 n ≫
      Pi.π _ y = _
    simp only [additiveCechPullbackBidegree, Category.assoc, Pi.lift_comp_π]
    rw [← Category.assoc]
    erw [Pi.lift_comp_π]
    erw [Pi.lift_comp_π]
    exact congrArg (fun t ↦ t.f n)
      (Etale.resolutionSectionTransfer_naturality g I.cocomplex J.cocomplex α
        (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ U (y l)).ι (Category.comp_id _))
        (MorphismProperty.Over.homMk (∏ᶜ fun l ↦ V (y l)).ι (Category.comp_id _))
        (additiveCechTuplePullback g U V hinter 0 y)
        (Etale.terminalSectionPullback g)
        (tuple_terminal_square g U V hinter 0 y))
end AlgebraicGeometry.Scheme.Modules
