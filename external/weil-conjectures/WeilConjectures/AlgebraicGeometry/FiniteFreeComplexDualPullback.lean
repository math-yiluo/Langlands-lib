/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import all WeilConjectures.Algebra.Homology.HomComplexToSingle
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.RingedHomComplexPullbackShift
import WeilConjectures.AlgebraicGeometry.RingComplexEndomorphismSelfDual

/-! # Inverse image of termwise finite free complex duals

Source: Stacks Project, sites-modules.tex, remark-pullback-internal-hom;
algebraization.tex, Tag 0A0E, finite free dual calculation.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe v

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.ConstantCompletion

open CategoryTheory.RingedHomPullback

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

private theorem fanProjectionIso
    {A : Type*} [Category A] [HasZeroMorphisms A]
    {I : Type*} {Q : I → A} {X : A}
    (π : ∀ i, X ⟶ Q i) (hπ : IsLimit (Fan.mk X π))
    (k : I) (hz : ∀ i, i ≠ k → IsZero (Q i)) : IsIso (π k) := by
  classical
  let v : Q k ⟶ X := Fan.IsLimit.lift hπ
    (fun i ↦ if h : k = i then eqToHom (congrArg Q h) else 0)
  have hv (i) : v ≫ π i = if h : k = i then eqToHom (congrArg Q h) else 0 :=
    Fan.IsLimit.fac hπ _ i
  refine ⟨⟨v, ?_, ?_⟩⟩
  · apply Fan.IsLimit.hom_ext hπ
    intro i
    by_cases hi : i = k
    · subst i
      simp [Category.assoc, hv]
    · exact (hz i hi).eq_of_tgt _ _
  · simpa using hv k

private theorem homZeroTarget
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) (X Y : Mod R) (hY : IsZero Y) :
    IsZero (SheafOfModules.homObj (R := R) X Y) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := R), hY.eq_of_tgt (𝟙 Y) 0]
  exact homObjMap_zero_target (𝟙 X)

private theorem homProjectionIso
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) (E I : Cx R)
    (hI : ∀ k : ℤ, k ≠ 0 → IsZero (I.X k)) (n : ℤ) :
    IsIso (homComplexπ E I n (-n) 0 (neg_add_cancel n)) := by
  have h := fanProjectionIso
    (fun p : ℤ ↦ homComplexπ E I n p (p + n) rfl)
    (homComplexIsLimit E I n) (-n) (fun p hp ↦
      homZeroTarget R _ _ (hI (p + n) (by omega)))
  exact isIso_dependent (fun q hq ↦ homComplexπ E I n (-n) q hq)
    (neg_add_cancel n) h

private theorem abstractMap_naturality_left
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (a : HomData A) (b : HomData B) (P : A ⥤ B) [P.Additive]
    (tr : TransportData a b P) (E E' I : CochainComplex A ℤ) (f : E' ⟶ E) :
    (mapped P).map ((a.H.flip.obj I).map f.op) ≫ abstractMap a b P tr E' I =
      abstractMap a b P tr E I ≫
        (b.H.flip.obj ((mapped P).obj I)).map ((mapped P).map f).op := by
  simpa only [Functor.flip_obj_map, Functor.map_id, Category.comp_id] using
    abstractMap_naturality a b P tr E E' I I f (𝟙 I)

private theorem abstractComparisonIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (a : HomData A) (b : HomData B) (P : A ⥤ B) [P.Additive]
    (tr : TransportData a b P) (E I : CochainComplex A ℤ)
    (hπ : ∀ n : ℤ, IsIso (a.π E I n (-n) 0 (neg_add_cancel n)))
    (hπ' : ∀ n : ℤ, IsIso (b.π ((mapped P).obj E) ((mapped P).obj I)
      n (-n) 0 (neg_add_cancel n)))
    (htr : ∀ n : ℤ, IsIso (tr.map (𝟙 (a.obj (E.X (-n)) (I.X 0))))) :
    IsIso (abstractMap a b P tr E I) := by
  suffices ∀ n : ℤ, IsIso ((abstractMap a b P tr E I).f n) from
    HomologicalComplex.Hom.isIso_of_components _
  intro n
  have he : (abstractMap a b P tr E I).f n ≫
      b.π ((mapped P).obj E) ((mapped P).obj I) n (-n) 0 (neg_add_cancel n) =
        P.map (a.π E I n (-n) 0 (neg_add_cancel n)) ≫
          tr.map (𝟙 (a.obj (E.X (-n)) (I.X 0))) := by
    rw [abstractMap_f, abstractComponent_π]
    simpa only [Category.comp_id] using tr.pre (a.π E I n (-n) 0 (neg_add_cancel n)) (𝟙 _)
  have : IsIso ((abstractMap a b P tr E I).f n ≫
      b.π ((mapped P).obj E) ((mapped P).obj I) n (-n) 0 (neg_add_cancel n)) := by
    rw [he]
    have := htr n
    have := hπ n
    infer_instance
  have := hπ' n
  exact IsIso.of_isIso_comp_right _
    (b.π ((mapped P).obj E) ((mapped P).obj I) n (-n) 0 (neg_add_cancel n))

private theorem transportComparisonIso
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{v}) (S : Sheaf K CommRingCat.{v})
    (P : Mod R ⥤ Mod S) [P.Additive]
    (tr : TransportData (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P)
    (E I : Cx R) (hI : ∀ k : ℤ, k ≠ 0 → IsZero (I.X k))
    (htr : ∀ n : ℤ, IsIso (tr.map (𝟙
      (SheafOfModules.homObj (R := R) (E.X (-n)) (I.X 0))))) :
    IsIso (abstractMap (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E I) := by
  exact abstractComparisonIso (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E I
    (homProjectionIso R E I hI)
    (homProjectionIso S ((P.mapHomologicalComplex (.up ℤ)).obj E)
      ((P.mapHomologicalComplex (.up ℤ)).obj I) (fun k hk ↦ P.map_isZero (hI k hk))) htr

private theorem tensorAdjunctionIso
    {A : Type*} [Category A] [MonoidalCategory A]
    (X T Y : A) (H : A ⥤ A) (a : tensorLeft X ⊣ H)
    (s : X ≅ 𝟙_ A) (g : T ⟶ H.obj Y) :
    IsIso ((a.homEquiv T Y).symm g) ↔ IsIso g := by
  let e : tensorLeft X ≅ 𝟭 A :=
    (curriedTensor A).mapIso s ≪≫ leftUnitorNatIso A
  have : (tensorLeft X).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  have he : IsIso (a.counit.app Y) := inferInstance
  rw [a.homEquiv_counit T Y g]
  constructor
  · intro hi
    have : IsIso ((tensorLeft X).map g) :=
      IsIso.of_isIso_comp_right _ (a.counit.app Y)
    exact isIso_of_reflects_iso g (tensorLeft X)
  · intro hi
    infer_instance

private theorem unc_isIso_iff
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) (X Y T : Mod R)
    (s : X ≅ SheafOfModules.unit (siteModuleRings R))
    (g : T ⟶ SheafOfModules.homObj (R := R) X Y) :
    IsIso (unc.{v, v, v} R g) ↔ IsIso g := by
  let a := WeilConjectures.ZeroClassAux.tensorHomAdjunction.{v, v, v} R X
  have ha : a.homEquiv T Y =
      WeilConjectures.ZeroClassAux.tensorHomEquiv.{v, v, v} R X T Y := by
    dsimp only [a]
    erw [WeilConjectures.ZeroClassAux.tensorHomAdjunction,
      Adjunction.mkOfHomEquiv_homEquiv]
  have h := tensorAdjunctionIso X T Y _ a s g
  rw [ha] at h
  unfold unc
  constructor
  · intro hi
    apply h.mp
    exact IsIso.of_isIso_comp_left (β_ T X).hom _
  · intro hi
    have := h.mpr hi
    infer_instance

private theorem opBiproductNatTransIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {F G : Aᵒᵖ ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    {T : Type} [Finite T] (f : T → A) [HasBiproduct f]
    (hi : ∀ j, IsIso (α.app (op (f j)))) : IsIso (α.app (op (⨁ f))) := by
  classical
  let := Fintype.ofFinite T
  have total : ∑ j, (biproduct.ι f j).op ≫ (biproduct.π f j).op = 𝟙 (op (⨁ f)) := by
    simpa only [← op_comp, ← op_sum, op_id] using
      congrArg Quiver.Hom.op (biproduct.total (f := f))
  refine ⟨⟨∑ j, G.map (biproduct.ι f j).op ≫ inv (α.app (op (f j))) ≫
      F.map (biproduct.π f j).op, ?_, ?_⟩⟩
  · simp only [Preadditive.comp_sum, ← NatTrans.naturality_assoc,
      IsIso.hom_inv_id_assoc, ← F.map_comp, ← F.map_sum, total, F.map_id]
  · simp only [Preadditive.sum_comp, Category.assoc, NatTrans.naturality,
      IsIso.inv_hom_id_assoc, ← G.map_comp, ← G.map_sum, total, G.map_id]

private theorem ordinaryTransportNaturality
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    (a : HomData A) (b : HomData B) (P : A ⥤ B) [P.Additive]
    (tr : TransportData a b P) {X X' : A} (u : X' ⟶ X) (Y : A) :
    P.map (a.map u (𝟙 Y)) ≫ tr.map (𝟙 (a.obj X' Y)) =
      tr.map (𝟙 (a.obj X Y)) ≫ b.map (P.map u) (𝟙 (P.obj Y)) := by
  have h := tr.naturality u (𝟙 Y) (𝟙 (a.obj X Y))
  have hp := tr.pre (a.map u (𝟙 Y)) (𝟙 (a.obj X' Y))
  simp only [Category.id_comp, P.map_id] at h
  simp only [Category.comp_id] at hp
  exact hp.symm.trans h

private noncomputable def transportNatTrans
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{v}) (S : Sheaf K CommRingCat.{v})
    (P : Mod R ⥤ Mod S) [P.Additive]
    (tr : TransportData (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P)
    (Y : Mod R) :
    (SheafOfModules.homFunctor R).flip.obj Y ⋙ P ⟶
      P.op ⋙ (SheafOfModules.homFunctor S).flip.obj (P.obj Y) where
  app X := tr.map (𝟙 (SheafOfModules.homObj (R := R) X.unop Y))
  naturality {X X'} f := by
    exact ordinaryTransportNaturality (siteHomData.{v, v, v} R)
      (siteHomData.{v, v, v} S) P tr f.unop Y

private theorem transportNatTrans_app
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{v}) (S : Sheaf K CommRingCat.{v})
    (P : Mod R ⥤ Mod S) [P.Additive]
    (tr : TransportData (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P)
    (X Y : Mod R) :
    (transportNatTrans R S P tr Y).app (op X) =
      tr.map (𝟙 (SheafOfModules.homObj (R := R) X Y)) := rfl

attribute [local irreducible] transportNatTrans

attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor
  closedTransport abstractMap

private theorem closedTransport_unc
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    [MonoidalCategory A] [MonoidalCategory B]
    {a : HomData A} {b : HomData B}
    (ca : ClosedData a.obj (@a.map)) (cb : ClosedData b.obj (@b.map))
    (P : A ⥤ B) [P.Additive]
    (μ : ∀ X Y : A, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (hμ : ∀ {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y'),
      (P.map f ⊗ₘ P.map g) ≫ (μ X' Y').inv = (μ X Y).inv ≫ P.map (f ⊗ₘ g))
    {X Y T : A} (g : T ⟶ a.obj X Y) :
    cb.unc ((closedTransport ca cb P μ hμ).map g) = (μ T X).inv ≫ P.map (ca.unc g) := by
  rw [closedTransport_map, cb.unc_cur]

private theorem siteClosedData_unc
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) {X Y T : Mod R}
    (g : T ⟶ SheafOfModules.homObj (R := R) X Y) :
    (siteClosedData.{v, v, v} R).unc g = unc.{v, v, v} R g := rfl

attribute [local irreducible] siteClosedData

private theorem finiteFreeNatTransIso
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) {B : Type*} [Category B] [Preadditive B]
    {F G : (Mod R)ᵒᵖ ⥤ B} [F.Additive] [G.Additive] (α : F ⟶ G)
    (hu : IsIso (α.app (op (SheafOfModules.unit (siteModuleRings R)))))
    (X : Mod R)
    (hX : ∃ (T : Type v) (_ : Fintype T),
      Nonempty (X ≅ SheafOfModules.free (R := siteModuleRings R) T)) :
    IsIso (α.app (op X)) := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hX
  let U := SheafOfModules.unit (siteModuleRings R)
  let f : Fin (Fintype.card T) → Mod R := fun _ ↦ U
  have hb : IsIso (α.app (op (⨁ f))) :=
    opBiproductNatTransIso α f (fun _ ↦ hu)
  let ef : X ≅ ⨁ f := e ≪≫
    Sigma.reindex (Fintype.equivFin T) (fun _ : Fin (Fintype.card T) ↦ U) ≪≫
      (biproduct.isoCoproduct f).symm
  exact NatTrans.isIso_app_of_iso α ef.symm.op

private theorem transportFiniteFreeIso
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{v}) (S : Sheaf K CommRingCat.{v})
    (P : Mod R ⥤ Mod S) [P.Additive]
    (μ : ∀ X Y : Mod R, P.obj (X ⊗ Y) ≅ P.obj X ⊗ P.obj Y)
    (hμ : ∀ {X X' Y Y' : Mod R} (f : X ⟶ X') (g : Y ⟶ Y'),
      (P.map f ⊗ₘ P.map g) ≫ (μ X' Y').inv = (μ X Y).inv ≫ P.map (f ⊗ₘ g))
    (j : P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S))
    (X Y : Mod R)
    (hX : ∃ (T : Type v) (_ : Fintype T),
      Nonempty (X ≅ SheafOfModules.free (R := siteModuleRings R) T)) :
    let tr := closedTransport (a := siteHomData.{v, v, v} R)
      (b := siteHomData.{v, v, v} S) (siteClosedData.{v, v, v} R)
      (siteClosedData.{v, v, v} S) P μ hμ
    IsIso (tr.map (𝟙 (SheafOfModules.homObj (R := R) X Y))) := by
  classical
  let tr := closedTransport (a := siteHomData.{v, v, v} R)
      (b := siteHomData.{v, v, v} S) (siteClosedData.{v, v, v} R)
    (siteClosedData.{v, v, v} S) P μ hμ
  let α := transportNatTrans R S P tr Y
  let U := SheafOfModules.unit (siteModuleRings R)
  have hR : IsIso (unc.{v, v, v} R (𝟙 (SheafOfModules.homObj (R := R) U Y))) :=
    (unc_isIso_iff R U Y _ (Iso.refl _) _).mpr inferInstance
  have hu : IsIso (α.app (op U)) := by
    dsimp only [α]
    rw [transportNatTrans_app]
    apply (unc_isIso_iff S (P.obj U) (P.obj Y) _ j _).mp
    rw [← siteClosedData_unc]
    dsimp only [tr]
    erw [closedTransport_unc (a := siteHomData.{v, v, v} R)
      (b := siteHomData.{v, v, v} S) (siteClosedData.{v, v, v} R)
      (siteClosedData.{v, v, v} S) P μ hμ]
    rw [siteClosedData_unc]
    infer_instance
  simpa only [α, transportNatTrans_app] using finiteFreeNatTransIso R α hu X hX

private theorem normalizeDualComparison
    {A B : Type*} [Category A] [Category B]
    (P : A ⥤ B) (H : Aᵒᵖ ⥤ A) (G : Bᵒᵖ ⥤ B)
    (U : A) (V : B) (e : H.obj (op U) ≅ U) (e' : G.obj (op V) ≅ V)
    (j : P.obj U ≅ V) (d : P.obj (H.obj (op U)) ≅ G.obj (op (P.obj U)))
    (hd : ∀ a : V ⟶ V, G.map a.op ≫ e'.hom = e'.hom ≫ a) :
    ∃ u : P.obj U ≅ V,
      P.map e.inv ≫ d.hom = j.hom ≫ e'.inv ≫ G.map u.hom.op := by
  let a : V ≅ V := j.symm ≪≫ P.mapIso e.symm ≪≫ d ≪≫ G.mapIso j.symm.op ≪≫ e'
  have ha : a.hom ≫ e'.inv = e'.inv ≫ G.map a.hom.op := by
    apply (cancel_mono e'.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hd, Iso.inv_hom_id_assoc]
  refine ⟨j ≪≫ a, ?_⟩
  change _ = j.hom ≫ e'.inv ≫ G.map (j.hom ≫ a.hom).op
  rw [op_comp, G.map_comp]
  rw [← Category.assoc e'.inv (G.map a.hom.op), ← ha]
  simp [a, Category.assoc, ← G.map_comp]

/-- Finite free duality commutes with ordinary module inverse image. The target of
Hom is the ring complex in degree zero; the source need not be bounded. The
comparison is contravariantly natural on the termwise finite free complexes.

Source: Stacks Project, sites-modules.tex, remark-pullback-internal-hom and
lemma-tensor-product-pullback; algebraization.tex, Tag 0A0E, dual calculation.
(auxiliary; not a blueprint node).

Proof in words: transpose pulled-back evaluation using the inverse ordinary tensor
comparison, and use the existing signed Hom-complex construction to obtain a
natural chain map. Tensoring by the rank-one ring module is equivalent to the
identity, so its tensor-Hom adjunction shows that the ordinary comparison is
invertible for that source. Additive naturality extends this to every finite
biproduct of copies of the ring, including the empty biproduct; reindexing a
finite basis gives invertibility for every finite free source.

In degree n, Hom(E,R[0]) has just its possibly nonzero factor Hom(E.X(-n),R).
The projection to it is an isomorphism by the product universal property: all
other factors have zero target. Pullback preserves zero objects and isomorphisms.
The comparison on the surviving factor is the ordinary finite free comparison,
so the chain map is an isomorphism. Postcompose its target with the specified j.
Naturality in every source chain map follows from the Hom bifunctor and the
evaluation characterization, without a choice of basis in the construction.

Every endomorphism of the ring module is multiplication by its value at one.
Commutativity implies that it is self-dual under evaluation at one, and the same
holds for the ring complex in degree zero. Let a be the automorphism of S[0]
obtained by composing j.inv, pullback of inverse evaluation, the constructed dual
comparison at R[0], contravariant Hom of j.inv, and evaluation over S. Set
u = j followed by a. Self-duality of a gives the displayed normalization by
cancelling the evaluation and j isomorphisms. Arbitrary j, zero rings, empty sites
and unbounded sources cause no extra products or convergence condition; no
flatness of the coefficient map is used. -/
theorem finiteFreeComplexDualPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    {R : Sheaf J CommRingCat.{v}} {S : Sheaf K CommRingCat.{v}}
    (c : F.rings.obj R ⟶ S)
    (j : ((pull F c).mapHomologicalComplex (.up ℤ)).obj
      (ringedSiteRingComplex R) ≅ ringedSiteRingComplex S) :
    let P := (pull F c).mapHomologicalComplex (.up ℤ)
    let Free := fun E : Cx R ↦ ∀ n : ℤ, ∃ (T : Type v) (_ : Fintype T),
      Nonempty (E.X n ≅ SheafOfModules.free (R := siteModuleRings R) T)
    let HR := (homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)
    let HS := (homComplexFunctor (R := S)).flip.obj (ringedSiteRingComplex S)
    ∃ (u : P.obj (ringedSiteRingComplex R) ≅ ringedSiteRingComplex S)
      (d : ∀ (E : Cx R) (_ : Free E), P.obj (HR.obj (op E)) ≅ HS.obj (op (P.obj E))),
      (∀ (E E' : Cx R) (hE : Free E) (hE' : Free E') (f : E' ⟶ E),
        P.map (HR.map f.op) ≫ (d E' hE').hom =
          (d E hE).hom ≫ HS.map (P.map f).op) ∧
      (∀ hR : Free (ringedSiteRingComplex R),
        P.map (ringedHomUnitEvaluationIso R (ringedSiteRingComplex R)).inv ≫
            (d (ringedSiteRingComplex R) hR).hom =
          j.hom ≫ (ringedHomUnitEvaluationIso S (ringedSiteRingComplex S)).inv ≫
            HS.map u.hom.op) := by
  classical
  dsimp only
  let P : Mod R ⥤ Mod S := pull F c
  let Pc := P.mapHomologicalComplex (.up ℤ)
  let U := ringedSiteRingComplex R
  let W := ringedSiteRingComplex S
  let HR := (homComplexFunctor (R := R)).flip.obj U
  let HS := (homComplexFunctor (R := S)).flip.obj W
  let Free := fun E : Cx R ↦ ∀ n : ℤ, ∃ (T : Type v) (_ : Fintype T),
    Nonempty (E.X n ≅ SheafOfModules.free (R := siteModuleRings R) T)
  let hobj : ∀ M : Mod R, P.obj M =
      SheafOfModules.changeOfRings c ((F.algebra R).modules.obj M) := fun _ ↦ rfl
  have hmap : ∀ {M N : Mod R} (f : M ⟶ N), P.map f =
      eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom c
        ((F.algebra R).modules.obj M) ((F.algebra R).modules.map f) ≫
          eqToHom (hobj N).symm := by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨⟨k⟩, _⟩ := SheafOfModules.canonicalRingedTensorComparison_existsUnique
    R S (F.rings.obj R) L (F.algebra R) c P hobj V adj hmap
  let j₀ : P.obj (SheafOfModules.unit (siteModuleRings R)) ≅
      SheafOfModules.unit (siteModuleRings S) :=
    (P.mapIso (HomologicalComplex.singleObjXSelf (.up ℤ) 0 _)).symm ≪≫
      (HomologicalComplex.eval (Mod S) (.up ℤ) 0).mapIso j ≪≫
        HomologicalComplex.singleObjXSelf (.up ℤ) 0 _
  have hμ : ∀ {X X' Y Y' : Mod R} (f : X ⟶ X') (g : Y ⟶ Y'),
      (P.map f ⊗ₘ P.map g) ≫ (k.mu X' Y').inv =
        (k.mu X Y).inv ≫ P.map (f ⊗ₘ g) := by
    intro X X' Y Y' f g
    apply (cancel_mono (k.mu X' Y').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [k.naturality]
    simp
  let tr : TransportData (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P :=
    closedTransport (a := siteHomData.{v, v, v} R) (b := siteHomData.{v, v, v} S)
      (siteClosedData.{v, v, v} R) (siteClosedData.{v, v, v} S) P k.mu hμ
  let g (E : Cx R) : Pc.obj (HR.obj (op E)) ⟶ HS.obj (op (Pc.obj E)) :=
    abstractMap (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E U ≫
      ((homComplexFunctor (R := S)).obj (op (Pc.obj E))).map j.hom
  have hg (E : Cx R) (hE : Free E) : IsIso (g E) := by
    have ht : ∀ n : ℤ, IsIso (tr.map (𝟙
        (SheafOfModules.homObj (R := R) (E.X (-n)) (U.X 0)))) := fun n ↦
      transportFiniteFreeIso R S P k.mu hμ j₀ _ _ (hE (-n))
    have hc := transportComparisonIso R S P tr E U
      (fun n hn ↦ HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn) ht
    dsimp only [g]
    infer_instance
  let d (E : Cx R) (hE : Free E) : Pc.obj (HR.obj (op E)) ≅
      HS.obj (op (Pc.obj E)) := @asIso _ _ _ _ (g E) (hg E hE)
  have hn (E E' : Cx R) (hE : Free E) (hE' : Free E') (f : E' ⟶ E) :
      Pc.map (HR.map f.op) ≫ (d E' hE').hom =
        (d E hE).hom ≫ HS.map (Pc.map f).op := by
    have ha' := abstractMap_naturality_left
      (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E E' U f
    change Pc.map (HR.map f.op) ≫
        abstractMap (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E' U =
      abstractMap (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E U ≫
        ((homComplexFunctor (R := S)).flip.obj (Pc.obj U)).map (Pc.map f).op at ha'
    change Pc.map (HR.map f.op) ≫ g E' = g E ≫ HS.map (Pc.map f).op
    dsimp only [g]
    rw [← Category.assoc, ha', Category.assoc]
    simpa only [HS, Functor.flip_obj_map, Category.assoc] using congrArg
      (fun z ↦ abstractMap (siteHomData.{v, v, v} R) (siteHomData.{v, v, v} S) P tr E U ≫ z)
      (((homComplexFunctor (R := S)).map (Pc.map f).op).naturality j.hom).symm
  have hU : Free U := by
    intro n
    by_cases hn : n = 0
    · subst n
      refine ⟨PUnit.{v + 1}, inferInstance, ⟨?_⟩⟩
      exact HomologicalComplex.singleObjXSelf (.up ℤ) 0 _ ≪≫
        (coproductUniqueIso (fun _ : PUnit.{v + 1} ↦ SheafOfModules.unit _)).symm
    · refine ⟨PEmpty.{v + 1}, inferInstance, ⟨?_⟩⟩
      have hz : IsZero (SheafOfModules.free (R := siteModuleRings R) PEmpty.{v + 1}) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply Sigma.hom_ext
        intro i
        exact PEmpty.elim i
      exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n hn).iso hz
  obtain ⟨u, hu⟩ := normalizeDualComparison Pc HR HS U W
    (ringedHomUnitEvaluationIso R U) (ringedHomUnitEvaluationIso S W)
    j (d U hU) (ringComplexEndomorphism_selfDual S)
  refine ⟨u, d, hn, ?_⟩
  intro hR
  exact hu

end CategoryTheory.ConstantCompletion
