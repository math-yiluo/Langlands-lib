/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientEncodingData
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteRestrictionEncoding
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback

/-! # Finite presentations under finite discrete encoding -/

@[expose] public section

universe u v w v₁ v₂ u₁ u₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

local instance instEssentiallySmallProfinite_finiteDiscreteEncodedPresentation
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace CategoryTheory.ConstantInternalModuleSheafEncoding

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J Ab.{w}] [(J.W (A := Ab.{w})).IsMonoidal]
  (R : Type w) [Ring R]
  (G : Mod Ab.{w} (AddCommGrpCat.of R) ⥤ ModuleCat.{w} R) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w} = Mod.forget (AddCommGrpCat.of R))
  [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [HasSheafify J (ModuleCat.{w} R)]

local instance : HasWeakSheafify J Ab.{w} := HasSheafify.isRightAdjoint
local instance : HasWeakSheafify J (ModuleCat.{w} R) := HasSheafify.isRightAdjoint

noncomputable local instance : MonoidalCategory (Sheaf J Ab.{w}) :=
  Sheaf.monoidalCategory J Ab.{w}
noncomputable local instance : BraidedCategory (Sheaf J Ab.{w}) :=
  Sheaf.braidedCategory J Ab.{w}

@[irreducible] private noncomputable def encSheafifyIso :
    (presheafToSheaf J Ab.{w}).mapMod (A (C := Cᵒᵖ) R) ⋙ sheafEncoding J R G hG ≅
      modulePresheafEncoding (C := C) R G ⋙ presheafToSheaf J (ModuleCat.{w} R) := by
  let H := sheafEncoding J R G hG
  let P := modulePresheafEncoding (C := C) R G
  let Q := moduleLocalizationRight J (A (C := Cᵒᵖ) R)
  let U := sheafToPresheaf J (ModuleCat.{w} R)
  let e : Q ⋙ P ≅ H ⋙ U := Iso.refl _
  let i : (H.inv ⋙ Q) ⋙ P ≅ U :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft H.inv e ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight H.asEquivalence.counitIso U ≪≫ Functor.leftUnitor U
  let j : H.inv ⋙ Q ≅ U ⋙ P.inv := Iso.isoCompInverse (H := P.asEquivalence) i
  exact ((moduleLocalizationAdjunction J (A (C := Cᵒᵖ) R)).comp
    H.asEquivalence.toAdjunction).ofNatIsoRight j |>.leftAdjointUniq
      (P.asEquivalence.toAdjunction.comp (sheafificationAdjunction J (ModuleCat.{w} R)))

@[irreducible] private noncomputable def encPresheafRegularIso :
    (modulePresheafEncoding (C := C) R G).obj (Mod.regular (A (C := Cᵒᵖ) R)) ≅
      (Functor.const Cᵒᵖ).obj (G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  refine NatIso.ofComponents (fun U ↦ ?_) (fun f ↦ ?_)
  · exact G.mapIso (Mod.isoMk (Iso.refl _) (by simp))
  · change G.map _ ≫ G.map _ = G.map _ ≫ 𝟙 _
    rw [Category.comp_id, ← G.map_comp]
    congr 1

@[irreducible] private noncomputable def encRegularIso :
    (sheafEncoding J R G hG).obj
      (Mod.regular ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R))) ≅
      (constantSheaf J (ModuleCat.{w} R)).obj (G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  let e : ((presheafToSheaf J Ab.{w}).mapMod (A (C := Cᵒᵖ) R)).obj
      (Mod.regular (A (C := Cᵒᵖ) R)) ≅
      Mod.regular ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) :=
    Mod.isoMk (Iso.refl _) (by simp)
  exact (sheafEncoding J R G hG).mapIso e.symm ≪≫
    (encSheafifyIso J R G hG).app _ ≪≫
    (presheafToSheaf J (ModuleCat.{w} R)).mapIso (encPresheafRegularIso R G)

variable [HasFiniteLimits (Mod (Sheaf J Ab.{w})
  ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)))]

@[irreducible] private noncomputable def encFiniteFreeIso (n : ℕ) :
    (sheafEncoding J R G hG).obj
      (Mod.finiteFree ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)) n) ≅
      (constantSheaf J (ModuleCat.{w} R)).obj
        (⨁ fun _ : Fin n ↦ G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  let H := sheafEncoding J R G hG
  let S := constantSheaf J (ModuleCat.{w} R)
  have : H.IsEquivalence := sheafEncodingIsEquivalence J R G hG
  have : H.Full := sheafEncodingFull J R G hG
  have : H.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full H
  have : HasBinaryProducts (Mod (Sheaf J Ab.{w})
      ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R))) :=
    HasFiniteLimits.out _
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  have : PreservesFiniteColimits S := inferInstance
  have : S.Additive := Functor.additive_of_preserves_binary_products S
  exact H.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ encRegularIso J R G hG) ≪≫
    (S.mapBiproduct _).symm

omit [G.IsEquivalence] [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})] in
include hG in
private lemma finiteGRegular [Finite R] : Finite (G.obj (Mod.regular (AddCommGrpCat.of R))) := by
  change Finite (((G ⋙ forget₂ (ModuleCat.{w} R) Ab.{w}).obj
    (Mod.regular (AddCommGrpCat.of R))))
  rw [hG]
  exact inferInstanceAs (Finite R)

omit [G.IsEquivalence] [HasLimitsOfSize.{v, u} (ModuleCat.{w} R)]
  [PreservesLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})]
  [ReflectsLimitsOfSize.{v, u} (forget₂ (ModuleCat.{w} R) Ab.{w})] in
include hG in
private lemma finiteSumRegular [Finite R] (n : ℕ) :
    Finite ((⨁ fun _ : Fin n ↦ G.obj (Mod.regular (AddCommGrpCat.of R))) :
      ModuleCat.{w} R) := by
  have := finiteGRegular R G hG
  exact Finite.of_equiv _
    (((forget (ModuleCat.{w} R)).mapIso (ModuleCat.biproductIsoPi _)).toEquiv.symm)

variable [PreservesFiniteColimits
  (tensorLeft ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)))]

private lemma encodedFinitePresentation [Finite R]
    (M : Mod (Sheaf J Ab.{w})
      ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R)))
    (hM : Mod.IsFinitelyPresented _ M) :
    ∃ P Q : ModuleCat.{w} R, Finite P ∧ Finite Q ∧
      ∃ f : (constantSheaf J (ModuleCat.{w} R)).obj P ⟶
        (constantSheaf J (ModuleCat.{w} R)).obj Q,
        Nonempty ((sheafEncoding J R G hG).obj M ≅ cokernel f) := by
  have : HasFiniteColimits (Sheaf J (ModuleCat.{w} R)) := inferInstance
  have : HasCokernels (Sheaf J (ModuleCat.{w} R)) := inferInstance
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  let H := sheafEncoding J R G hG
  let P : ModuleCat.{w} R := ⨁ fun _ : Fin m ↦ G.obj (Mod.regular (AddCommGrpCat.of R))
  let Q : ModuleCat.{w} R := ⨁ fun _ : Fin n ↦ G.obj (Mod.regular (AddCommGrpCat.of R))
  let em := encFiniteFreeIso J R G hG m
  let en := encFiniteFreeIso J R G hG n
  have : H.IsEquivalence := sheafEncodingIsEquivalence J R G hG
  have : H.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full H
  have : HasBinaryProducts (Mod (Sheaf J Ab.{w})
      ((presheafToSheaf J Ab.{w}).obj (A (C := Cᵒᵖ) R))) := HasFiniteLimits.out _
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  let f : (constantSheaf J (ModuleCat.{w} R)).obj P ⟶
      (constantSheaf J (ModuleCat.{w} R)).obj Q := em.inv ≫ H.map g ≫ en.hom
  let : HasCokernel f := HasCokernels.has_colimit f
  let : HasCokernel (H.map g) := HasCokernels.has_colimit (H.map g)
  refine ⟨P, Q, finiteSumRegular R G hG m, finiteSumRegular R G hG n, f, ⟨?_⟩⟩
  exact H.mapIso eg ≪≫ PreservesCokernel.iso H g ≪≫
    cokernel.mapIso (H.map g) f em en (by dsimp only [f]; simp)

end CategoryTheory.ConstantInternalModuleSheafEncoding

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

local instance : HasWeakSheafify (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  HasSheafify.isRightAdjoint
local instance : ((coherentTopology Profinite.{u}).W (A := Ab.{u + 1})).IsMonoidal :=
  GrothendieckTopology.W.monoidal (J := coherentTopology Profinite.{u}) (A := Ab.{u + 1})
noncomputable local instance :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (coherentTopology Profinite.{u}) Ab.{u + 1}

attribute [local instance] finiteDiscreteRestrictionEncodingInst1
  finiteDiscreteRestrictionEncodingInst2
noncomputable local instance (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  Sheaf.monoidalCategory (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}

open MonoidalCategory

section Presentation

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    {R : C} {S : D} [MonObj R] [MonObj S]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)]

private lemma finitePresentation_map_of_presentation
    (F : Mod C R ⥤ Mod D S) [F.Additive]
    [PreservesFiniteColimits F]
    (e : ∀ n : ℕ, F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n)
    {n m : ℕ} (g : Mod.finiteFree R m ⟶ Mod.finiteFree R n)
    {M : Mod C R} (eg : M ≅ cokernel g) :
    Mod.IsFinitelyPresented S (F.obj M) := by
  refine ⟨n, m, (e m).inv ≫ F.map g ≫ (e n).hom, ⟨?_⟩⟩
  exact F.mapIso eg ≪≫ PreservesCokernel.iso F g ≪≫
    cokernel.mapIso _ _ (e m) (e n) (by simp)

end Presentation

section SheafPresentation

variable {X : AlgebraicGeometry.Scheme.{u}}
    {R S : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S]

@[irreducible] private noncomputable def finiteFree_comap
    (φ : S ⟶ R) [IsMonHom φ] [IsIso φ] (n : ℕ) :
    (Mod.comap φ).obj (Mod.finiteFree R n) ≅ Mod.finiteFree S n :=
  (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

end SheafPresentation

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
  (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1}
      (coherentTopology Profinite.{u}) ((Functor.const Profinite.{u}ᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} B))) ≅ Profinite.continuousMapRingObj.{u} B)
  [IsMonHom eR.hom]
  (G : Mod Ab.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} B)) ⥤
    ModuleCat.{u + 1} (ULift.{u + 1} B)) [G.IsEquivalence]
  (hG : G ⋙ forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} B)) Ab.{u + 1} =
    Mod.forget (AddCommGrpCat.of (ULift.{u + 1} B)))

private lemma encoded_fp [Finite B] (T : Scheme.{u})
    (M : FiniteDiscreteInternalModules B T)
    (hM : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T) M) :
    ∃ P Q : ModuleCat.{u + 1} (ULift.{u + 1} B), Finite P ∧ Finite Q ∧
      ∃ f : (constantSheaf (ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P ⟶
        (constantSheaf (ProEt.topology T)
          (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj Q,
        Nonempty ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M ≅
          cokernel f) := by
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat.{u + 1} (ULift.{u + 1} B)) :=
    ModuleCat.hasLimitsOfSize.{u, u + 1, u + 1, u + 1}
  let φ := (finiteDiscreteSchemeRingIso B T eR).hom
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  have hN := finitePresentation_map_of_presentation
    (Mod.comap φ) (finiteFree_comap φ) g eg
  obtain ⟨P, Q, hP, hQ, f, ⟨ef⟩⟩ :=
    CategoryTheory.ConstantInternalModuleSheafEncoding.encodedFinitePresentation
      (ProEt.topology T) (ULift.{u + 1} B) G hG ((Mod.comap φ).obj M) hN
  refine ⟨P, Q, hP, hQ, f, ⟨?_⟩⟩
  unfold finiteDiscreteCoefficientEquivalence
  exact ef

/-- Inverse image with coefficients identified by restriction of scalars.
Keep the composite irreducible so iterated restrictions use the proved API below. -/
@[irreducible] private noncomputable def normalizedPullback (T U : Scheme.{u})
    (j : U ⟶ T) : FiniteDiscreteInternalModules B T ⥤ FiniteDiscreteInternalModules B U :=
  ((ProEtale.upperStar Ab.{u + 1} j).mapMod
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)) ⋙
      Mod.comap (inv (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j))

private lemma normalizedPullback_locallyFP (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B T)
    (hM : IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} j).obj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T))
      (((ProEtale.upperStar Ab.{u + 1} j).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M)) :
    IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj.{u} B) U)
      ((normalizedPullback B T U j).obj M) := by
  unfold normalizedPullback
  exact localFinitePresentation_comap
    (inv (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j)) hM

private lemma normalizedPullback_fp (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B T)
    (hM : Mod.IsFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} j).obj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T))
      (((ProEtale.upperStar Ab.{u + 1} j).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M)) :
    Mod.IsFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj.{u} B) U)
      ((normalizedPullback B T U j).obj M) := by
  unfold normalizedPullback
  obtain ⟨n, m, g, ⟨eg⟩⟩ := hM
  exact finitePresentation_map_of_presentation
    (Mod.comap (inv (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j)))
    (finiteFree_comap (inv (condensedPullbackHom (Profinite.continuousMapRingObj.{u} B) j))) g eg

private lemma normalizedPullback_encoding (T U : Scheme.{u}) (j : U ⟶ T)
    (M : FiniteDiscreteInternalModules B T) :
    Nonempty (((j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
      ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M) ≅
        (finiteDiscreteCoefficientEquivalence B eR G hG U).inverse.obj
          ((normalizedPullback B T U j).obj M)) := by
  unfold normalizedPullback
  exact finiteDiscreteCoefficient_restrictionEncoding B eR G hG T U j M

/-- Transport an internal finite local presentation to an ordinary presentation
by finite constant module sheaves, before refining the matrix to be constant.
Source: Bhatt--Scholze, Proposition 5.3.2 and Lemmas 5.4.1 and 5.4.3.
(auxiliary; not a blueprint node)

Proof in words. Choose the cover and finite free cokernel presentations from hM.
Pull the coefficient identification to each cover member. The common sectionwise
encoding commutes with these inverse images: on the underlying additive sheaves
this is inverse-image composition, and scalar compatibility follows from the
single fixed coefficient identification eR. It is an equivalence, hence preserves
finite sums and cokernels. Its image of the regular module is the constant sheaf
of the image under G of the regular internal module in abelian groups. The equality
hG identifies the underlying additive group of that module with ULift B, so it is
finite. Finite sums of this module remain finite. Applying the encoding to each
presentation therefore gives the displayed morphism f and cokernel isomorphism.
No constancy of the matrix entries is asserted here; that is a separate geometric
step. Empty covering families and rank-zero finite sums are included. -/
theorem finiteDiscreteCoefficient_encoded_presentation [DiscreteTopology B] [Finite B]
    (T U : Scheme.{u}) (j : U ⟶ T) (M : FiniteDiscreteInternalModules B T)
    (hM : IsLocallyFinitelyPresented
      ((ProEtale.upperStar Ab.{u + 1} j).obj
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T))
      (((ProEtale.upperStar Ab.{u + 1} j).mapMod
        (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)).obj M)) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage U, ∀ i : C.I₀,
      ∃ P Q : ModuleCat.{u + 1} (ULift.{u + 1} B), Finite P ∧ Finite Q ∧
        ∃ f : (constantSheaf (ProEt.topology (C.X i))
            (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj P ⟶
          (constantSheaf (ProEt.topology (C.X i))
            (ModuleCat.{u + 1} (ULift.{u + 1} B))).obj Q,
          Nonempty (((C.f i)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
            (((j)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).obj
              ((finiteDiscreteCoefficientEquivalence B eR G hG T).inverse.obj M)) ≅
            cokernel f) := by
  let Mj := (normalizedPullback B T U j).obj M
  obtain ⟨C, hC⟩ := normalizedPullback_locallyFP B T U j M hM
  refine ⟨C, fun i ↦ ?_⟩
  let Mi := (normalizedPullback B U (C.X i) (C.f i)).obj Mj
  have hi := normalizedPullback_fp B U (C.X i) (C.f i) Mj (hC i)
  obtain ⟨P, Q, hP, hQ, f, ⟨ef⟩⟩ := encoded_fp B eR G hG (C.X i) Mi hi
  obtain ⟨ej⟩ := normalizedPullback_encoding B eR G hG T U j M
  obtain ⟨ei⟩ := normalizedPullback_encoding B eR G hG U (C.X i) (C.f i) Mj
  exact ⟨P, Q, hP, hQ, f,
    ⟨((C.f i)^*[ModuleCat.{u + 1} (ULift.{u + 1} B)]).mapIso ej ≪≫ ei ≪≫ ef⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
