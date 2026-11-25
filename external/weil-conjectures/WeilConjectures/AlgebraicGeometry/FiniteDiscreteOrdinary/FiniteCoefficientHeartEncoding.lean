/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientOperationEncoding
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingPullbackFixed

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
import all WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import all WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ProEtaleSectionModuleFunctors
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal

/-! # The normalized coefficient comparison before deriving

The coefficient functor, its tensor structure, and its pullback comparison are
constructed here. The remaining equality is a tensor equation on the abelian hearts.

Source: blueprint proper-base-change-finite, transport paragraph and clause (3).
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

attribute [local instance 20000] sheafBraidedCategory
-- Proof imports supply transported instances too; retain the native structure of the statement.
attribute [local instance 30000] CondensedRing.monoidal_upperStar
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

private theorem isMonoidal_of_tensor
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal]
    (i : F ≅ G)
    (h : ∀ M N, Functor.LaxMonoidal.μ F M N ≫ i.hom.app (M ⊗ N) =
      (i.hom.app M ⊗ₘ i.hom.app N) ≫ Functor.LaxMonoidal.μ G M N) :
    NatTrans.IsMonoidal i.hom := by
  let : MonObj (F.obj (𝟙_ C)) := Functor.monObjObj (F := F) (𝟙_ C)
  let mg : MonObj (G.obj (𝟙_ C)) := Functor.monObjObj (F := G) (𝟙_ C)
  let mt : MonObj (G.obj (𝟙_ C)) := MonObj.ofIso (i.app (𝟙_ C))
  have hm : mt.mul = mg.mul := by
    change (i.inv.app _ ⊗ₘ i.inv.app _) ≫
      (Functor.LaxMonoidal.μ F _ _ ≫ F.map (λ_ (𝟙_ C)).hom) ≫ i.hom.app _ =
      Functor.LaxMonoidal.μ G _ _ ≫ G.map (λ_ (𝟙_ C)).hom
    simp only [Category.assoc]
    rw [i.hom.naturality, ← Category.assoc (Functor.LaxMonoidal.μ F _ _), h]
    simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
      Iso.inv_hom_id_app, tensorHom_id, id_whiskerRight, Category.id_comp]
  have hu := congrArg (fun m : MonObj (G.obj (𝟙_ C)) ↦ m.one) (MonObj.ext mt mg hm)
  refine ⟨?_, h⟩
  change (Functor.LaxMonoidal.ε F ≫ F.map (𝟙 _)) ≫ i.hom.app _ =
    Functor.LaxMonoidal.ε G ≫ G.map (𝟙 _) at hu
  rw [F.map_id, G.map_id] at hu
  simpa only [Category.comp_id] using hu

private theorem leftUniq_ofNatIsoRight_eq
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {G G' : D ⥤ C}
    (a : L ⊣ G) (b : L' ⊣ G') (i : G' ≅ G) :
    (a.leftAdjointUniq (b.ofNatIsoRight i)).hom =
      (conjugateEquiv b a).symm i.hom := by
  apply NatTrans.ext
  funext M
  apply (a.homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.homEquiv_unit]
  exact (unit_conjugateEquiv_symm b a i.hom M)

private theorem leftUniq_ofNatIsoRight_monoidal
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    {L L' : C ⥤ D} {G G' : D ⥤ C}
    [L.Monoidal] [L'.Monoidal] [G.LaxMonoidal] [G'.LaxMonoidal]
    (a : L ⊣ G) (b : L' ⊣ G') [a.IsMonoidal] [b.IsMonoidal]
    (i : G' ≅ G) [NatTrans.IsMonoidal i.hom] :
    NatTrans.IsMonoidal (a.leftAdjointUniq (b.ofNatIsoRight i)).hom := by
  rw [leftUniq_ofNatIsoRight_eq]
  constructor
  · apply (cancel_mono (Functor.OplaxMonoidal.η L')).mp
    rw [Category.assoc, conjugateEquiv_symm_app_unit_comp_η b a i.hom,
      Functor.Monoidal.ε_η, Functor.Monoidal.ε_η]
  · intro M N
    apply (cancel_epi (Functor.OplaxMonoidal.δ L M N)).mp
    apply (cancel_mono (Functor.OplaxMonoidal.δ L' M N)).mp
    simp only [Category.assoc, Functor.Monoidal.δ_μ_assoc,
      conjugateEquiv_symm_app_tensor_comp_δ b a i.hom,
      Functor.Monoidal.μ_δ, Category.comp_id]

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]
variable {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R]

private theorem internal_push_pure {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (V : Y.ProEtᵒᵖ)
    (x : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V))
    (y : N.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V)) :
    letI : (CondensedRing.upperStar R p).OplaxMonoidal :=
      (CondensedRing.monoidal_upperStar R p).toOplaxMonoidal
    ((((CondensedRing.upperStarLowerStarAdjunction R p).rightAdjointLaxMonoidal.μ
        M N).hom.hom.app V).hom)
      (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology Y)
        (condensedRingObj R Y) _ _ V x y) =
      InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology X)
        (condensedRingObj R X) M N
          ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V) x y := by
  exact ModuleRingedComparison.canonicalInternalPush_normalized R p M N V x y

/-- The actual coefficient restriction followed by the normalized section encoding.
Source: finite coefficient transport, heart-level construction
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square). -/
def coefficientHeartEncoding (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T) ⥤
      Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) :=
  Mod.comap (coefficientMap e.inv.hom T) ⋙ (E.ordinary.functor ⋙ E.fixed.functor)

/-- The inverse coefficient map stays invertible after pulling to a scheme.
Source: functoriality of the coefficient ring pullback
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square). -/
instance inverseCoefficient_isIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) : IsIso (coefficientMap e.inv.hom T) := by
  have : IsIso e.inv.hom := by
    change IsIso ((Mon.forget _).map e.inv)
    infer_instance
  dsimp [coefficientMap]
  infer_instance

/-- All factors of the heart encoding are equivalences.
Source: scalar restriction along an isomorphism and the normalized encoding
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square). -/
instance coefficientHeartEncoding_isEquivalence
    (e : Mon.mk R ≅ Mon.mk (coefficient A)) (T : Scheme.{u}) (E : Encoding A T) :
    (coefficientHeartEncoding A e T E).IsEquivalence := by
  have : (Mod.comap (coefficientMap e.inv.hom T)).IsEquivalence :=
    (inferInstance : (Mod.comapEquivalenceOfIsIso
      (coefficientMap e.inv.hom T)).functor.IsEquivalence)
  unfold coefficientHeartEncoding
  infer_instance

/-- The heart encoding preserves addition of morphisms.
Source: additivity of scalar restriction and both encoding factors
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square). -/
instance coefficientHeartEncoding_additive
    (e : Mon.mk R ≅ Mon.mk (coefficient A)) (T : Scheme.{u}) (E : Encoding A T) :
    (coefficientHeartEncoding A e T E).Additive := by
  unfold coefficientHeartEncoding
  infer_instance

omit [Finite A] [DiscreteTopology A] in
/-- The direct-image comparison is identity on the common underlying additive sections.
Source: coefficient-map naturality and normalized constant-section action
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square). -/
def coefficientHeartPushIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (p : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    CondensedRing.lowerStar R p ⋙ coefficientHeartEncoding A e Y EY ≅
      coefficientHeartEncoding A e X EX ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (CondensedRing.comapLowerStarIso e.inv.hom p) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (encodingPushforwardNatIso A Y X p EY EX) ≪≫
    (Functor.associator _ _ _).symm

/-- The pullback comparison obtained by uniqueness of left adjoints from the specified
identity-on-sections direct-image comparison.
Source: finite coefficient transport and the adjunction mate construction
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square). -/
def coefficientHeartPullIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (p : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    coefficientHeartEncoding A e Y EY ⋙
        ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p ≅
      CondensedRing.upperStar R p ⋙ coefficientHeartEncoding A e X EX := by
  let NX := (coefficientHeartEncoding A e X EX).asEquivalence
  let NY := (coefficientHeartEncoding A e Y EY).asEquivalence
  let i : CondensedRing.lowerStar R p ⋙ NY.functor ≅
      NX.functor ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p :=
    coefficientHeartPushIso A e p EX EY
  let k := Iso.isoCompInverse (H := NY) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := NX) k
  let a := NY.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) p)
  let b := (CondensedRing.upperStarLowerStarAdjunction R p).comp NX.toAdjunction
  exact a.leftAdjointUniq (b.ofNatIsoRight kr)

private def heartSectionsIso (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    coefficientHeartEncoding A e T E ⋙
        sheafCompose (Scheme.ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ≅
      Mod.forget (condensedRingObj R T) :=
  eqToIso (by
    unfold coefficientHeartEncoding
    rw [E.ordinary_functor, E.fixed_functor]
    rfl)

omit [Finite A] [DiscreteTopology A] in
private theorem heart_tensor_normalized (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T) :
    ∃ m : (coefficientHeartEncoding A e T E).Monoidal,
      ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T))
        (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
        ((m.toLaxMonoidal.μ M N).hom.app V)
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
            ((coefficientHeartEncoding A e T E).obj M)
            ((coefficientHeartEncoding A e T E).obj N) V
            ((((heartSectionsIso A e T E).inv.app M).hom.app V).hom x)
            ((((heartSectionsIso A e T E).inv.app N).hom.app V).hom y)) =
          (((heartSectionsIso A e T E).inv.app (M ⊗ N)).hom.app V).hom
            (InternalAbelianSheafModule.comparison_internalTmul (Scheme.ProEt.topology T)
              (condensedRingObj R T) M N V x y) := by
  let G := Mod.comap (coefficientMap e.inv.hom T) ⋙
    (sectionEncoding A T E.ringIso ⋙ fixedRestriction A T)
  have aux : ∀ (F : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj R T) ⥤
        Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
      (h : F = G),
      let s : F ⋙ sheafCompose (Scheme.ProEt.topology T)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) Ab.{u + 1}) ≅
            Mod.forget (condensedRingObj R T) := eqToIso (by rw [h]; rfl)
      ∃ m : F.Monoidal,
        ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
            (condensedRingObj R T))
          (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) (y : N.X.obj.obj V),
          ((m.toLaxMonoidal.μ M N).hom.app V)
            (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T)
              (ULift.{u + 1} A) (F.obj M) (F.obj N) V
              (((s.inv.app M).hom.app V).hom x)
              (((s.inv.app N).hom.app V).hom y)) =
            (((s.inv.app (M ⊗ N)).hom.app V).hom)
              (InternalAbelianSheafModule.comparison_internalTmul
                (Scheme.ProEt.topology T) (condensedRingObj R T) M N V x y) := by
    intro F h
    subst F
    exact coefficientSectionTensor_normalized A e T E.ringIso
  exact aux (coefficientHeartEncoding A e T E) (by
    unfold coefficientHeartEncoding G
    rw [E.ordinary_functor, E.fixed_functor])

omit [Finite A] [DiscreteTopology A] [IsCommMonObj R] in
private theorem heart_map_sections (e : Mon.mk R ≅ Mon.mk (coefficient A))
    (T : Scheme.{u}) (E : Encoding A T)
    {M N : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj R T)}
    (f : M ⟶ N) (V : T.ProEtᵒᵖ) (x : M.X.obj.obj V) :
    (((coefficientHeartEncoding A e T E).map f).hom.app V)
      ((((heartSectionsIso A e T E).inv.app M).hom.app V).hom x) =
        (((heartSectionsIso A e T E).inv.app N).hom.app V).hom
          ((f.hom.hom.app V).hom x) := by
  exact (congrArg (fun g ↦ ((g.hom.app V).hom x))
    ((heartSectionsIso A e T E).inv.naturality f)).symm

omit [Finite A] [DiscreteTopology A] [IsCommMonObj R] in
private theorem heart_push_sections (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (p : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj R X))
    (V : Y.ProEtᵒᵖ)
    (x : M.X.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V)) :
    (((coefficientHeartPushIso A e p EX EY).hom.app M).hom.app V)
        ((((heartSectionsIso A e Y EY).inv.app
          ((CondensedRing.lowerStar R p).obj M)).hom.app V).hom x) =
      (((heartSectionsIso A e X EX).inv.app M).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V)).hom x := by
  rcases EX with ⟨cX, nX, oX, hoX, fX, hfX, oaX, oiX, faX, fiX⟩
  rcases oX with ⟨O, Oi, Ou, Oc, Ot⟩
  rcases fX with ⟨F, Fi, Fu, Fc, Ft⟩
  dsimp only at hoX hfX
  subst O F
  rcases EY with ⟨cY, nY, oY, hoY, fY, hfY, oaY, oiY, faY, fiY⟩
  rcases oY with ⟨O, Oi, Ou, Oc, Ot⟩
  rcases fY with ⟨F, Fi, Fu, Fc, Ft⟩
  dsimp only at hoY hfY
  subst O F
  rfl

omit [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
private theorem fixed_tensor_pure (T : Scheme.{u})
    {M M' N N' : Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))}
    (f : M ⟶ M') (g : N ⟶ N') (V : T.ProEtᵒᵖ)
    (x : M.obj.obj V) (y : N.obj.obj V) :
    ((f ⊗ₘ g).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
          M N V x y) =
      ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology T) (ULift.{u + 1} A)
        M' N' V ((f.hom.app V) x) ((g.hom.app V) y) := by
  exact (congrArg (fun z ↦ (z.app V) (x ⊗ₜ[ULift.{u + 1} A] y))
    (Functor.LaxMonoidal.μ_natural
      (sheafToPresheaf (Scheme.ProEt.topology T)
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) f g)).symm

omit [Finite A] [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A] in
private theorem fixed_push_pure {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (V : Y.ProEtᵒᵖ)
    (x : M.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V))
    (y : N.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V)) :
    ((Functor.LaxMonoidal.μ
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p) M N).hom.app V)
        (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology Y) (ULift.{u + 1} A)
          _ _ V x y) =
      ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology X) (ULift.{u + 1} A)
        M N ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V) x y := by
  exact congrArg (fun g ↦ (g (x ⊗ₜ[ULift.{u + 1} A] y)))
    (Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ p)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) M N V)

attribute [local irreducible] heartSectionsIso coefficientHeartEncoding
  coefficientHeartPushIso coefficientHeartPullIso

-- Retain the finite discrete hypotheses of the existing public statement.
set_option linter.unusedSectionVars false in
/-- The normalized mate respects the balanced tensor comparisons on the hearts.

Source: blueprint proper-base-change-finite, transport paragraph and clause (3),
and step 2 of lem-sfb-finite-coefficient-tensor-pullback-encoding; Stacks 03D3.
(blueprint: lem-sfb-finite-coefficient-heart-tensor-square).

Proof: use the pure-tensor normalized structures mX and mY supplied by the
internal/section tensor comparison and the normalized scalar restriction tensor
comparisons. Restrict the internal action along the inverse coefficient isomorphism.
The section-action tensor comparison sends a balanced pure tensor x tensor y to
that same pure tensor, as does restriction to constant scalars. Normalization of
Encoding identifies each constant scalar with the canonical constant function.
The direct-image comparison used to define coefficientHeartPullIso is the identity
on these additive sections over every fibre product. Transpose under the specified
pullback/direct-image adjunctions. The unit and counit formulas for that mate show
that both composites in the monoidal tensor equation send a pulled-back pure tensor
to the same pulled-back pure tensor. The balanced tensor universal property and
sheafification identify the maps. For the monoidal unit both maps send the constant
section 1 to 1, and the same adjunction equation identifies them. These arguments
also apply to the empty scheme and the zero coefficient ring. -/
theorem coefficientHeartPullIso_monoidal
    (e : Mon.mk R ≅ Mon.mk (coefficient A))
    {X Y : Scheme.{u}} (p : X ⟶ Y) (EX : Encoding A X) (EY : Encoding A Y) :
    ∃ (mX : (coefficientHeartEncoding A e X EX).Monoidal)
      (mY : (coefficientHeartEncoding A e Y EY).Monoidal),
      letI := mX
      letI := mY
      NatTrans.IsMonoidal (coefficientHeartPullIso A e p EX EY).hom := by
  obtain ⟨mX, hX⟩ := heart_tensor_normalized A e X EX
  obtain ⟨mY, hY⟩ := heart_tensor_normalized A e Y EY
  let := mX
  let := mY
  let : (CondensedRing.upperStar R p).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar R p).toOplaxMonoidal
  let aI := CondensedRing.upperStarLowerStarAdjunction R p
  let := aI.rightAdjointLaxMonoidal
  have hi : NatTrans.IsMonoidal (coefficientHeartPushIso A e p EX EY).hom := by
    apply isMonoidal_of_tensor
    intro M N
    apply ConstantScalarRestriction.fixedTensor_ext
      (Scheme.ProEt.topology Y) (ULift.{u + 1} A)
    intro V x y
    obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (((heartSectionsIso A e Y EY).inv.app
        ((CondensedRing.lowerStar R p).obj M)).hom.app V)).2 x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (((heartSectionsIso A e Y EY).inv.app
        ((CondensedRing.lowerStar R p).obj N)).hom.app V)).2 y
    change (((coefficientHeartPushIso A e p EX EY).hom.app (M ⊗ N)).hom.app V)
      ((((coefficientHeartEncoding A e Y EY).map
        (Functor.LaxMonoidal.μ (CondensedRing.lowerStar R p) M N)).hom.app V)
        ((Functor.LaxMonoidal.μ (coefficientHeartEncoding A e Y EY) _ _).hom.app V
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology Y)
            (ULift.{u + 1} A) _ _ V _ _))) = _
    rw [hY, heart_map_sections, heart_push_sections]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ModuleCat.comp_apply]
    rw [fixed_tensor_pure, heart_push_sections, heart_push_sections]
    change _ = ((Functor.LaxMonoidal.μ (coefficientHeartEncoding A e X EX) M N).hom.app
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V))
      (((Functor.LaxMonoidal.μ
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p) _ _).hom.app V)
          (ConstantScalarRestriction.fixedPure (Scheme.ProEt.topology Y)
            (ULift.{u + 1} A) _ _ V _ _))
    rw [fixed_push_pure, hX]
    exact congrArg (fun z ↦
      (((heartSectionsIso A e X EX).inv.app (M ⊗ N)).hom.app
        ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ p).op.obj V)).hom z)
      (internal_push_pure p M N V x y)
  let NX := (coefficientHeartEncoding A e X EX).asEquivalence
  let NY := (coefficientHeartEncoding A e Y EY).asEquivalence
  let : NX.functor.Monoidal := mX
  let : NY.functor.Monoidal := mY
  let : NX.inverse.Monoidal := NX.inverseMonoidal
  let : NY.inverse.Monoidal := NY.inverseMonoidal
  let : NX.IsMonoidal := inferInstance
  let : NY.IsMonoidal := inferInstance
  let i : CondensedRing.lowerStar R p ⋙ NY.functor ≅
      NX.functor ⋙ ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) p :=
    coefficientHeartPushIso A e p EX EY
  have : NatTrans.IsMonoidal i.hom := hi
  let k := Iso.isoCompInverse (H := NY) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := NX) k
  have : NatTrans.IsMonoidal kr.hom := by
    dsimp only [kr, k, Iso.isoCompInverse, Iso.inverseCompIso]
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom]
    infer_instance
  let a := NY.toAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) p)
  let b := aI.comp NX.toAdjunction
  refine ⟨mX, mY, ?_⟩
  unfold coefficientHeartPullIso
  change NatTrans.IsMonoidal (a.leftAdjointUniq (b.ofNatIsoRight kr)).hom
  exact leftUniq_ofNatIsoRight_monoidal a b kr

end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
