/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-! # Internal Hom from a locally finite free internal module preserves colimits

The proof works with ordinary module objects. Weakly etale pullback commutes with
internal Hom; this follows by comparison with restriction of sheaves and its local
internal-Hom calculation. Pullbacks along a covering family jointly reflect isomorphisms.
On a finite free trivialization, internal Hom is a finite power, hence a finite
coproduct. Transport the canonical colimit comparison through these identifications.

The pullback and conservativity calculations adapt the proved source-library arguments
in `ProEtale.UpperLowerStar.InternalHom` and
`ProEtale.LowerShriek.OpenImmersion.Conservative` to the current pullback API.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Opposite

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]
  {V X : Scheme.{u}} (g : V ⟶ X) (h : WeaklyEtale g)
  [((Scheme.ProEt.topology X).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology V).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory

section

variable [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

open Functor.OplaxMonoidal

/-- The identification of the pullback along a weakly étale morphism with the restriction is a
monoidal natural isomorphism. -/
private instance : NatTrans.IsMonoidal (ProEtale.upperStarIsoSheafPushforward A g h).hom where
  unit := by
    have hhomapp (P : Sheaf (Scheme.ProEt.topology X) A) (U : X.ProEtᵒᵖ) :
        ((sheafToPresheaf _ A).map
          ((localizationRestrictionLowerStarAdjunction A g h).unit.app P)).app U =
          P.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g h trivial).counit.app
            U.unop).op := by
      simp [localizationRestrictionLowerStarAdjunction,
        Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft]
    have hunit :
        (localizationRestrictionLowerStarAdjunction A g h).unit.app (𝟙_ _) =
          ε (g)_*[A] ≫ (g)_*[A].map (ε ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
            A (Scheme.ProEt.topology V) (Scheme.ProEt.topology X))) := by
      apply Sheaf.hom_ext_of_ε_comp
      ext U : 2
      simp only [NatTrans.comp_app, Functor.map_comp, hhomapp]
      erw [← (ε (sheafToPresheaf (ProEt.topology X) A)).naturality]
      erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
      erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
        (F := MorphismProperty.Over.map ⊤ h)]
      erw [Monoidal.tensorUnit_map, Category.id_comp]
      rfl
    rw [← cancel_epi (η (g)^*[A])]
    simp only [Functor.Monoidal.η_ε_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    dsimp only [upperStarIsoSheafPushforward, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_app_unit_comp_map_η]
    exact hunit
  tensor P Q := by
    have hhomapp (P : Sheaf (Scheme.ProEt.topology X) A) (U : X.ProEtᵒᵖ) :
        ((sheafToPresheaf _ A).map
          ((localizationRestrictionLowerStarAdjunction A g h).unit.app P)).app U =
          P.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ g h trivial).counit.app
            U.unop).op := by
      simp [localizationRestrictionLowerStarAdjunction,
        Adjunction.sheafPushforwardContinuous, Adjunction.whiskerLeft]
    have htensor (P Q : Sheaf (Scheme.ProEt.topology X) A) :
        (localizationRestrictionLowerStarAdjunction A g h).unit.app (P ⊗ Q) =
          ((localizationRestrictionLowerStarAdjunction A g h).unit.app P ⊗ₘ
            (localizationRestrictionLowerStarAdjunction A g h).unit.app Q) ≫
          μ (g)_*[A] _ _ ≫ (g)_*[A].map
            (μ ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
              A (Scheme.ProEt.topology V) (Scheme.ProEt.topology X)) P Q) := by
      apply Sheaf.tensor_hom_ext
      rw [Functor.map_comp, ← μ_natural_assoc]
      ext U : 2
      simp only [NatTrans.comp_app, Functor.map_comp, Monoidal.tensorHom_app, hhomapp]
      erw [← (μ (sheafToPresheaf (ProEt.topology X) A) P Q).naturality]
      erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
      erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
        (F := MorphismProperty.Over.map ⊤ h)]
      rfl
    rw [← cancel_epi (δ (g)^*[A] P Q)]
    simp only [Functor.Monoidal.δ_μ_assoc]
    apply ((upperStarLowerStarAdjunction A g).homEquiv _ _).injective
    dsimp only [upperStarIsoSheafPushforward, upperStarIsoLocalizationRestriction]
    erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_app_tensor_comp_map_δ, Functor.map_comp, Category.assoc,
      ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
      Adjunction.unit_leftAdjointUniq_hom_app]
    exact htensor P Q

end

end AlgebraicGeometry

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
attribute [local instance] Sheaf.symmetricCategory
open scoped MonoidalClosed.FunctorCategory

private noncomputable def pullIhomIso
    {X Y : Scheme.{u}} (g : Y ⟶ X) [WeaklyEtale g]
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
    let F := (upperStar Ab.{u + 1} g).mapMod R
    Mod.ihom P ⋙ F ≅ F ⋙ Mod.ihom (F.obj P) := by
  let G := upperStar Ab.{u + 1} g
  let φ := 𝟙 (G.obj R)
  let F := Mod.mapModComap (G := G) φ
  let F' := G.mapMod R
  let c : F ≅ F' := NatIso.ofComponents
    (fun M ↦ Mod.isoMk (Iso.refl _) (by simp [F, F', φ, Mod.act]))
    (fun f ↦ by ext : 1; rfl)
  let e (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
      Mod.ihom M ≅ Mod.ihom' R M :=
    (Mod.ihomAdjunction M).rightAdjointUniq (Mod.ihom'Adjunction _ M)
  let e' (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (G.obj R)) :
      Mod.ihom M ≅ Mod.ihom' (G.obj R) M :=
    (Mod.ihomAdjunction M).rightAdjointUniq (Mod.ihom'Adjunction _ M)
  have hIso (P0 : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      IsIso (ihomComparison (g)^*[Ab.{u + 1}] P0) := by
    let h : WeaklyEtale g := inferInstance
    let R := (MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous Ab.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    let W := (Functor.whiskeringLeft _ _ Ab.{u + 1}).obj
      (MorphismProperty.Over.map ⊤ h).op
    have : ∀ k : Y.ProEtᵒᵖ,
        (Under.post (MorphismProperty.Over.map ⊤ h).op (X := k)).IsEquivalence :=
      fun k ↦ MorphismProperty.Over.isEquivalence_post_map_op h k.unop
    have hW : IsIso (ihomComparison W ((sheafToPresheaf _ Ab.{u + 1}).obj
        P0)) := inferInstance
    have hι : ∀ Y : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1},
        IsIso (ihomComparison (sheafToPresheaf _ Ab.{u + 1}) Y) :=
      Monoidal.Reflective.isIso_ihomComparison
        (sheafificationAdjunction (Scheme.ProEt.topology _) Ab.{u + 1})
    have hιV : ∀ Y : Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1},
        IsIso (ihomComparison (sheafToPresheaf _ Ab.{u + 1}) Y) :=
      Monoidal.Reflective.isIso_ihomComparison
        (sheafificationAdjunction (Scheme.ProEt.topology _) Ab.{u + 1})
    have h1 : IsIso (ihomComparison (sheafToPresheaf _ Ab.{u + 1} ⋙ W)
        P0) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Q
      rw [ihomComparison_comp_app]
      infer_instance
    let τ := Functor.sheafPullbackConstruction.sheafToPresheafCompWhiskeringLeftIsoPushforward
      (MorphismProperty.Over.map ⊤ h) Ab.{u + 1} (Scheme.ProEt.topology Y)
      (Scheme.ProEt.topology X)
    have : NatTrans.IsMonoidal τ.symm.hom := inferInstanceAs (NatTrans.IsMonoidal τ.inv)
    have h2 : IsIso (ihomComparison (R ⋙ sheafToPresheaf _ Ab.{u + 1})
        P0) := isIso_ihomComparison_of_iso τ.symm _
    have hR : IsIso (ihomComparison R P0) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro Q
      have hq := NatIso.isIso_app_of_isIso
        (ihomComparison (R ⋙ sheafToPresheaf _ Ab.{u + 1})
          P0) Q
      rw [ihomComparison_comp_app] at hq
      have := IsIso.of_isIso_comp_right ((sheafToPresheaf _ Ab.{u + 1}).map
        ((ihomComparison R P0).app Q))
        ((ihomComparison (sheafToPresheaf _ Ab.{u + 1}) (R.obj P0)).app
          (R.obj Q))
      exact isIso_of_reflects_iso _ (sheafToPresheaf _ Ab.{u + 1})
    exact isIso_ihomComparison_of_iso (upperStarIsoSheafPushforward Ab.{u + 1} g h)
      P0
  letI (Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      IsIso (ihomComparison (g)^*[Ab.{u + 1}] Q) := hIso Q
  have (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) :
      PreservesLimit (parallelPair (Mod.homModPre (Mod.act P.X) N)
        (Mod.homModB _ P N)) F := by
    dsimp [F, Mod.mapModComap]
    infer_instance
  let d : Mod.ihom P ⋙ F ≅ F ⋙ Mod.ihom (F.obj P) :=
    Functor.isoWhiskerRight (e P) F ≪≫
      NatIso.ofComponents (F := Mod.ihom' _ P ⋙ F)
        (G := F ⋙ Mod.ihom' _ (F.obj P)) (fun N ↦
        have := Mod.isIso_mapIhom'Hom G φ P N
        asIso (Mod.mapIhom'Hom G φ P N))
        (fun f ↦ Mod.mapIhom'Hom_naturality _ _ P f) ≪≫
      Functor.isoWhiskerLeft F (e' (F.obj P)).symm
  exact Functor.isoWhiskerLeft _ c.symm ≪≫ d ≪≫
    Functor.isoWhiskerRight c _ ≪≫ Functor.isoWhiskerLeft F' (Mod.ihomMapIso (c.app P)).symm
end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Mod
open CategoryTheory Limits MonoidalCategory MonObj
universe v w
variable {C : Type w} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [BraidedCategory C] [MonoidalPreadditive C] [IsGrothendieckAbelian.{v} C]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{v, v} (MonoidalCategory.tensorRight X)]
  {A : C} [MonObj A] [IsCommMonObj A]
attribute [local instance] Mod.isGrothendieckAbelian Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
private noncomputable def ihomFreePowerIso (n : ℕ) :
    Mod.ihom (⨁ fun _ : Fin n ↦ Mod.regular A) ≅
      Functor.const (Discrete (Fin n)) ⋙ (lim : (Discrete (Fin n) ⥤ Mod C A) ⥤ Mod C A) :=
  NatIso.ofComponents (fun N ↦ Mod.ihomBiproductIso _ N ≪≫
    biproduct.mapIso (fun _ ↦ Mod.ihomRegularIso.app N) ≪≫
    biproduct.isoProduct (fun _ : Fin n ↦ N) ≪≫ Pi.isoLimit ((Functor.const _).obj N))
    (fun f ↦ by
      apply limit.hom_ext
      intro j
      rcases j with ⟨j⟩
      simp only [Iso.trans_hom, Category.assoc, Functor.comp_map, Functor.const_obj_obj,
        Functor.const_map_app, lim_map,
        limMap_π, Pi.isoLimit_hom_π, biproduct.isoProduct_hom, Pi.lift_comp_π,
        biproduct.mapIso_hom]
      simp only [Mod.ihomBiproductIso, biproduct.uniqueUpToIso, Mod.ihomBiproductBicone]
      simp only [Pi.isoLimit_hom_π_assoc]
      dsimp only [Functor.const] at *
      erw [biproduct.map_π, biproduct.lift_π_assoc, Pi.lift_comp_π_assoc,
        biproduct.map_π_assoc, biproduct.lift_π_assoc]
      rw [(Mod.ihomMap (biproduct.ι (fun _ : Fin n ↦ Mod.regular A) j)).naturality_assoc]
      exact congrArg ((Mod.ihomMap
        (biproduct.ι (fun _ : Fin n ↦ Mod.regular A) j)).app _ ≫ ·)
        (Mod.ihomRegularIso.hom.naturality f))

private theorem ihom_preservesColimits_of_finiteFree {M : Mod C A} {n : ℕ}
    (e : M ≅ ⨁ fun _ : Fin n ↦ Mod.regular A) :
    PreservesColimitsOfSize.{v, v} (Mod.ihom M) := by
  have : PreservesColimitsOfSize.{v, v}
      (lim : (Discrete (Fin n) ⥤ Mod C A) ⥤ Mod C A) :=
    preservesColimits_of_natIso HasBiproductsOfShape.colimIsoLim
  have : PreservesColimitsOfSize.{v, v}
      (Functor.const (Discrete (Fin n)) ⋙
        (lim : (Discrete (Fin n) ⥤ Mod C A) ⥤ Mod C A)) := inferInstance
  exact preservesColimits_of_natIso
    ((Mod.ihomMapIso e).symm ≪≫ ihomFreePowerIso n).symm

end CategoryTheory.Mod

namespace AlgebraicGeometry

variable (A : Type u') [Category.{u + 1} A]
variable {X : Scheme.{u}} {G G' : Sheaf (Scheme.ProEt.topology X) A} (φ : G ⟶ G')

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale
open CategoryTheory Limits
private theorem isIso_mapMod_of_cover {X : Scheme.{u}}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (f : M ⟶ N)
    (hf : ∀ s : C.I₀, IsIso (((upperStar Ab.{u + 1} (C.f s)).mapMod R).map f)) :
    IsIso f := by
  have (s : C.I₀) : WeaklyEtale (C.f s) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
  have hi : IsIso f.hom := by
    refine isIso_of_isIso_localizationRestriction Ab.{u + 1} f.hom C.f C.mem₀ fun s ↦ ?_
    have := hf s
    have hi : IsIso ((upperStar Ab.{u + 1} (C.f s)).map f.hom) :=
      inferInstanceAs (IsIso ((Mod.forget _).map
        (((upperStar Ab.{u + 1} (C.f s)).mapMod R).map f)))
    exact (NatIso.isIso_map_iff
      (upperStarIsoLocalizationRestriction Ab.{u + 1} (C.f s) inferInstance) f.hom).1 hi
  have : IsIso ((Mod.forget R).map f) := hi
  exact isIso_of_reflects_iso f (Mod.forget R)
end AlgebraicGeometry.ProEtale

namespace CategoryTheory.Limits
universe x y z
private theorem isIso_map_desc_of_preserves
    {A B C : Type*} [Category A] [Category B] [Category C]
    {J : Type x} [Category.{y} J] (D : J ⥤ A) (H : A ⥤ B) (F : B ⥤ C)
    [HasColimit D] [HasColimit (D ⋙ H)]
    [PreservesColimit D (H ⋙ F)] [PreservesColimit (D ⋙ H) F] :
    IsIso (F.map (colimit.desc _ (H.mapCocone (colimit.cocone D)))) := by
  let hc : IsColimit (F.mapCocone (H.mapCocone (colimit.cocone D))) :=
    (isColimitOfPreserves (H ⋙ F) (colimit.isColimit D)).ofIsoColimit
      (Functor.mapCoconeMapCocone (colimit.cocone D)).symm
  let hd := isColimitOfPreserves F (colimit.isColimit (D ⋙ H))
  let e := hd.coconePointUniqueUpToIso hc
  have he : F.map (colimit.desc _ (H.mapCocone (colimit.cocone D))) = e.hom := by
    apply hd.hom_ext
    intro s
    change F.map (colimit.ι (D ⋙ H) s) ≫
      F.map (colimit.desc _ (H.mapCocone (colimit.cocone D))) = _
    rw [← F.map_comp, colimit.ι_desc]
    exact (hd.fac (F.mapCocone (H.mapCocone (colimit.cocone D))) s).symm
  rw [he]
  infer_instance
end CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale
open CategoryTheory Limits
attribute [local instance] Mod.isGrothendieckAbelian

/-- Internal Hom from a pro-etale locally finite free module preserves small colimits.
Source: Hemo--Richarz--Scholbach, Lemma 5.3(2), finite locally free calculation.
(auxiliary; not a blueprint node)

Proof: pullback along a weakly etale morphism commutes with internal Hom. This is
proved by restriction to the localized site, where internal Hom is computed locally,
and by comparison of the two right adjoints of module tensor. Each pullback on
module objects preserves colimits, as the underlying sheaf pullback does and the
module forgetful functor creates and reflects them. On a covering trivializing P,
internal Hom is a finite power of the identity, naturally in the input module.
Finite powers are finite coproducts, which preserve every small colimit. Thus every
pullback of the canonical colimit comparison is invertible. Covering restrictions
jointly reflect isomorphisms, first for underlying sheaves and then for module
objects. The original comparison is therefore invertible. This also treats rank
zero and empty schemes. -/
theorem condensed_locally_free_ihom_preservesColimits {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hP : IsLocallyFree R P) :
    PreservesColimitsOfSize.{u + 1, u + 1} (Mod.ihom P) := by
  obtain ⟨C, hC⟩ := hP
  have (s : C.I₀) : WeaklyEtale (C.f s) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk s)
  refine ⟨fun {J} _ ↦ ⟨fun {D} ↦ ?_⟩⟩
  have h : IsIso (colimit.desc _ ((Mod.ihom P).mapCocone (colimit.cocone D))) := by
    apply isIso_mapMod_of_cover C R
    intro s
    let F := (upperStar Ab.{u + 1} (C.f s)).mapMod R
    have : PreservesColimitsOfSize.{u + 1, u + 1}
        (upperStar Ab.{u + 1} (C.f s)) :=
      (upperStarLowerStarAdjunction Ab.{u + 1} (C.f s)).leftAdjoint_preservesColimits
    have : PreservesColimitsOfSize.{u + 1, u + 1} F := by
      refine ⟨fun {J} _ ↦ ?_⟩
      let forgetY :
          Mod (Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1})
              ((upperStar Ab.{u + 1} (C.f s)).obj R) ⥤
            Sheaf (Scheme.ProEt.topology (C.X s)) Ab.{u + 1} := Mod.forget _
      have : PreservesColimitsOfShape J (F ⋙ forgetY) :=
        inferInstanceAs (PreservesColimitsOfShape J
          (Mod.forget R ⋙ upperStar Ab.{u + 1} (C.f s)))
      have : ReflectsColimitsOfShape J forgetY :=
        reflectsColimitsOfShape_of_reflectsIsomorphisms
      exact preservesColimitsOfShape_of_reflects_of_preserves F forgetY
    obtain ⟨n, ⟨e⟩⟩ := hC s
    have : PreservesColimitsOfSize.{u + 1, u + 1} (Mod.ihom (F.obj P)) :=
      Mod.ihom_preservesColimits_of_finiteFree e
    have : PreservesColimit D (Mod.ihom P ⋙ F) :=
      preservesColimit_of_natIso D (pullIhomIso (C.f s) R P).symm
    exact isIso_map_desc_of_preserves D (Mod.ihom P) F
  obtain ⟨hc⟩ := (colimit.isColimit _).nonempty_isColimit_iff_isIso_desc.2 h
  exact preservesColimit_of_preserves_colimit_cocone (colimit.isColimit D) hc
end AlgebraicGeometry.ProEtale
