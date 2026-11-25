/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.ArtinSchreier
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Proper.Smooth.ProperSmoothCurvesGaHigherDirectImageVanishing
import WeilConjectures.AlgebraicGeometry.EtaleTensorUnitRestrictionEquation
public import WeilConjectures.AlgebraicGeometry.Proper.Flat.ProperFlatGlobalSections
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-!
# The étale direct image of `𝔾ₐ` in a family of curves

For a proper smooth morphism `f: C ⟶ S` with geometrically connected fibres, the étale direct
image `f_* 𝔾ₐ` is `𝔾ₐ` on `S`, i.e. the universe lift of the étale sheaf of `𝒪_S`, and the
Artin--Schreier map `℘ = Frob - 1` of `C` induces `F - 1` for the Frobenius `F: x ↦ xᵖ`.

This is the degree `0` case of `properSmoothCurves_higherDirectImage_ga_frobeniusLinear`.

## References

* Stacks Project, Tag 0GKV, case (b), and Tag 0E0L (`f_* 𝒪_C = 𝒪_S` universally)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

attribute [local instance]
  instIsQuasicoherentOpensCarrierCarrierCommRingCatUnitRingCatSheaf_weilConjectures

namespace Scheme.Modules

private theorem etaleTensorSectionsSheaf_map_eq {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] {U V : X.Etaleᵒᵖ} (g : U ⟶ V) :
    (etaleTensorSectionsSheaf F).obj.map g = etaleTensorSectionsRestriction F g.unop := rfl

private theorem exists_sections_addEquiv_of_isIso_unit {Y : Scheme.{u}} {M : Y.Modules}
    (f : M ⟶ SheafOfModules.unit Y.ringCatSheaf) [IsIso f] :
    ∃ b : Γ(M, ⊤) ≃+ Γ(Y, ⊤),
      (∀ x : Γ(M, ⊤), b x = f.app ⊤ x) ∧
        ∀ (a : Γ(Y, ⊤)) (x : Γ(M, ⊤)), b (a • x) = a * b x := by
  classical
  let b : Γ(M, ⊤) ≃+ Γ(Y, ⊤) :=
    AddEquiv.ofBijective (f.app ⊤).hom (ConcreteCategory.bijective_of_isIso (f.app ⊤))
  refine ⟨b, fun _ ↦ rfl, ?_⟩
  intro a x
  exact Hom.app_smul f a x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The sections of the étale sheaf of `𝒪_X` over an étale `X`-scheme `U` are `Γ(U, 𝒪_U)`,
compatibly with restriction and turning the module structure into multiplication
(Stacks, Tags 0096 and 01CA). -/
theorem exists_etaleTensorUnit_sections_natural_smul (X : Scheme.{u}) :
    ∃ b : ∀ U : X.Etaleᵒᵖ,
        (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U ≃+
          Γ(U.unop.left, ⊤),
      (∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V)
          (x : (etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.obj U),
        b V ((etaleTensorSectionsSheaf (SheafOfModules.unit X.ringCatSheaf)).obj.map g x) =
          g.unop.left.appTop (b U x)) ∧
      ∀ (U : X.Etale) (a : Γ(U.left, ⊤))
        (x : Γ((tensorPullback U.hom).obj (SheafOfModules.unit X.ringCatSheaf), ⊤)),
        b (op U) (a • x) = a * b (op U) x := by
  classical
  have hi (U : X.Etaleᵒᵖ) : IsIso (tensorPullbackObjUnitToUnit U.unop.hom) :=
    (tensorPullbackObjUnitToUnit_isIso U.unop.hom).1
  choose b hb hs using fun U : X.Etaleᵒᵖ ↦
    exists_sections_addEquiv_of_isIso_unit (Y := U.unop.left)
      (M := (tensorPullback U.unop.hom).obj (SheafOfModules.unit X.ringCatSheaf))
      (tensorPullbackObjUnitToUnit U.unop.hom)
  refine ⟨b, ?_, ?_⟩
  · intro U V g x
    erw [etaleTensorSectionsSheaf_map_eq, hb, hb]
    exact etaleTensorUnitRestriction_equation g.unop x
  · intro U a x
    exact hs (op U) a x

end Scheme.Modules

namespace Scheme

/-- The Frobenius `x ↦ xᵖ` of an abelian étale sheaf whose sections are identified with the
global functions, compatibly with restriction, on a scheme where the prime `p` vanishes. -/
noncomputable def frobeniusOfSectionsAddEquiv {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (ha : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (p : ℕ) [Fact p.Prime] (hp : (p : Γ(X, ⊤)) = 0) : G ⟶ G :=
  ⟨{ app U := AddCommGrpCat.ofHom
        { toFun x := (a U).symm (a U x ^ p)
          map_zero' := by simp [(Fact.out : p.Prime).ne_zero]
          map_add' x y := by
            rw [map_add, add_pow_prime_of_natCast_eq_zero p
              (natCast_eq_zero_of_etale X p hp U.unop), map_add] }
     naturality U V g := by
       ext x
       apply (a V).injective
       change a V ((a V).symm (a V (G.obj.map g x) ^ p)) =
         a V (G.obj.map g ((a U).symm (a U x ^ p)))
       rw [AddEquiv.apply_symm_apply, ha, ha, AddEquiv.apply_symm_apply, map_pow] }⟩

lemma apply_frobeniusOfSectionsAddEquiv_hom_app {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤)) (ha) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) (U : X.Etaleᵒᵖ) (x : G.obj.obj U) :
    a U ((frobeniusOfSectionsAddEquiv G a ha p hp).hom.app U x) = a U x ^ p :=
  (a U).apply_symm_apply _

/-- Under an identification of the universe lift of `G` with `𝔾ₐ`, the map `F - 1` for the
Frobenius `F` of `G` is the Artin--Schreier map `℘`. -/
lemma uliftMap_frobeniusOfSectionsAddEquiv_sub_comp_hom {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤)) (ha) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
        (frobeniusOfSectionsAddEquiv G a ha p hp - 𝟙 G) ≫
        (uliftIsoGaSheafOfSectionsAddEquiv G a ha).hom =
      (uliftIsoGaSheafOfSectionsAddEquiv G a ha).hom ≫ X.gaArtinSchreier p hp := by
  ext U x
  obtain ⟨y⟩ := x
  apply ULift.ext
  have key (z : G.obj.obj U) :
      a U ((frobeniusOfSectionsAddEquiv G a ha p hp - 𝟙 G).hom.app U z) = a U z ^ p - a U z := by
    rw [← apply_frobeniusOfSectionsAddEquiv_hom_app G a ha p hp U z]
    exact map_sub (a U) _ z
  exact key y

/-- The inverse form of `uliftMap_frobeniusOfSectionsAddEquiv_sub_comp_hom`. -/
lemma gaArtinSchreier_comp_uliftIsoGaSheafOfSectionsAddEquiv_inv {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤)) (ha) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0) :
    X.gaArtinSchreier p hp ≫ (uliftIsoGaSheafOfSectionsAddEquiv G a ha).inv =
      (uliftIsoGaSheafOfSectionsAddEquiv G a ha).inv ≫
        (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
          (frobeniusOfSectionsAddEquiv G a ha p hp - 𝟙 G) := by
  rw [Iso.comp_inv_eq, Category.assoc, uliftMap_frobeniusOfSectionsAddEquiv_sub_comp_hom,
    Iso.inv_hom_id_assoc]

/-- For `f : X ⟶ S` proper, flat, of finite presentation, with geometrically reduced and
geometrically connected fibres, the pullback `Γ(T, 𝒪_T) → Γ(T ×_S X, 𝒪)` is bijective for
every `T ⟶ S`: `𝒪_S → f_* 𝒪_X` is an isomorphism universally (Stacks, Tag 0E0L). -/
theorem bijective_appTop_pullback_fst_of_proper_flat {X S T : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (hred : ∀ s : S, GeometricallyReduced (f.fiberToSpecResidueField s))
    (hconn : ∀ s : S, GeometricallyConnected (f.fiberToSpecResidueField s)) (g : T ⟶ S) :
    Function.Bijective (pullback.fst g f).appTop := by
  have hu := (isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers
    f hred hconn).2 g
  obtain ⟨hiso, hcomp⟩ := Modules.tensorPullbackObjUnitToUnit_isIso (pullback.snd f g)
  have : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (pullback.snd f g).toRingCatSheafHom) := by
    rw [← hcomp]
    infer_instance
  have hb : Function.Bijective (pullback.snd f g).appTop :=
    ConcreteCategory.bijective_of_isIso (Modules.Hom.app
      (SheafOfModules.unitToPushforwardObjUnit (pullback.snd f g).toRingCatSheafHom) ⊤)
  rw [← pullbackSymmetry_hom_comp_snd, Scheme.Hom.comp_appTop]
  exact (ConcreteCategory.bijective_of_isIso (pullbackSymmetry g f).hom.appTop).comp hb

/-- If `Γ(V, 𝒪_V) → Γ(V ×_S C, 𝒪)` is bijective for every étale `V ⟶ S`, the étale direct
image `f_* 𝔾ₐ` is `𝔾ₐ`. -/
noncomputable def lowerStarGaSheafIsoOfBijective {C S : Scheme.{u}} (f : C ⟶ S)
    (hf : ∀ V : S.Etale, Function.Bijective (pullback.fst V.hom f).appTop) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj C.gaSheaf ≅ S.gaSheaf :=
  isoGaSheafOfSectionsAddEquiv _
    (fun V ↦ AddEquiv.ulift.trans (RingEquiv.ofBijective _ (hf V.unop)).symm.toAddEquiv)
    (fun V W g x ↦ by
      obtain ⟨y⟩ := x
      apply (RingEquiv.ofBijective _ (hf W.unop)).injective
      have h : ((MorphismProperty.Over.pullback @Etale ⊤ f).map g.unop).left ≫
          pullback.fst V.unop.hom f = pullback.fst W.unop.hom f ≫ g.unop.left :=
        pullback.lift_fst _ _ _
      change (RingEquiv.ofBijective _ (hf W.unop)) ((RingEquiv.ofBijective _ (hf W.unop)).symm
          (((MorphismProperty.Over.pullback @Etale ⊤ f).map g.unop).left.appTop y)) =
        (RingEquiv.ofBijective _ (hf W.unop))
          (g.unop.left.appTop ((RingEquiv.ofBijective _ (hf V.unop)).symm y))
      rw [RingEquiv.apply_symm_apply, RingEquiv.ofBijective_apply]
      have h2 := congrArg (fun φ ↦ ConcreteCategory.hom (Scheme.Hom.appTop φ)
        ((RingEquiv.ofBijective _ (hf V.unop)).symm y)) h
      simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] at h2
      refine Eq.trans ?_ h2
      congr 1
      exact ((RingEquiv.ofBijective _ (hf V.unop)).apply_symm_apply y).symm)

/-- The identification `f_* 𝔾ₐ ≅ 𝔾ₐ` is compatible with the Artin--Schreier maps. -/
@[reassoc]
lemma lowerStar_map_gaArtinSchreier_comp_lowerStarGaSheafIsoOfBijective_hom {C S : Scheme.{u}}
    (f : C ⟶ S) (hf : ∀ V : S.Etale, Function.Bijective (pullback.fst V.hom f).appTop)
    (p : ℕ) [Fact p.Prime] (hpS : (p : Γ(S, ⊤)) = 0) (hpC : (p : Γ(C, ⊤)) = 0) :
    (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (C.gaArtinSchreier p hpC) ≫
        (lowerStarGaSheafIsoOfBijective f hf).hom =
      (lowerStarGaSheafIsoOfBijective f hf).hom ≫ S.gaArtinSchreier p hpS := by
  ext V x
  obtain ⟨y⟩ := x
  apply ULift.ext
  have k (z : Γ(pullback V.unop.hom f, ⊤)) :
      (RingEquiv.ofBijective _ (hf V.unop)).symm (z ^ p - z) =
        (RingEquiv.ofBijective _ (hf V.unop)).symm z ^ p -
          (RingEquiv.ofBijective _ (hf V.unop)).symm z := by
    rw [map_sub, map_pow]
  exact k y

end Scheme

namespace Etale

open Scheme

/-- **The étale direct image of `𝔾ₐ` in a family of curves** (degree `0` case of
`properSmoothCurves_higherDirectImage_ga_frobeniusLinear`). For `f: C ⟶ S` proper and smooth
with geometrically connected fibres, on a base where the prime `p` vanishes, `H⁰(Rf_* 𝔾ₐ)` is
the universe lift of the étale sheaf of `𝒪_S`, with the map induced by `℘ = Frob - 1`
corresponding to `F - 1` for the Frobenius `F: x ↦ xᵖ`. -/
theorem properSmoothCurves_higherDirectImage_ga_frobeniusLinear_zero_aux
    {C S : Scheme.{u}} (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (p : ℕ) [Fact p.Prime] (hpS : (p : Γ(S, ⊤)) = 0) (hpC : (p : Γ(C, ⊤)) = 0) :
    ∃ (E : S.Modules) (_ : E.IsQuasicoherent) (_ : E.IsFiniteLocallyFree)
      (F : Scheme.Modules.etaleTensorSectionsSheaf E ⟶
        Scheme.Modules.etaleTensorSectionsSheaf E),
      (∀ (U : S.Etale) (a : Γ(U.left, ⊤))
        (e : Γ((Scheme.Modules.tensorPullback U.hom).obj E, ⊤)),
        F.hom.app (op U)
            ((((Scheme.Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
          (((Scheme.Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
            (F.hom.app (op U) e)) ∧
      ∃ e : (DerivedCategory.homologyFunctor _ 0).obj
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.obj
              ((DerivedCategory.singleFunctor _ 0).obj C.gaSheaf)) ≅
          (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Scheme.Modules.etaleTensorSectionsSheaf E),
        (DerivedCategory.homologyFunctor _ 0).map
            ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctor.map
              ((DerivedCategory.singleFunctor _ 0).map (C.gaArtinSchreier p hpC))) ≫ e.hom =
          e.hom ≫ (sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).map
            (F - 𝟙 _) := by
  have := Smooth.geometricallyReduced f
  have hf (V : S.Etale) : Function.Bijective (pullback.fst V.hom f).appTop :=
    bijective_appTop_pullback_fst_of_proper_flat f (fun _ ↦ inferInstance)
      (fun _ ↦ inferInstance) V.hom
  obtain ⟨b, hb, hs⟩ := Modules.exists_etaleTensorUnit_sections_natural_smul S
  let Φ := lowerStar AddCommGrpCat.{u + 1} f
  have : (SheafOfModules.unit S.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  refine ⟨SheafOfModules.unit S.ringCatSheaf, inferInstance,
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _,
    frobeniusOfSectionsAddEquiv _ b hb p hpS, fun U a e ↦ ?_,
    Φ.homologyRightDerivedFunctorObjSingleFunctorIso C.gaSheaf 0 ≪≫
      Φ.rightDerivedZeroIsoSelf.app C.gaSheaf ≪≫ lowerStarGaSheafIsoOfBijective f hf ≪≫
      (uliftIsoGaSheafOfSectionsAddEquiv _ b hb).symm, ?_⟩
  · rw [Modules.smul_apply, Modules.smul_apply]
    apply (b (op U)).injective
    rw [hs, apply_frobeniusOfSectionsAddEquiv_hom_app,
      apply_frobeniusOfSectionsAddEquiv_hom_app, hs, mul_pow]
  · simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Category.assoc]
    erw [Φ.homologyRightDerivedFunctorObjSingleFunctorIso_hom_naturality_assoc]
    rw [NatTrans.naturality_assoc,
      lowerStar_map_gaArtinSchreier_comp_lowerStarGaSheafIsoOfBijective_hom_assoc f hf p hpS hpC,
      gaArtinSchreier_comp_uliftIsoGaSheafOfSectionsAddEquiv_inv]

end Etale

end AlgebraicGeometry
