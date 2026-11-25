/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import WeilConjectures.AlgebraicGeometry.CondensedFiniteLocalSubmodules
import WeilConjectures.AlgebraicGeometry.ProEtaleLocalSubmoduleGluing

/-!
# Gluing local finite coefficient models after enlarging the field

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph,
overlap and gluing steps (auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

section ScalarComparison

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (g : Y ⟶ X)
  (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

omit [IsCommMonObj S] in
private lemma local_adjoint (P : Mod _ R) (M : Mod _ S)
    (t : (Mod.extendScalars φ).obj P ⟶ M) :
    (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map φ)).homEquiv _ _
      ((pullbackExtendScalarsIso g R S φ).inv.app P ≫
        ((upperStar Ab.{u + 1} g).mapMod S).map t) =
      ((upperStar Ab.{u + 1} g).mapMod R).map
        ((Mod.extendRestrictAdjunction φ).homEquiv _ _ t) ≫
          ((upperStar Ab.{u + 1} g).mapModComapIso φ).hom.app M := by
  let F := upperStar Ab.{u + 1} g
  let G := lowerStar Ab.{u + 1} g
  let adj := upperStarLowerStarAdjunction Ab.{u + 1} g
  let a := (Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction S)
  let b := (adj.mapModAdjunction R).comp
    (Mod.extendRestrictAdjunction (F.map φ))
  have : IsMonHom (adj.unitAlgHom R) := Adjunction.isMonHom_unitAlgHom adj R
  have : IsMonHom (adj.unitAlgHom S) := Adjunction.isMonHom_unitAlgHom adj S
  have hφ : adj.unitAlgHom R ≫ G.map (F.map φ) = φ ≫ adj.unitAlgHom S :=
    (adj.unit.naturality φ).symm
  let e : Mod.comap (F.map φ) ⋙
      (G.mapMod (F.obj R) ⋙ Mod.comap (adj.unitAlgHom R)) ≅
      (G.mapMod (F.obj S) ⋙ Mod.comap (adj.unitAlgHom S)) ⋙ Mod.comap φ :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr hφ) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm
  have huniq := (b.ofNatIsoRight e).homEquiv_naturality_right
    ((a.leftAdjointUniq (b.ofNatIsoRight e)).inv.app P)
    ((F.mapMod S).map t)
  rw [Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app] at huniq
  have hh : (b.ofNatIsoRight e).homEquiv _ _
      ((pullbackExtendScalarsIso g R S φ).inv.app P ≫ (F.mapMod S).map t) =
        a.homEquiv _ _ ((F.mapMod S).map t) := by
    rw [Adjunction.homEquiv_unit]
    exact huniq
  apply Mod.hom_ext
  apply (adj.homEquiv P.X _).injective
  have hhh := congrArg Mod.Hom.hom hh
  simp only [Adjunction.homEquiv_ofNatIsoRight_apply] at hhh
  dsimp only [a, b] at hhh
  simp only [Adjunction.comp_homEquiv] at hhh
  have he : (e.hom.app ((F.mapMod S).obj M)).hom = 𝟙 _ := by
    simp only [e, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Mod.comp_hom', Mod.comap_map_hom,
      Functor.mapModComapIso_hom_app_hom]
    change (𝟙 (G.obj (F.obj M.X))) ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  change (adj.homEquiv _ _
    (((Mod.extendRestrictAdjunction (F.map φ)).homEquiv _ _
      ((pullbackExtendScalarsIso g R S φ).inv.app P ≫ (F.mapMod S).map t)).hom)) ≫
        (e.hom.app ((F.mapMod S).obj M)).hom =
    (Mod.extendUnit φ P).hom ≫ adj.homEquiv _ _ (F.map t.hom) at hhh
  rw [he] at hhh
  change adj.homEquiv _ _ _ ≫ 𝟙 (G.obj (F.obj M.X)) = _ at hhh
  rw [Category.comp_id] at hhh
  refine hhh.trans ?_
  change (Mod.extendUnit φ P).hom ≫ adj.homEquiv _ _ (F.map t.hom) =
    adj.homEquiv _ _ (F.map ((Mod.extendUnit φ P).hom ≫ t.hom) ≫ 𝟙 _)
  rw [Category.comp_id, F.map_comp, adj.homEquiv_naturality_left]

end ScalarComparison

attribute [local irreducible] pullbackExtendScalarsIso

private lemma isIso_app_of_local_restriction {X : Scheme.{u}}
    {G G' : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} (φ : G ⟶ G')
    {W : Scheme.{u}} (g : W ⟶ X) [WeaklyEtale g]
    (h : IsIso ((localizationRestriction Ab.{u + 1} g inferInstance).map φ))
    (V : X.ProEt) (p : V.left ⟶ W) (hp : p ≫ g = V.hom) :
    IsIso (φ.hom.app (op V)) := by
  have hpweaklyEtale : WeaklyEtale p := by
    have : WeaklyEtale (p ≫ g) := hp ▸ V.prop
    exact WeaklyEtale.of_comp p g
  have h1 : IsIso (((localizationRestriction Ab.{u + 1} g inferInstance).map φ).hom.app
      (op (MorphismProperty.Over.mk ⊤ p hpweaklyEtale))) := inferInstance
  rw [localizationRestriction_map_hom_app] at h1
  have e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale g)).obj
      (MorphismProperty.Over.mk ⊤ p hpweaklyEtale) ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl _) (by simpa using hp.symm)
  exact @NatTrans.isIso_app_of_iso _ _ _ _ _ _ φ.hom _ _ e.op h1

private lemma module_isIso_of_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {P Q : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (t : P ⟶ Q) (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsIso (((upperStar Ab.{u + 1} (U.f i)).mapMod R).map t)) :
    IsIso t := by
  have (i : U.I₀) : WeaklyEtale (U.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ U.mem₀ (.mk i)
  have hlocal (i : U.I₀) :
      IsIso ((localizationRestriction Ab.{u + 1} (U.f i) inferInstance).map t.hom) := by
    have : IsIso ((upperStar Ab.{u + 1} (U.f i)).map t.hom) :=
      (Mod.forget _).map_isIso (((upperStar Ab.{u + 1} (U.f i)).mapMod R).map t)
    exact (NatIso.isIso_map_iff (upperStarIsoLocalizationRestriction _ (U.f i)
      inferInstance) t.hom).mp inferInstance
  have : IsIso t.hom := by
    refine Sheaf.isIso_of_isIso_app_of_mem _ t.hom fun V ↦
      ⟨_, Scheme.ProEt.ofArrows_baseChange_mem_topology V U.f U.mem₀, ?_⟩
    rintro T f ⟨-, a, -, ⟨i⟩, rfl⟩
    refine isIso_app_of_local_restriction t.hom (U.f i) (hlocal i) T
      (a.left ≫ pullback.snd V.hom (U.f i)) ?_
    rw [Category.assoc, ← pullback.condition]
    exact MorphismProperty.Over.w a
  have : IsIso ((Mod.forget R).map t) := ‹IsIso t.hom›
  exact isIso_of_reflects_iso t (Mod.forget R)

private lemma exists_scalar_model_of_compatible_local_monomorphisms
    (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [MonObj S] [IsCommMonObj R]
    (a : R ⟶ S) [IsMonHom a]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S)
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (L : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj R))
    (q : ∀ i, L i ⟶ ((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj
      ((Mod.comap a).obj M))
    (hq : ∀ i, Mono (q i))
    (hqΩ : ∀ i, IsIso (((Mod.extendRestrictAdjunction
      ((upperStar Ab.{u + 1} (U.f i)).map a)).homEquiv (L i)
        (((upperStar Ab.{u + 1} (U.f i)).mapMod S).obj M)).symm
          (q i ≫ ((upperStar Ab.{u + 1} (U.f i)).mapModComapIso a).hom.app M)))
    (hcompatible : ∀ i j, ∃ c :
      (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).obj (L i).X ≅
        (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).obj (L j).X,
      c.hom ≫ (upperStar Ab.{u + 1} (pullback.snd (U.f i) (U.f j))).map (q j).hom =
        (upperStar Ab.{u + 1} (pullback.fst (U.f i) (U.f j))).map (q i).hom ≫
          (upperStarCompIso Ab.{u + 1}
            (pullback.condition (f := U.f i) (g := U.f j))).hom.app
              ((Mod.comap a).obj M).X) :
    ∃ P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R,
      (∀ i, Nonempty (((upperStar Ab.{u + 1} (U.f i)).mapMod R).obj P ≅ L i)) ∧
      Nonempty ((Mod.extendScalars a).obj P ≅ M) := by
  obtain ⟨D⟩ := exists_module_of_compatible_local_monomorphisms
    X R ((Mod.comap a).obj M) U L q hq hcompatible
  let P := D.globalModule
  let j := D.hom
  let eP := D.localIso
  have hj := D.hom_eq
  let t : (Mod.extendScalars a).obj P ⟶ M :=
    ((Mod.extendRestrictAdjunction a).homEquiv P M).symm j
  have hlocal (i : U.I₀) : IsIso (((upperStar Ab.{u + 1} (U.f i)).mapMod S).map t) := by
    let B := upperStar Ab.{u + 1} (U.f i)
    let adj := Mod.extendRestrictAdjunction (B.map a)
    let d := (adj.homEquiv (L i) ((B.mapMod S).obj M)).symm
      (q i ≫ (B.mapModComapIso a).hom.app M)
    have hd : IsIso d := hqΩ i
    have ht : (pullbackExtendScalarsIso (U.f i) R S a).inv.app P ≫
        (B.mapMod S).map t =
        (Mod.extendScalars (B.map a)).map (eP i).hom ≫ d := by
      apply (adj.homEquiv _ _).injective
      rw [local_adjoint (U.f i) R S a P M t, adj.homEquiv_naturality_left]
      rw [show ((Mod.extendRestrictAdjunction a).homEquiv P M) t = j from
        Equiv.apply_symm_apply _ _]
      rw [hj i]
      simp only [d, Equiv.apply_symm_apply, Category.assoc]
      rfl
    have : IsIso ((pullbackExtendScalarsIso (U.f i) R S a).inv.app P ≫
        (B.mapMod S).map t) := by
      rw [ht]
      infer_instance
    have h : (B.mapMod S).map t =
        (pullbackExtendScalarsIso (U.f i) R S a).hom.app P ≫
          ((pullbackExtendScalarsIso (U.f i) R S a).inv.app P ≫
            (B.mapMod S).map t) := by simp
    rw [h]
    infer_instance
  have : IsIso t := module_isIso_of_cover t U hlocal
  exact ⟨P, (fun i ↦ ⟨eP i⟩), ⟨asIso t⟩⟩

/-- Finite affine local coefficient models glue after one finite enlargement.

Source: upstream ModuleObject/Colimit/TwoColimit.lean, (Obj) descent paragraph;
Stacks Tags 04TR, 04TQ and 03EL
(auxiliary; not a blueprint node).

Proof: descend the adjoints of the given local model isomorphisms to compatible
local monomorphisms at one finite coefficient stage. Glue their underlying abelian
subobjects by the kernel of the simultaneous local quotient map; lift the module
action using its proved local factorization property. The resulting local module
isomorphisms commute with the global inclusion into M restricted to the finite
coefficient ring. Transpose this inclusion by extension/restriction adjunction.
The pullback/scalar-extension comparison identifies its local adjoints with the
supplied invertible maps. The resulting global extension map is an isomorphism
because the pro-etale cover detects isomorphisms of sheaves, hence of modules.
Thus the original conclusion follows without gluing scalar-extension inverses or
imposing triple-overlap equations separately. The empty cover is included in the
same cover-detection and kernel argument. -/
theorem exists_finiteCoefficient_gluing_of_local_models
    (T X : Scheme.{u}) [QuasiSeparatedSpace X]
    (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (hfinite : Finite U.I₀) (haffine : ∀ i, IsAffine (U.X i))
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (U.X i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented
      ((upperStar Ab.{u + 1} (U.f i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, Nonempty ((Mod.extendScalars
      ((upperStar Ab.{u + 1} (U.f i)).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj
          (N i) ≅
      ((upperStar Ab.{u + 1} (U.f i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F)
      (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))),
      (∀ i, Nonempty (
        ((upperStar Ab.{u + 1} (U.f i)).mapMod
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ F))).obj P ≅
        (Mod.extendScalars ((upperStar Ab.{u + 1} (U.f i)).map
          ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjMap T ℓ hEF)))).obj (N i))) ∧
      Nonempty ((Mod.extendScalars
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj P ≅ M) := by
  obtain ⟨F, hEF, q, hq, hqΩ, hcompatible⟩ :=
    exists_finiteCoefficient_compatible_local_monomorphisms T X f ℓ M E U
      hfinite haffine N hN e
  obtain ⟨P, heP, ht⟩ := exists_scalar_model_of_compatible_local_monomorphisms
    X _ _ _ M U _ q hq hqΩ hcompatible
  exact ⟨F, hEF, P, heP, ht⟩

end AlgebraicGeometry.ProEtale
