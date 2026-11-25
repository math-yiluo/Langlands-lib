/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Transport of integral lattice pairs along coefficient isomorphisms

Source: Bhatt--Scholze, Proposition 6.8.4(6), invariance of lattice pairs under
identifying the integral and rational coefficient rings.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false

private noncomputable def coefficientTensorIso
    (R S R' S' : CommRingCat.{u}) (a : R ⟶ S) (a' : R' ⟶ S')
    (eR : R' ≅ R) (eS : S' ≅ S) (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (M : ModuleCat.{u} R') :
    (ModuleCat.extendScalars a.hom).obj
        ((ModuleCat.restrictScalars eR.inv.hom).obj M) ≅
      (ModuleCat.restrictScalars eS.inv.hom).obj
        ((ModuleCat.extendScalars a'.hom).obj M) := by
  let σ := eR.symm.commRingCatIsoToRingEquiv
  let τ := eS.symm.commRingCatIsoToRingEquiv
  let N := (ModuleCat.restrictScalars eR.inv.hom).obj M
  let : Module R S := Module.compHom S a.hom
  let : Module R' S' := Module.compHom S' a'.hom
  have h (r : R) : τ (a r) = a' (σ r) := by
    apply eS.commRingCatIsoToRingEquiv.injective
    change eS.hom (eS.inv (a r)) = eS.hom (a' (eR.inv r))
    have q := ConcreteCategory.congr_hom hsquare (eR.inv r)
    have hr : eR.hom (eR.inv r) = r :=
      ConcreteCategory.congr_hom eR.inv_hom_id r
    have hs : eS.hom (eS.inv (a r)) = a r :=
      ConcreteCategory.congr_hom eS.inv_hom_id (a r)
    dsimp at q
    rw [hr] at q
    exact hs.trans q.symm
  have : RingHomInvPair σ.toRingHom σ.symm.toRingHom := by
    constructor
    · ext x; exact σ.symm_apply_apply x
    · ext x; exact σ.apply_symm_apply x
  have : RingHomInvPair σ.symm.toRingHom σ.toRingHom := by
    constructor
    · ext x; exact σ.apply_symm_apply x
    · ext x; exact σ.symm_apply_apply x
  let f : S ≃ₛₗ[σ.toRingHom] S' :=
    { τ.toAddEquiv with
      map_smul' := by
        intro r s
        change τ (a r * s) = a' (σ r) * τ s
        rw [map_mul, h] }
  let g : N ≃ₛₗ[σ.toRingHom] M :=
    { Equiv.refl _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let t := TensorProduct.congr f g
  let T := (ModuleCat.restrictScalars eS.inv.hom).obj
    ((ModuleCat.extendScalars a'.hom).obj M)
  let e : (ModuleCat.extendScalars a.hom).obj N ≃ₗ[S] T :=
    { t.toAddEquiv with
      map_smul' := by
        intro s x
        induction x using TensorProduct.inductionOn with
        | tmul r m =>
          change τ (s * (show S from r)) ⊗ₜ[R'] m =
            τ s • (τ (show S from r) ⊗ₜ[R'] m)
          rw [map_mul, TensorProduct.smul_tmul']
          rfl
        | add x y hx hy =>
          change t (s • (show (ModuleCat.extendScalars a.hom).obj N from x + y)) =
            s • (show T from t (x + y))
          rw [smul_add, map_add, map_add, smul_add]
          exact congrArg₂ (· + ·) hx hy }
  exact e.toModuleIso
private noncomputable def pushforwardSheafificationIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    [HasWeakSheafify K AddCommGrpCat.{u + 1}] [K.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K] [G.IsEquivalence]
    (R : Sheaf K RingCat.{u + 1}) (S : Sheaf J RingCat.{u + 1})
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (P : PresheafOfModules.{u + 1} R.obj) :
    (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).obj
        ((PresheafOfModules.pushforward (F := G) φ.hom).obj P) ≅
      (SheafOfModules.pushforward (F := G) φ).obj
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P) := by
  let T := (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj P
  let Q := (PresheafOfModules.pushforward (F := G) φ.hom).obj P
  let N := (SheafOfModules.pushforward (F := G) φ).obj T
  let g : Q ⟶ N.val :=
    (PresheafOfModules.pushforward (F := G) φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)).unit.app P)
  let f : (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).obj Q ⟶ N :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm g
  have hf : (SheafOfModules.toSheaf S).map f =
      (G.pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1} J K).hom.app
        P.presheaf := by
    dsimp only [f]
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm]
    apply Sheaf.hom_ext
    rw [Functor.pushforwardContinuousSheafificationCompatibility_hom_app_hom]
    rfl
  have : IsIso ((SheafOfModules.toSheaf S).map f) := by
    rw [hf]
    infer_instance
  have : IsIso f := isIso_of_reflects_iso f (SheafOfModules.toSheaf S)
  exact asIso f

private theorem coefficientTensorIso_hom_tmul
    (R S R' S' : CommRingCat.{u}) (a : R ⟶ S) (a' : R' ⟶ S')
    (eR : R' ≅ R) (eS : S' ≅ S) (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (M : ModuleCat.{u} R') (s : S) (m : (ModuleCat.restrictScalars eR.inv.hom).obj M) :
    (coefficientTensorIso R S R' S' a a' eR eS hsquare M).hom
      (s ⊗ₜ[R, a.hom] m) = eS.inv s ⊗ₜ[R', a'.hom] (show M from m) := rfl

attribute [irreducible] coefficientTensorIso

private noncomputable def coefficientTensorPresheafIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    {R S R' S' : Sheaf J CommRingCat.{u + 1}}
    (a : R ⟶ S) (a' : R' ⟶ S') (eR : R' ≅ R) (eS : S' ≅ S)
    (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R')) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a
      ((SheafOfModules.pushforward (F := 𝟭 C)
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eR.inv)).obj M) ≅
    (PresheafOfModules.pushforward (F := 𝟭 C)
      (((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eS.inv).hom)).obj
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a' M) := by
  let N := (SheafOfModules.pushforward (F := 𝟭 C)
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eR.inv)).obj M
  let er := (sheafToPresheaf J CommRingCat).mapIso eR
  let es := (sheafToPresheaf J CommRingCat).mapIso eS
  have square (V : Cᵒᵖ) : a'.hom.app V ≫ (es.app V).hom =
      (er.app V).hom ≫ a.hom.app V :=
    congrArg (fun t : R' ⟶ S ↦ t.hom.app V) hsquare
  refine PresheafOfModules.isoMk (fun V ↦ coefficientTensorIso
    (R.obj.obj V) (S.obj.obj V) (R'.obj.obj V) (S'.obj.obj V)
    (a.hom.app V) (a'.hom.app V) (er.app V) (es.app V) (square V)
    (M.val.obj V)) ?_
  intro V V' f
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (coefficientTensorIso (R.obj.obj V') (S.obj.obj V')
    (R'.obj.obj V') (S'.obj.obj V') (a.hom.app V') (a'.hom.app V')
    (er.app V') (es.app V') (square V') (M.val.obj V')).hom
      (SheafOfModules.changeOfRingsMap a N f
        ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] m)) =
    SheafOfModules.changeOfRingsMap a' M f
      ((coefficientTensorIso (R.obj.obj V) (S.obj.obj V)
        (R'.obj.obj V) (S'.obj.obj V) (a.hom.app V) (a'.hom.app V)
        (er.app V) (es.app V) (square V) (M.val.obj V)).hom
          ((1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (a.hom.app V).hom] m))
  erw [Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap a N f) 1 m,
    coefficientTensorIso_hom_tmul, coefficientTensorIso_hom_tmul]
  simp only [map_one]
  symm
  have hh := Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap a' M f) 1 m
  rw [map_one] at hh
  exact hh

attribute [irreducible] coefficientTensorPresheafIso

private noncomputable def coefficientPushforwardCancel
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Sheaf J RingCat.{u + 1}} (e : S ≅ R) (M : SheafOfModules.{u + 1} R) :
    (SheafOfModules.pushforward (F := 𝟭 C) e.inv).obj
      ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj M) ≅ M := by
  let N := (SheafOfModules.pushforward (F := 𝟭 C) e.inv).obj
    ((SheafOfModules.pushforward (F := 𝟭 C) e.hom).obj M)
  apply (SheafOfModules.fullyFaithfulForget R).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦
    (show N.val.obj V ≃ₗ[R.obj.obj V] M.val.obj V from
      { Equiv.refl _ with
        map_add' := fun _ _ ↦ rfl
        map_smul' := by
          intro r m
          change e.hom.hom.app V (e.inv.hom.app V r) • (show M.val.obj V from m) =
            r • (show M.val.obj V from m)
          rw [show e.hom.hom.app V (e.inv.hom.app V r) = r from
            ConcreteCategory.congr_hom
              (congrArg (fun t : R ⟶ R ↦ t.hom.app V) e.inv_hom_id) r] }).toModuleIso) ?_
  intro V V' f
  ext m
  rfl

attribute [irreducible] coefficientPushforwardCancel pushforwardSheafificationIso

set_option backward.isDefEq.respectTransparency true in
/-- A commuting square of coefficient isomorphisms transports a given integral lattice pair.
Source: Bhatt--Scholze, Proposition 6.8.4(6), lattice pairs and their rationalizations.
(auxiliary; not a blueprint node)

Proof: restrict both coefficient isomorphisms to the slice at U. Restrict the integral
module of P along the inverse integral isomorphism, obtaining an R-module M. Local finite
free generators transport along this isomorphism: their finite index sets are unchanged,
and restriction on the further slices is an equivalence, so it preserves the free
presentations. Thus M is finite locally free. On each object of the slice, the commuting
coefficient square identifies S tensor_R M with P's rationalization restricted along the
inverse rational isomorphism: the map sends s tensor m to eS.inv(s) tensor m. The balancing
relation follows from the commuting square; the map with eS.hom gives its inverse.
Both maps commute with restrictions, checked on pure tensors. Restriction along a ring
isomorphism preserves sheafification, by the sheafification universal property and its
inverse restriction. The tensor isomorphism therefore passes to module sheaves. Compose
with P.rationalization and the restriction of eL to U, and cancel the inverse rational
coefficient restrictions. This gives the required rationalization isomorphism to L.over U.
No nonzero rank or nonempty scheme is required. -/
theorem integral_lattice_pair_of_coefficient_iso {X : Scheme.{u}}
    {R S R' S' : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (a' : R' ⟶ S') (eR : R' ≅ R) (eS : S' ≅ S)
    (hsquare : a' ≫ eS.hom = eR.hom ≫ a)
    (L : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (L' : SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S'))
    (eL : L' ≅ (SheafOfModules.pushforward (F := 𝟭 X.ProEt)
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map eS.hom)).obj L)
    (U : X.ProEt) (P : IntegralLatticePair a' L' U) :
    Nonempty (IntegralLatticePair a L U) := by
  let K := Scheme.ProEt.topology X
  let J := K.over U
  let res := (Over.forget U).sheafPushforwardContinuous CommRingCat.{u + 1} J K
  let er := res.mapIso eR
  let es := res.mapIso eS
  let a₀ := latticeScalarMap a U
  let a'₀ := latticeScalarMap a' U
  have square : a'₀ ≫ es.hom = er.hom ≫ a₀ := by
    change res.map a' ≫ res.map eS.hom = res.map eR.hom ≫ res.map a
    simpa only [Functor.map_comp] using congrArg (fun t : R' ⟶ S ↦ res.map t) hsquare
  let forgetRing := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let erRing := forgetRing.mapIso er
  let esRing := forgetRing.mapIso es
  let M := (SheafOfModules.pushforward (F := 𝟭 (Over U)) erRing.inv).obj P.module
  have := P.locallyFree
  have hfree : M.IsFiniteLocallyFree :=
    finiteLocallyFree_restrict J _ _ erRing.symm P.module
  let T := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a'₀ P.module
  let t := coefficientTensorPresheafIso J a₀ a'₀ er es square P.module
  let ψ := SheafOfModules.pushforward (F := 𝟭 (Over U))
    (R := forgetRing.obj (S'.over U)) (S := forgetRing.obj (S.over U)) esRing.inv
  let χ := SheafOfModules.pushforward (F := 𝟭 (Over U))
    (R := forgetRing.obj (S.over U)) (S := forgetRing.obj (S'.over U)) esRing.hom
  let rationalization : SheafOfModules.changeOfRings.{u, u + 1, u + 1} a₀ M ≅
      ψ.obj (SheafOfModules.changeOfRings.{u, u + 1, u + 1} a'₀ P.module) :=
    (PresheafOfModules.sheafification (R := forgetRing.obj (S.over U)) (𝟙 _)).mapIso t ≪≫
      pushforwardSheafificationIso J J (𝟭 (Over U))
        (forgetRing.obj (S'.over U)) (forgetRing.obj (S.over U)) esRing.inv T
  let el : L'.over U ≅
      χ.obj (L.over U) :=
    (SheafOfModules.overFunctor
      ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S') U).mapIso eL
  refine ⟨{ module := M, locallyFree := hfree, rationalization := ?_ }⟩
  change SheafOfModules.changeOfRings.{u, u + 1, u + 1} a₀ M ≅ L.over U
  let r₂ := ψ.mapIso P.rationalization
  let r₃ := ψ.mapIso el
  let r₄ := coefficientPushforwardCancel J esRing (L.over U)
  exact rationalization ≪≫ r₂ ≪≫ r₃ ≪≫ r₄

end AlgebraicGeometry.ProEtale
