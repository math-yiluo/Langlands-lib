/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Endomorphism
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilPathFrobeniusElement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# The local Frobenius and the Weil fundamental representation

Let `ℱ` be a lisse Weil sheaf on the curve `C₀`, `x` a closed point of degree `m` with geometric
point `xb`, and `π : F_xb ≅ F_t` a path to the base point. Transporting the stalk `ℱ_xb` with its
local Frobenius `Fₓ` along `π` gives the stalk `ℱ_t` with the operator `Φᵐ ρ_geom(h)`, where
`Φ` is the Frobenius of the Weil fundamental representation and `h` the loop at `t` obtained
from the local Frobenius loop `F_t ≅ F_xb ≅ F_{σᵐ ≫ xb} = F_{xb ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}`
(`AlgebraicGeometry.WeilGroup.BasePointData.frobeniusLoop`) and the iterate `β_m` of the path
`β : F_t ≅ F_{t ≫ Fr}` (`AlgebraicGeometry.WeilGroup.monoLinear_stalk_frobenius`).

The main step is the description of `Φᵐ` through the iterated Weil structure `φ_m`
(`AlgebraicGeometry.WeilGroup.frobPowStalk_frobPathPow`): for a path `δ : F_t ≅ F_{t ≫ Frᵐ}`
let `Ψ_m(δ)` be the transport along `δ` followed by `ℱ_{t ≫ Frᵐ} = ((Frᵐ)^* ℱ)_t` and the stalk
of `φ_m : (Frᵐ)^* ℱ ≅ ℱ`; then `Ψ_m(β_m) = Φᵐ`.
-/

@[expose] public section

universe u

-- The stalk functors of `WeilConjectures.WeilSheaf.Stalk` and
-- `WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy` are elaborated without this instance;
-- elaborating `Sheaf.Γ` through it here would produce terms which the kernel compares slowly.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

open CategoryTheory

namespace AlgebraicGeometry.WeilGroup

open ProEtale Scheme.FiniteEtale

variable {K : Type u} [Field K] [Finite K] {C : Scheme.{u}} [C.Over (Spec (.of K))]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))]
  {W : WeilGroup (C ↘ Spec (.of K))}
  (M : LisseMonodromy l (C ↘ Spec (.of K)).geometricFiber K)
  {B : BasePointData W}

/-- The iterated Weil structure `φ_m : (Frᵐ)^* ℱ ≅ ℱ` as an isomorphism of lisse sheaves. -/
noncomputable def _root_.AlgebraicGeometry.WeilSheaf.lisseFrobPowStr (F : WeilSheaf K l C)
    (hF : F.IsLisse) (n : ℕ) :
    (F.toLisse hF).upperStar l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom ≅
      F.toLisse hF :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    ((adicUpperStarIsoLowerStarInv l
      ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso).app _ ≪≫
      F.frobeniusPowIso n)

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The iterated Weil structure of the underlying lisse sheaf is that of the Weil sheaf. -/
lemma _root_.AlgebraicGeometry.WeilSheaf.lisseFrobPowStr_hom_hom (F : WeilSheaf K l C)
    (hF : F.IsLisse) (n : ℕ) :
    (F.lisseFrobPowStr hF n).hom.hom.hom = F.frobeniusPowStr n := by
  change ((adicUpperStarIsoLowerStarInv l _).hom.app _ ≫ (F.frobeniusPowIso n).hom).hom = _
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom]
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The Weil structure of the underlying lisse sheaf is that of the Weil sheaf. -/
lemma _root_.AlgebraicGeometry.WeilSheaf.lisseFrobStr_hom_hom_hom' (F : WeilSheaf K l C)
    (hF : F.IsLisse) : (F.lisseFrobStr hF).hom.hom.hom = F.frobeniusStr := by
  change ((adicUpperStarIsoLowerStarInv l _).hom.app _ ≫ F.obj.str.hom).hom = _
  rw [Mod.comp_hom', adicUpperStarIsoLowerStarInv_hom_app_hom]
  rfl

variable (B) in
/-- The operator `Ψ_n(δ)` on the stalk `ℱ_t`, for a path `δ : F_t ≅ F_{t ≫ Frⁿ}`: transport along
`δ`, the identification `ℱ_{t ≫ Frⁿ} = ((Frⁿ)^* ℱ)_t`, and the stalk of the iterated Weil
structure `φ_n`. -/
noncomputable def frobPowStalk (F : WeilSheaf K l C) (hF : F.IsLisse) (n : ℕ)
    (δ : fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom)) :
    (lisseStalk l B.t).obj (F.toLisse hF) ⟶ (lisseStalk l B.t).obj (F.toLisse hF) :=
  (M.mono δ).hom.app _ ≫
    (upperStarStalkIso l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom B.t
      F.obj.carrier.X).hom ≫
    (lisseStalk l B.t).map (F.lisseFrobPowStr hF n).hom

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- Associativity of the identifications `Γ(Spec, (t ≫ f ≫ g)^* G) ≅ Γ(Spec, t^* f^* g^* G)`. -/
lemma Γ_map_upperStarComp_comp {S P Z Y : Scheme.{u}} (t : S ⟶ P) (f : P ⟶ Z) (g : Z ⟶ Y)
    {h : P ⟶ Y} (e : f ≫ g = h) (G : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) :
    (Sheaf.Γ _ _).map ((upperStarComp _ (t ≫ f) g).hom.app G) ≫
        (Sheaf.Γ _ _).map ((upperStarComp _ t f).hom.app ((g)^*[_].obj G)) =
      (Sheaf.Γ _ _).map ((upperStarCongr (WeilCoefficients.{u} l)
          (show (t ≫ f) ≫ g = t ≫ h by rw [Category.assoc, e])).hom.app G) ≫
        (Sheaf.Γ _ _).map ((upperStarComp _ t h).hom.app G) ≫
        (Sheaf.Γ _ _).map ((t)^*[_].map ((upperStarFactor _ e).hom.app G)) := by
  subst e
  rw [upperStarFactor_rfl, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    upperStarComp_hom_app_comp_upperStarComp_hom_app]

/-- Changing the path in `Ψ_n` multiplies by the monodromy of a loop. -/
lemma frobPowStalk_eq_mono_comp (F : WeilSheaf K l C) (hF : F.IsLisse) (n : ℕ)
    (δ δ' : fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ n).asIso.hom)) :
    frobPowStalk M B F hF n δ =
      (M.mono (δ ≪≫ δ'.symm)).hom.app _ ≫ frobPowStalk M B F hF n δ' := by
  have : δ = (δ ≪≫ δ'.symm) ≪≫ δ' := by simp
  conv_lhs => rw [this]
  simp only [frobPowStalk, M.mono_trans, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

/-- `Ψ_m(δ)` followed by the Frobenius `Φ` is `Ψ_{m+1}(δ ≫ (Frᵐ)_* β)`: this is
`φ_{m+1} = φ ∘ Fr^* φ_m` on the stalks. -/
theorem frobPowStalk_comp_frobStalkIso (F : WeilSheaf K l C) (hF : F.IsLisse) (m : ℕ)
    (δ : fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom)) :
    frobPowStalk M B F hF m δ ≫ (frobStalkIso M B F hF).hom =
      frobPowStalk M B F hF (m + 1) (δ ≪≫
        pullbackPathIso ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom B.frobPath ≪≫
        eqToIso (by rw [pow_succ, Aut.mul_asIso, Iso.trans_hom, Category.assoc])) := by
  set Fr := (C ↘ Spec (.of K)).geometricGaloisFrobenius
  have e : Fr.asIso.hom ≫ (Fr ^ m).asIso.hom = (Fr ^ (m + 1)).asIso.hom := by
    rw [pow_succ, Aut.mul_asIso, Iso.trans_hom]
  -- naturality of the transport along `β` with respect to `φ_m`
  have n₁ : (lisseStalk l B.t).map (F.lisseFrobPowStr hF m).hom ≫
      (M.mono B.frobPath).hom.app (F.toLisse hF) =
      (M.mono B.frobPath).hom.app _ ≫ (lisseStalk l _).map (F.lisseFrobPowStr hF m).hom :=
    (M.mono B.frobPath).hom.naturality _
  -- naturality of `ℱ_{t ≫ Fr} = (Fr^* ℱ)_t` with respect to `φ_m`
  have n₂ := upperStarStalkIso_hom_naturality l Fr.asIso.hom B.t
    (F.lisseFrobPowStr hF m).hom.hom.hom
  -- compatibility of the transport with pullback along `Frᵐ`
  have n₃ := M.mono_upperStar (Fr ^ m).asIso.hom B.frobPath (F.toLisse hF)
  -- `φ_{m+1} = φ ∘ Fr^* φ_m`
  have n₄ := F.upperStarFactor_hom_app_comp_frobeniusPowStr_succ m e
  have hE := M.mono_eqToIso_hom_app (show (B.t ≫ Fr.asIso.hom) ≫ (Fr ^ m).asIso.hom =
    B.t ≫ (Fr ^ (m + 1)).asIso.hom by rw [Category.assoc, e]) (F.toLisse hF)
  have hC := Γ_map_upperStarComp_comp (l := l) B.t Fr.asIso.hom (Fr ^ m).asIso.hom e F.obj.carrier.X
  simp only [frobPowStalk, frobStalkIso, M.mono_trans, Iso.trans_hom, NatTrans.comp_app,
    Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  congr 1
  erw [reassoc_of% n₁, ← reassoc_of% n₃]
  congr 1
  erw [reassoc_of% n₂, hE]
  have h₁ : (lisseStalk l B.t).map (F.lisseFrobStr hF).hom =
      (Sheaf.Γ _ _).map ((B.t)^*[_].map F.frobeniusStr) := by
    change (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.lisseFrobStr hF).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobStr_hom_hom_hom']
  have h₂ : (lisseStalk l B.t).map (F.lisseFrobPowStr hF (m + 1)).hom =
      (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.frobeniusPowStr (m + 1))) := by
    change (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.lisseFrobPowStr hF (m + 1)).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  rw [h₁, h₂, ← n₄]
  simp only [upperStarStalkIso, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp]
  rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  erw [reassoc_of% hC]

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- The identifications `(t ≫ g)^* ≅ t^* g^*` and `g^* ≅ 𝟭` for `g = 𝟙` compose to the
identity. -/
lemma upperStar_id_coherence {S P : Scheme.{u}} (t : S ⟶ P) {g : P ⟶ P} (p : g = 𝟙 P)
    (h : t = t ≫ g) (X : Sheaf (Scheme.ProEt.topology P) (WeilCoefficients.{u} l)) :
    (upperStarCongr _ h).hom.app X ≫ (upperStarComp _ t g).hom.app X ≫
        (t)^*[_].map ((upperStarCongr _ p).hom.app X ≫ (upperStarId _ P).hom.app X) = 𝟙 _ := by
  have n := upperStarCongr_hom_app_comp_upperStarComp_hom_app' (WeilCoefficients.{u} l) t p X
  rw [Functor.map_comp, ← reassoc_of% n, upperStarComp_id_right]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj, Functor.id_obj]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Iso.trans_hom, ← Iso.trans_hom,
    upperStarCongr_trans, upperStarCongr_trans]
  simp [upperStarCongr]

/-- `Ψ_0(β_0)` is the identity: `φ_0` is the identification `(𝟙)^* ≅ 𝟭`. -/
theorem frobPowStalk_zero (F : WeilSheaf K l C) (hF : F.IsLisse) :
    frobPowStalk M B F hF 0 (B.frobPathPow 0) = 𝟙 _ := by
  set Fr := (C ↘ Spec (.of K)).geometricGaloisFrobenius
  have p : (Fr ^ 0).asIso.hom = 𝟙 _ := by rw [pow_zero]; rfl
  have h : B.t = B.t ≫ (Fr ^ 0).asIso.hom := by rw [p, Category.comp_id]
  have h₀ : B.frobPathPow 0 = eqToIso (congrArg fiber h) := rfl
  have h₂ : (lisseStalk l B.t).map (F.lisseFrobPowStr hF 0).hom =
      (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.frobeniusPowStr 0)) := by
    change (Sheaf.Γ _ _).map ((B.t)^*[_].map (F.lisseFrobPowStr hF 0).hom.hom.hom) = _
    rw [WeilSheaf.lisseFrobPowStr_hom_hom]
  simp only [frobPowStalk, h₀, h₂, F.frobeniusPowStr_zero p, upperStarStalkIso,
    Functor.mapIso_hom, Iso.app_hom, Functor.map_comp]
  rw [M.mono_eqToIso_hom_app h]
  simp only [← Functor.map_comp]
  erw [upperStar_id_coherence (l := l) B.t p h]
  exact CategoryTheory.Functor.map_id _ _

/-- **`Ψ_m(β_m) = Φᵐ`**: the transport along the iterated path `β_m` followed by the iterated
Weil structure `φ_m` is the `m`-th power of the Frobenius `Φ` of the Weil fundamental
representation. -/
theorem frobPowStalk_frobPathPow (F : WeilSheaf K l C) (hF : F.IsLisse) (m : ℕ) :
    ((WeilCoefficients.toModuleCat l).map (frobPowStalk M B F hF m (B.frobPathPow m))).hom =
      ((frobStalk M B F hF) ^ m).toLinearMap := by
  induction m with
  | zero =>
    rw [frobPowStalk_zero, CategoryTheory.Functor.map_id, pow_zero]
    rfl
  | succ m ih =>
    have h := frobPowStalk_comp_frobStalkIso M F hF m (B.frobPathPow m)
    rw [show B.frobPathPow (m + 1) = B.frobPathPow m ≪≫ pullbackPathIso
      ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom B.frobPath ≪≫ eqToIso (by
        rw [pow_succ, Aut.mul_asIso, Iso.trans_hom, Category.assoc]) from rfl, ← h,
      CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, ih, pow_succ']
    rfl

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The identification of stalks of a Weil sheaf along an equality of geometric points. -/
lemma eqToIso_stalkObj_hom (F : WeilSheaf K l C) (hF : F.IsLisse)
    {y z : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber} (h : y = z) :
    (eqToIso (congrArg F.stalkObj h)).hom =
      (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app (F.toLisse hF).obj.X) := by
  subst h
  simp [upperStarCongr]
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The isomorphism `ℱ_{s ≫ Frᵐ} ≅ ℱ_s` of the iterated Weil structure, through
`ℱ_{s ≫ Frᵐ} = ((Frᵐ)^* ℱ)_s`. -/
lemma stalkObjFrobeniusPowIso_hom_eq (F : WeilSheaf K l C) (hF : F.IsLisse) (m : ℕ)
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) :
    (F.stalkObjFrobeniusPowIso m s).hom =
      (upperStarStalkIso l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom s
        (F.toLisse hF).obj.X).hom ≫ (stalkFunctor l s).map (F.frobeniusPowStr m) := by
  simp only [WeilSheaf.stalkObjFrobeniusPowIso, upperStarStalkIso, Functor.mapIso_hom,
    Iso.trans_hom, Iso.app_hom, Functor.map_comp, WeilSheaf.frobeniusPowStr]
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The reparametrisation of the stalk of a Weil sheaf is that of its underlying lisse sheaf. -/
lemma stalkObjSpecFrobeniusPowIso_eq (F : WeilSheaf K l C) (hF : F.IsLisse) (m : ℕ)
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) :
    F.stalkObjSpecFrobeniusPowIso m s =
      reparamStalkIso l (specGeometricFrobenius K ^ m).asIso s (F.toLisse hF).obj.X :=
  rfl

/-- The loop `F_t ≅ F_s ≅ F_{σᵐ ≫ s} = F_{s ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}` at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s`, for a path `π : F_s ≅ F_t`. For a closed point this is
`AlgebraicGeometry.WeilGroup.BasePointData.frobeniusLoop`. -/
noncomputable def frobeniusLoopAt
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius K ^ m).asIso.hom ≫ s) (π : fiber s ≅ fiber B.t) :
    fiber B.t ≅ fiber (B.t ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom) :=
  π.symm ≪≫ (fiberReparamIso (specGeometricFrobenius K ^ m).asIso s).symm ≪≫
    eqToIso (congrArg fiber hs.symm) ≪≫
    pullbackPathIso ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom π

/-- Transport along a path `π : F_s ≅ F_t` intertwines the operator
`ℱ_s ≅ ℱ_{σᵐ ≫ s} = ℱ_{s ≫ Frᵐ} = ((Frᵐ)^* ℱ)_s ⟶ ℱ_s` of the iterated Weil structure with `Ψ_m`
of the loop `frobeniusLoopAt`. -/
theorem mono_comp_frobPowStalk_frobeniusLoopAt (F : WeilSheaf K l C) (hF : F.IsLisse)
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius K ^ m).asIso.hom ≫ s) (π : fiber s ≅ fiber B.t) :
    (M.mono (fiberReparamIso (specGeometricFrobenius K ^ m).asIso s)).inv.app (F.toLisse hF) ≫
        (M.mono (eqToIso (congrArg fiber hs.symm))).hom.app (F.toLisse hF) ≫
        (upperStarStalkIso l ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom s
          F.obj.carrier.X).hom ≫
        (lisseStalk l s).map (F.lisseFrobPowStr hF m).hom ≫ (M.mono π).hom.app (F.toLisse hF) =
      (M.mono π).hom.app (F.toLisse hF) ≫
        frobPowStalk M B F hF m (frobeniusLoopAt s m hs π) := by
  rw [frobPowStalk, frobeniusLoopAt]
  exact M.reparam_comp_upperStar_comp_mono _ _ hs π _ _

omit [Finite K] [Fact (ringChar K ≠ l)] [IsCurve (C ↘ Spec (.of K))] in
/-- The `ℚ̄_ℓ`-linear map underlying a morphism of `WeilCoefficients`. -/
lemma toModuleCat_map_hom_apply {A A' : WeilCoefficients.{u} l} (f : A ⟶ A') (x : A) :
    ((WeilCoefficients.toModuleCat l).map f).hom x = f.hom x :=
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The Frobenius of the stalk at a geometric point `s` with `s ≫ Frᵐ = σᵐ ≫ s`, on the
underlying sheaves: the reparametrisation `ℱ_s ≅ ℱ_{σᵐ ≫ s}`, the identification
`ℱ_{σᵐ ≫ s} = ℱ_{s ≫ Frᵐ} = ((Frᵐ)^* ℱ)_s` and the stalk of `φ_m`. -/
theorem stalkAt_frobenius_apply (F : WeilSheaf K l C) (hF : F.IsLisse)
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius K ^ m).asIso.hom ≫ s) (v : (F.stalkAt s m hs).carrier) :
    (F.stalkAt s m hs).frobenius v =
      ((WeilCoefficients.toModuleCat l).map ((stalkFunctor l s).map
        (F.lisseFrobPowStr hF m).hom.hom.hom)).hom
      (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l
        ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom s (F.toLisse hF).obj.X).hom).hom
        (((WeilCoefficients.toModuleCat l).map
          ((Sheaf.Γ _ _).map ((upperStarCongr _ hs.symm).hom.app (F.toLisse hF).obj.X))).hom
          (((WeilCoefficients.toModuleCat l).map
            (reparamStalkIso l (specGeometricFrobenius K ^ m).asIso s (F.toLisse hF).obj.X).inv).hom
              v))) := by
  rw [show (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) from rfl]
  erw [show ∀ e : F.stalkObj s ≅ F.stalkObj s, WeilCoefficients.linearEquivOfIso e v =
      ((WeilCoefficients.toModuleCat l).map e.hom).hom v from fun _ ↦ rfl]
  rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, eqToIso_stalkObj_hom F hF hs.symm,
    stalkObjFrobeniusPowIso_hom_eq F hF, stalkObjSpecFrobeniusPowIso_eq F hF,
    WeilSheaf.lisseFrobPowStr_hom_hom, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, ModuleCat.hom_comp,
    ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearMap.comp_apply]
  rfl

omit [IsCurve (C ↘ Spec (.of K))] in
private theorem frobenius_reparam_step (F : WeilSheaf K l C) (hF : F.IsLisse)
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius K ^ m).asIso.hom ≫ s)
    (v : (F.stalkAt s m hs).carrier) :
    ((WeilCoefficients.toModuleCat l).map ((lisseStalk l s).map (F.lisseFrobPowStr hF m).hom)).hom
      (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l (((C ↘ Spec (.of
        K)).geometricGaloisFrobenius ^ m).asIso.hom) s (F.toLisse hF).obj.X).hom).hom
        (((WeilCoefficients.toModuleCat l).map
          ((M.mono (eqToIso (congrArg fiber hs.symm))).hom.app (F.toLisse hF))).hom
          (((WeilCoefficients.toModuleCat l).map
            ((M.mono (fiberReparamIso (specGeometricFrobenius K ^ m).asIso s)).inv.app (F.toLisse
              hF))).hom v))) =
    ((WeilCoefficients.toModuleCat l).map ((stalkFunctor l s).map (F.lisseFrobPowStr hF
      m).hom.hom.hom)).hom
      (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l (((C ↘ Spec (.of
        K)).geometricGaloisFrobenius ^ m).asIso.hom) s (F.toLisse hF).obj.X).hom).hom
        (((WeilCoefficients.toModuleCat l).map
          ((Sheaf.Γ _ _).map ((upperStarCongr _ hs.symm).hom.app (F.toLisse hF).obj.X))).hom
          (((WeilCoefficients.toModuleCat l).map (reparamStalkIso l
            (specGeometricFrobenius K ^ m).asIso s (F.toLisse hF).obj.X).inv).hom v))) := by
  have hcongr
      {y z : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber}
      (h : y = z) (G : LisseSheaf l (C ↘ Spec (.of K)).geometricFiber) :
      (M.mono (eqToIso (congrArg fiber h))).hom.app G =
        (Sheaf.Γ _ _).map ((upperStarCongr _ h).hom.app G.obj.X) := by
    subst h
    simp [M.mono_refl, upperStarCongr]
    rfl
  have e₃ : (M.mono (fiberReparamIso (specGeometricFrobenius K ^ m).asIso s)).app (F.toLisse hF) =
    reparamStalkIso l (specGeometricFrobenius K ^ m).asIso s (F.toLisse hF).obj.X :=
    Iso.ext (M.mono_reparam (specGeometricFrobenius K ^ m).asIso s (F.toLisse hF))
  have h₁ : ((WeilCoefficients.toModuleCat l).map
      ((M.mono (fiberReparamIso (specGeometricFrobenius K ^ m).asIso s)).inv.app
        (F.toLisse hF))).hom v =
      ((WeilCoefficients.toModuleCat l).map (reparamStalkIso l
        (specGeometricFrobenius K ^ m).asIso s (F.toLisse hF).obj.X).inv).hom v := by
    rw [← Iso.app_inv, e₃]
    rfl
  have h₂ : ∀ w, ((WeilCoefficients.toModuleCat l).map
      ((M.mono (eqToIso (congrArg fiber hs.symm))).hom.app (F.toLisse hF))).hom w =
      ((WeilCoefficients.toModuleCat l).map
        ((Sheaf.Γ _ _).map ((upperStarCongr _ hs.symm).hom.app (F.toLisse hF).obj.X))).hom w := fun
          w ↦ by
    rw [hcongr]
    rfl
  rw [h₁, h₂]
  rfl

/-- **The local Frobenius transported to the base point**: transport along a path
`π : F_s ≅ F_t` carries the Frobenius of the stalk at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s` to `Ψ_m` of the loop `frobeniusLoopAt`. -/
theorem monoLinear_stalkAt_frobenius (F : WeilSheaf K l C) (hF : F.IsLisse)
    (s : Spec (.of (AlgebraicClosure K)) ⟶ (C ↘ Spec (.of K)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((C ↘ Spec (.of K)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius K ^ m).asIso.hom ≫ s) (π : fiber s ≅ fiber B.t)
    (v : (F.stalkAt s m hs).carrier) :
    M.monoLinear π (F.toLisse hF) ((F.stalkAt s m hs).frobenius v) =
      ((WeilCoefficients.toModuleCat l).map
        (frobPowStalk M B F hF m (frobeniusLoopAt s m hs π))).hom (M.monoLinear π _ v) := by
  rw [stalkAt_frobenius_apply F hF, ← frobenius_reparam_step M F hF s m hs v,
    M.reparam_comp_upperStar_comp_mono_apply _ _ hs π (F.toLisse hF) (F.lisseFrobPowStr hF m).hom v,
    frobPowStalk, frobeniusLoopAt,
    M.mono_comp_upperStar_comp_apply]

omit [IsCurve (C ↘ Spec (.of K))] in
/-- The local Frobenius of the stalk at a closed point is that of the stalk at the attached
geometric point. (Stated through `congrArg`: the kernel checks the direct definitional
unfolding slowly.) -/
lemma stalk_frobenius_apply (F : WeilSheaf K l C) (x : C.finitePoints)
    (v : (F.stalk x).carrier) :
    (F.stalk x).frobenius v = (F.stalkAt _ _
      ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
        x)).frobenius v :=
  congrArg (fun f : (F.stalk x).carrier ≃ₗ[PadicAlgCl l] (F.stalk x).carrier ↦ f v) rfl

/-- The local Frobenius loop at a closed point is `frobeniusLoopAt` at the attached geometric
point. -/
lemma frobeniusLoop_eq_frobeniusLoopAt (x : C.finitePoints)
    (π : fiber ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) ≅ fiber B.t) :
    B.frobeniusLoop x π = frobeniusLoopAt _ _
      ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x)
        π :=
  rfl

/-- **The local Frobenius at a closed point and the Weil fundamental representation.** For a
closed point `x` of degree `m` and a path `π : F_xb ≅ F_t`, transport along `π` carries the
local Frobenius `Fₓ` on `ℱ_xb` to `Φᵐ ρ_geom(h)`, where `h` is the local Frobenius loop
followed by `β_m⁻¹` (`situation-weil`). -/
theorem monoLinear_stalk_frobenius (F : WeilSheaf K l C) (hF : F.IsLisse) (x : C.finitePoints)
    (π : fiber ((C ↘ Spec (.of K)).geometricFiberPointOfFinitePoint x) ≅ fiber B.t)
    (v : (F.stalk x).carrier) :
    M.monoLinear π (F.toLisse hF) ((F.stalk x).frobenius v) =
      (frobStalk M B F hF ^ (C ↘ Spec (.of K)).degreeOver x.1)
        (M.monoLinear (B.frobeniusLoop x π ≪≫ (B.frobPathPow _).symm) (F.toLisse hF)
          (M.monoLinear π (F.toLisse hF) v)) := by
  rw [stalk_frobenius_apply, monoLinear_stalkAt_frobenius, frobeniusLoop_eq_frobeniusLoopAt,
    frobPowStalk_eq_mono_comp M F hF _ _ (B.frobPathPow _), CategoryTheory.Functor.map_comp,
    ModuleCat.hom_comp, LinearMap.comp_apply, frobPowStalk_frobPathPow]
  rfl

end AlgebraicGeometry.WeilGroup
