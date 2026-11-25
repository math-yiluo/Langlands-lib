/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupResolutionData
import WeilConjectures.AlgebraicGeometry.ModuleCupGodementPairing
import WeilConjectures.AlgebraicGeometry.ModuleCupFlasqueAcyclicity
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

/-! # Existence of a computing tensor-paired resolution

Source: Stacks Project, Cohomology of Sheaves, Section 20.31, Tags 0FKU and 0FKV.
(blueprint: lem-sc-module-cup-pairing-exists)
-/

@[expose] public section

universe uM
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Equip a flasque resolution with a computing injective comparison. -/
private def computingFlasqueResolution {X : Scheme.{uM}} {F : X.Modules}
    (K : CochainComplex X.Modules ℕ)
    (a : (CochainComplex.single₀ X.Modules).obj F ⟶ K) [QuasiIso a]
    (hK : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K.X n))) :
    CupAcyclicResolution F := by
  let : EnoughInjectives (SheafOfModules.{uM} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) := by
    change PreservesFiniteLimits
      (SheafOfModules.evaluation.{uM} (moduleRings X.toRingedSpace) (op ⊤))
    infer_instance
  let I := injectiveResolution F
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 F) I a
  have hA : ∀ n, (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightAcyclic
      (K.X n) := by
    intro n q
    have := hK n
    exact moduleCup_flasque_acyclicity X (K.X n) (q + 1) (by omega)
  have := Functor.quasiIso_map_of_rightAcyclic_nat
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) φ hA
      (fun _ ↦ Functor.rightAcyclic_of_injective _)
  exact {
    K := K
    augmentation := a
    quasiIso := inferInstance
    I := I
    comparison := φ
    over := by simp [φ]
    computes := fun n ↦ inferInstance }

private theorem supportedNat {X : Scheme.{uM}} (K : CochainComplex X.Modules ℤ)
    [K.IsStrictlyGE 0] : K.IsStrictlySupported ComplexShape.embeddingUpNat := by
  constructor
  intro i hi
  refine K.isZero_of_isStrictlyGE 0 i ?_
  by_contra h
  exact hi i.toNat (by
    change (i.toNat : ℤ) = i
    exact Int.toNat_of_nonneg (by omega))

private theorem restrictionQuasiIso {X : Scheme.{uM}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) [QuasiIso f]
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] :
    QuasiIso (HomologicalComplex.restrictionMap f ComplexShape.embeddingUpNat) := by
  let e := ComplexShape.embeddingUpNat
  have := supportedNat K
  have := supportedNat L
  have : IsIso (K.restrictionToTruncGE' e) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (L.restrictionToTruncGE' e) :=
    HomologicalComplex.Hom.isIso_of_components _
  have h : QuasiIso (HomologicalComplex.truncGEMap f e) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff f e).2 (fun _ _ _ ↦ inferInstance)
  have : QuasiIso (HomologicalComplex.truncGE'Map f e) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ e).1 h
  have hcomp : QuasiIso (K.restrictionToTruncGE' e ≫
      HomologicalComplex.truncGE'Map f e) := inferInstance
  rw [HomologicalComplex.restrictionToTruncGE'_naturality] at hcomp
  exact quasiIso_of_comp_right _ (L.restrictionToTruncGE' e)

private def natAugmentation {X : Scheme.{uM}} {F : X.Modules}
    {K : CochainComplex X.Modules ℤ}
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K) :
    (CochainComplex.single₀ X.Modules).obj F ⟶ K.restriction ComplexShape.embeddingUpNat :=
  (CochainComplex.fromSingle₀Equiv _ F).symm ⟨a.f 0, by
    change a.f 0 ≫ K.d 0 1 = 0
    rw [a.comm 0 1]
    simp⟩

private def singleNatIso {X : Scheme.{uM}} (F : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj F ≅
      ((CochainComplex.singleFunctor X.Modules 0).obj F).restriction
        ComplexShape.embeddingUpNat := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ ?_) ?_
  · exact eqToIso (by
      change ((HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj F).X n =
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F).X (n : ℤ)
      by_cases hn : n = 0
      · subst n; rfl
      · simp [HomologicalComplex.single, hn])
  · intro i j hij
    simp [HomologicalComplex.restriction]

private theorem natAugmentation_quasiIso {X : Scheme.{uM}} {F : X.Modules}
    {K : CochainComplex X.Modules ℤ}
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
    [QuasiIso a] [K.IsStrictlyGE 0] : QuasiIso (natAugmentation a) := by
  have := restrictionQuasiIso a
  have h : natAugmentation a = (singleNatIso F).hom ≫
      HomologicalComplex.restrictionMap a ComplexShape.embeddingUpNat := by
    apply (CochainComplex.fromSingle₀Equiv _ F).injective
    apply Subtype.ext
    simp [natAugmentation, singleNatIso, HomologicalComplex.restrictionMap,
      ComplexShape.embeddingUpNat]
    rfl
  rw [h]
  infer_instance

private def tensorChainSectionPair {X : Scheme.{uM}} [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (r s : ℕ) (V : X.Opens) :
    Γ(K.X (r : ℤ), V) →ₗ[Γ(X, V)] Γ(L.X (s : ℤ), V) →ₗ[Γ(X, V)]
      Γ(M.X ((r + s : ℕ) : ℤ), V) :=
  TensorProduct.curry
    (((HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
      (by simp) ≫ t.f _).val.app (op V)).hom.comp (tensorSectionsMap _ _ V))

private theorem tensorChainSectionPair_apply {X : Scheme.{uM}}
    [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (r s : ℕ) (V : X.Opens)
    (a : Γ(K.X (r : ℤ), V)) (b : Γ(L.X (s : ℤ), V)) :
    tensorChainSectionPair K L M t r s V a b =
      (t.f _).val.app (op V)
        ((HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
          (by simp)).val.app (op V) (tmulSection a b)) := by
  simp [tensorChainSectionPair, TensorProduct.curry_apply]
  rfl

private theorem app_val_apply {X : Scheme.{uM}} {A B : X.Modules}
    (f : A ⟶ B) (V : X.Opens) (z : Γ(A, V)) :
    f.app V z = f.val.app (op V) z := rfl

private theorem tensorSection_restriction {X : Scheme.{uM}} {A B C : X.Modules}
    (f : A ⊗ B ⟶ C) (V W : X.Opens) (h : W ≤ V)
    (x : Γ(A, V)) (y : Γ(B, V)) :
    C.presheaf.map (homOfLE h).op (f.app V (tmulSection x y)) =
      f.app W (tmulSection (A.presheaf.map (homOfLE h).op x)
        (B.presheaf.map (homOfLE h).op y)) := by
  rw [← Hom.app_presheaf_map f, tmulSection_map]

private theorem val_id_apply {X : Scheme.{uM}} (A : X.Modules)
    (V : X.Opens) (z : Γ(A, V)) : (𝟙 A : A ⟶ A).val.app (op V) z = z := rfl

private theorem tensorChainSectionPair_transport {X : Scheme.{uM}}
    [MonoidalPreadditive X.Modules] (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (r s n : ℕ) (h : r + s = n)
    (V : X.Opens) (x : Γ(K.X (r : ℤ), V)) (y : Γ(L.X (s : ℤ), V)) :
    (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ)) h)).val.app (op V)
      (tensorChainSectionPair K L M t r s V x y) =
      (t.f (n : ℤ)).val.app (op V)
        ((HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) (n : ℤ)
          (by exact_mod_cast h)).val.app (op V) (tmulSection x y)) := by
  subst n
  simpa only [eqToHom_refl, val_id_apply] using
    tensorChainSectionPair_apply K L M t r s V x y

private theorem app_zsmul_apply {X : Scheme.{uM}} {A B : X.Modules}
    (n : ℤ) (f : A ⟶ B) (V : X.Opens) (z : Γ(A, V)) :
    (n • f).app V z = n • f.app V z := by
  let e : (A ⟶ B) →+ (Γ(A, V) →+ Γ(B, V)) :=
    { toFun := fun f ↦ (f.app V).hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact congrArg (fun f : Γ(A, V) →+ Γ(B, V) ↦ f z) (e.map_zsmul n f)

private theorem tensorChain_leibniz {X : Scheme.{uM}} [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (p q : ℤ) (V : X.Opens)
    (x : Γ(K.X p, V)) (y : Γ(L.X q, V)) :
    (M.d (p + q) (p + q + 1)).app V
      ((t.f (p + q)).app V
        ((HomologicalComplex.ιTensorObj K L p q (p + q) rfl).app V (tmulSection x y))) =
      (t.f (p + q + 1)).app V
        ((HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by omega)).app V
          (tmulSection ((K.d p (p + 1)).app V x) y)) +
      p.negOnePow • (t.f (p + q + 1)).app V
        ((HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by omega)).app V
          (tmulSection x ((L.d q (q + 1)).app V y))) := by
  have hd : HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
      (HomologicalComplex.tensorObj K L).d (p + q) (p + q + 1) =
      K.d p (p + 1) ▷ L.X q ≫
        HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by omega) +
      p.negOnePow • (K.X p ◁ L.d q (q + 1) ≫
        HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by omega)) := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
        (show p + 1 + q = p + q + 1 by omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
        (show p + (q + 1) = p + q + 1 by omega)]
    simp
  have h := congrArg (fun f ↦ f ≫ t.f (p + q + 1)) hd
  simp only [Units.smul_def, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc] at h
  rw [← t.comm (p + q) (p + q + 1)] at h
  have hs := congrArg (fun f ↦ f.app V (tmulSection x y)) h
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.add_app,
    AddCommGrpCat.hom_add_apply, app_zsmul_apply, whiskerRight_app_tmulSection,
    whiskerLeft_app_tmulSection, Units.smul_def] using hs

/-- Module sheaves admit computing resolutions with a sectionwise tensor pairing.
Source: Stacks Project, Section 20.31 (0FKU), naive cup product and the
flasque/Godement proof of Lemma 20.31.4 (0FKV).
(blueprint: lem-sc-module-cup-pairing-exists)
Proof: take the existential strictly nonnegative flasque integer complexes,
quasi-isomorphic augmentations and tensor cochain map supplied by
moduleCup_godement_pairing. Restrict to natural degrees. On each tensor summand,
tensor sections and apply the supplied chain map; its cochain identity gives
signed Leibniz, and its degree-zero formula gives augmentation_pair. Restrictions
commute because its components are sheaf morphisms. Choose injective resolutions
and extend each augmentation to a comparison degree by degree by injectivity.
moduleCup_flasque_acyclicity makes the supplied terms acyclic, and the separately
cited Leray acyclic-resolution comparison criterion makes every global comparison
homology map invertible. Assemble the fields of CupResolutionPairing.
No specific Godement model or natural choice of the existential complexes is
assumed, and no coefficient flatness is required. -/
theorem exists_moduleCupResolutionPairing {X : Scheme.{uM}} (F G : X.Modules) :
    Nonempty (CupResolutionPairing F G) := by
  let : MonoidalPreadditive X.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  obtain ⟨K, L, M, a, b, c, ha, hb, hc, hK, hL, hM, fK, fL, fM, t, ht⟩ :=
    moduleCup_godement_pairing X F G
  have := ha
  have := hb
  have := hc
  have := hK
  have := hL
  have := hM
  have := natAugmentation_quasiIso a
  have := natAugmentation_quasiIso b
  have := natAugmentation_quasiIso c
  refine ⟨{
    left := computingFlasqueResolution _ (natAugmentation a) (fun n ↦ fK n)
    right := computingFlasqueResolution _ (natAugmentation b) (fun n ↦ fL n)
    target := computingFlasqueResolution _ (natAugmentation c) (fun n ↦ fM n)
    pair := tensorChainSectionPair K L M t
    restriction := ?_
    leibniz := ?_
    augmentation_pair := ?_ }⟩
  · intro r s V W h x y
    change (M.X ((r + s : ℕ) : ℤ)).presheaf.map (homOfLE h).op
      (tensorChainSectionPair K L M t r s V x y) =
        tensorChainSectionPair K L M t r s W
          ((K.X (r : ℤ)).presheaf.map (homOfLE h).op x)
          ((L.X (s : ℤ)).presheaf.map (homOfLE h).op y)
    have hres := tensorSection_restriction
      (HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
        (by simp) ≫ t.f _) V W h x y
    simpa only [tensorChainSectionPair_apply, Hom.comp_app,
      ConcreteCategory.comp_apply, app_val_apply] using hres
  · intro r s V x y
    have hs := tensorChain_leibniz K L M t (r : ℤ) (s : ℤ) V x y
    change (M.d ((r + s : ℕ) : ℤ) ((r + s + 1 : ℕ) : ℤ)).val.app (op V)
      (tensorChainSectionPair K L M t r s V x y) =
      (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
        (show r + 1 + s = r + s + 1 by omega))).val.app (op V)
        (tensorChainSectionPair K L M t (r + 1) s V
          ((K.d (r : ℤ) ((r + 1 : ℕ) : ℤ)).val.app (op V) x) y) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
          (show r + (s + 1) = r + s + 1 by omega))).val.app (op V)
          (tensorChainSectionPair K L M t r (s + 1) V x
            ((L.d (s : ℤ) ((s + 1 : ℕ) : ℤ)).val.app (op V) y))
    rw [tensorChainSectionPair_transport K L M t (r + 1) s (r + s + 1) (by omega),
      tensorChainSectionPair_transport K L M t r (s + 1) (r + s + 1) (by omega),
      tensorChainSectionPair_apply]
    simp only [app_val_apply, Units.smul_def, Int.coe_negOnePow_natCast] at hs
    exact hs
  · intro V x y
    change tensorChainSectionPair K L M t 0 0 V
      (((natAugmentation a).f 0).val.app (op V) x)
      (((natAugmentation b).f 0).val.app (op V) y) =
      ((natAugmentation c).f 0).val.app (op V) (tmulSection x y)
    simp only [natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    rw [tensorChainSectionPair_apply]
    exact ht V x y

end
end AlgebraicGeometry.Scheme.Modules
