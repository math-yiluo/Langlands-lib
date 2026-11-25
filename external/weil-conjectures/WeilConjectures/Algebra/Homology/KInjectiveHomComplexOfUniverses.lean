/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence

/-! # K-injective Hom complexes with independent coefficient universes

Source: Stacks Project, Tag 0A96.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

universe u c v
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric

namespace ZeroClassAux

open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SignedHomComparison

open CochainComplex
universe a b
variable {D : Type a} [Category.{b} D] [Preadditive D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
  [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]
  (L M K : CochainComplex D ℤ)
  (π : ∀ (n p q : ℤ), p + n = q → (K.X n ⟶ (ihom (L.X p)).obj (M.X q)))
  (hπ : ∀ n, IsLimit (Fan.mk (K.X n) (fun p ↦ π n p (p + n) rfl)))
  (hd : ∀ (n m p q q' p' : ℤ) (_hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q),
    K.d n m ≫ π m p q hpq =
      π n p q' hq' ≫ (ihom (L.X p)).map (M.d q' q) -
        n.negOnePow • (π n p' q hp' ≫ (pre (L.d p p')).app (M.X q)))

set_option linter.unusedSectionVars false in
include hd in
private lemma homComplex_d_ihomπ_of_smul (n p q : ℤ) (h : p + (n + 1) = q) (h₁ : p + 1 + n = q) :
    K.d n (n + 1) ≫
        ((p * (n + 1)).negOnePow • π (n + 1) p q h) =
      ((p * (n + 1)).negOnePow : ℤ) • (π n p (p + n) rfl ≫
        (ihom (C := D) (L.X p)).map (M.d (p + n) q) -
        (n.negOnePow : ℤ) • (π n (p + 1) q h₁ ≫
          (pre (C := D) (L.d p (p + 1))).app (M.X q))) := by
  rw [Units.smul_def, Preadditive.comp_zsmul,
    hd n (n + 1) p q (p + n) (p + 1) rfl h rfl h₁, Units.smul_def]

/-- The degree `n` part of `homComplexIsoInternalHomObj`, from `homComplex` to
`internalHomObj`: `(-1)^(p n)` times the identity on the factor `𝓗om(L^p, M^(p+n))`. -/
@[no_expose] private noncomputable def homComplexToInternalHomObjX (n : ℤ) :
    K.X n ⟶ (internalHomObj (C := D) L M).X n :=
  Pi.lift fun T : HomComplex.Triplet n ↦
    (T.p * n).negOnePow • π n T.p T.q T.hpq

/-- The degree `n` part of `homComplexIsoInternalHomObj`, from `internalHomObj` to
`homComplex`. -/
@[no_expose] private noncomputable def internalHomObjToHomComplexX (n : ℤ) :
    (internalHomObj (C := D) L M).X n ⟶ K.X n :=
  (hπ n).lift
    (Fan.mk _ fun p ↦ (p * n).negOnePow • internalHomπ (C := D) L M n p (p + n) rfl)

set_option linter.unusedSectionVars false in
private lemma homComplexToInternalHomObjX_π (n p q : ℤ) (h : p + n = q) :
    homComplexToInternalHomObjX L M K π n ≫ internalHomπ (C := D) L M n p q h =
      (p * n).negOnePow • π n p q h :=
  Pi.lift_comp_π _ _

set_option linter.unusedSectionVars false in
private lemma internalHomObjToHomComplexX_π (n p q : ℤ) (h : p + n = q) :
    internalHomObjToHomComplexX L M K π hπ n ≫ π n p q h =
      (p * n).negOnePow • internalHomπ (C := D) L M n p q h := by
  subst h
  exact (hπ n).fac _ ⟨p⟩

/-- The degree `n` part of `homComplexIsoInternalHomObj`. -/
@[no_expose] private noncomputable def homComplexXIsoInternalHomObjX (n : ℤ) :
    K.X n ≅ (internalHomObj (C := D) L M).X n where
  hom := homComplexToInternalHomObjX L M K π n
  inv := internalHomObjToHomComplexX L M K π hπ n
  hom_inv_id := by
    apply Fan.IsLimit.hom_ext (hπ n)
    intro p
    change _ ≫ π n p (p + n) rfl = 𝟙 _ ≫ π n p (p + n) rfl
    rw [Category.assoc, internalHomObjToHomComplexX_π L M K π hπ, Linear.comp_units_smul,
      homComplexToInternalHomObjX_π L M K π, smul_smul, Int.units_mul_self, one_smul,
      Category.id_comp]
  inv_hom_id := internalHomObj_hom_ext fun p q h ↦ by
    rw [Category.assoc, homComplexToInternalHomObjX_π L M K π, Linear.comp_units_smul,
      internalHomObjToHomComplexX_π L M K π hπ, smul_smul, Int.units_mul_self, one_smul,
      Category.id_comp]

include hd in
private lemma homComplexToInternalHomObjX_comm (n m : ℤ) (hnm : n + 1 = m) :
    homComplexToInternalHomObjX L M K π n ≫ (internalHomObj (C := D) L M).d n m =
      K.d n m ≫ homComplexToInternalHomObjX L M K π m := by
  subst hnm
  refine internalHomObj_hom_ext fun p q h ↦ ?_
  have h₁ : p + 1 + n = q := by omega
  rw [Category.assoc, Category.assoc,
    internalHomObj_d_π L M n (n + 1) p q h (p + n) (p + 1) rfl h₁,
    homComplexToInternalHomObjX_π L M K π, homComplex_d_ihomπ_of_smul L M K π hd n p q h h₁]
  simp only [Units.smul_def, Preadditive.comp_zsmul, Preadditive.comp_sub,
    reassoc_of% homComplexToInternalHomObjX_π L M K π, Preadditive.zsmul_comp]
  rw [show p * (n + 1) = p * n + p by ring, show (p + 1) * n = p * n + n by ring,
    Int.negOnePow_add, Int.negOnePow_add]
  simp only [Units.val_mul, smul_sub, smul_smul, mul_comm, mul_left_comm]

/-- The comparison isomorphism `homComplex L M ≅ internalHomObj (C := D) L M` between the sheaf Hom
complex and the internal hom complex of the monoidal closed category of sheaves of modules. In
degree `n`, it is `(-1)^(p n)` times the identity on the factor `𝓗om(L^p, M^(p+n))`; the sign
converts the differential `d_M f - (-1)^n f d_L` of `homComplex` into the differential
`(-1)^p (d_M f - f d_L)` of `internalHomObj`. -/
@[no_expose] private noncomputable def homComplexIsoInternalHomObj :
    K ≅ internalHomObj (C := D) L M :=
  HomologicalComplex.Hom.isoOfComponents (homComplexXIsoInternalHomObjX L M K π hπ)
    (fun n m hnm ↦ homComplexToInternalHomObjX_comm L M K π hd n m hnm)

end SignedHomComparison

namespace TensorHomKInjective

variable {D : Type*} [Category* D] [Abelian D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D]
  [SymmetricCategory D] [HasLimitsOfSize.{0, 0} D] [HasColimitsOfSize.{0, 0} D]

open CochainComplex

private theorem internalHomKInjective
    (L I : CochainComplex D ℤ)
    (hL : ∀ Z : CochainComplex D ℤ, Z.Acyclic → (Z ⊗ L).Acyclic) [I.IsKInjective] :
    (internalHomObj L I).IsKInjective := by
  classical
  refine ⟨fun {Z} f hZ ↦ ?_⟩
  have hT : (L ⊗ Z).Acyclic := by
    intro n
    exact (hL Z hZ n).of_iso (CochainComplex.Monoidal.braiding Z L)
  let e := internalHomEquiv (C := D) L I Z
  have he0 : e 0 = 0 := by
    apply HomComplex.Cochain.ofHom_injective
    rw [ofHom_internalHomEquiv, HomComplex.Cochain.ofHom_zero,
      ← InternalHom.cochainEquiv_apply, map_zero, HomComplex.Cochain.ofHom_zero]
  obtain ⟨H⟩ := IsKInjective.nonempty_homotopy_zero (e.symm f) hT
  refine ⟨?_⟩
  simpa only [e, Equiv.apply_symm_apply, he0] using H.internalHomEquiv

end TensorHomKInjective

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

variable [J.HasSheafCompose (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})]

set_option hygiene false in
local notation "RawMod" => SheafOfModules.{max c v u}
  ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

/-- A local category alias keeps the ambient universe visible to instance inference. -/
@[implicit_reducible, no_expose] private def ModuleCategory := RawMod

set_option hygiene false in
local notation "WMod" => ModuleCategory.{u, c, v} R

private instance kInjectiveHomComplexOfUniversesInst1
    : Category.{max c v u} WMod := inferInstanceAs (Category RawMod)
private instance kInjectiveHomComplexOfUniversesInst2
    : Preadditive WMod := inferInstanceAs (Preadditive RawMod)
private instance kInjectiveHomComplexOfUniversesInst3
    : Abelian WMod := inferInstanceAs (Abelian RawMod)
private noncomputable instance kInjectiveHomComplexOfUniversesInst4
    : HasLimitsOfSize.{max c v u, max c v u} WMod :=
  inferInstanceAs (HasLimitsOfSize.{max c v u, max c v u} RawMod)
private noncomputable instance kInjectiveHomComplexOfUniversesInst5
    : HasColimitsOfSize.{max c v u, max c v u} WMod :=
  inferInstanceAs (HasColimitsOfSize.{max c v u, max c v u} RawMod)
private noncomputable instance kInjectiveHomComplexOfUniversesInst6 : MonoidalCategory WMod :=
  SheafOfModules.monoidalCategory R
private noncomputable instance kInjectiveHomComplexOfUniversesInst7 : SymmetricCategory WMod :=
  SheafOfModules.symmetricCategory R

set_option hygiene false in
local notation "Mod" => ModuleCategory.{u, c, v} R

@[no_expose] private noncomputable def presheafHomEquiv
    (M P N : PresheafOfModules.{max c v u}
      (R.obj ⋙ forget₂ CommRingCat.{max c v u} RingCat.{max c v u})) :=
  CategoryTheory.IsoTensorHom.homObjEquiv.{c, v, u} M P N

set_option linter.unusedSectionVars false in
private lemma presheafHomEquiv_left
    {M P P' N : PresheafOfModules.{max c v u}
      (R.obj ⋙ forget₂ CommRingCat.{max c v u} RingCat.{max c v u})}
    (f : P ⟶ P') (g : M ⊗ P' ⟶ N) :
    presheafHomEquiv.{u, c, v} R M P N (M ◁ f ≫ g) =
      f ≫ presheafHomEquiv.{u, c, v} R M P' N g := by
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : P.obj U) ↦ ?_)
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (y : M.obj (op W.unop.left)) ↦ ?_)
  exact congrArg (fun t : P'.obj (op W.unop.left) ↦
    g.app (op W.unop.left) (y ⊗ₜ[R.obj.obj (op W.unop.left)] t))
      (PresheafOfModules.naturality_apply f W.unop.hom.op x)

set_option linter.unusedSectionVars false in
private lemma presheafHomEquiv_right
    {M P N N' : PresheafOfModules.{max c v u}
      (R.obj ⋙ forget₂ CommRingCat.{max c v u} RingCat.{max c v u})}
    (f : M ⊗ P ⟶ N) (g : N ⟶ N') :
    presheafHomEquiv.{u, c, v} R M P N' (f ≫ g) =
      presheafHomEquiv.{u, c, v} R M P N f ≫
        PresheafOfModules.homObjMap.{max c v u, v, c, max c v u} (𝟙 M) g := by
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : P.obj U) ↦ ?_)
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (y : _ ) ↦ ?_)
  rfl

set_option linter.unusedSectionVars false in
private lemma presheafHomEquiv_pre
    {M M' P N : PresheafOfModules.{max c v u}
      (R.obj ⋙ forget₂ CommRingCat.{max c v u} RingCat.{max c v u})}
    (f : M' ⟶ M) (g : M ⊗ P ⟶ N) :
    presheafHomEquiv.{u, c, v} R M' P N (f ▷ P ≫ g) =
      presheafHomEquiv.{u, c, v} R M P N g ≫
        PresheafOfModules.homObjMap.{max c v u, v, c, max c v u} f (𝟙 N) := by
  apply PresheafOfModules.hom_ext
  intro U
  refine ModuleCat.hom_ext (LinearMap.ext fun (x : P.obj U) ↦ ?_)
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (y : _ ) ↦ ?_)
  rfl

attribute [local irreducible] presheafHomEquiv

@[no_expose] private noncomputable def tensorHomEquiv (A T N : RawMod) :
    (A ⊗ T ⟶ N) ≃ (T ⟶ SheafOfModules.homObj (R := R) A N) :=
  (SheafOfModules.tensorObjIsoSheafification (R := R) A T).homFromEquiv.trans
    (((PresheafOfModules.sheafificationAdjunction.{max c v u}
      (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).homEquiv _ N).trans
      ((presheafHomEquiv.{u, c, v} R A.val T.val N.val).trans
        ((SheafOfModules.fullyFaithfulForget _).homEquiv
          (X := T) (Y := SheafOfModules.homObj (R := R) A N)).symm))

private lemma tensorHomEquiv_val (A T N : RawMod) (φ : A ⊗ T ⟶ N) :
    (tensorHomEquiv.{u, c, v} R A T N φ).val =
      presheafHomEquiv.{u, c, v} R A.val T.val N.val
        ((PresheafOfModules.sheafificationAdjunction.{max c v u}
          (𝟙 ((sheafCompose J
          (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).homEquiv _ N
            ((SheafOfModules.tensorObjIsoSheafification (R := R) A T).inv ≫ φ)) := rfl

attribute [local irreducible] tensorHomEquiv

private lemma tensorHomEquiv_left (A : RawMod) {T T' N : RawMod}
    (f : T ⟶ T') (φ : A ⊗ T' ⟶ N) :
    tensorHomEquiv.{u, c, v} R A T N (A ◁ f ≫ φ) = f ≫ tensorHomEquiv.{u, c, v} R A T' N φ := by
  have h : (SheafOfModules.tensorObjIsoSheafification (R := R) A T).inv ≫ A ◁ f =
      (PresheafOfModules.sheafification.{max c v u}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).map
          (A.val ◁ f.val) ≫ (SheafOfModules.tensorObjIsoSheafification (R := R) A T').inv := by
    erw [Iso.inv_comp_eq, ← Category.assoc,
      ← SheafOfModules.whiskerLeft_tensorObjIsoSheafification_hom_kfi.{max c v u, c, v} (R := R),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply SheafOfModules.hom_ext
  erw [SheafOfModules.comp_val, tensorHomEquiv_val.{u, c, v}, tensorHomEquiv_val.{u, c, v}]
  erw [← Category.assoc, h, Category.assoc, Adjunction.homEquiv_naturality_left]
  exact presheafHomEquiv_left.{u, c, v} R _ _

set_option backward.isDefEq.respectTransparency.types true in
private lemma tensorHomEquiv_right (A : RawMod) {T N N' : RawMod}
    (φ : A ⊗ T ⟶ N) (g : N ⟶ N') :
    tensorHomEquiv.{u, c, v} R A T N' (φ ≫ g) =
      tensorHomEquiv.{u, c, v} R A T N φ ≫
        SheafOfModules.homObjMap.{max c v u, v, c, max c v u} (R := R) (𝟙 A) g := by
  apply SheafOfModules.hom_ext
  erw [SheafOfModules.comp_val, tensorHomEquiv_val.{u, c, v}, tensorHomEquiv_val.{u, c, v},
    SheafOfModules.homObjMap_val]
  erw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  exact presheafHomEquiv_right.{u, c, v} R _ _

open SheafOfModules.CochainScalarConstruction in
private lemma tensorHomEquiv_pre {A A' T N : RawMod} (f : A' ⟶ A) (φ : A ⊗ T ⟶ N) :
    tensorHomEquiv.{u, c, v} R A' T N (f ▷ T ≫ φ) =
      tensorHomEquiv.{u, c, v} R A T N φ ≫
        SheafOfModules.homObjMap.{max c v u, v, c, max c v u} f (𝟙 N) := by
  have h : (SheafOfModules.tensorObjIsoSheafification (R := R) A' T).inv ≫ f ▷ T =
      (PresheafOfModules.sheafification.{max c v u}
        (𝟙 ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R).obj)).map
          (f.val ▷ T.val) ≫
        (SheafOfModules.tensorObjIsoSheafification (R := R) A T).inv := by
    erw [Iso.inv_comp_eq, ← Category.assoc, ←
      whiskerRight_tensorObjIsoSheafification_hom.{max c v u, c, v}
        (R := R),
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply SheafOfModules.hom_ext
  erw [SheafOfModules.comp_val, tensorHomEquiv_val.{u, c, v}, tensorHomEquiv_val.{u, c, v},
    ← Category.assoc, h, Category.assoc, Adjunction.homEquiv_naturality_left]
  exact presheafHomEquiv_pre.{u, c, v} R _ _

@[irreducible, no_expose] private noncomputable def tensorHomAdjunction (A : RawMod) :
    tensorLeft A ⊣ (SheafOfModules.homFunctor.{max c v u, v, c, max c v u} R).obj (op A) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv.{u, c, v} R A
      homEquiv_naturality_left_symm f g := by
        erw [Equiv.symm_apply_eq]
        exact ((congrArg (f ≫ ·)
          (Equiv.apply_symm_apply (tensorHomEquiv.{u, c, v} R A _ _) g).symm).trans
            (tensorHomEquiv_left.{u, c, v} R A f _).symm)
      homEquiv_naturality_right f g := tensorHomEquiv_right.{u, c, v} R A f g }

@[instance_reducible, no_expose] private noncomputable def moduleMonoidalClosed :
    MonoidalClosed Mod where
  closed A :=
    { rightAdj := (SheafOfModules.homFunctor.{max c v u, v, c, max c v u} R).obj (op A)
      adj := tensorHomAdjunction.{u, c, v} R A }

private noncomputable instance kInjectiveHomComplexOfUniversesInst8
    : MonoidalClosed Mod := moduleMonoidalClosed.{u, c, v} R

private lemma uncurry_eq_tensorHomEquiv_symm {A T N : Mod}
    (g : T ⟶ SheafOfModules.homObj (R := R) A N) :
    MonoidalClosed.uncurry g = (tensorHomEquiv.{u, c, v} R A T N).symm g := by
  change ((tensorHomAdjunction.{u, c, v} R A).homEquiv _ _).symm g = _
  erw [tensorHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private lemma ihom_map_eq (P N N' : Mod) (f : N ⟶ N') :
    (ihom P).map f =
      SheafOfModules.homObjMap.{max c v u, v, c, max c v u} (𝟙 P) f := rfl

private lemma ihom_ev_app (A N : Mod) :
    (ihom.ev A).app N =
      (tensorHomEquiv.{u, c, v} R A ((ihom A).obj N) N).symm (𝟙 _) := by
  erw [← MonoidalClosed.uncurry_id_eq_ev, uncurry_eq_tensorHomEquiv_symm]

private lemma pre_app {A A' : Mod} (f : A' ⟶ A) (N : Mod) :
    (MonoidalClosed.pre f).app N =
      SheafOfModules.homObjMap.{max c v u, v, c, max c v u} f (𝟙 N) := by
  apply MonoidalClosed.uncurry_injective
  erw [MonoidalClosed.uncurry_pre, uncurry_eq_tensorHomEquiv_symm, Equiv.eq_symm_apply,
    tensorHomEquiv_pre, ihom_ev_app, Equiv.apply_symm_apply]
  exact Category.id_comp _

open CochainComplex

variable {R}

private noncomputable instance kInjectiveHomComplexOfUniversesInst9 : MonoidalPreadditive Mod :=
  SheafOfModules.monoidalPreadditive_kfi.{max c v u, c, v} R
private noncomputable instance kInjectiveHomComplexOfUniversesInst10 : HasLimitsOfSize.{0, 0} Mod :=
  hasLimitsOfSizeShrink.{0, 0, max c v u, max c v u} Mod
private noncomputable instance kInjectiveHomComplexOfUniversesInst11
    : HasColimitsOfSize.{0, 0} Mod :=
  hasColimitsOfSizeShrink.{0, 0, max c v u, max c v u} Mod

/-- The projection `homComplexπ` of the Hom complex, as a morphism to the internal hom
`(ihom (C := Mod) (L.X p)).obj (M.X q) = 𝓗om(L^p, M^q)`. -/
private noncomputable abbrev homComplexIhomπ (L M : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex.{c, v, max c v u, max c v u} L M).X n ⟶ (ihom (C := Mod) (L.X p)).obj (M.X q) :=
  homComplexπ L M n p q h

private lemma homComplex_d_ihomπ (L M : CochainComplex Mod ℤ)
    (n m p q q' p' : ℤ) (hnm : n + 1 = m) (hpq : p + m = q)
    (hq' : p + n = q') (hp' : p' + n = q) :
    (homComplex.{c, v, max c v u, max c v u} L M).d n m ≫ homComplexIhomπ.{u, c, v} L M m p q hpq =
      homComplexIhomπ.{u, c, v} L M n p q' hq' ≫ (ihom (C := Mod) (L.X p)).map (M.d q' q) -
        n.negOnePow • (homComplexIhomπ.{u, c, v} L M n p' q hp' ≫
          (pre (C := Mod) (L.d p p')).app (M.X q)) := by
  have hpre : (pre (C := Mod) (L.d p p')).app (M.X q) =
      SheafOfModules.homObjMap.{max c v u, v, c, max c v u} (L.d p p') (𝟙 (M.X q)) :=
    pre_app.{u, c, v} R _ _
  rw [hpre, ihom_map_eq]
  exact homComplex_d_π L M n m p q q' p' hnm hpq hq' hp'

@[no_expose] private noncomputable def homComplexIsoInternalHomObj
    (L M : CochainComplex Mod ℤ) :
    homComplex (R := R) L M ≅ internalHomObj (C := Mod) L M :=
  SignedHomComparison.homComplexIsoInternalHomObj L M (homComplex (R := R) L M)
    (homComplexIhomπ L M) (fun n ↦ homComplexIsLimit L M n)
    (homComplex_d_ihomπ L M)

private theorem isKInjective_homComplex (L I : CochainComplex Mod ℤ)
    (hL : CochainComplex.IsKFlatIndependentCoefficients (R := R) L) [I.IsKInjective] :
    (homComplex (R := R) L I).IsKInjective := by
  let : (internalHomObj (C := Mod) L I).IsKInjective :=
    TensorHomKInjective.internalHomKInjective L I hL
  exact CochainComplex.isKInjective_of_iso
    (homComplexIsoInternalHomObj.{u, c, v} L I).symm

end ZeroClassAux
end WeilConjectures

namespace CochainComplex

/-- Hom from a K-flat complex into a K-injective complex is K-injective.
Source: Stacks Project, Tag 0A96.
(auxiliary; not a blueprint node).

Proof: for any acyclic Z, K-flatness makes Z tensor L acyclic. Symmetry makes
L tensor Z acyclic too. Tensor-Hom adjunction identifies maps Z to Hom(L,I)
with maps L tensor Z to I, and also transports homotopies. The latter maps
are null-homotopic because I is K-injective. Equivalently, use the degreewise
product isomorphism with the monoidal internal Hom: multiply the (p,n)
factor by (-1)^(p*n) to reconcile the two differential conventions. All
products, coproducts and sectionwise adjunctions take place in max c v u,
which contains the object, arrow and coefficient universes of the site. -/
theorem isKInjective_homComplex_of_isKFlatOfUniverses
    {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    {R : Sheaf J CommRingCat.{max c v u}}
    (L I : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj R)) ℤ)
    (hL : IsKFlatIndependentCoefficients (R := R) L) [I.IsKInjective] :
    (homComplex (R := R) L I).IsKInjective := by
  exact WeilConjectures.ZeroClassAux.isKInjective_homComplex.{u, c, v} L I hL

end CochainComplex
