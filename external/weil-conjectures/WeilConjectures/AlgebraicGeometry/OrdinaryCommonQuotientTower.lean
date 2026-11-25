/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.AlgebraicGeometry.CommonQuotientTowerPresentation
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all WeilConjectures.Algebra.Homology.OrdinaryFlatCoefficientComparison
import all WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Ordinary common-quotient scalar extensions

Source: Stacks Project, Modules on Sites, Tag 03EK (section-tensor-product).
The result concerns module sheaves before passing to complexes or derived categories.
Quotient units are proved epic, their local ideal-product kernels are computed, and their
transition compatibility follows from the pure-section formulas. The existence theorem
constructs the normalized ordinary comparison and coefficient transitions.
The quotient units themselves are constructed by the sheafification adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency false
universe u v r wR wB wS
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings TensorProduct
namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

set_option quotPrecheck false in
set_option hygiene false in
local notation:max "Mod" A:arg => ringedSiteModules.{r}
  (derivedChangeRingIndependentCoefficients J A)
set_option quotPrecheck false in
set_option hygiene false in
local notation:max "Res" f:arg => restrictScalars
  ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

section QuotientKernel
variable {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)

private def K (U : Cᵒᵖ) : Ideal (R.obj.obj U) := RingHom.ker (q.hom.app U).hom

end QuotientKernel

/-- The sectionwise quotient unit, sending x to 1 tensor x.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def commonQuotientPresheafUnit
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    M.val ⟶ (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).obj
        (changeOfRingsPresheaf q M) where
  app U := (ModuleCat.ExtendRestrictScalarsAdj.unit (q.hom.app U).hom).app (M.val.obj U)
  naturality {U V} f := by
    apply ModuleCat.hom_ext
    ext x
    change (1 : S.obj.obj V) ⊗ₜ[R.obj.obj V, (q.hom.app V).hom] M.val.restrictₛₗ f x =
      changeOfRingsMap q M f ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x)
    rw [show changeOfRingsMap q M f
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x) =
        S.obj.map f 1 ⊗ₜ[R.obj.obj V, (q.hom.app V).hom] M.val.restrictₛₗ f x from
      Classical.choose_spec (exists_changeOfRingsMap q M f) 1 x, map_one]

/-- The actual sheaf quotient unit constructed from the sheafification adjunction.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def commonQuotientUnit
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S) (M : Mod R) :
    M ⟶ (Res q).obj (changeOfRings q M) where
  val := commonQuotientPresheafUnit q M ≫
    (PresheafOfModules.restrictScalars
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map q).hom).map
        (PresheafOfModules.sheafificationHomEquiv
          (𝟙 (derivedChangeRingIndependentCoefficients J S).obj)
          (𝟙 (changeOfRings q M)))

/-- The actual quotient units are natural in the module.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
theorem commonQuotientUnit_naturality
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    {M N : Mod R} (f : M ⟶ N) :
    f ≫ commonQuotientUnit q N = commonQuotientUnit q M ≫ (Res q).map (changeOfRingsHom q M f) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let g := changePresheafHom q f
  have h := congrArg (fun a ↦ a.app U
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U,(q.hom.app U).hom] x))
      (toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map g))
  exact h

/-- The quotient unit transported to a prescribed ordinary scalar-extension model.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
noncomputable def commonQuotientModelUnit
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wS} (Mod S)]
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} q) :
    𝟭 (Mod R) ⟶ F.E ⋙ Res q where
  app M := commonQuotientUnit q M ≫ (Res q).map (eqToHom (F.obj_eq M).symm)
  naturality {M N} f := by
    dsimp only [Functor.id_map, Functor.comp_map]
    rw [← Category.assoc, commonQuotientUnit_naturality q f, Category.assoc]
    rw [F.map_eq, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc, ← Functor.map_comp]
    apply congrArg (fun g ↦ commonQuotientUnit q M ≫ (Res q).map g)
    rw [← Category.assoc (eqToHom (F.obj_eq M).symm) (eqToHom (F.obj_eq M)),
      eqToHom_trans, eqToHom_refl, Category.id_comp]

section RingPushout

set_option backward.isDefEq.respectTransparency.types false

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ring_hasSheafify : HasSheafify J CommRingCat.{r} :=
  hasSheafifyEssentiallySmallSite J CommRingCat.{r}

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ring_locallyBijective : J.WEqualsLocallyBijective CommRingCat.{r} := by
  let : PreservesFilteredColimitsOfSize.{r, r} (CategoryTheory.forget CommRingCat.{r}) :=
    preservesFilteredColimitsOfSize_shrink _
  have : ∀ X : Cᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (equivSmallModel.{r} C).inverse.op)
        CommRingCat.{r} := fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{r} _ _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall J

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem pushout_local
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (b : B ⟶ S)
    (h : IsPushout φ q b (𝟙 S)) :
    Presheaf.IsLocallyInjective J
      (pushout.desc b.hom (𝟙 S.obj) (by
        have hw := congrArg (fun f : R ⟶ S ↦ f.hom) h.w
        simpa using hw)) := by
  let := ring_hasSheafify (J := J)
  let := ring_locallyBijective (J := J)
  let P := pushout φ.hom q.hom
  let μ : P ⟶ S.obj := pushout.desc b.hom (𝟙 S.obj) (by
    have hw := congrArg (fun f : R ⟶ S ↦ f.hom) h.w
    simpa using hw)
  let adj := sheafificationAdjunction J CommRingCat.{r}
  let T := (presheafToSheaf J CommRingCat.{r}).obj P
  let iB : B ⟶ T := ⟨pushout.inl φ.hom q.hom ≫ toSheafify J P⟩
  let iS : S ⟶ T := ⟨pushout.inr φ.hom q.hom ≫ toSheafify J P⟩
  have hw : φ ≫ iB = q ≫ iS := by
    apply Sheaf.hom_ext
    change φ.hom ≫ pushout.inl φ.hom q.hom ≫ toSheafify J P =
      q.hom ≫ pushout.inr φ.hom q.hom ≫ toSheafify J P
    rw [← Category.assoc, pushout.condition, Category.assoc]
  let e := h.desc iB iS hw
  have he : e = iS := by
    have hh : 𝟙 S ≫ e = iS := h.inr_desc iB iS hw
    exact (Category.id_comp e).symm.trans hh
  have hb : b ≫ iS = iB := by rw [← he]; exact h.inl_desc iB iS hw
  let δ : T ⟶ S := (adj.homEquiv P S).symm μ
  have hδ : toSheafify J P ≫ δ.hom = μ :=
    (adj.homEquiv P S).apply_symm_apply μ
  have hleft : iS ≫ δ = 𝟙 S := by
    apply Sheaf.hom_ext
    change (pushout.inr φ.hom q.hom ≫ toSheafify J P) ≫ δ.hom = _
    rw [Category.assoc, hδ]
    exact pushout.inr_desc _ _ _
  have hright : δ ≫ iS = 𝟙 T := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _ T.property
    change toSheafify J P ≫ (δ.hom ≫ iS.hom) = toSheafify J P ≫ 𝟙 _
    rw [← Category.assoc, hδ, Category.comp_id]
    apply pushout.hom_ext
    · change (pushout.inl φ.hom q.hom ≫
        pushout.desc b.hom (𝟙 S.obj) _) ≫ iS.hom = _
      rw [pushout.inl_desc]
      exact congrArg (fun f : B ⟶ T ↦ f.hom) hb
    · change (pushout.inr φ.hom q.hom ≫
        pushout.desc b.hom (𝟙 S.obj) _) ≫ iS.hom = _
      rw [pushout.inr_desc, Category.id_comp]
  have : IsIso δ := ⟨⟨iS, hright, hleft⟩⟩
  have : Presheaf.IsLocallyInjective J δ.hom := inferInstance
  have : Presheaf.IsLocallyInjective J (toSheafify J P) :=
    (J.W_toSheafify P).isLocallyInjective
  change Presheaf.IsLocallyInjective J μ
  rw [← hδ]
  infer_instance

private noncomputable def ringTensorIso
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    CommRingCat.of (B.obj.obj U ⊗[R.obj.obj U] S.obj.obj U) ≅
      (pushout φ.hom q.hom).obj U := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  let h := (IsPushout.of_hasPushout φ.hom q.hom).map
    ((CategoryTheory.evaluation Cᵒᵖ CommRingCat).obj U)
  exact (CommRingCat.isPushout_tensorProduct
    (R.obj.obj U) (B.obj.obj U) (S.obj.obj U)).isoPushout ≪≫ h.isoPushout.symm

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ringTensorIso_left
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ)
    (x : B.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    (ringTensorIso φ q U).hom
      (x ⊗ₜ[R.obj.obj U] (1 : S.obj.obj U)) =
        (pushout.inl φ.hom q.hom).app U x := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct
    (R.obj.obj U) (B.obj.obj U) (S.obj.obj U)
  let he := (IsPushout.of_hasPushout φ.hom q.hom).map
    ((CategoryTheory.evaluation Cᵒᵖ CommRingCat).obj U)
  have hh := congrArg (fun f : B.obj.obj U ⟶ (pushout φ.hom q.hom).obj U ↦ f x)
    ((ht.inl_isoPushout_hom_assoc he.isoPushout.inv).trans he.inl_isoPushout_inv)
  exact hh

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ringTensorIso_right
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ)
    (y : S.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    (ringTensorIso φ q U).hom
      ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U] y) =
        (pushout.inr φ.hom q.hom).app U y := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  let ht := CommRingCat.isPushout_tensorProduct
    (R.obj.obj U) (B.obj.obj U) (S.obj.obj U)
  let he := (IsPushout.of_hasPushout φ.hom q.hom).map
    ((CategoryTheory.evaluation Cᵒᵖ CommRingCat).obj U)
  exact congrArg (fun f : S.obj.obj U ⟶ (pushout φ.hom q.hom).obj U ↦ f y)
    ((ht.inr_isoPushout_hom_assoc he.isoPushout.inv).trans he.inr_isoPushout_inv)

omit [EssentiallySmall.{r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}] in
private theorem ringTensorIso_tmul
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (U : Cᵒᵖ)
    (x : B.obj.obj U) (y : S.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (q.hom.app U).hom.toAlgebra
    (ringTensorIso φ q U).hom
      (x ⊗ₜ[R.obj.obj U] y) =
        (pushout.inl φ.hom q.hom).app U x *
          (pushout.inr φ.hom q.hom).app U y := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (q.hom.app U).hom.toAlgebra
  have ht : x ⊗ₜ[R.obj.obj U] y =
      (x ⊗ₜ[R.obj.obj U] (1 : S.obj.obj U)) *
        ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U] y) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [ht, map_mul, ringTensorIso_left, ringTensorIso_right]

private noncomputable def multiplicationRaw
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) :
    changeOfRingsPresheaf φ ((Res φ).obj ((Res b).obj
      (unit (derivedChangeRingIndependentCoefficients J S)))) ⟶
        ((Res b).obj (unit (derivedChangeRingIndependentCoefficients J S))).val :=
  CoefficientOrdinaryProof.restrictionToTensor φ _ _ (𝟙 _)

private noncomputable def tensorRingEmbedding
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) :
    (changeOfRingsPresheaf φ ((Res φ).obj ((Res b).obj
      (unit (derivedChangeRingIndependentCoefficients J S))))).presheaf ⋙
        CategoryTheory.forget AddCommGrpCat ⟶
      pushout φ.hom (φ ≫ b).hom ⋙ CategoryTheory.forget CommRingCat where
  app U := TypeCat.ofHom fun z ↦ (ringTensorIso φ (φ ≫ b) U).hom z
  naturality {U V} f := by
    ext z
    change (ringTensorIso φ (φ ≫ b) V).hom
      ((changeOfRingsPresheaf φ _).map f z) =
        (pushout φ.hom (φ ≫ b).hom).map f ((ringTensorIso φ (φ ≫ b) U).hom z)
    let := (φ.hom.app U).hom.toAlgebra
    let := ((φ ≫ b).hom.app U).hom.toAlgebra
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      change (ringTensorIso φ (φ ≫ b) V).hom
        ((changeOfRingsPresheaf φ _).map f (x + y)) =
          (pushout φ.hom (φ ≫ b).hom).map f
            ((ringTensorIso φ (φ ≫ b) U).hom (x + y))
      simp only [map_add, hx, hy]
    | tmul x y =>
      change (ringTensorIso φ (φ ≫ b) V).hom
        (changeOfRingsMap φ _ f (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] y)) = _
      rw [show changeOfRingsMap φ _ f
          (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] y) = _ from
        Classical.choose_spec (exists_changeOfRingsMap φ _ f) x y]
      rw [ringTensorIso_tmul]
      change _ = (pushout φ.hom (φ ≫ b).hom).map f
        ((ringTensorIso φ (φ ≫ b) U).hom (x ⊗ₜ[R.obj.obj U] y))
      rw [ringTensorIso_tmul, map_mul]
      exact congrArg₂ (· * ·)
        (NatTrans.naturality_apply (pushout.inl φ.hom (φ ≫ b).hom) f x)
        (NatTrans.naturality_apply (pushout.inr φ.hom (φ ≫ b).hom) f y)

private theorem multiplicationRaw_locallyInjective
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S)
    (h : IsPushout φ (φ ≫ b) b (𝟙 S)) :
    PresheafOfModules.IsLocallyInjective J (multiplicationRaw φ b) := by
  let μ : pushout φ.hom (φ ≫ b).hom ⟶ S.obj :=
    pushout.desc b.hom (𝟙 S.obj) (by rfl)
  have : Presheaf.IsLocallyInjective J μ := pushout_local φ (φ ≫ b) b h
  let e := tensorRingEmbedding φ b
  have : Presheaf.IsLocallyInjective J e :=
    Presheaf.isLocallyInjective_of_injective J e (fun U ↦
      (ConcreteCategory.bijective_of_isIso (ringTensorIso φ (φ ≫ b) U).hom).injective)
  have hfac : e ≫ Functor.whiskerRight μ (CategoryTheory.forget CommRingCat) =
      Functor.whiskerRight
        ((PresheafOfModules.toPresheaf _).map (multiplicationRaw φ b))
          (CategoryTheory.forget AddCommGrpCat) := by
    ext U z
    change μ.app U ((ringTensorIso φ (φ ≫ b) U).hom z) =
      (multiplicationRaw φ b).app U z
    let := (φ.hom.app U).hom.toAlgebra
    let := ((φ ≫ b).hom.app U).hom.toAlgebra
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      change μ.app U ((ringTensorIso φ (φ ≫ b) U).hom (x + y)) =
        (multiplicationRaw φ b).app U (x + y)
      simp only [map_add, hx, hy]
    | tmul x y =>
      change μ.app U ((ringTensorIso φ (φ ≫ b) U).hom (x ⊗ₜ[R.obj.obj U] y)) = _
      rw [ringTensorIso_tmul, map_mul]
      have hl := NatTrans.congr_app (pushout.inl_desc (f := φ.hom) (g := (φ ≫ b).hom)
        b.hom (𝟙 S.obj) (by rfl)) U
      have hr := NatTrans.congr_app (pushout.inr_desc (f := φ.hom) (g := (φ ≫ b).hom)
        b.hom (𝟙 S.obj) (by rfl)) U
      change μ.app U ((pushout.inl φ.hom (φ ≫ b).hom).app U x) *
        μ.app U ((pushout.inr φ.hom (φ ≫ b).hom).app U y) = _
      exact congrArg₂ (· * ·) (ConcreteCategory.congr_hom hl x)
        (ConcreteCategory.congr_hom hr y)
  apply (Presheaf.isLocallyInjective_forget_iff J _).mp
  rw [← hfac]
  infer_instance

private noncomputable def multiplicationSheaf
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) :
    changeOfRings φ ((Res φ).obj ((Res b).obj
      (unit (derivedChangeRingIndependentCoefficients J S)))) ⟶
        (Res b).obj (unit (derivedChangeRingIndependentCoefficients J S)) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 _)).symm (multiplicationRaw φ b)

omit [EssentiallySmall.{r} C] in
private theorem multiplicationSheaf_sections
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S) (U : Cᵒᵖ)
    (x : B.obj.obj U) (y : S.obj.obj U) :
    (multiplicationSheaf φ b).val.app U
      ((toSheafify J (changeOfRingsPresheaf φ ((Res φ).obj ((Res b).obj
        (unit (derivedChangeRingIndependentCoefficients J S))))).presheaf).app U
          (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
            (show ((Res φ).obj ((Res b).obj
              (unit (derivedChangeRingIndependentCoefficients J S)))).val.obj U from y))) =
      b.hom.app U x * y := by
  let H := (Res b).obj (unit (derivedChangeRingIndependentCoefficients J S))
  let P := changeOfRingsPresheaf φ ((Res φ).obj H)
  have h := congrArg (fun f : P ⟶
      (PresheafOfModules.restrictScalars (𝟙 _)).obj H.val ↦ f.app U
        (x ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
          (show ((Res φ).obj H).val.obj U from y)))
      ((PresheafOfModules.sheafificationHomEquiv
        (R := derivedChangeRingIndependentCoefficients J B) (P := P) (F := H)
          (𝟙 _)).apply_symm_apply (multiplicationRaw φ b))
  exact h

private theorem multiplicationSheaf_isIso
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (b : B ⟶ S)
    (h : IsPushout φ (φ ≫ b) b (𝟙 S)) : IsIso (multiplicationSheaf φ b) := by
  have := multiplicationRaw_locallyInjective φ b h
  have : PresheafOfModules.IsLocallySurjective J (multiplicationRaw φ b) := by
    apply Presheaf.isLocallySurjective_of_surjective
    intro U y
    refine ⟨(1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom]
      (show ((Res φ).obj ((Res b).obj
        (unit (derivedChangeRingIndependentCoefficients J S)))).val.obj U from y), ?_⟩
    change b.hom.app U 1 * (show S.obj.obj U from y) = (show S.obj.obj U from y)
    rw [map_one, one_mul]
  have : IsIso ((presheafToSheaf J AddCommGrpCat).map
      ((PresheafOfModules.toPresheaf _).map (multiplicationRaw φ b))) :=
    (J.W_iff _).mp (J.W_of_isLocallyBijective _)
  have : IsIso ((toSheaf _).map (multiplicationSheaf φ b)) := by
    unfold multiplicationSheaf
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm,
      Adjunction.homEquiv_counit]
    infer_instance
  exact isIso_of_reflects_iso _ (toSheaf _)

private noncomputable def ordinaryModelIso
    {R S : Sheaf J CommRingCat.{r}} (q : R ⟶ S)
    (F G : Mod R ⥤ Mod S)
    (hF : ∀ M, F.obj M = changeOfRings q M)
    (hG : ∀ M, G.obj M = changeOfRings q M)
    (hmF : ∀ {M N} (f : M ⟶ N), F.map f =
      eqToHom (hF M) ≫ changeOfRingsHom q M f ≫ eqToHom (hF N).symm)
    (hmG : ∀ {M N} (f : M ⟶ N), G.map f =
      eqToHom (hG M) ≫ changeOfRingsHom q M f ≫ eqToHom (hG N).symm) : F ≅ G :=
  NatIso.ofComponents (fun M ↦ eqToIso ((hF M).trans (hG M).symm)) (by
    intro M N f
    dsimp only [eqToIso.hom]
    rw [hmF, hmG]
    simp)

private theorem ordinaryComparison
    {R B S : Sheaf J CommRingCat.{r}} (φ : R ⟶ B) (q : R ⟶ S) (b : B ⟶ S)
    (hpush : IsPushout φ q b (𝟙 S))
    [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wB} (Mod B)]
    [HasDerivedCategory.{wS} (Mod S)]
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} q)
    (G : DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} b) :
    ∃ e : Res φ ⋙ F.E ≅ G.E,
      ∀ (M : Mod B) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U),
        (e.hom.app M).val.app U
          ((eqToHom (F.obj_eq ((Res φ).obj M)).symm).val.app U
            ((toSheafify J (changeOfRingsPresheaf q ((Res φ).obj M)).presheaf).app U
              (s ⊗ₜ[R.obj.obj U, (q.hom.app U).hom] x))) =
        (eqToHom (G.obj_eq M).symm).val.app U
          ((toSheafify J (changeOfRingsPresheaf b M).presheaf).app U
            (s ⊗ₜ[B.obj.obj U, (b.hom.app U).hom] x)) := by
  have hq : φ ≫ b = q := by simpa using hpush.w
  subst q
  let EF := F.E
  let EG := G.E
  have hF := F.obj_eq
  have hG := G.obj_eq
  have hmF : ∀ {M M'} (f : M ⟶ M'), EF.map f =
      eqToHom (hF M) ≫ changeOfRingsHom (φ ≫ b) M f ≫ eqToHom (hF M').symm :=
    fun f ↦ F.map_eq f
  have hmG : ∀ {M M'} (f : M ⟶ M'), EG.map f =
      eqToHom (hG M) ≫ changeOfRingsHom b M f ≫ eqToHom (hG M').symm :=
    fun f ↦ G.map_eq f
  let : ∀ T : Sheaf J CommRingCat.{r}, HasDerivedCategory.{max (max u v) (r + 1)} (Mod T) :=
    fun T ↦ HasDerivedCategory.standard _
  obtain ⟨p, ⟨N⟩⟩ := SuccessiveDerivedQuotient.successive_derived_quotient_normalization
    (C := C) (J := J)
  let H := (Res b).obj (unit (derivedChangeRingIndependentCoefficients J S))
  have hm : (N.ordinaryAdjunction φ).counit.app H =
      eqToHom ((p φ).obj_eq ((Res φ).obj H)) ≫ multiplicationSheaf φ b := by
    apply ((N.ordinaryAdjunction φ).homEquiv _ _).injective
    have hh := (N.ordinaryAdjunction φ).homEquiv_symm_id H
    have hh' := ((N.ordinaryAdjunction φ).homEquiv ((Res φ).obj H) H).apply_symm_apply
      (𝟙 ((Res φ).obj H))
    rw [hh] at hh'
    change ((N.ordinaryAdjunction φ).homEquiv ((Res φ).obj H) H)
      ((N.ordinaryAdjunction φ).counit.app H) =
        ((N.ordinaryAdjunction φ).homEquiv ((Res φ).obj H) H)
          (eqToHom ((p φ).obj_eq ((Res φ).obj H)) ≫ multiplicationSheaf φ b)
    rw [hh', Adjunction.homEquiv_unit]
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change x = (multiplicationSheaf φ b).val.app U
      ((eqToHom ((p φ).obj_eq ((Res φ).obj H))).val.app U
        (((N.ordinaryAdjunction φ).unit.app ((Res φ).obj H)).val.app U x))
    rw [N.ordinary_unit]
    dsimp only [SuccessiveDerivedQuotient.sectionTensor, SuccessiveDerivedQuotient.pure]
    let z := (toSheafify J (changeOfRingsPresheaf φ ((Res φ).obj H)).presheaf).app U
      ((1 : B.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
    have hc : (eqToHom ((p φ).obj_eq ((Res φ).obj H))).val.app U
        ((eqToHom ((p φ).obj_eq ((Res φ).obj H)).symm).val.app U z) = z :=
      congrArg (fun k ↦ k.val.app U z)
        (eqToHom_trans ((p φ).obj_eq ((Res φ).obj H)).symm
          ((p φ).obj_eq ((Res φ).obj H)))
    rw [hc]
    change (show S.obj.obj U from x) = (multiplicationSheaf φ b).val.app U z
    rw [multiplicationSheaf_sections, map_one, one_mul]
  have hmul := multiplicationSheaf_isIso φ b hpush
  have hμ : IsIso ((N.ordinaryAdjunction φ).counit.app H) := by
    rw [hm]
    infer_instance
  obtain ⟨e, he⟩ := ordinary_flatCoefficientComparison p N φ b hμ
  let iF := ordinaryModelIso (φ ≫ b) EF (p (φ ≫ b)).ordinary hF
    (p (φ ≫ b)).obj_eq hmF (p (φ ≫ b)).map_eq
  let iG := ordinaryModelIso b EG (p b).ordinary hG (p b).obj_eq
    hmG (p b).map_eq
  refine ⟨Functor.isoWhiskerLeft (Res φ) iF ≪≫ e ≪≫ iG.symm, ?_⟩
  intro M U s x
  let P := (Res φ).obj M
  let z := (toSheafify J (changeOfRingsPresheaf (φ ≫ b) P).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, ((φ ≫ b).hom.app U).hom] x)
  let z' := (toSheafify J (changeOfRingsPresheaf b M).presheaf).app U
    (s ⊗ₜ[B.obj.obj U, (b.hom.app U).hom] x)
  have hcF : eqToHom (hF P).symm ≫ iF.hom.app P =
      eqToHom ((p (φ ≫ b)).obj_eq P).symm := by
    change eqToHom (hF P).symm ≫
      eqToHom ((hF P).trans ((p (φ ≫ b)).obj_eq P).symm) = _
    simp
  have hcG : eqToHom ((p b).obj_eq M).symm ≫ iG.inv.app M =
      eqToHom (hG M).symm := by
    change eqToHom ((p b).obj_eq M).symm ≫
      eqToHom (((hG M).trans ((p b).obj_eq M).symm).symm) = _
    simp
  have hFi := congrArg (fun k ↦ k.val.app U z) hcF
  have hGi := congrArg (fun k ↦ k.val.app U z') hcG
  change (iF.hom.app P).val.app U ((eqToHom (hF P).symm).val.app U z) =
    (eqToHom ((p (φ ≫ b)).obj_eq P).symm).val.app U z at hFi
  have hp := he M U s x
  change (e.hom.app M).val.app U
    ((eqToHom ((p (φ ≫ b)).obj_eq P).symm).val.app U z) =
      (eqToHom ((p b).obj_eq M).symm).val.app U z' at hp
  change (iG.inv.app M).val.app U ((e.hom.app M).val.app U
    ((iF.hom.app P).val.app U ((eqToHom (hF P).symm).val.app U z))) = _
  rw [hFi, hp]
  exact hGi

end RingPushout

variable {R B : Sheaf J CommRingCat.{r}} {φ : R ⟶ B}
  (D : CommonQuotientTowerPresentation φ)
  [HasDerivedCategory.{wR} (Mod R)] [HasDerivedCategory.{wB} (Mod B)]
  [∀ n : ℕ, HasDerivedCategory.{wS} (Mod(D.S.obj (op n)))]
  (a : ∀ n : ℕ, DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} (D.projection n))
  (b : ∀ n : ℕ,
    DerivedChangeOfRingsCochainModel.{u, v, r, wB, wS} (D.extensionProjection n))

/-- Ordinary common-quotient maps, characterized on the sheafification-unit images
of pure tensors. There are no complexes, K-flatness, or derived comparisons here.
Source: Stacks 03EK
(auxiliary; not a blueprint node). -/
structure OrdinaryCommonQuotientTower where
  ordinary : ∀ n : ℕ, Res φ ⋙ (a n).E ≅ (b n).E
  ordinary_sections : ∀ (n : ℕ) (M : Mod B) (U : Cᵒᵖ)
    (s : (D.S.obj (op n)).obj.obj U) (x : M.val.obj U),
    ((ordinary n).hom.app M).val.app U
      ((eqToHom ((a n).obj_eq ((Res φ).obj M)).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection n)
          ((Res φ).obj M)).presheaf).app U
            (s ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x))) =
      (eqToHom ((b n).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.extensionProjection n) M).presheaf).app U
          (s ⊗ₜ[B.obj.obj U, ((D.extensionProjection n).hom.app U).hom] x))
  transition : ∀ n : ℕ,
    (a (n + 1)).E ⋙ Res (D.projection (n + 1)) ⟶ (a n).E ⋙ Res (D.projection n)
  transition_sections : ∀ (n : ℕ) (M : Mod R) (U : Cᵒᵖ)
    (s : (D.S.obj (op (n + 1))).obj.obj U) (x : M.val.obj U),
    ((transition n).app M).val.app U
      ((eqToHom ((a (n + 1)).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection (n + 1)) M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, ((D.projection (n + 1)).hom.app U).hom] x))) =
      (eqToHom ((a n).obj_eq M).symm).val.app U
        ((toSheafify J (changeOfRingsPresheaf (D.projection n) M).presheaf).app U
          (((D.S.map (homOfLE (Nat.le_succ n)).op).hom.app U s)
            ⊗ₜ[R.obj.obj U, ((D.projection n).hom.app U).hom] x))

variable {D a b}

/-- The quotient units are constructed, rather than chosen as part of the comparison.
Source: Stacks 03EK (auxiliary; not a blueprint node). -/
def OrdinaryCommonQuotientTower.unit (_O : OrdinaryCommonQuotientTower D a b) (n : ℕ) :
    𝟭 (Mod R) ⟶ (a n).E ⋙ Res (D.projection n) :=
  commonQuotientModelUnit (D.projection n) (a n)

variable (D a b)

end SheafOfModules
