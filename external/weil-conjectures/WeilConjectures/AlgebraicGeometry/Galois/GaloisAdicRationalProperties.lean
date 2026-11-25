/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Galois.GaloisAdicDataFromFinite
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.Abelian.Transfer
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.Lisse.LisseScalarFiberMaps
import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkTensorScalar
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

set_option linter.privateModule false

/-! # Integral and rational clauses of the adic correspondence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

open MonoidalCategory
open scoped TensorProduct

attribute [local instance] Sheaf.monoidalCategory
attribute [local irreducible] lisseRationalFiberFunctor Padic Padic.coefficientExtensionIntegers
  IsLisseIntegralDiagram

private theorem tensor_projection_kernel {R : Type*} [CommRing R]
    {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup M'] [AddCommGroup N'] [Module R M] [Module R N]
    [Module R M'] [Module R N'] (I : Ideal R) (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hkf : LinearMap.ker f = I • ⊤) (hkg : LinearMap.ker g = I • ⊤) :
    Function.Surjective (TensorProduct.map f g) ∧
      LinearMap.ker (TensorProduct.map f g) = I • ⊤ := by
  constructor
  · exact TensorProduct.map_surjective hf hg
  · rw [TensorProduct.map_ker f.exact_subtype_ker_map hf g.exact_subtype_ker_map hg]
    apply le_antisymm
    · apply sup_le
      · rintro _ ⟨z, rfl⟩
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          change TensorProduct.tmul R x y.val ∈ I • ⊤
          have hy : y.val ∈ I • (⊤ : Submodule R N) := by
            rw [← hkg]; exact y.property
          refine Submodule.smul_induction_on hy ?_ ?_
          · intro a ha y _
            rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro y z hy hz
            rw [TensorProduct.tmul_add]
            exact Submodule.add_mem _ hy hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
      · rintro _ ⟨z, rfl⟩
        induction z using TensorProduct.inductionOn with
        | tmul x y =>
          change TensorProduct.tmul R x.val y ∈ I • ⊤
          have hx : x.val ∈ I • (⊤ : Submodule R M) := by
            rw [← hkf]; exact x.property
          refine Submodule.smul_induction_on hx ?_ ?_
          · intro a ha x _
            rw [← TensorProduct.smul_tmul']
            exact Submodule.smul_mem_smul ha Submodule.mem_top
          · intro x z hx hz
            rw [TensorProduct.add_tmul]
            exact Submodule.add_mem _ hx hz
        | add x y hx hy =>
          rw [map_add]
          exact Submodule.add_mem _ hx hy
    · apply Submodule.smul_le.mpr
      intro a ha z hz
      clear hz
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        refine (le_sup_right : (LinearMap.rTensor N f.ker.subtype).range ≤ _) ?_
        refine ⟨TensorProduct.tmul R ⟨a • x, ?_⟩ y, ?_⟩
        · rw [hkf]
          exact Submodule.smul_mem_smul ha Submodule.mem_top
        · exact (TensorProduct.smul_tmul' a x y).symm
      | add x y hx hy =>
        rw [smul_add]
        exact Submodule.add_mem _ hx hy

private noncomputable def adicConeIsLimit
    {R : Type*} [CommRing R] (I : Ideal R) {D : ℕᵒᵖ ⥤ ModuleCat.{u + 1} R}
    (C : Cone D) [IsAdicComplete I C.pt]
    (hp : ∀ n : ℕ, Function.Surjective (C.π.app (op n)).hom ∧
      LinearMap.ker (C.π.app (op n)).hom =
        I ^ (n + 1) • (⊤ : Submodule R C.pt)) : IsLimit C := by
  classical
  let p := fun n ↦ (C.π.app (op n)).hom
  let e (n : ℕ) :
      (C.pt ⧸ (I ^ (n + 1) • ⊤ : Submodule R C.pt)) ≃ₗ[R] D.obj (op n) :=
    (Submodule.quotEquivOfEq _ _ (hp n).2.symm).trans
      ((p n).quotKerEquivOfSurjective (hp n).1)
  have he (n : ℕ) (x : C.pt) : e n (Submodule.Quotient.mk x) = p n x := rfl
  have hei (n : ℕ) (x : C.pt) : (e n).symm (p n x) = Submodule.Quotient.mk x :=
    (e n).symm_apply_apply (Submodule.Quotient.mk x)
  let a : ℕ → ℕ := fun n ↦ n + 1
  have ha : StrictMono a := fun _ _ h ↦ Nat.add_lt_add_right h 1
  let q (s : Cone D) (n : ℕ) := (e n).symm.toLinearMap.comp (s.π.app (op n)).hom
  have hq (s : Cone D) (n : ℕ) :
      (Submodule.factorPow I C.pt (ha.monotone n.le_succ)).comp (q s (n + 1)) = q s n := by
    ext x
    obtain ⟨z, hz⟩ := (hp (n + 1)).1 (s.π.app (op (n + 1)) x)
    have hC := congrArg (fun f ↦ f z) (C.w (homOfLE (Nat.le_succ n)).op)
    have hs := congrArg (fun f ↦ f x) (s.w (homOfLE (Nat.le_succ n)).op)
    change (D.map (homOfLE (Nat.le_succ n)).op) (p (n + 1) z) = p n z at hC
    change (D.map (homOfLE (Nat.le_succ n)).op)
      (s.π.app (op (n + 1)) x) = s.π.app (op n) x at hs
    change Submodule.factorPow I C.pt (ha.monotone n.le_succ)
      ((e (n + 1)).symm (s.π.app (op (n + 1)) x)) =
        (e n).symm (s.π.app (op n) x)
    rw [← hz, hei, ← hs, ← hz, hC, hei]
    rfl
  let lift (s : Cone D) : s.pt →ₗ[R] C.pt :=
    IsAdicComplete.StrictMono.lift (N := C.pt) I ha (q s) (fun {n} ↦ hq s n)
  have hlift (s : Cone D) (n : ℕ) (x : s.pt) : p n (lift s x) = s.π.app (op n) x := by
    rw [← he]
    have h := IsAdicComplete.StrictMono.mk_lift (N := C.pt) I ha (q s) (fun {n} ↦ hq s n) (n := n) x
    change Submodule.Quotient.mk (lift s x) = (e n).symm (s.π.app (op n) x) at h
    rw [h, (e n).apply_symm_apply]
  refine
    { lift := fun s ↦ ModuleCat.ofHom (lift s)
      fac := fun s j ↦ ?_
      uniq := fun s m hm ↦ ?_ }
  · ext x
    exact hlift s j.unop x
  · apply ModuleCat.hom_ext
    apply DFunLike.coe_injective
    apply IsHausdorff.StrictMono.funext I ha
    intro n x
    apply (e n).injective
    rw [he, he]
    change p n (m x) = p n (lift s x)
    rw [hlift]
    exact congrArg (fun f ↦ f x) (hm (op n))

-- Only objectwise comparisons are needed: fullness supplies all coherence maps.
@[instance_reducible]
private noncomputable def monoidalStructOfComparisons
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (T : C → C → C) (U : C)
    (μ : ∀ X Z, F.obj X ⊗ F.obj Z ≅ F.obj (T X Z)) (ε : 𝟙_ D ≅ F.obj U) :
    MonoidalCategoryStruct C where
  tensorObj := T
  tensorUnit := U
  whiskerLeft X _ _ f := F.preimage ((μ _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μ _ _).hom)
  whiskerRight f Z := F.preimage ((μ _ _).inv ≫ (F.map f ▷ F.obj Z) ≫ (μ _ _).hom)
  tensorHom f g := F.preimage ((μ _ _).inv ≫ (F.map f ⊗ₘ F.map g) ≫ (μ _ _).hom)
  associator X Z W := F.preimageIso
    (((μ _ _).symm ≪≫ ((μ _ _).symm ⊗ᵢ Iso.refl _)) ≪≫
      α_ (F.obj X) (F.obj Z) (F.obj W) ≪≫
        ((Iso.refl _ ⊗ᵢ μ _ _) ≪≫ μ _ _))
  leftUnitor X := F.preimageIso
    (((μ _ _).symm ≪≫ (ε.symm ⊗ᵢ Iso.refl _)) ≪≫ λ_ (F.obj X))
  rightUnitor X := F.preimageIso
    (((μ _ _).symm ≪≫ (Iso.refl _ ⊗ᵢ ε.symm)) ≪≫ ρ_ (F.obj X))

private noncomputable def inducingDataOfComparisons
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (T : C → C → C) (U : C)
    (μ : ∀ X Z, F.obj X ⊗ F.obj Z ≅ F.obj (T X Z)) (ε : 𝟙_ D ≅ F.obj U) :
    let := monoidalStructOfComparisons F T U μ ε
    Monoidal.InducingFunctorData F := by
  let := monoidalStructOfComparisons F T U μ ε
  exact
    { μIso := μ
      εIso := ε
      whiskerLeft_eq := by intros; apply F.map_preimage
      whiskerRight_eq := by intros; apply F.map_preimage
      tensorHom_eq := by intros; apply F.map_preimage
      associator_eq := by intros; apply F.map_preimage
      leftUnitor_eq := by intros; apply F.map_preimage
      rightUnitor_eq := by intros; apply F.map_preimage }

private theorem monoidal_of_comparisons
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (T : C → C → C) (U : C)
    (μ : ∀ X Z, Nonempty (F.obj X ⊗ F.obj Z ≅ F.obj (T X Z)))
    (ε : Nonempty (𝟙_ D ≅ F.obj U)) :
    ∃ m : MonoidalCategory C, m.toMonoidalCategoryStruct.tensorObj = T ∧
      @MonoidalCategoryStruct.tensorUnit C _ m.toMonoidalCategoryStruct = U ∧
      Nonempty (@Functor.Monoidal C _ m D _ _ F) := by
  classical
  let μ' := fun X Z ↦ (μ X Z).some
  let ε' := ε.some
  let := monoidalStructOfComparisons F T U μ' ε'
  let h := inducingDataOfComparisons F T U μ' ε'
  let m := Monoidal.induced F h
  exact ⟨m, rfl, rfl, ⟨Monoidal.fromInducedMonoidal F h⟩⟩

private theorem galoisFiniteEtale_preservesFiniteLimits (Y : Scheme.{u}) : PreservesFiniteLimits
    (ObjectProperty.ι (fun P : Y.Etale ↦ IsFinite P.hom)) := by
  let : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).HasOfPostcompProperty
      (@IsFinite ⊓ @Etale) := by
    refine ⟨fun {X Y Z} f g hg hfg ↦ ?_⟩
    have := hg.1; have := hg.2; have := hfg.1; have := hfg.2
    exact ⟨IsFinite.of_comp f g, Etale.of_comp f g⟩
  let H := MorphismProperty.Over.changeProp (Q := ⊤) (Q' := ⊤) Y
    (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale) le_rfl
  have : PreservesFiniteLimits H :=
    MorphismProperty.Over.preservesFiniteLimits_changeProp Y
      (inf_le_right : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ @Etale)
  have : PreservesFiniteLimits (FiniteEtale.toFiniteEtaleOver Y ⋙ H) := inferInstance
  exact this

private theorem galoisFLC_preservesFiniteLimits
    {Y : Scheme.{u}}
    (Φ : Y.FiniteEtale ≌ Y.FLC)
    (hΦ : Nonempty (Φ.functor ⋙ ObjectProperty.ι _ ≅
      ObjectProperty.ι _ ⋙ Y.smallEtaleTopology.uliftYoneda.{u + 1})) :
    PreservesFiniteLimits (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))) := by
  obtain ⟨α⟩ := hΦ
  let I := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))
  let : PreservesFiniteLimits
      (ObjectProperty.ι (fun P : Y.Etale ↦ IsFinite P.hom)) :=
    galoisFiniteEtale_preservesFiniteLimits Y
  let : PreservesFiniteLimits Y.smallEtaleTopology.uliftYoneda.{u + 1} :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : PreservesFiniteLimits (Φ.functor ⋙ I) :=
    preservesFiniteLimits_of_natIso α.symm
  let e : Φ.inverse ⋙ (Φ.functor ⋙ I) ≅ I :=
    (Functor.associator Φ.inverse Φ.functor I).symm ≪≫
      Functor.isoWhiskerRight Φ.counitIso I ≪≫ Functor.leftUnitor I
  exact preservesFiniteLimits_of_natIso e

section StalkActions

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) {R : Type (u + 1)} [CommRing R]

private theorem stalk_pairing_action
    [HasFiniteProducts Y.FLC]
    [PreservesFiniteProducts (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (F H K : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (hF : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F))
    (hH : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R H))
    (hK : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R K))
    (κF : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) ≃
      ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj (galoisUnderlyingSetSheaf R F))
    (κH : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj H) ≃
      ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj (galoisUnderlyingSetSheaf R H))
    (κK : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj K) ≃
      ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj (galoisUnderlyingSetSheaf R K))
    (hgF : ∀ U x z, κF ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ F.obj z) =
      (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R F).obj z)
    (hgH : ∀ U x z, κH ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ H.obj z) =
      (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R H).obj z)
    (hgK : ∀ U x z, κK ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ K.obj z) =
      (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R K).obj z)
    (ν : F.obj ⊗ H.obj ⟶ K.obj)
    (β : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F) ⊗
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj H) ⟶
      (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj K))
    (hβ : ∀ U x,
      ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ F.obj ⊗ₘ
        (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ H.obj) ≫ β =
      ν.app (op U) ≫ (pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ K.obj)
    (σ : Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (a : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj F)
    (b : ((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj H) :
    κK (β (κF.symm (σ.asIso.hom.app (galoisUnderlyingFLC R F hF) (κF a)) ⊗ₜ[R]
      κH.symm (σ.asIso.hom.app (galoisUnderlyingFLC R H hH) (κH b)))) =
      σ.asIso.hom.app (galoisUnderlyingFLC R K hK) (κK (β (a ⊗ₜ[R] b))) := by
  classical
  let p := pointSmallEtale y
  let T : Y.FLC ⥤ Type (u + 1) := ObjectProperty.ι _ ⋙ p.sheafFiber
  let : AB5OfSize.{u, u} (Type (u + 1)) :=
    AB5OfSize_of_univLE.{u, u, u + 1, u + 1} (Type (u + 1))
  let : PreservesFiniteLimits (p.sheafFiber (A := Type (u + 1))) := inferInstance
  let : PreservesFiniteProducts T := inferInstance
  let X := galoisUnderlyingFLC R F hF
  let Z := galoisUnderlyingFLC R H hH
  let W := galoisUnderlyingFLC R K hK
  let P := X ⨯ Z
  let π₁ : P ⟶ X := prod.fst
  let π₂ : P ⟶ Z := prod.snd
  let s₁ (U : Y.Etaleᵒᵖ) : P.obj.obj.obj U → F.obj.obj U :=
    fun z ↦ π₁.hom.hom.app U z
  let s₂ (U : Y.Etaleᵒᵖ) : P.obj.obj.obj U → H.obj.obj U :=
    fun z ↦ π₂.hom.hom.app U z
  let f : P ⟶ W := ObjectProperty.homMk
    { hom :=
        { app := fun U ↦ TypeCat.ofHom (fun z ↦ ν.app U
            (s₁ U z ⊗ₜ[R] s₂ U z))
          naturality := by
            intro U V i
            ext z
            have h₁ := ConcreteCategory.congr_hom (π₁.hom.hom.naturality i) z
            have h₂ := ConcreteCategory.congr_hom (π₂.hom.hom.naturality i) z
            have hn := ConcreteCategory.congr_hom (ν.naturality i)
              (s₁ U z ⊗ₜ[R] s₂ U z)
            change s₁ V (P.obj.obj.map i z) =
              F.obj.map i (s₁ U z) at h₁
            change s₂ V (P.obj.obj.map i z) =
              H.obj.map i (s₂ U z) at h₂
            change ν.app V (s₁ V (P.obj.obj.map i z) ⊗ₜ[R]
              s₂ V (P.obj.obj.map i z)) = K.obj.map i
                (ν.app U (s₁ U z ⊗ₜ[R] s₂ U z))
            rw [h₁, h₂]
            exact hn } }
  have hf (w : T.obj P) : T.map f w =
      κK (β (κF.symm (T.map π₁ w) ⊗ₜ[R] κH.symm (T.map π₂ w))) := by
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := P.obj.obj) w
    have hn := p.toPresheafFiber_naturality_apply f.hom.hom U x s
    have h₁ := p.toPresheafFiber_naturality_apply π₁.hom.hom U x s
    have h₂ := p.toPresheafFiber_naturality_apply π₂.hom.hom U x s
    change T.map f (p.toPresheafFiber U x P.obj.obj s) =
      p.toPresheafFiber U x (galoisUnderlyingSetSheaf R K).obj _ at hn
    change T.map π₁ (p.toPresheafFiber U x P.obj.obj s) =
      p.toPresheafFiber U x (galoisUnderlyingSetSheaf R F).obj _ at h₁
    change T.map π₂ (p.toPresheafFiber U x P.obj.obj s) =
      p.toPresheafFiber U x (galoisUnderlyingSetSheaf R H).obj _ at h₂
    rw [hn, h₁, h₂, ← hgF, ← hgH, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rw [← hgK]
    apply congrArg κK
    exact (ConcreteCategory.congr_hom (hβ U x)
      (s₁ (op U) s ⊗ₜ[R] s₂ (op U) s)).symm
  let e : T.obj P ≅ T.obj X × T.obj Z :=
    asIso (prodComparison T X Z) ≪≫ Types.binaryProductIso _ _
  let w := e.inv (κF a, κH b)
  have hw₁ : T.map π₁ w = κF a := by
    have he : e.hom ≫ TypeCat.ofHom
        (Prod.fst : T.obj X × T.obj Z → T.obj X) = T.map π₁ := by
      simp only [e, Iso.trans_hom, asIso_hom, Category.assoc,
        Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
      rfl
    have hi : e.inv ≫ T.map π₁ = TypeCat.ofHom
        (Prod.fst : T.obj X × T.obj Z → T.obj X) := by
      rw [← he, Iso.inv_hom_id_assoc]
    exact congrArg (fun k : TypeCat.Hom (T.obj X × T.obj Z) (T.obj X) ↦
      k.hom (κF a, κH b)) hi
  have hw₂ : T.map π₂ w = κH b := by
    have he : e.hom ≫ TypeCat.ofHom
        (Prod.snd : T.obj X × T.obj Z → T.obj Z) = T.map π₂ := by
      simp only [e, Iso.trans_hom, asIso_hom, Category.assoc,
        Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
      rfl
    have hi : e.inv ≫ T.map π₂ = TypeCat.ofHom
        (Prod.snd : T.obj X × T.obj Z → T.obj Z) := by
      rw [← he, Iso.inv_hom_id_assoc]
    exact congrArg (fun k : TypeCat.Hom (T.obj X × T.obj Z) (T.obj Z) ↦
      k.hom (κF a, κH b)) hi
  have hn₁ := ConcreteCategory.congr_hom (σ.asIso.hom.naturality π₁) w
  have hn₂ := ConcreteCategory.congr_hom (σ.asIso.hom.naturality π₂) w
  have hn := ConcreteCategory.congr_hom (σ.asIso.hom.naturality f) w
  change σ.asIso.hom.app X (T.map π₁ w) = T.map π₁ (σ.asIso.hom.app P w) at hn₁
  change σ.asIso.hom.app Z (T.map π₂ w) = T.map π₂ (σ.asIso.hom.app P w) at hn₂
  change σ.asIso.hom.app W (T.map f w) = T.map f (σ.asIso.hom.app P w) at hn
  rw [hf, hf, ← hn₁, ← hn₂, hw₁, hw₂,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hn
  exact hn.symm

private theorem constant_germ (M : ModuleCat.{u + 1} R)
    (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (a : M) :
    let p := (pointSmallEtale y).ulift.{u + 1}
    let C := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
    let j := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
    p.toPresheafFiber U ⟨x⟩ C.obj (j.app (op U) a) =
      (p.sheafFiberConstantSheafIso M).inv a := by
  dsimp only
  let p := (pointSmallEtale y).ulift.{u + 1}
  let j := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let e := p.sheafFiberConstantSheafIso M
  apply e.toLinearEquiv.injective
  change e.hom (p.toPresheafFiber U ⟨x⟩
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M).obj
      (j.app (op U) a)) = e.hom (e.inv a)
  rw [ModuleCat.hom_inv_apply]
  have hj := ConcreteCategory.congr_hom (p.toPresheafFiber_naturality j U ⟨x⟩) a
  change p.presheafFiber.map j
      (p.toPresheafFiber U ⟨x⟩ ((Functor.const Y.Etaleᵒᵖ).obj M) a) =
    p.toPresheafFiber U ⟨x⟩
    ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M).obj (j.app (op U) a) at hj
  rw [← hj]
  change (p.presheafFiberConstIso M).hom
      ((inv (p.presheafFiber.map j)) ((p.presheafFiber.map j)
        (p.toPresheafFiber U ⟨x⟩ ((Functor.const Y.Etaleᵒᵖ).obj M) a))) = a
  have hi := ConcreteCategory.congr_hom (IsIso.hom_inv_id (p.presheafFiber.map j))
    (p.toPresheafFiber U ⟨x⟩ ((Functor.const Y.Etaleᵒᵖ).obj M) a)
  change (inv (p.presheafFiber.map j)) ((p.presheafFiber.map j)
      (p.toPresheafFiber U ⟨x⟩ ((Functor.const Y.Etaleᵒᵖ).obj M) a)) =
    p.toPresheafFiber U ⟨x⟩ ((Functor.const Y.Etaleᵒᵖ).obj M) a at hi
  rw [hi]
  exact ConcreteCategory.congr_hom
    (p.toPresheafFiber_presheafFiberConstIso_hom M U ⟨x⟩) a

private theorem stalk_constant_action (M : ModuleCat.{u + 1} R)
    (h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)))
    (κ : (((pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)) ≃
      ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj (galoisUnderlyingSetSheaf R
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)))
    (hg : ∀ U x z, κ ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M).obj z) =
      (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf R
        ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)).obj z)
    (σ : Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
      (pointSmallEtale y).sheafFiber (A := Type (u + 1))))
    (z : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj (galoisUnderlyingSetSheaf R
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M))) :
    σ.asIso.hom.app (galoisUnderlyingFLC R _ h) z = z := by
  classical
  let p := pointSmallEtale y
  let C := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  let X := galoisUnderlyingFLC R C h
  let j := toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj M)
  let a := (p.ulift.{u + 1}.sheafFiberConstantSheafIso M).hom (κ.symm z)
  let f : X ⟶ X := ObjectProperty.homMk
    { hom :=
        { app := fun U ↦ TypeCat.ofHom (fun _ ↦ j.app U a)
          naturality := fun U V i ↦ by
            ext s
            exact ConcreteCategory.congr_hom (j.naturality i) a } }
  let T := ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙ p.sheafFiber
  have hf (w : T.obj X) : T.map f w = z := by
    obtain ⟨U, x, s, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := X.obj.obj) w
    have hn := p.toPresheafFiber_naturality_apply f.hom.hom U x s
    change T.map f (p.toPresheafFiber U x X.obj.obj s) =
      p.toPresheafFiber U x (galoisUnderlyingSetSheaf R C).obj (j.app (op U) a) at hn
    rw [hn, ← hg, constant_germ]
    have he := ConcreteCategory.congr_hom
      ((p.ulift.{u + 1}.sheafFiberConstantSheafIso M).hom_inv_id) (κ.symm z)
    change (p.ulift.{u + 1}.sheafFiberConstantSheafIso M).inv a = κ.symm z at he
    rw [he, κ.apply_symm_apply]
  have hn := ConcreteCategory.congr_hom (σ.asIso.hom.naturality f) z
  change σ.asIso.hom.app X (T.map f z) = T.map f (σ.asIso.hom.app X z) at hn
  rw [hf, hf] at hn
  exact hn

end StalkActions

section ScalarComparisons

variable {R E : Type (u + 1)} [CommRing R] [CommRing E] [Algebra R E]
  {G : Type u} [Group G]
section TensorLinear

variable {A B C M N L : Type (u + 1)}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup L]
  [Module R A] [Module R B] [Module R C] [Module R M] [Module R N] [Module R L]

private noncomputable def tensor_linear_comparison
    (τF : A ≃ₗ[R] M) (τH : B ≃ₗ[R] N) (τK : C ≃ₗ[R] L)
    (t : M ⊗[R] N ≃ₗ[R] L) : A ⊗[R] B ≃ₗ[R] C :=
  ((TensorProduct.congr τF τH).trans t).trans τK.symm

private theorem tensor_linear_comparison_apply
    (τF : A ≃ₗ[R] M) (τH : B ≃ₗ[R] N) (τK : C ≃ₗ[R] L)
    (t : M ⊗[R] N ≃ₗ[R] L) (x : A) (z : B) :
    τK (tensor_linear_comparison τF τH τK t (x ⊗ₜ[R] z)) = t (τF x ⊗ₜ[R] τH z) := by
  simp only [tensor_linear_comparison, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.apply_symm_apply]

end TensorLinear

private theorem module_tensor_projection
    {A B M N L P : ModuleCat.{u + 1} R} (t : A ⊗ B ⟶ L) (p : L ⟶ P)
    (f : A ⟶ M) (g : B ⟶ N) (μ : M ⊗ N ⟶ P)
    (h : t ≫ p = (f ⊗ₘ g) ≫ μ) (x : A) (z : B) :
    p (t (x ⊗ₜ[R] z)) = μ (f x ⊗ₜ[R] g z) := by
  have hh := congrArg (fun k : A ⊗ B ⟶ P ↦ k (x ⊗ₜ[R] z)) h
  simpa only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.tensorHom_tmul] using hh

private theorem unit_iso_of_fixed (X : Rep.{u + 1} R G) (e : X.V ≃ₗ[R] R)
    (hfix : ∀ g z, X.ρ g z = z) : Nonempty (X ≅ Rep.trivial R G R) := by
  refine ⟨Rep.mkIso { e with isIntertwining' := ?_ }⟩
  intro g
  apply LinearMap.ext
  intro z
  change e (X.ρ g z) = e z
  exact congrArg e (hfix g z)

private theorem tensorAction_eq {R : Type (u + 1)} [CommRing R]
    {G : Type u} [Group G] (X Z : Rep.{u + 1} R G) (g : G)
    (w : X.V ⊗[R] Z.V) :
    galoisTensorAction R X Z g w = (X ⊗ Z).ρ g w := rfl

private theorem tensor_equivariant_of_pure
    (X Z W : Rep.{u + 1} R G) (β : X.V ⊗[R] Z.V ≃ₗ[R] W.V)
    (hp : ∀ g x z, β (X.ρ g x ⊗ₜ[R] Z.ρ g z) = W.ρ g (β (x ⊗ₜ[R] z))) :
    ∀ g w, β (galoisTensorAction R X Z g w) = W.ρ g (β w) := by
  intro g w
  rw [tensorAction_eq]
  change β (TensorProduct.map (X.ρ g) (Z.ρ g) w) = W.ρ g (β w)
  have h : β.toLinearMap.comp (TensorProduct.map (X.ρ g) (Z.ρ g)) =
      (W.ρ g).comp β.toLinearMap := by
    apply TensorProduct.ext'
    exact hp g
  exact LinearMap.congr_fun h w

private theorem tensor_iso_of_comparison
    (X Z W : Rep.{u + 1} R G) (e : X.V ⊗[R] Z.V ≃ₗ[R] W.V)
    (he : ∀ g w, e (galoisTensorAction R X Z g w) = W.ρ g (e w)) :
    Nonempty (X ⊗ Z ≅ W) := by
  refine ⟨Rep.mkIso { e with isIntertwining' := ?_ }⟩
  intro g
  apply LinearMap.ext
  intro w
  change e ((X ⊗ Z).ρ g w) = W.ρ g (e w)
  rw [← tensorAction_eq]
  exact he g w

private theorem scalar_tensor_comparison
    (X Z W : Rep.{u + 1} R G) (X' Z' W' : Rep.{u + 1} E G)
    (e : X.V ⊗[R] Z.V ≃ₗ[R] W.V)
    (he : ∀ g w, e (galoisTensorAction R X Z g w) = W.ρ g (e w))
    (ηF : E ⊗[R] X.V ≃ₗ[E] X'.V)
    (ηH : E ⊗[R] Z.V ≃ₗ[E] Z'.V)
    (ηT : E ⊗[R] W.V ≃ₗ[E] W'.V)
    (hF : ∀ g a x, ηF (a ⊗ₜ[R] X.ρ g x) = X'.ρ g (ηF (a ⊗ₜ[R] x)))
    (hH : ∀ g a z, ηH (a ⊗ₜ[R] Z.ρ g z) = Z'.ρ g (ηH (a ⊗ₜ[R] z)))
    (hT : ∀ g a w, ηT (a ⊗ₜ[R] W.ρ g w) = W'.ρ g (ηT (a ⊗ₜ[R] w))) :
    ∃ β : X'.V ⊗[E] Z'.V ≃ₗ[E] W'.V,
      ∀ g w, β (galoisTensorAction E X' Z' g w) = W'.ρ g (β w) := by
  classical
  let t := (TensorProduct.AlgebraTensorModule.distribBaseChange R E X.V Z.V).symm
  let e' := e.baseChange R E _ _
  let β := ((TensorProduct.congr ηF.symm ηH.symm).trans t).trans (e'.trans ηT)
  have hβ (a b : E) (x : X.V) (z : Z.V) :
      β (ηF (a ⊗ₜ[R] x) ⊗ₜ[E] ηH (b ⊗ₜ[R] z)) =
        ηT ((a * b) ⊗ₜ[R] e (x ⊗ₜ[R] z)) := by
    simp only [β, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
      LinearEquiv.symm_apply_apply, t,
      TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
      e', LinearEquiv.baseChange_tmul]
  refine ⟨β, ?_⟩
  intro g w
  rw [tensorAction_eq]
  change β (TensorProduct.map (X'.ρ g) (Z'.ρ g) w) = W'.ρ g (β w)
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simp only [map_add, hw, hw']
  | tmul x z =>
      obtain ⟨x, rfl⟩ := ηF.surjective x
      obtain ⟨z, rfl⟩ := ηH.surjective z
      induction x using TensorProduct.inductionOn with
      | add x x' hx hx' => simp only [map_add, TensorProduct.add_tmul, hx, hx']
      | tmul a x =>
          induction z using TensorProduct.inductionOn with
          | add z z' hz hz' => simp only [map_add, TensorProduct.tmul_add, hz, hz']
          | tmul b z =>
              rw [TensorProduct.map_tmul,
                ← hF, ← hH, hβ, hβ, ← hT]
              apply congrArg (fun v ↦ ηT ((a * b) ⊗ₜ[R] v))
              have h := he g (x ⊗ₜ[R] z)
              rw [tensorAction_eq] at h
              change e (TensorProduct.map (X.ρ g) (Z.ρ g) (x ⊗ₜ[R] z)) = _ at h
              simpa only [TensorProduct.map_tmul] using h

private theorem scalar_unit_comparison (X : Rep.{u + 1} R G) (X' : Rep.{u + 1} E G)
    (e : X ≅ Rep.trivial R G R) (η : E ⊗[R] X.V ≃ₗ[E] X'.V)
    (hη : ∀ g a z, η (a ⊗ₜ[R] X.ρ g z) = X'.ρ g (η (a ⊗ₜ[R] z))) :
    Nonempty (X' ≅ Rep.trivial E G E) := by
  let e₀ := ((forget₂ (Rep.{u + 1} R G) (ModuleCat.{u + 1} R)).mapIso e).toLinearEquiv
  let β := η.symm.trans ((e₀.baseChange R E _ _).trans
    (TensorProduct.AlgebraTensorModule.rid R E E))
  have hβ (a : E) (z : X.V) : β (η (a ⊗ₜ[R] z)) = (e₀ z) • a := by
    simp only [β, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  refine ⟨Rep.mkIso { β with isIntertwining' := ?_ }⟩
  intro g
  apply LinearMap.ext
  intro z
  obtain ⟨z, rfl⟩ := η.surjective z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a z =>
      change β (X'.ρ g (η (a ⊗ₜ[R] z))) = β (η (a ⊗ₜ[R] z))
      rw [← hη, hβ, hβ]
      have he := Rep.hom_comm_apply e.hom g z
      change e₀ (X.ρ g z) = e₀ z at he
      rw [he]

end ScalarComparisons

section CoefficientAbelian

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {G : Type u} [Group G] [TopologicalSpace G]
  (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)

private abbrev coefficientProperty : ObjectProperty (Rep.{u + 1} E G) :=
  fun X ↦ Representation.IsContinuousCoefficient l E P X.V
    ((galoisRepLinearAction E X).comp δ.symm.toMonoidHom)

private theorem coefficient_subobjects :
    (coefficientProperty l E P δ).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := by
    classical
    let : FiniteDimensional E Y.V := hY.1
    have hf : Function.Injective f.hom := (Rep.mono_iff_injective f).mp inferInstance
    let : FiniteDimensional E X.V := Module.Finite.of_injective f.hom.toLinearMap hf
    refine ⟨inferInstance, ?_⟩
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace X.V := moduleTopology E X.V
    let : TopologicalSpace Y.V := moduleTopology E Y.V
    let : ContinuousAdd X.V := IsModuleTopology.toContinuousAdd E X.V
    let : ContinuousAdd Y.V := IsModuleTopology.toContinuousAdd E Y.V
    obtain ⟨r, hr⟩ := f.hom.toLinearMap.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hf)
    have hc := (IsModuleTopology.continuous_of_linearMap r).comp
      (hY.2.comp (continuous_fst.prodMk
        ((IsModuleTopology.continuous_of_linearMap f.hom.toLinearMap).comp continuous_snd)))
    apply hc.congr
    intro ⟨g, x⟩
    change r (Y.ρ (δ.symm g) (f.hom x)) = X.ρ (δ.symm g) x
    rw [← Rep.hom_comm_apply f]
    exact LinearMap.congr_fun hr (X.ρ (δ.symm g) x)

private theorem coefficient_quotients :
    (coefficientProperty l E P δ).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := by
    classical
    let : FiniteDimensional E X.V := hX.1
    have hf : Function.Surjective f.hom := (Rep.epi_iff_surjective f).mp inferInstance
    let : FiniteDimensional E Y.V := Module.Finite.of_surjective f.hom.toLinearMap hf
    refine ⟨inferInstance, ?_⟩
    let := spectralNorm.nontriviallyNormedField ℚ_[l] E
    let : TopologicalSpace X.V := moduleTopology E X.V
    let : TopologicalSpace Y.V := moduleTopology E Y.V
    let : ContinuousAdd X.V := IsModuleTopology.toContinuousAdd E X.V
    let : ContinuousAdd Y.V := IsModuleTopology.toContinuousAdd E Y.V
    obtain ⟨r, hr⟩ := f.hom.toLinearMap.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hf)
    have hc := (IsModuleTopology.continuous_of_linearMap f.hom.toLinearMap).comp
      (hX.2.comp (continuous_fst.prodMk
        ((IsModuleTopology.continuous_of_linearMap r).comp continuous_snd)))
    apply hc.congr
    intro ⟨g, x⟩
    change f.hom (X.ρ (δ.symm g) (r x)) = Y.ρ (δ.symm g) x
    rw [Rep.hom_comm_apply]
    exact congrArg (Y.ρ (δ.symm g)) (LinearMap.congr_fun hr x)

private theorem coefficient_product (X Z : Rep.{u + 1} E G)
    (hX : coefficientProperty l E P δ X) (hZ : coefficientProperty l E P δ Z) :
    coefficientProperty l E P δ (Rep.of (X.ρ.prod Z.ρ)) := by
  let : FiniteDimensional E X.V := hX.1
  let : FiniteDimensional E Z.V := hZ.1
  refine ⟨inferInstance, ?_⟩
  let := spectralNorm.nontriviallyNormedField ℚ_[l] E
  let : TopologicalSpace X.V := moduleTopology E X.V
  let : TopologicalSpace Z.V := moduleTopology E Z.V
  let : ContinuousAdd X.V := IsModuleTopology.toContinuousAdd E X.V
  let : ContinuousAdd Z.V := IsModuleTopology.toContinuousAdd E Z.V
  let τ : TopologicalSpace (X.V × Z.V) := inferInstance
  have hτ : τ = moduleTopology E (X.V × Z.V) :=
    eq_moduleTopology E (X.V × Z.V)
  change @Continuous (P × (X.V × Z.V)) (X.V × Z.V)
    (@instTopologicalSpaceProd _ _ _ (moduleTopology E (X.V × Z.V)))
    (moduleTopology E (X.V × Z.V)) _
  rw [← hτ]
  have hfst := IsModuleTopology.continuous_of_linearMap (LinearMap.fst E X.V Z.V)
  have hsnd := IsModuleTopology.continuous_of_linearMap (LinearMap.snd E X.V Z.V)
  have hc := (hX.2.comp (continuous_fst.prodMk (hfst.comp continuous_snd))).prodMk
    (hZ.2.comp (continuous_fst.prodMk (hsnd.comp continuous_snd)))
  exact hc

private theorem coefficient_abelian :
    Nonempty (Abelian (galoisCoefficientRepresentations l E P δ)) := by
  classical
  let C := coefficientProperty l E P δ
  have : C.IsClosedUnderSubobjects := coefficient_subobjects l E P δ
  have : C.IsClosedUnderQuotients := coefficient_quotients l E P δ
  have : C.ContainsZero := by
    refine ⟨⟨Rep.trivial E G PUnit, ?_, ?_⟩⟩
    · apply (IsZero.iff_id_eq_zero _).mpr
      ext x
    · refine ⟨inferInstance, ?_⟩
      let := spectralNorm.nontriviallyNormedField ℚ_[l] E
      let : TopologicalSpace PUnit := moduleTopology E PUnit
      exact (continuous_const : Continuous
        (fun _ : P × PUnit.{u + 2} ↦ PUnit.unit)).congr (fun _ ↦ Subsingleton.elim _ _)
  have : C.IsClosedUnderBinaryProducts := .mk' (by
    rintro _ ⟨D, hD⟩
    let X := D.obj ⟨.left⟩
    let Z := D.obj ⟨.right⟩
    let W := Rep.of (X.ρ.prod Z.ρ)
    let π₁ : W ⟶ X := Rep.ofHom (.fst E X.ρ Z.ρ)
    let π₂ : W ⟶ Z := Rep.ofHom (.snd E X.ρ Z.ρ)
    let c := BinaryFan.mk π₁ π₂
    have hc : IsLimit c := BinaryFan.isLimitMk
      (fun S ↦ Rep.ofHom (Representation.IntertwiningMap.prod S.fst.hom S.snd.hom))
      (by intros; rfl) (by intros; rfl) (by
        intro S m hm₁ hm₂
        apply Rep.hom_ext
        apply Representation.IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        exact Prod.ext (congrArg (fun f ↦ f.hom x) hm₁)
          (congrArg (fun f ↦ f.hom x) hm₂))
    exact C.prop_of_iso
      (hc.conePointUniqueUpToIso (limit.isLimit (pair X Z)) ≪≫
        (HasLimit.isoOfNatIso (diagramIsoPair D)).symm)
      (coefficient_product l E P δ X Z (hD ⟨.left⟩) (hD ⟨.right⟩)))
  have : C.IsClosedUnderFiniteProducts := .mk'
  exact ⟨inferInstanceAs (Abelian C.FullSubcategory)⟩

end CoefficientAbelian

section IntegralFiberTensor

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (l : ℕ) [Fact l.Prime]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]

private noncomputable def integralTensorCone (F H : LisseIntegralSheaf l E Y) :
    Cone ((lisseIntegralTensor l E Y F H).obj ⋙
      (pointSmallEtale y).ulift.{u + 1}.sheafFiber) where
  pt := lisseIntegralFiber l E Y y F ⊗ lisseIntegralFiber l E Y y H
  π :=
    { app j := (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) j ⊗ₘ
          limit.π (H.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) j) ≫
        Functor.LaxMonoidal.μ ((pointSmallEtale y).ulift.{u + 1}.sheafFiber)
          (F.obj.obj j) (H.obj.obj j)
      naturality i j f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber
          (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        change _ = _ ≫ T.map (F.obj.map f ⊗ₘ H.obj.map f)
        rw [Category.assoc, ← Functor.LaxMonoidal.μ_natural, ← Category.assoc,
          tensorHom_comp_tensorHom]
        have hF := limit.w (F.obj ⋙ T) f
        have hH := limit.w (H.obj ⋙ T) f
        change limit.π (F.obj ⋙ T) i ≫ T.map (F.obj.map f) =
          limit.π (F.obj ⋙ T) j at hF
        change limit.π (H.obj ⋙ T) i ≫ T.map (H.obj.map f) =
          limit.π (H.obj ⋙ T) j at hH
        rw [hF, hH] }

private noncomputable def integralTensorConeIsLimit (F H : LisseIntegralSheaf l E Y) :
    IsLimit (integralTensorCone y l E F H) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  let M := lisseIntegralFiber l E Y y F
  let N := lisseIntegralFiber l E Y y H
  have : Module.Finite R M := lisseIntegralFiber_finite Y y l E F
  have : Module.Finite R N := lisseIntegralFiber_finite Y y l E H
  let : IsAdicComplete I (integralTensorCone y l E F H).pt := by
    change IsAdicComplete I (M ⊗[R] N)
    exact AdicCompletion.of_bijective_iff.mp
      ((Padic.finite_module_adic_complete_and_hom.{u + 1, u + 1, u + 1} l E).1
        (M ⊗[R] N)).2.1
  apply adicConeIsLimit I
  intro n
  have hF := lisseIntegralFiber_projection Y y l E F n
  have hH := lisseIntegralFiber_projection Y y l E H n
  have ht := tensor_projection_kernel (I ^ (n + 1)) _ _ hF.1 hH.1 hF.2 hH.2
  let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
  let e := (Functor.Monoidal.μIso T (F.obj.obj (op n)) (H.obj.obj (op n))).toLinearEquiv
  constructor
  · exact e.surjective.comp ht.1
  · change LinearMap.ker (e.toLinearMap.comp _) = _
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr e.injective,
      Submodule.comap_bot]
    exact ht.2

private noncomputable def integralFiberTensorIso (F H : LisseIntegralSheaf l E Y) :
    (lisseIntegralFiber l E Y y F ⊗ lisseIntegralFiber l E Y y H) ≅
      lisseIntegralFiber l E Y y (lisseIntegralTensor l E Y F H) :=
  (integralTensorConeIsLimit y l E F H).conePointUniqueUpToIso (limit.isLimit _)

private theorem integralFiberTensorIso_hom_π (F H : LisseIntegralSheaf l E Y)
    (j : ℕᵒᵖ) :
    let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber
      (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
    (integralFiberTensorIso y l E F H).hom ≫
        limit.π ((lisseIntegralTensor l E Y F H).obj ⋙ T) j =
      (limit.π (F.obj ⋙ T) j ⊗ₘ limit.π (H.obj ⋙ T) j) ≫
        Functor.LaxMonoidal.μ T (F.obj.obj j) (H.obj.obj j) := by
  dsimp only
  exact (integralTensorConeIsLimit y l E F H).conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) j

private noncomputable def integralUnitCone :
    Cone ((lisseIntegralUnit l E Y).obj ⋙
      (pointSmallEtale y).ulift.{u + 1}.sheafFiber) where
  pt := ModuleCat.of (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionIntegers l E)
  π :=
    { app j := ModuleCat.ofHom
        (Submodule.mkQ (Padic.coefficientExtensionIdeal l E (j.unop + 1))) ≫
        ((pointSmallEtale y).ulift.{u + 1}.sheafFiberConstantSheafIso
          (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionRing l E (j.unop + 1)))).inv
      naturality i j f := by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
        apply (cancel_mono ((pointSmallEtale y).ulift.{u + 1}.sheafFiberConstantSheafIso
          (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
            (Padic.coefficientExtensionRing l E (j.unop + 1)))).hom).mp
        dsimp only [lisseIntegralUnit, lisseIntegralUnitDiagram, Functor.comp_map]
        simp only [Category.assoc]
        rw [(pointSmallEtale y).ulift.{u + 1}.sheafFiberConstantSheafIso_hom_naturality,
          Iso.inv_hom_id_assoc, Iso.inv_hom_id]
        ext
        rfl }

private noncomputable def integralUnitConeIsLimit : IsLimit (integralUnitCone y l E) := by
  let R := Padic.coefficientExtensionIntegers l E
  let I := Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R)
  let : IsAdicComplete I (integralUnitCone y l E).pt := by
    change IsAdicComplete I R
    exact AdicCompletion.of_bijective_iff.mp
      ((Padic.finite_module_adic_complete_and_hom.{u + 1, u + 1, u + 1} l E).1 R).2.1
  apply adicConeIsLimit I
  intro n
  let e := ((pointSmallEtale y).ulift.{u + 1}.sheafFiberConstantSheafIso
    (ModuleCat.of R (Padic.coefficientExtensionRing l E (n + 1)))).symm.toLinearEquiv
  constructor
  · exact e.surjective.comp (Submodule.mkQ_surjective _)
  · change LinearMap.ker (e.toLinearMap.comp (Submodule.mkQ _)) = _
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr e.injective,
      Submodule.comap_bot, Submodule.ker_mkQ]
    change I ^ (n + 1) = I ^ (n + 1) • (⊤ : Ideal R)
    rw [Ideal.smul_eq_mul, Ideal.mul_top]

private noncomputable def integralFiberUnitIso :
    ModuleCat.of (Padic.coefficientExtensionIntegers l E)
      (Padic.coefficientExtensionIntegers l E) ≅
      lisseIntegralFiber l E Y y (lisseIntegralUnit l E Y) :=
  (integralUnitConeIsLimit y l E).conePointUniqueUpToIso (limit.isLimit _)

end IntegralFiberTensor

section GenericIntegralActions

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  (y : Spec (.of Ω) ⟶ Y) (l : ℕ) [Fact l.Prime]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {G : Type u} [Group G]
  (r : LisseIntegralSheaf l E Y → Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
  (τ : ∀ F, (r F).V ≃ₗ[Padic.coefficientExtensionIntegers l E]
    lisseIntegralFiber l E Y y F)
  (σ : G → Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
    (pointSmallEtale y).sheafFiber (A := Type (u + 1))))

private def integralNormalizedAction : Prop :=
  ∀ (F : LisseIntegralSheaf l E Y) (n : ℕ), ∃ h :
    IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
    (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))), ∃ κ : (((pointSmallEtale
    y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l
    E))).obj (F.obj.obj (op n))) ≃ (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
    (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n)))), (∀
    (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (z : (F.obj.obj (op n)).obj.obj (op U)), κ
    ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ (F.obj.obj (op n)).obj z) =
    (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf
    (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n))).obj z) ∧
    ∀ (g : G) (z : (r F).V),
      κ (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
        (τ F ((r F).ρ g z))) = (σ g).asIso.hom.app
    (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E) (F.obj.obj (op n)) h) (κ
    (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) (τ F z)))

attribute [local irreducible] integralFiberTensorIso integralFiberUnitIso
  tensor_linear_comparison

attribute [local irreducible] Representation.IsContinuousIntegral
  Representation.IsContinuousCoefficient Representation.IsLAdic galoisUnderlyingSetSheaf
  galoisTensorAction galoisRepLinearAction constantSheaf
  GrothendieckTopology.Point.sheafFiber GrothendieckTopology.Point.presheafFiber

-- Comparisons use the normalized finite stalk actions.
private theorem integral_tensor_generic
    [HasFiniteLimits Y.FLC]
    [PreservesFiniteLimits (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)))]
    (hn : integralNormalizedAction y l E r τ σ) :
    ∀ F H, ∃ β : (r F).V ⊗[Padic.coefficientExtensionIntegers l E] (r H).V ≃ₗ[
      Padic.coefficientExtensionIntegers l E] (r (lisseIntegralTensor l E Y F H)).V,
      ∀ g w, β (galoisTensorAction _ (r F) (r H) g w) =
        (r (lisseIntegralTensor l E Y F H)).ρ g (β w) := by
  classical
  have heval := hn
  intro F H
  let R := Padic.coefficientExtensionIntegers l E
  let K := lisseIntegralTensor l E Y F H
  let := (sheafificationAdjunction Y.smallEtaleTopology
    (ModuleCat.{u + 1} R)).rightAdjointLaxMonoidal
  let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
  let τF : (r F).V ≃ₗ[R]
      lisseIntegralFiber l E Y y F := τ F
  let τH : (r H).V ≃ₗ[R]
      lisseIntegralFiber l E Y y H := τ H
  let τK : (r K).V ≃ₗ[R]
      lisseIntegralFiber l E Y y K := τ K
  let t := integralFiberTensorIso y l E F H
  let β : (r F).V ⊗[R]
      (r H).V ≃ₗ[R] (r K).V :=
    tensor_linear_comparison τF τH τK t.toLinearEquiv
  have hβ (n : ℕ) (x) (z) :
      limit.π (K.obj ⋙ T) (op n) (τK (β (x ⊗ₜ[R] z))) =
        Functor.LaxMonoidal.μ T (F.obj.obj (op n)) (H.obj.obj (op n))
          (limit.π (F.obj ⋙ T) (op n) (τF x) ⊗ₜ[R]
            limit.π (H.obj ⋙ T) (op n) (τH z)) := by
    have h : t.hom ≫ limit.π (K.obj ⋙ T) (op n) =
        (limit.π (F.obj ⋙ T) (op n) ⊗ₘ limit.π (H.obj ⋙ T) (op n)) ≫
          Functor.LaxMonoidal.μ T (F.obj.obj (op n)) (H.obj.obj (op n)) :=
      integralFiberTensorIso_hom_π y l E F H (op n)
    have hh := module_tensor_projection t.hom (limit.π (K.obj ⋙ T) (op n))
      (limit.π (F.obj ⋙ T) (op n)) (limit.π (H.obj ⋙ T) (op n))
      (Functor.LaxMonoidal.μ T (F.obj.obj (op n)) (H.obj.obj (op n))) h (τF x) (τH z)
    have hb := tensor_linear_comparison_apply τF τH τK t.toLinearEquiv x z
    have ht := Iso.toLinearEquiv_apply t (τF x ⊗ₜ[R] τH z)
    exact (congrArg (fun v ↦ limit.π (K.obj ⋙ T) (op n) v) hb).trans
      ((congrArg (fun v ↦ limit.π (K.obj ⋙ T) (op n) v) ht).trans hh)
  refine ⟨β, tensor_equivariant_of_pure _ _ _ β ?_⟩
  intro g x z
  apply τK.injective
  apply Concrete.limit_ext (K.obj ⋙ T)
  intro j
  let n := j.unop
  obtain ⟨hF, κF, hgF, haF⟩ := heval F n
  obtain ⟨hH, κH, hgH, haH⟩ := heval H n
  obtain ⟨hK, κK, hgK, haK⟩ := heval K n
  apply κK.injective
  rw [hβ, haK, hβ]
  have hn := stalk_pairing_action y (F.obj.obj (op n)) (H.obj.obj (op n))
    (K.obj.obj (op n)) hF hH hK κF κH κK hgF hgH hgK
    (Functor.LaxMonoidal.μ (sheafToPresheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} R)) (F.obj.obj (op n)) (H.obj.obj (op n)))
    (Functor.LaxMonoidal.μ T (F.obj.obj (op n)) (H.obj.obj (op n)))
    (fun U x ↦ (etale_stalk_tensor_unique y
      (F.obj.obj (op n)) (H.obj.obj (op n))).2.1 U ⟨x⟩)
    (σ g) (limit.π (F.obj ⋙ T) (op n) (τF x))
      (limit.π (H.obj ⋙ T) (op n) (τH z))
  rw [← haF, ← haH, κF.symm_apply_apply, κH.symm_apply_apply] at hn
  exact hn

-- Comparisons use the normalized finite stalk actions.
private theorem integral_unit_generic (hn : integralNormalizedAction y l E r τ σ) :
    Nonempty (r (lisseIntegralUnit l E Y) ≅
      Rep.trivial (Padic.coefficientExtensionIntegers l E) G
        (Padic.coefficientExtensionIntegers l E)) := by
  classical
  have heval := hn
  let R := Padic.coefficientExtensionIntegers l E
  let U := lisseIntegralUnit l E Y
  let T := (pointSmallEtale y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} R)
  let τ : (r U).V ≃ₗ[R]
      lisseIntegralFiber l E Y y U := τ U
  have hρ (g : G) (z : (r U).V) :
      (r U).ρ g z = z := by
    apply τ.injective
    apply Concrete.limit_ext (U.obj ⋙ T)
    intro j
    obtain ⟨h, κ, hg, ha⟩ := heval U j.unop
    apply κ.injective
    exact (ha g z).trans (stalk_constant_action y
      (ModuleCat.of R (Padic.coefficientExtensionRing l E (j.unop + 1)))
      h κ hg (σ g) _)
  let e : (r U).V ≃ₗ[R] R :=
    τ.trans (integralFiberUnitIso y l E).symm.toLinearEquiv
  exact unit_iso_of_fixed (r U) e hρ

end GenericIntegralActions
attribute [local irreducible] integralFiberTensorIso integralFiberUnitIso
  tensor_linear_comparison

attribute [local irreducible] Representation.IsContinuousIntegral
  Representation.IsContinuousCoefficient Representation.IsLAdic galoisUnderlyingSetSheaf
  galoisTensorAction galoisRepLinearAction constantSheaf
  GrothendieckTopology.Point.sheafFiber GrothendieckTopology.Point.presheafFiber

section GenericRationalActions

variable {Y : Scheme.{u}} (l : ℕ) [Fact l.Prime]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  [IsNoetherian Y] [Y.IsSeparated] [∀ x : Y, Invertible (l : Y.residueField x)]
  {G : Type u} [Group G]
  (rI : LisseIntegralSheaf l E Y → Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G)
  (rR : LisseRationalSheaf l E Y → Rep.{u + 1} E G)
  (hloc : ∀ F, ∃ η : E ⊗[Padic.coefficientExtensionIntegers l E]
      (rI F.integral).V ≃ₗ[E] (rR F).V,
    ∀ g a z, η (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] (rI F.integral).ρ g z) =
      (rR F).ρ g (η (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] z)))

include hloc

private theorem rational_tensor_generic
    (hIT : ∀ F H, ∃ β :
      (rI F).V ⊗[Padic.coefficientExtensionIntegers l E] (rI H).V
        ≃ₗ[Padic.coefficientExtensionIntegers l E]
          (rI (lisseIntegralTensor l E Y F H)).V,
      ∀ g w, β (galoisTensorAction _ (rI F) (rI H) g w) =
        (rI (lisseIntegralTensor l E Y F H)).ρ g (β w)) :
    ∀ F H, ∃ β : (rR F).V ⊗[E] (rR H).V ≃ₗ[E]
      (rR (lisseRationalTensor l E Y F H)).V,
      ∀ g w, β (galoisTensorAction E (rR F) (rR H) g w) =
        (rR (lisseRationalTensor l E Y F H)).ρ g (β w) := by
  classical
  intro F H
  let X := rI F.integral
  let Z := rI H.integral
  obtain ⟨e, he⟩ := hIT F.integral H.integral
  obtain ⟨ηF, hF⟩ := hloc F
  obtain ⟨ηH, hH⟩ := hloc H
  obtain ⟨ηT, hT⟩ := hloc (lisseRationalTensor l E Y F H)
  obtain ⟨β, hβ⟩ := scalar_tensor_comparison X Z
    (rI (lisseIntegralTensor l E Y F.integral H.integral))
    (rR F) (rR H)
    (rR (lisseRationalTensor l E Y F H))
    e (fun g w ↦ he g w) ηF ηH ηT hF hH hT
  refine ⟨β, ?_⟩
  intro g w
  exact hβ g w

include hloc

private theorem rational_unit_generic
    (hIU : Nonempty (rI (lisseIntegralUnit l E Y) ≅
      Rep.trivial (Padic.coefficientExtensionIntegers l E) G
        (Padic.coefficientExtensionIntegers l E))) :
    Nonempty (rR (lisseRationalUnit l E Y) ≅ Rep.trivial E G E) := by
  classical
  obtain ⟨e⟩ := hIU
  obtain ⟨η, hη⟩ := hloc (lisseRationalUnit l E Y)
  exact scalar_unit_comparison
    (rI (lisseIntegralUnit l E Y))
    (rR (lisseRationalUnit l E Y)) e η hη

end GenericRationalActions
section Rationalization

variable {Y : Scheme.{u}} [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (c : GaloisLisseFiniteCorrespondence y G)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
  (d : GaloisLisseAdicData y G c l Q)

-- The normalized stalk and tensor comparisons have large dependent module types.
private theorem integralEvaluation_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisIntegralEvaluationAction y G c l Q d := by
  unfold galoisIntegralEvaluationAction
  intro E F n
  have hi := GaloisAdicCanonicalConstruction.inverseLimit
    (y := y) (G := G) (c := c) (l := l) (Q := Q) (d := d) hcanon E F
  rcases hi with ⟨V, hV⟩
  rcases hV with ⟨α, hα⟩
  rcases hα with ⟨C, hC⟩
  rcases hC with ⟨e, _, hp, hfinite⟩
  have hf := hfinite n
  rcases hf with ⟨h, hκ⟩
  rcases hκ with ⟨κ, hgerm, haction⟩
  refine ⟨h, κ, hgerm, ?_⟩
  intro g z
  have hproj (w : ((d.eI E).functor.obj F).obj.V) :
      (α.hom.app (op n)) ((e.inv ≫ C.π.app (op n)).hom w) =
        limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n)
          ((d.τI E).hom.app F w) := by
    exact congrArg (fun f ↦ f w) (hp n)
  calc
    _ = κ ((α.hom.app (op n))
        ((e.inv ≫ C.π.app (op n)).hom (((d.eI E).functor.obj F).obj.ρ g z))) :=
      congrArg κ (hproj _).symm
    _ = κ ((α.hom.app (op n))
        ((V.obj (op n)).ρ g ((e.inv ≫ C.π.app (op n)).hom z))) :=
      congrArg (fun w ↦ κ ((α.hom.app (op n)) w))
        (Rep.hom_comm_apply (e.inv ≫ C.π.app (op n)) g z)
    _ = _ := haction g _
    _ = _ := congrArg (fun w ↦ (c.γ g).asIso.hom.app
      (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val)
        (F.obj.obj (op n)) h) (κ w)) (hproj z)

-- Allow elaboration of the large dependent representation and fibre comparison types.
private theorem integral_tensor_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisIntegralTensor y G c l Q d := by
  classical
  let : HasFiniteLimits Y.FLC :=
    ⟨fun _ _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence c.Φ.inverse⟩
  let : PreservesFiniteLimits (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y))) :=
    galoisFLC_preservesFiniteLimits c.Φ c.yonedaComparison
  have heval := integralEvaluation_from_construction y G c l Q d hcanon
  intro E
  exact integral_tensor_generic y l E.val
    (fun F ↦ ((d.eI E).functor.obj F).obj)
    (fun F ↦ ((d.τI E).app F).toLinearEquiv) c.γ (heval E)

-- Allow elaboration of the large dependent representation and fibre comparison types.
private theorem integral_unit_from_construction
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d) :
    galoisIntegralUnit y G c l Q d := by
  classical
  have heval := integralEvaluation_from_construction y G c l Q d hcanon
  intro E
  exact integral_unit_generic y l E.val
    (fun F ↦ ((d.eI E).functor.obj F).obj)
    (fun F ↦ ((d.τI E).app F).toLinearEquiv) c.γ (heval E)

-- Allow elaboration of the large dependent representation and fibre comparison types.
omit [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G] in
private theorem rational_abelian :
    galoisRationalSheavesAbelian y G c l Q d ∧
      galoisRationalRepresentationsAbelian y G c l Q d := by
  have hR : galoisRationalRepresentationsAbelian y G c l Q d :=
    fun E ↦ coefficient_abelian l E.val d.P d.δ
  refine ⟨?_, hR⟩
  intro E
  let := (hR E).some
  let := Preadditive.ofFullyFaithful (d.eR E).fullyFaithfulFunctor
  let (J : ℕ) : HasLimitsOfShape (Discrete (Fin J))
      (galoisCoefficientRepresentations l E.val d.P d.δ) :=
    @HasFiniteProducts.out _ _ Abelian.has_finite_products J
  let : HasFiniteProducts (LisseRationalSheaf l E.val Y) :=
    ⟨fun J ↦ Adjunction.hasLimitsOfShape_of_equivalence (d.eR E).functor⟩
  exact ⟨abelianOfEquivalence (d.eR E).functor⟩

-- Allow elaboration of the large dependent representation and fibre comparison types.
private theorem rational_tensor_from_integral
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d)
    (hIT : galoisIntegralTensor y G c l Q d) :
    galoisRationalTensor y G c l Q d := by
  classical
  intro E
  refine rational_tensor_generic (l := l) (E := E.val)
    (rI := fun F ↦ ((d.eI E).functor.obj F).obj)
    (rR := fun F ↦ ((d.eR E).functor.obj F).obj)
    (hloc := ?_) (hIT := hIT E)
  intro F
  exact (hcanon.localization E F).imp fun _ h ↦ h.1

-- Allow elaboration of the large dependent representation and fibre comparison types.
private theorem rational_unit_from_integral
    (hcanon : GaloisAdicCanonicalConstruction y G c l Q d)
    (hIU : galoisIntegralUnit y G c l Q d) :
    galoisRationalUnit y G c l Q d := by
  classical
  intro E
  refine rational_unit_generic (l := l) (E := E.val)
    (rI := fun F ↦ ((d.eI E).functor.obj F).obj)
    (rR := fun F ↦ ((d.eR E).functor.obj F).obj)
    (hloc := ?_) (hIU := hIU E)
  intro F
  exact (hcanon.localization E F).imp fun _ h ↦ h.1

-- Allow elaboration of the large dependent representation and fibre comparison types.
omit [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G] in
private theorem integral_monoidal_from_tensor_unit
    (hIT : galoisIntegralTensor y G c l Q d)
    (hIU : galoisIntegralUnit y G c l Q d) :
    galoisIntegralMonoidal y G c l Q d := by
  intro E
  let F := (d.eI E).functor ⋙ ObjectProperty.ι _
  apply monoidal_of_comparisons F (lisseIntegralTensor l E.val Y)
    (lisseIntegralUnit l E.val Y)
  · intro X Z
    obtain ⟨e, he⟩ := hIT E X Z
    exact tensor_iso_of_comparison _ _ _ e he
  · exact ⟨(hIU E).some.symm⟩

-- Allow elaboration of the large dependent representation and fibre comparison types.
omit [ConnectedSpace Y] [IsTopologicalGroup G] [CompactSpace G]
  [IsFundamentalGroup (FiniteEtale.fiber y) G] in
private theorem rational_monoidal_from_tensor_unit
    (hRT : galoisRationalTensor y G c l Q d)
    (hRU : galoisRationalUnit y G c l Q d) :
    galoisRationalMonoidal y G c l Q d := by
  intro E
  let F := (d.eR E).functor ⋙ ObjectProperty.ι _
  apply monoidal_of_comparisons F (lisseRationalTensor l E.val Y)
    (lisseRationalUnit l E.val Y)
  · intro X Z
    obtain ⟨e, he⟩ := hRT E X Z
    exact tensor_iso_of_comparison _ _ _ e he
  · exact ⟨(hRU E).some.symm⟩

end Rationalization

end AlgebraicGeometry.Scheme
