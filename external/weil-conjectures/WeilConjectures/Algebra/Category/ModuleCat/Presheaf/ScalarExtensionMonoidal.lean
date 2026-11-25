/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct

/-! # Monoidal change of coefficients for module presheaves

Source: Stacks Project, Modules on Sites, section Presheaves of modules and
lemma-tensor-product-pullback, applied before sheafification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace PresheafOfModules

private def bottomRing {C : Type u} [SmallCategory C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u} :=
  ⟨R, Presheaf.isSheaf_bot _⟩

private def bottomModule {C : Type u} [SmallCategory C]
    {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    SheafOfModules.{u} ((sheafCompose ⊥
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (bottomRing R)) :=
  ⟨M, Presheaf.isSheaf_bot _⟩

section
variable {C : Type u} [SmallCategory C]
  {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
  (φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
    (𝟭 C).op ⋙ (S ⋙ forget₂ CommRingCat.{u} RingCat.{u}))

private abbrev coeff (X : Cᵒᵖ) : R.obj X →+* S.obj X := (φ.app X).hom

private def bottomMap : bottomRing R ⟶ bottomRing S where
  hom :=
    { app X := CommRingCat.ofHom (coeff φ X)
      naturality := by
        intro X Y f
        apply CommRingCat.hom_ext
        exact congrArg RingCat.Hom.hom (φ.naturality f) }

private def sectionExtension : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⥤
    PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u}) where
  obj M := SheafOfModules.changeOfRingsPresheaf.{u, u, u} (C := C) (J := ⊥)
    (R₁ := bottomRing R) (R₂ := bottomRing S) (bottomMap φ) (bottomModule M)
  map {M N} f :=
    { app X := (ModuleCat.extendScalars (coeff φ X)).map (f.app X)
      naturality := SheafOfModules.changeOfRingsHom_naturality.{u, u, u}
        (C := C) (J := ⊥) (R₁ := bottomRing R) (R₂ := bottomRing S)
        (bottomMap φ) (bottomModule M) (N := bottomModule N) ⟨f⟩ }
  map_id M := by
    ext1 X
    exact (ModuleCat.extendScalars (coeff φ X)).map_id _
  map_comp f g := by
    ext1 X
    exact (ModuleCat.extendScalars (coeff φ X)).map_comp _ _

local instance localInst_ScalarExtensionMonoidal_1
    {M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Module (R.obj Y)
      ((ModuleCat.restrictScalars ((R ⋙ forget₂ CommRingCat RingCat).map f).hom).obj
        (M.obj Y)) :=
  inferInstanceAs (Module (R.obj Y) (M.obj Y))

private theorem sectionExtension_map_tmul
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : S.obj X) (m : M.obj X) :
    ((sectionExtension φ).obj M).map f
      (s ⊗ₜ[R.obj X, coeff φ X] m) =
        S.map f s ⊗ₜ[R.obj Y, coeff φ Y] M.map f m :=
  Classical.choose_spec
    (SheafOfModules.exists_changeOfRingsMap.{u, u, u} (C := C) (J := ⊥)
    (R₁ := bottomRing R) (R₂ := bottomRing S) (bottomMap φ) (bottomModule M) f) s m

private theorem lift_one (X : Cᵒᵖ) (M : ModuleCat.{u} (R.obj X))
    (N : ModuleCat.{u} (S.obj X))
    (g : M ⟶ (ModuleCat.restrictScalars (coeff φ X)).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv _ _).symm g
      ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] m) = g m :=
  congrArg (fun f ↦ f m)
    (((ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv _ _).apply_symm_apply g)

private theorem unit_one (X : Cᵒᵖ) (r : R.obj X) :
    Functor.OplaxMonoidal.η (ModuleCat.extendScalars (coeff φ X))
      ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] r) = coeff φ X r := by
  exact ModuleCat.restrictScalars_η (coeff φ X) r

private def sectionHomEquiv
    (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (N : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    ((sectionExtension φ).obj M ⟶ N) ≃ (M ⟶ (pushforward φ).obj N) where
  toFun f :=
    { app X := (ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv _ _ (f.app X)
      naturality := by
        intro X Y i
        ext m
        have h := naturality_apply f i
          ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] m)
        change f.app Y ((1 : S.obj Y) ⊗ₜ[R.obj Y, coeff φ Y] M.map i m) =
          N.map i (f.app X ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] m))
        simpa only [sectionExtension_map_tmul, map_one] using h }
  invFun g :=
    { app X := ((ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv _ _).symm
        (g.app X)
      naturality := by
        intro X Y i
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        have h := naturality_apply g i m
        change (((ModuleCat.extendRestrictScalarsAdj (coeff φ Y)).homEquiv _ _).symm
          (g.app Y)) ((((sectionExtension φ).obj M).map i)
            ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] m)) =
          N.map i ((((ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv _ _).symm
            (g.app X)) ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] m))
        rw [sectionExtension_map_tmul, map_one]
        erw [lift_one, lift_one]
        exact h }
  left_inv f := by
    ext1 X
    exact Equiv.symm_apply_apply _ _
  right_inv g := by
    ext1 X
    exact Equiv.apply_symm_apply _ _

private def sectionAdjunction : sectionExtension φ ⊣ pushforward φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sectionHomEquiv φ
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        ext1 X
        exact (ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv_naturality_left_symm
          (f.app X) (g.app X)
      homEquiv_naturality_right := by
        intro M N N' f g
        ext1 X
        exact (ModuleCat.extendRestrictScalarsAdj (coeff φ X)).homEquiv_naturality_right
          (f.app X) (g.app X) }

private def sectionUnitIso :
    (sectionExtension φ).obj (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}))) ≅
        𝟙_ (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) := by
  refine isoMk (fun X ↦ Functor.Monoidal.εIso
    (ModuleCat.extendScalars (coeff φ X)) |>.symm) ?_
  intro X Y f
  apply ModuleCat.ExtendScalars.hom_ext
  intro r
  change Functor.OplaxMonoidal.η (ModuleCat.extendScalars (coeff φ Y))
    (((sectionExtension φ).obj (𝟙_ (PresheafOfModules.{u}
      (R ⋙ forget₂ CommRingCat RingCat)))).map f
        ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] r)) =
      S.map f (Functor.OplaxMonoidal.η (ModuleCat.extendScalars (coeff φ X))
        ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] r))
  rw [sectionExtension_map_tmul, map_one, unit_one, unit_one]
  exact ConcreteCategory.congr_hom (φ.naturality f) r

private def sectionTensorIso
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    (sectionExtension φ).obj (M ⊗ N) ≅
      (sectionExtension φ).obj M ⊗ (sectionExtension φ).obj N := by
  refine isoMk (fun X ↦ (Functor.Monoidal.μIso
    (ModuleCat.extendScalars (coeff φ X)) (M.obj X) (N.obj X)).symm) ?_
  intro X Y f
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
  | tmul m n =>
    change Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (coeff φ Y))
      (M.obj Y) (N.obj Y)
      (((sectionExtension φ).obj (M ⊗ N)).map f
        ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] (m ⊗ₜ[R.obj X] n))) =
        ((sectionExtension φ).obj M ⊗ (sectionExtension φ).obj N).map f
          (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (coeff φ X)) (M.obj X) (N.obj X)
            ((1 : S.obj X) ⊗ₜ[R.obj X, coeff φ X] (m ⊗ₜ[R.obj X] n)))
    rw [sectionExtension_map_tmul, map_one]
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    rw [ModuleCat.extendScalars_δ_tmul, ModuleCat.extendScalars_δ_tmul]
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul]
    rw [sectionExtension_map_tmul, sectionExtension_map_tmul, map_one]

@[instance_reducible]
private def sectionMonoidal : (sectionExtension φ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (.mk'
    (εIso := (sectionUnitIso φ).symm)
    (μIso := fun M N ↦ (sectionTensorIso φ M N).symm)
    (μIso_inv_natural_left := fun f N ↦ by
      ext1 X
      exact Functor.OplaxMonoidal.δ_natural_left
        (ModuleCat.extendScalars (coeff φ X)) (f.app X) (N.obj X))
    (μIso_inv_natural_right := fun M f ↦ by
      ext1 X
      exact Functor.OplaxMonoidal.δ_natural_right
        (ModuleCat.extendScalars (coeff φ X)) (M.obj X) (f.app X))
    (oplax_associativity := fun M N P ↦ by
      ext1 X
      exact Functor.OplaxMonoidal.oplax_associativity
        (ModuleCat.extendScalars (coeff φ X)) (M.obj X) (N.obj X) (P.obj X))
    (oplax_left_unitality := fun M ↦ by
      ext1 X
      exact Functor.OplaxMonoidal.oplax_left_unitality
        (ModuleCat.extendScalars (coeff φ X)) (M.obj X))
    (oplax_right_unitality := fun M ↦ by
      ext1 X
      exact Functor.OplaxMonoidal.oplax_right_unitality
        (ModuleCat.extendScalars (coeff φ X)) (M.obj X)))
end

/-- Change of coefficients on one category is strong monoidal, with coefficient
homomorphism as the transpose of its inverse unit constraint.
Source: Stacks Project, sites-modules.tex, section-presheaves-modules and
lemma-tensor-product-pullback.
(auxiliary; not a blueprint node).

Proof: construct extension sectionwise as S(X) tensor over R(X) with M(X).
Its restriction sends s tensor m to S(f)(s) tensor M(f)(m); naturality of the
coefficient homomorphism proves balancing. Sectionwise tensor adjunctions give
an adjunction to restriction of coefficients, naturally in both presheaves.
Uniqueness of left adjoints identifies this construction with the chosen pullback,
compatibly with the adjunction. Its inverse unit constraint is multiplication
s tensor r to s times phi(r), and its inverse tensor constraint sends
s tensor (m tensor n) to (s tensor m) tensor (1 tensor n). The inverse map sends
(s tensor m) tensor (t tensor n) to st tensor (m tensor n). The balancing relations
prove these formulas well-defined and inverse on generators. Restricting each
factor proves naturality. Associativity sends a triple pure tensor to the same
triple with the same scalar coefficient; the unit laws are multiplication by one.
Transport this strong monoidal structure along the adjunction comparison. The
transpose of multiplication sends r to phi(r), as asserted. No flatness, topology,
nonzero-ring, or nonempty-category hypothesis occurs in this calculation. -/
theorem exists_pullback_monoidal_normalized
    {C : Type u} [SmallCategory C]
    (R S : Cᵒᵖ ⥤ CommRingCat.{u})
    (φ : (R ⋙ forget₂ CommRingCat.{u} RingCat.{u}) ⟶
      (𝟭 C).op ⋙ (S ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :
    ∃ mon : (pullback.{u} φ).Monoidal,
      letI := mon
      ∀ (X : Cᵒᵖ) (r : R.obj X),
        ((pullbackPushforwardAdjunction φ).homEquiv _ _
          (Functor.OplaxMonoidal.η (pullback φ))).app X r = φ.app X r := by
  let := sectionMonoidal φ
  let a := sectionAdjunction φ
  let b := pullbackPushforwardAdjunction φ
  let := Functor.Monoidal.transport (a.leftAdjointUniq b)
  refine ⟨inferInstance, ?_⟩
  intro X r
  change ((b.homEquiv _ _) ((a.leftAdjointUniq b).inv.app _ ≫
    Functor.OplaxMonoidal.η (sectionExtension φ))).app X r = _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.leftAdjointUniq_inv_app, Adjunction.unit_leftAdjointUniq_hom_app]
  exact unit_one φ X r

end PresheafOfModules
