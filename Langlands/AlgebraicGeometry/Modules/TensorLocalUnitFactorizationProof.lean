import Langlands.AlgebraicGeometry.Modules.TensorLocalUnitFactorizationStatement
import Langlands.AlgebraicGeometry.Modules.TensorLocalFiniteDecompositionProof
import Langlands.AlgebraicGeometry.Modules.TensorSections
import Langlands.AlgebraicGeometry.Modules.StructureUnitScalars
import Langlands.AlgebraicGeometry.Modules.RestrictTensorProof

/-! # Local unit factorization of a tensor-invertible pair of scheme modules -/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.Scheme.Modules

section Unitors

open TopologicalSpace Opposite

/-- The left unitor is the transpose of the presheaf left unitor. -/
lemma tensorLeftUnitor_hom_eq {Y : Scheme.{u}} (P : Y.Modules) :
    (tensorLeftUnitor P).hom = (tensorHomEquiv _ _ _).symm (λ_ P.val).hom :=
  ((sheafifyAdjunction Y).homEquiv_counit _ _ _).symm

/-- The left unitor sends the sheafified pure tensor `1 ⊗ 1` to one. -/
lemma tensorLeftUnitor_hom_app_one {Y : Scheme.{u}} (V : Y.Opens) :
    let one : (structureSheaf Y).val.obj (op V) := (1 : Γ(Y, V))
    ((tensorLeftUnitor (structureSheaf Y)).hom.val.app (op V)).hom
      (((tensorSheafifyUnit (structureSheaf Y) (structureSheaf Y)).app (op V)).hom
        (one ⊗ₜ[Y.presheaf.obj (op V)] one)) = one := by
  intro one
  have h := congrArg (fun f => (f.app (op V)).hom (one ⊗ₜ[Y.presheaf.obj (op V)] one))
    (tensorSheafifyUnit_comp_tensorHomEquiv_symm _ _ _ (λ_ (structureSheaf Y).val).hom)
  rw [← tensorLeftUnitor_hom_eq] at h
  refine h.trans ?_
  change (1 : Γ(Y, V)) • (1 : Γ(Y, V)) = (1 : Γ(Y, V))
  exact mul_one _

end Unitors

section Factorization

open TopologicalSpace Opposite Langlands.SchemeModule

variable {X : Scheme.{u}}

/-- The value of a map `E : M ⊗ N ⟶ 𝒪_X` on the sheafified pure tensor of two sections. -/
def tensorUnitValue {M N : X.Modules} (E : tensorObj M N ⟶ structureSheaf X) (V : X.Opens)
    (m : M.val.obj (op V)) (n : N.val.obj (op V)) : Γ(X, V) :=
  (E.val.app (op V)).hom (((tensorSheafifyUnit M N).app (op V)).hom
    (m ⊗ₜ[X.presheaf.obj (op V)] n))

/-- The value on pure tensors is compatible with restriction. -/
lemma tensorUnitValue_res {M N : X.Modules} (E : tensorObj M N ⟶ structureSheaf X)
    {V W : X.Opens} (h : W ≤ V) (m : M.val.obj (op V)) (n : N.val.obj (op V)) :
    tensorUnitValue E W (M.val.map (homOfLE h).op m) (N.val.map (homOfLE h).op n) =
      X.presheaf.map (homOfLE h).op (tensorUnitValue E V m n) := by
  have h₁ := PresheafOfModules.naturality_apply (tensorSheafifyUnit M N) (homOfLE h).op
    (m ⊗ₜ[X.presheaf.obj (op V)] n)
  have h₂ := PresheafOfModules.naturality_apply E.val (homOfLE h).op
    (((tensorSheafifyUnit M N).app (op V)).hom (m ⊗ₜ[X.presheaf.obj (op V)] n))
  exact (congrArg (E.val.app (op W)).hom h₁).trans h₂

/-- The inverse left unitor sends one to the sheafified pure tensor `1 ⊗ 1`. -/
lemma tensorLeftUnitor_inv_app_one {Y : Scheme.{u}} (V : Y.Opens) :
    let one : (structureSheaf Y).val.obj (op V) := (1 : Γ(Y, V))
    ((tensorLeftUnitor (structureSheaf Y)).inv.val.app (op V)).hom one =
      ((tensorSheafifyUnit (structureSheaf Y) (structureSheaf Y)).app (op V)).hom
        (one ⊗ₜ[Y.presheaf.obj (op V)] one) := by
  intro one
  have h := congrArg (fun f => (f.val.app (op V)).hom
      (((tensorSheafifyUnit (structureSheaf Y) (structureSheaf Y)).app (op V)).hom
        (one ⊗ₜ[Y.presheaf.obj (op V)] one)))
    (tensorLeftUnitor (structureSheaf Y)).hom_inv_id
  refine Eq.trans ?_ h
  exact congrArg _ (tensorLeftUnitor_hom_app_one V).symm

/-- The section morphism of a global section sends one to that section. -/
lemma sectionHom_app_top_one {Y : Scheme.{u}} (P : Y.Modules) (s : GlobalSections P) :
    let one : (structureModule Y).val.obj (op ⊤) := (1 : Γ(Y, ⊤))
    ((sectionHom P s).val.app (op ⊤)).hom one = s := by
  intro one
  refine (sectionHom_app_one P s ⊤).trans ?_
  rw [show (homOfLE (le_top : (⊤ : Y.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl,
    CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The composite `𝒪_W ≅ 𝒪_W ⊗ 𝒪_W → M|_W ⊗ N|_W ≅ (M ⊗ N)|_W → 𝒪_X|_W ≅ 𝒪_W` built from two
sections over `W` acts on one by the value of `E` on their pure tensor. -/
lemma structureEndValue_restrictTensor {M N : X.Modules}
    (E : tensorObj M N ⟶ structureSheaf X) (W : X.Opens)
    (mW : GlobalSections (M.restrict W.ι)) (nW : GlobalSections (N.restrict W.ι)) :
    structureEndValue ((tensorLeftUnitor (structureSheaf W.toScheme)).inv ≫
      tensorMap (sectionHom (M.restrict W.ι) mW) (sectionHom (N.restrict W.ι) nW) ≫
      restrictTensorHom W M N ≫ (AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).map E ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso W.ι).hom) ⊤ =
    (W.ι.appIso ⊤).hom (tensorUnitValue E (W.ι ''ᵁ ⊤) mW nW) := by
  let one : (structureSheaf W.toScheme).val.obj (op ⊤) := (1 : Γ(W.toScheme, ⊤))
  have h₁ : ((tensorLeftUnitor (structureSheaf W.toScheme)).inv.val.app (op ⊤)).hom one =
      ((tensorSheafifyUnit (structureSheaf W.toScheme) (structureSheaf W.toScheme)).app
        (op ⊤)).hom (one ⊗ₜ[W.toScheme.presheaf.obj (op ⊤)] one) :=
    tensorLeftUnitor_inv_app_one ⊤
  have hm : ((sectionHom (M.restrict W.ι) mW).val.app (op ⊤)).hom one = mW :=
    sectionHom_app_top_one _ _
  have hn : ((sectionHom (N.restrict W.ι) nW).val.app (op ⊤)).hom one = nW :=
    sectionHom_app_top_one _ _
  have h₂ : ((tensorSheafifyUnit (M.restrict W.ι) (N.restrict W.ι)).app (op ⊤)).hom
      (((sectionHom (M.restrict W.ι) mW).val.app (op ⊤)).hom one ⊗ₜ[W.toScheme.presheaf.obj (op ⊤)]
        ((sectionHom (N.restrict W.ι) nW).val.app (op ⊤)).hom one) =
      ((tensorMap (sectionHom (M.restrict W.ι) mW)
          (sectionHom (N.restrict W.ι) nW)).val.app (op ⊤)).hom
        (((tensorSheafifyUnit (structureSheaf W.toScheme) (structureSheaf W.toScheme)).app
          (op ⊤)).hom (one ⊗ₜ[W.toScheme.presheaf.obj (op ⊤)] one)) :=
    congrArg (fun f => (f.app (op ⊤)).hom (one ⊗ₜ[W.toScheme.presheaf.obj (op ⊤)] one))
      (tensorSheafifyUnit_naturality (sectionHom (M.restrict W.ι) mW)
        (sectionHom (N.restrict W.ι) nW))
  rw [hm, hn] at h₂
  have h₃ := (restrictTensorComparison X W M N).2 ⊤ mW nW
  change ((AlgebraicGeometry.Scheme.Modules.restrictUnitIso W.ι).hom.val.app (op ⊤)).hom
      ((E.val.app (op (W.ι ''ᵁ ⊤))).hom (((restrictTensorHom W M N).val.app (op ⊤)).hom
        (((tensorMap (sectionHom (M.restrict W.ι) mW)
          (sectionHom (N.restrict W.ι) nW)).val.app (op ⊤)).hom
          (((tensorLeftUnitor (structureSheaf W.toScheme)).inv.val.app (op ⊤)).hom one)))) = _
  rw [h₁, ← h₂, h₃]
  rfl

/-- If `E : M ⊗ N ⟶ 𝒪_X` is an isomorphism and its value on the pure tensor of two sections
over `W` is a unit, then the tensor of the corresponding section morphisms on `W` is an
isomorphism. -/
lemma isIso_tensorMap_sectionHom_of_isUnit {M N : X.Modules}
    (E : tensorObj M N ⟶ structureSheaf X) [IsIso E] (W : X.Opens)
    (mW : GlobalSections (M.restrict W.ι)) (nW : GlobalSections (N.restrict W.ι))
    (hu : IsUnit (tensorUnitValue E (W.ι ''ᵁ ⊤) mW nW)) :
    IsIso (tensorMap (sectionHom (M.restrict W.ι) mW) (sectionHom (N.restrict W.ι) nW)) := by
  let R : tensorObj (M.restrict W.ι) (N.restrict W.ι) ⟶ structureSheaf W.toScheme :=
    restrictTensorHom W M N ≫ (AlgebraicGeometry.Scheme.Modules.restrictFunctor W.ι).map E ≫
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso W.ι).hom
  have hR : IsIso R :=
    IsIso.comp_isIso' (restrictTensorComparison X W M N).1
      (IsIso.comp_isIso' (Functor.map_isIso _ E) (Iso.isIso_hom _))
  have hr : IsUnit ((W.ι.appIso ⊤).hom (tensorUnitValue E (W.ι ''ᵁ ⊤) mW nW)) :=
    hu.map (W.ι.appIso ⊤).hom.hom
  have hg : (tensorLeftUnitor (structureSheaf W.toScheme)).inv ≫
      tensorMap (sectionHom (M.restrict W.ι) mW) (sectionHom (N.restrict W.ι) nW) ≫ R =
      (structureAutOfUnit hr.unit).hom :=
    structureEnd_ext ((structureEndValue_restrictTensor E W mW nW).trans
      (structureEndValue_mulHom _).symm)
  have hg' : tensorMap (sectionHom (M.restrict W.ι) mW) (sectionHom (N.restrict W.ι) nW) ≫ R =
      (tensorLeftUnitor (structureSheaf W.toScheme)).hom ≫ (structureAutOfUnit hr.unit).hom := by
    rw [← hg]
    exact (Iso.hom_inv_id_assoc _ _).symm
  have h₂ : IsIso (tensorMap (sectionHom (M.restrict W.ι) mW)
      (sectionHom (N.restrict W.ι) nW) ≫ R) := by
    rw [hg']
    exact IsIso.comp_isIso' (Iso.isIso_hom _) (Iso.isIso_hom _)
  have := hR
  exact (isIso_comp_right_iff _ _).mp h₂

end Factorization

open TopologicalSpace Opposite Langlands.SchemeModule in
/-- A tensor-invertible pair of scheme modules locally admits sections whose tensor
trivializes the pair. -/
theorem tensorLocalUnitFactorization (X : Scheme.{u}) :
    TensorLocalUnitFactorizationStatement X := by
  intro M N e x
  let E : tensorObj M N ≅ structureSheaf X := (localizedTensorIso X M N).symm ≪≫ e
  let z : (tensorObj M N).val.obj (op ⊤) := (E.inv.val.app (op ⊤)).hom (1 : Γ(X, ⊤))
  obtain ⟨V, hVU, hxV, k, s, t, hst⟩ := tensorLocalFiniteDecomposition X M N ⊤ z x trivial
  have hsum : ∑ i, tensorUnitValue E.hom V (s i) (t i) = 1 := by
    have h₀ := map_sum ((tensorSheafifyUnit M N).app (op V)).hom
      (fun i => (s i ⊗ₜ[X.presheaf.obj (op V)] t i : (M.val ⊗ N.val).obj (op V))) Finset.univ
    have h₀' := map_sum (E.hom.val.app (op V)).hom
      (fun i => ((tensorSheafifyUnit M N).app (op V)).hom (s i ⊗ₜ[X.presheaf.obj (op V)] t i))
      Finset.univ
    have h₁ : (E.hom.val.app (op V)).hom (((tensorSheafifyUnit M N).app (op V)).hom
        (∑ i, s i ⊗ₜ[X.presheaf.obj (op V)] t i)) =
        (E.hom.val.app (op V)).hom ((tensorObj M N).val.map (homOfLE hVU).op z) :=
      congrArg (E.hom.val.app (op V)).hom hst
    have h₂ := PresheafOfModules.naturality_apply E.hom.val (homOfLE hVU).op z
    have h₃ : (E.hom.val.app (op ⊤)).hom z = (1 : Γ(X, ⊤)) :=
      congrArg (fun f => (f.val.app (op ⊤)).hom (1 : Γ(X, ⊤))) E.inv_hom_id
    refine h₀'.symm.trans ((congrArg (E.hom.val.app (op V)).hom h₀).symm.trans
      (h₁.trans (h₂.trans ?_)))
    refine (congrArg (fun y => ((structureSheaf X).val.map (homOfLE hVU).op).hom y) h₃).trans ?_
    exact map_one (X.presheaf.map (homOfLE hVU).op).hom
  have hunit : IsUnit (∑ i, (X.presheaf.germ V x hxV).hom
      (tensorUnitValue E.hom V (s i) (t i))) := by
    rw [← map_sum, hsum, map_one]
    exact isUnit_one
  obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum hunit
  set a := tensorUnitValue E.hom V (s i) (t i) with ha
  set W := X.basicOpen a with hW
  have hxW : x ∈ W := (X.mem_basicOpen _ x hxV).mpr hi
  have hWV : W.ι ''ᵁ ⊤ ≤ V := (W.ι_image_le ⊤).trans (X.basicOpen_le _)
  let mW : GlobalSections (M.restrict W.ι) := M.val.map (homOfLE hWV).op (s i)
  let nW : GlobalSections (N.restrict W.ι) := N.val.map (homOfLE hWV).op (t i)
  have hu : IsUnit (tensorUnitValue E.hom (W.ι ''ᵁ ⊤) mW nW) := by
    change IsUnit (tensorUnitValue E.hom (W.ι ''ᵁ ⊤) (M.val.map (homOfLE hWV).op (s i))
      (N.val.map (homOfLE hWV).op (t i)))
    rw [tensorUnitValue_res E.hom hWV (s i) (t i)]
    have h : X.presheaf.map (homOfLE hWV).op a =
        X.presheaf.map (homOfLE (W.ι_image_le ⊤)).op
          (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [h]
    exact (X.toRingedSpace.isUnit_res_basicOpen _).map _
  have core := isIso_tensorMap_sectionHom_of_isUnit E.hom W mW nW hu
  refine ⟨W, hxW, sectionHom (M.restrict W.ι) mW, sectionHom (N.restrict W.ι) nW, ?_⟩
  let fg : ((structureModule W.toScheme, structureModule W.toScheme) :
      W.toScheme.Modules × W.toScheme.Modules) ⟶ (M.restrict W.ι, N.restrict W.ι) :=
    (sectionHom (M.restrict W.ι) mW, sectionHom (N.restrict W.ι) nW)
  have hnat := (localizedTensorNatIso W.toScheme).hom.naturality fg
  have h : IsIso ((tensor _).map fg ≫
      (localizedTensorNatIso W.toScheme).hom.app (M.restrict W.ι, N.restrict W.ι)) := by
    rw [hnat]
    exact IsIso.comp_isIso' inferInstance core
  exact (isIso_comp_right_iff _ _).mp h

end Langlands.Scheme.Modules
