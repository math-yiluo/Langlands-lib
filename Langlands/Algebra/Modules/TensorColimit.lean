import Langlands.Algebra.Modules.TensorColimitStatement
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.Ring.Colimits

open CategoryTheory Limits MonoidalCategory PresheafOfModules

universe u

namespace Langlands.Algebra.Modules

namespace TensorColimit

attribute [local instance] IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

variable {C : Type u} [SmallCategory C] [IsCofiltered C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

variable (R) in
/-- The colimit cocone of the ring presheaf `R`, viewed in `RingCat`. -/
noncomputable abbrev ringColimit : IsColimit (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)) :=
  colimit.isColimit _

variable [InitiallySmall.{u} C]

/-- The colimit of the underlying abelian-group presheaf of `M`, with its module structure over
the colimit ring. -/
abbrev Col (M : PresheafOfModulesOfCommRing.{u} R) : Type u :=
  ModuleColimit (ringColimit R) (colimit.isColimit M.presheaf)

/-- The canonical map `M(U) → colim M`. -/
noncomputable abbrev ι (M : PresheafOfModulesOfCommRing.{u} R) {U : Cᵒᵖ} : M.obj U →+ Col M :=
  ModuleColimit.ιM (hcR := ringColimit R) (hcM := colimit.isColimit M.presheaf)

/-- The map of colimit modules induced by a morphism of presheaves of modules. -/
noncomputable abbrev mapCol {M M' : PresheafOfModulesOfCommRing.{u} R} (f : M ⟶ M') :
    Col M →ₗ[(colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt] Col M' :=
  ModuleColimit.map (ringColimit R) (colimit.isColimit M.presheaf)
    (colimit.isColimit M'.presheaf) f

omit [InitiallySmall.{u} C] in
lemma ι_map (M : PresheafOfModulesOfCommRing.{u} R) {U V : Cᵒᵖ} (f : U ⟶ V) (m : M.obj U) :
    ι M (U := V) (M.map f m) = ι M m :=
  ConcreteCategory.congr_hom (colimit.w M.presheaf f) m

lemma mapCol_ι {M M' : PresheafOfModulesOfCommRing.{u} R} (f : M ⟶ M') {U : Cᵒᵖ}
    (m : M.obj U) : mapCol f (ι M m) = ι M' (f.app U m) :=
  ModuleColimit.map_apply _ _ _ f m

lemma smul_ι (M : PresheafOfModulesOfCommRing.{u} R) {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    ModuleColimit.ιR (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)) r • ι M m =
      ι M (r • m) :=
  ModuleColimit.smul_eq _ _ r m

section

variable {P : Type u} [AddCommGroup P]

/-- The cocone on the underlying abelian-group presheaf of `M` given by a family of additive maps
on sections that is compatible with restriction. -/
noncomputable def descCocone (M : PresheafOfModulesOfCommRing.{u} R)
    (φ : ∀ U : Cᵒᵖ, M.obj U →+ P)
    (hφ : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (m : M.obj U), φ V (M.map f m) = φ U m) :
    Cocone M.presheaf where
  pt := AddCommGrpCat.of P
  ι.app U := AddCommGrpCat.ofHom (φ U)
  ι.naturality U V f := by
    ext m
    exact hφ f m

/-- The additive map out of `colim M` induced by a compatible family of additive maps. -/
noncomputable def descCol (M : PresheafOfModulesOfCommRing.{u} R)
    (φ : ∀ U : Cᵒᵖ, M.obj U →+ P)
    (hφ : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (m : M.obj U), φ V (M.map f m) = φ U m) :
    Col M →+ P :=
  (colimit.desc M.presheaf (descCocone M φ hφ)).hom

omit [InitiallySmall.{u} C] in
lemma descCol_ι (M : PresheafOfModulesOfCommRing.{u} R) (φ : ∀ U : Cᵒᵖ, M.obj U →+ P)
    (hφ : ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V) (m : M.obj U), φ V (M.map f m) = φ U m)
    {U : Cᵒᵖ} (m : M.obj U) :
    descCol M φ hφ (ι M m) = φ U m :=
  ConcreteCategory.congr_hom (colimit.ι_desc (descCocone M φ hφ) U) m

end

variable (M N : PresheafOfModulesOfCommRing.{u} R)

/-- The canonical map `M(U) ⊗ N(U) → colim (M ⊗ N)`, typed on the tensor product of sections. -/
noncomputable def ιT {U : Cᵒᵖ} : TensorProduct (R.obj U) (M.obj U) (N.obj U) →+ Col (M ⊗ N) :=
  ι (M ⊗ N) (U := U)

/-- The cocone on the product of the underlying type-valued presheaves of `M` and `N` with point
`colim (M ⊗ N)`, sending `(m, n)` at `U` to the class of `m ⊗ₜ n`. -/
noncomputable def tmulCocone :
    Cocone (M.presheaf ⋙ forget _ ⊗ N.presheaf ⋙ forget _) where
  pt := Col (M ⊗ N)
  ι.app U := ↾fun p ↦ ιT M N (TensorProduct.tmul (R.obj U) (M := M.obj U) (N := N.obj U) p.1 p.2)
  ι.naturality V U f := by
    ext ⟨m, n⟩
    exact ι_map (M ⊗ N) f (TensorProduct.tmul (R.obj V) (M := M.obj V) (N := N.obj V) m n)

/-- The pairing `colim M × colim N → colim (M ⊗ N)` induced by `m, n ↦ m ⊗ₜ n`. -/
noncomputable def tmulAux : Col M → Col N → Col (M ⊗ N) :=
  (((isColimitOfPreserves (forget _) (colimit.isColimit M.presheaf)).tensor
    (isColimitOfPreserves (forget _) (colimit.isColimit N.presheaf))).desc
      (tmulCocone M N) : _ → _).curry

variable {M N}

lemma tmulAux_ι {U : Cᵒᵖ} (m : M.obj U) (n : N.obj U) :
    tmulAux M N (ι M m) (ι N n) = ιT M N (m ⊗ₜ[R.obj U] n) := by
  have h := ConcreteCategory.congr_hom (((isColimitOfPreserves (forget _)
    (colimit.isColimit M.presheaf)).tensor (isColimitOfPreserves (forget _)
      (colimit.isColimit N.presheaf))).fac (tmulCocone M N) U) (⟨m, n⟩ : M.obj U × N.obj U)
  exact h

lemma tmulAux_add_left (x x' : Col M) (y : Col N) :
    tmulAux M N (x + x') y = tmulAux M N x y + tmulAux M N x' y := by
  obtain ⟨U, m, m', n, rfl, rfl, rfl⟩ := ModuleColimit.ιM_jointly_surjective₃ x x' y
  rw [← map_add, tmulAux_ι, tmulAux_ι, tmulAux_ι, TensorProduct.add_tmul, map_add]

lemma tmulAux_add_right (x : Col M) (y y' : Col N) :
    tmulAux M N x (y + y') = tmulAux M N x y + tmulAux M N x y' := by
  obtain ⟨U, m, n, n', rfl, rfl, rfl⟩ := ModuleColimit.ιM_jointly_surjective₃ x y y'
  rw [← map_add, tmulAux_ι, tmulAux_ι, tmulAux_ι, TensorProduct.tmul_add, map_add]

variable (M N)

/-- The pairing `colim M × colim N → colim (M ⊗ N)` as a bi-additive map. -/
noncomputable def tmulHom : Col M →+ Col N →+ Col (M ⊗ N) :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (tmulAux M N x) (tmulAux_add_right x))
    (fun x x' ↦ by ext y; exact tmulAux_add_left x x' y)

variable {M N}

lemma tmulHom_ι {U : Cᵒᵖ} (m : M.obj U) (n : N.obj U) :
    tmulHom M N (ι M m) (ι N n) = ιT M N (m ⊗ₜ[R.obj U] n) :=
  tmulAux_ι m n

lemma tmulHom_smul (a : (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt) (x : Col M)
    (y : Col N) : tmulHom M N (a • x) y = tmulHom M N x (a • y) := by
  obtain ⟨U, r, m, n, rfl, rfl, rfl⟩ := ModuleColimit.jointly_surjective₃' a x y
  rw [smul_ι, smul_ι, tmulHom_ι, tmulHom_ι, TensorProduct.smul_tmul]

lemma mapCol_ιT {M₁ M₂ N₁ N₂ : PresheafOfModulesOfCommRing.{u} R} (f : M₁ ⟶ M₂)
    (g : N₁ ⟶ N₂) {U : Cᵒᵖ} (m : M₁.obj U) (n : N₁.obj U) :
    mapCol (f ⊗ₘ g) (ιT M₁ N₁ (m ⊗ₜ[R.obj U] n)) =
      ιT M₂ N₂ (TensorProduct.tmul (R.obj U) (M := M₂.obj U) (N := N₂.obj U)
        (f.app U m) (g.app U n)) :=
  mapCol_ι (f ⊗ₘ g) (U := U) (m ⊗ₜ[R.obj U] n : (M₁ ⊗ N₁).obj U)

lemma mapCol_tmulHom {M₁ M₂ N₁ N₂ : PresheafOfModulesOfCommRing.{u} R} (f : M₁ ⟶ M₂)
    (g : N₁ ⟶ N₂) (x : Col M₁) (y : Col N₁) :
    mapCol (f ⊗ₘ g) (tmulHom M₁ N₁ x y) = tmulHom M₂ N₂ (mapCol f x) (mapCol g y) := by
  obtain ⟨U, m, n, rfl, rfl⟩ := ModuleColimit.ιM_jointly_surjective₂ x y
  rw [tmulHom_ι, mapCol_ιT, mapCol_ι, mapCol_ι, tmulHom_ι]

section

variable {P : Type u} [AddCommGroup P]

omit [IsCofiltered C] [InitiallySmall.{u} C] in
lemma tensor_addHom_ext {U : Cᵒᵖ} {F G : TensorProduct (R.obj U) (M.obj U) (N.obj U) →+ P}
    (h : ∀ (m : M.obj U) (n : N.obj U), F (m ⊗ₜ n) = G (m ⊗ₜ n)) : F = G := by
  refine AddMonoidHom.ext fun x ↦ ?_
  induction x with
  | tmul m n => exact h m n
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- Additive maps out of `colim (M ⊗ N)` agreeing on the classes of pure tensors are equal. -/
lemma col_tensor_ext {F G : Col (M ⊗ N) →+ P}
    (h : ∀ (U : Cᵒᵖ) (m : M.obj U) (n : N.obj U),
      F (ιT M N (m ⊗ₜ[R.obj U] n)) = G (ιT M N (m ⊗ₜ[R.obj U] n))) : F = G := by
  refine AddMonoidHom.ext fun z ↦ ?_
  obtain ⟨U, x, rfl⟩ := ModuleColimit.ιM_jointly_surjective z
  exact DFunLike.congr_fun
    (tensor_addHom_ext (F := F.comp (ιT M N)) (G := G.comp (ιT M N)) (h U)) x

/-- The sectionwise components of `liftCol`. -/
noncomputable def liftColApp (B : Col M →+ Col N →+ P)
    (hB : ∀ (a : (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt) (x : Col M)
      (y : Col N), B (a • x) y = B x (a • y)) (U : Cᵒᵖ) :
    TensorProduct (R.obj U) (M.obj U) (N.obj U) →+ P :=
  TensorProduct.liftAddHom ((B.comp (ι M (U := U))).compl₂ (ι N (U := U))) (fun r m n ↦ by
    simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.comp_apply]
    rw [← smul_ι, ← smul_ι, hB])

/-- A balanced bi-additive map `colim M × colim N → P` induces an additive map
`colim (M ⊗ N) → P`. -/
noncomputable def liftCol (B : Col M →+ Col N →+ P)
    (hB : ∀ (a : (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt) (x : Col M)
      (y : Col N), B (a • x) y = B x (a • y)) : Col (M ⊗ N) →+ P :=
  descCol (M ⊗ N) (liftColApp B hB) (fun U V f x ↦ DFunLike.congr_fun
    (tensor_addHom_ext (F := (liftColApp B hB V).comp ((M ⊗ N).map f).hom.toAddMonoidHom)
      (G := liftColApp B hB U) (fun m n ↦ by
        show B (ι M (U := V) (M.map f m)) (ι N (U := V) (N.map f n)) = B (ι M m) (ι N n)
        rw [ι_map, ι_map])) x)

lemma liftCol_ιT (B : Col M →+ Col N →+ P)
    (hB : ∀ (a : (colimit.cocone (R ⋙ forget₂ CommRingCat RingCat)).pt) (x : Col M)
      (y : Col N), B (a • x) y = B x (a • y)) {U : Cᵒᵖ} (m : M.obj U) (n : N.obj U) :
    liftCol B hB (ιT M N (m ⊗ₜ[R.obj U] n)) = B (ι M m) (ι N n) :=
  descCol_ι (M ⊗ N) _ _ (m ⊗ₜ[R.obj U] n : (M ⊗ N).obj U)

end

/-- If `colim f` and `colim g` are bijective, so is `colim (f ⊗ₘ g)`. -/
theorem bijective_mapCol_tensorHom {M₁ M₂ N₁ N₂ : PresheafOfModulesOfCommRing.{u} R}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (hf : Function.Bijective (mapCol f))
    (hg : Function.Bijective (mapCol g)) : Function.Bijective (mapCol (f ⊗ₘ g)) := by
  let e₁ := LinearEquiv.ofBijective (mapCol f) hf
  let e₂ := LinearEquiv.ofBijective (mapCol g) hg
  let ψ := liftCol (((tmulHom M₁ N₁).comp e₁.symm.toLinearMap.toAddMonoidHom).compl₂
    e₂.symm.toLinearMap.toAddMonoidHom) (fun a x y ↦ by
      simp only [AddMonoidHom.compl₂_apply, AddMonoidHom.comp_apply,
        LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, LinearEquiv.map_smul]
      exact tmulHom_smul a _ _)
  have hψ (U : Cᵒᵖ) (m : M₂.obj U) (n : N₂.obj U) :
      ψ (ιT M₂ N₂ (m ⊗ₜ[R.obj U] n)) = tmulHom M₁ N₁ (e₁.symm (ι M₂ m)) (e₂.symm (ι N₂ n)) :=
    liftCol_ιT _ _ m n
  have h₁ : ψ.comp (mapCol (f ⊗ₘ g)).toAddMonoidHom = AddMonoidHom.id _ :=
    col_tensor_ext fun U m n ↦ by
      rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, mapCol_ιT, hψ,
        ← mapCol_ι f, ← mapCol_ι g]
      show tmulHom M₁ N₁ (e₁.symm (e₁ (ι M₁ m))) (e₂.symm (e₂ (ι N₁ n))) = _
      rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, tmulHom_ι,
        AddMonoidHom.id_apply]
  have h₂ : (mapCol (f ⊗ₘ g)).toAddMonoidHom.comp ψ = AddMonoidHom.id _ :=
    col_tensor_ext fun U m n ↦ by
      rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hψ, mapCol_tmulHom]
      show tmulHom M₂ N₂ (e₁ (e₁.symm (ι M₂ m))) (e₂ (e₂.symm (ι N₂ n))) = _
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, tmulHom_ι,
        AddMonoidHom.id_apply]
  exact Function.bijective_iff_has_inverse.2
    ⟨ψ, fun x ↦ DFunLike.congr_fun h₁ x, fun x ↦ DFunLike.congr_fun h₂ x⟩

end TensorColimit

/-- The colimit functor of a presheaf of modules over a cofiltered category inverts the tensor
product of two morphisms that it inverts. -/
theorem tensorColimitIsIso (C : Type u) [SmallCategory C] [IsCofiltered C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) : tensorColimitIsIsoStatement C R := by
  have : InitiallySmall.{u} C := initiallySmall_of_essentiallySmall.{u} C
  intro M₁ M₂ N₁ N₂ f g hf hg
  rw [ConcreteCategory.isIso_iff_bijective] at hf hg ⊢
  exact TensorColimit.bijective_mapCol_tensorHom f g hf hg

end Langlands.Algebra.Modules
