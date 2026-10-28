import Langlands.AlgebraicGeometry.Modules.RestrictTensorStatement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Restriction to an open subscheme commutes with the sheaf tensor product

This file proves `RestrictTensorComparisonStatement`: the comparison
`restrictTensorHom U M N : M|_U ⊗ N|_U ⟶ (M ⊗ N)|_U` is an isomorphism and is the identity on
sheafified pure tensors of sections.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.Scheme.Modules

/-- Along a surjective ring map, the canonical map from the tensor product of the restricted
modules to the restricted tensor product is bijective. -/
lemma restrictScalarsTensorLift_id_bijective {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Surjective φ) (M N : ModuleCat.{u} S) :
    Function.Bijective (restrictScalarsTensorLift φ (𝟙 (M ⊗ N))).hom := by
  let M' := (ModuleCat.restrictScalars φ).obj M
  let N' := (ModuleCat.restrictScalars φ).obj N
  let f : M →+ N →+ (M' ⊗[R] N') :=
    AddMonoidHom.mk' (fun m => AddMonoidHom.mk' (fun n => (m : M') ⊗ₜ[R] (n : N'))
      (fun n₁ n₂ => TensorProduct.tmul_add _ _ _))
      (fun m₁ m₂ => by ext n; exact TensorProduct.add_tmul _ _ _)
  have hf : ∀ (s : S) (m : M) (n : N), f (s • m) n = f m (s • n) := by
    intro s m n
    obtain ⟨r, rfl⟩ := hφ s
    exact TensorProduct.smul_tmul (R := R) (M := M') (N := N') r m n
  let g : M ⊗[S] N →+ M' ⊗[R] N' := TensorProduct.liftAddHom f hf
  let A : M' ⊗[R] N' →+ M ⊗[S] N :=
    (restrictScalarsTensorLift φ (𝟙 (M ⊗ N))).hom.toAddMonoidHom
  have hgA : ∀ w : M' ⊗[R] N', g (A w) = w := by
    intro w
    induction w with
    | tmul m n => rfl
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  have hA : Function.Surjective A := by
    intro w
    induction w with
    | tmul m n => exact ⟨(m : M') ⊗ₜ[R] (n : N'), rfl⟩
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨v₁, rfl⟩ := h₁
      obtain ⟨v₂, rfl⟩ := h₂
      exact ⟨v₁ + v₂, map_add _ _ _⟩
  exact ⟨Function.LeftInverse.injective hgA, hA⟩

/-- A presheaf map whose underlying abelian presheaf map is a local isomorphism becomes an
isomorphism after module sheafification. -/
lemma isIso_sheafify_map_of_W {Y : Scheme.{u}} {P Q : Y.PresheafOfModules} (f : P ⟶ Q)
    (hf : (Opens.grothendieckTopology Y).W ((PresheafOfModules.toPresheaf _).map f)) :
    IsIso ((sheafify Y).map f) := by
  have h := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
    (J := Opens.grothendieckTopology Y) (𝟙 Y.ringCatSheaf.obj)
  exact (congrArg (fun (W : MorphismProperty _) => W f) h).mp hf

/-- The sheafification unit followed by the transpose of a presheaf map is that map. -/
lemma tensorSheafifyUnit_comp_tensorHomEquiv_symm {Y : Scheme.{u}} (P Q T : Y.Modules)
    (f : P.val ⊗ Q.val ⟶ T.val) :
    tensorSheafifyUnit P Q ≫ ((tensorHomEquiv P Q T).symm f).val = f :=
  ((sheafifyAdjunction Y).homEquiv_unit _ _ _).symm.trans
    ((tensorHomEquiv P Q T).apply_symm_apply f)

section RestrictTensor

open TopologicalSpace Opposite

variable {X : Scheme.{u}} (U : X.Opens)

/-- Each component `M(ιV) ⊗_{𝒪_U(V)} N(ιV) → M(ιV) ⊗_{𝒪_X(ιV)} N(ιV)` is bijective. -/
lemma restrictTensorLift_app_bijective (M N : X.Modules) (V : U.toScheme.Opensᵒᵖ) :
    Function.Bijective ((restrictTensorLift U M N).app V).hom :=
  restrictScalarsTensorLift_id_bijective _
    (fun y => ⟨(U.ι.appIso V.unop).hom y, Iso.hom_inv_id_apply _ _⟩) _ _

/-- Sheafifying the sectionwise comparison `restrictTensorLift` gives an isomorphism. -/
lemma isIso_sheafify_map_restrictTensorLift (M N : X.Modules) :
    IsIso ((sheafify U.toScheme).map (restrictTensorLift U M N)) := by
  have h₁ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      ((PresheafOfModules.toPresheaf _).map (restrictTensorLift U M N)) :=
    Presheaf.isLocallyInjective_of_injective _ _
      (fun V => (restrictTensorLift_app_bijective U M N V).1)
  have h₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      ((PresheafOfModules.toPresheaf _).map (restrictTensorLift U M N)) :=
    Presheaf.isLocallySurjective_of_surjective _ _
      (fun V => (restrictTensorLift_app_bijective U M N V).2)
  exact isIso_sheafify_map_of_W _ (GrothendieckTopology.W_of_isLocallyBijective _ _)

/-- Sheafifying the pushforward of the tensor sheafification unit gives an isomorphism. -/
lemma isIso_sheafify_map_pushforward_tensorSheafifyUnit (M N : X.Modules) :
    IsIso ((sheafify U.toScheme).map
      ((PresheafOfModules.pushforward (restrictRingMap U)).map (tensorSheafifyUnit M N))) := by
  have h₃ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.pushforward (restrictRingMap U)).map (tensorSheafifyUnit M N))) := by
    change Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (toSheafify (Opens.grothendieckTopology X) (M.val ⊗ N.val).presheaf))
    exact Presheaf.isLocallyInjective_whisker (Opens.grothendieckTopology U.toScheme)
      (Opens.grothendieckTopology X) U.ι.opensFunctor _
  have h₄ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      ((PresheafOfModules.toPresheaf _).map
        ((PresheafOfModules.pushforward (restrictRingMap U)).map (tensorSheafifyUnit M N))) := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (toSheafify (Opens.grothendieckTopology X) (M.val ⊗ N.val).presheaf))
    exact Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology U.toScheme)
      (Opens.grothendieckTopology X) U.ι.opensFunctor _
  exact isIso_sheafify_map_of_W _ (GrothendieckTopology.W_of_isLocallyBijective _ _)

/-- The comparison as a composite of two sheafified presheaf maps and the counit at a sheaf. -/
lemma restrictTensorHom_eq (M N : X.Modules) :
    restrictTensorHom U M N =
      (sheafify U.toScheme).map (restrictTensorLift U M N) ≫
        (sheafify U.toScheme).map
          ((PresheafOfModules.pushforward (restrictRingMap U)).map (tensorSheafifyUnit M N)) ≫
        (sheafifyAdjunction U.toScheme).counit.app ((tensorObj M N).restrict U.ι) := by
  refine ((sheafifyAdjunction U.toScheme).homEquiv_counit _ _ _).trans ?_
  exact (congrArg (· ≫ (sheafifyAdjunction U.toScheme).counit.app ((tensorObj M N).restrict U.ι))
    ((sheafify U.toScheme).map_comp (restrictTensorLift U M N) _)).trans (Category.assoc _ _ _)

/-- Restriction to an open subscheme commutes with the sheafified tensor product. -/
lemma isIso_restrictTensorHom (M N : X.Modules) : IsIso (restrictTensorHom U M N) := by
  have h₁ := isIso_sheafify_map_restrictTensorLift U M N
  have h₂ := isIso_sheafify_map_pushforward_tensorSheafifyUnit U M N
  have h₃ : IsIso ((sheafifyAdjunction U.toScheme).counit.app ((tensorObj M N).restrict U.ι)) :=
    inferInstance
  exact (restrictTensorHom_eq U M N) ▸
    @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₂ h₃)

/-- The comparison precomposed with the sheafification unit is `restrictTensorPresheafHom`. -/
lemma tensorSheafifyUnit_comp_restrictTensorHom (M N : X.Modules) :
    tensorSheafifyUnit (M.restrict U.ι) (N.restrict U.ι) ≫ (restrictTensorHom U M N).val =
      restrictTensorPresheafHom U M N :=
  tensorSheafifyUnit_comp_tensorHomEquiv_symm _ _ _ _

/-- On pure tensors of sections, the comparison is the identity of underlying sections. -/
lemma restrictTensorHom_app_tmul (M N : X.Modules) (V : U.toScheme.Opens)
    (m : (M.restrict U.ι).val.obj (op V)) (n : (N.restrict U.ι).val.obj (op V)) :
    ((restrictTensorHom U M N).val.app (op V)).hom
        (((tensorSheafifyUnit (M.restrict U.ι) (N.restrict U.ι)).app (op V)).hom
          (m ⊗ₜ[U.toScheme.presheaf.obj (op V)] n)) =
      ((tensorSheafifyUnit M N).app (op (U.ι ''ᵁ V))).hom
          (m ⊗ₜ[X.presheaf.obj (op (U.ι ''ᵁ V))] n) := by
  have h := congrArg (fun f => (f.app (op V)).hom (m ⊗ₜ[U.toScheme.presheaf.obj (op V)] n))
    (tensorSheafifyUnit_comp_restrictTensorHom U M N)
  exact h

end RestrictTensor

/-- Restriction to an open subscheme commutes with the sheaf tensor product, and the comparison
is the identity on sheafified pure tensors of sections. -/
theorem restrictTensorComparison (X : Scheme.{u}) : RestrictTensorComparisonStatement X :=
  fun U M N => ⟨isIso_restrictTensorHom U M N, restrictTensorHom_app_tmul U M N⟩

end Langlands.Scheme.Modules
