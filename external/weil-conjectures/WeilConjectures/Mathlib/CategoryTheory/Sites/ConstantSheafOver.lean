/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# The restriction of a constant sheaf to a localized site

For a site `(C, J)`, an object `U : C` and `M : A`, the restriction `(M_C).over U` of the
constant sheaf at `M` to the localized site `J.over U` receives a canonical map from the
constant sheaf at `M` on `J.over U`, adjoint to `M ⟶ M_C(U)`
(`CategoryTheory.constantSheafOverHom`). Its underlying map of presheaves, composed with the
sheafification map of the constant presheaf on `Over U`, is the restriction of the
sheafification map of the constant presheaf on `C`
(`CategoryTheory.toSheafify_constantSheafOverHom_hom`); as the latter is locally bijective,
the canonical map is an isomorphism when `A` is concrete and `J.W` is the class of locally
bijective morphisms (`CategoryTheory.isIso_constantSheafOverHom`).

This identifies, compatibly with the units `M ⟶ Γ`, the restriction of a constant sheaf with a
constant sheaf; `CategoryTheory.GrothendieckTopology.overPullbackConstantSheafIso` of
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf` is the same identification
without the compatibility.

Consequently, for a morphism `φ : M_C ⟶ N_C` of constant sheaves of modules with `M` finite,
there is a covering sieve of the terminal object over whose non-degenerate members `φ` is,
through these identifications, induced by a linear map `M ⟶ N`
(`CategoryTheory.exists_mem_forall_exists_constantSheafOverHom_comp_map_eq`).

-/

@[expose] public section

universe v u v' u'

open CategoryTheory Limits Opposite

namespace CategoryTheory

section General

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [HasWeakSheafify J A] (U : C) [HasWeakSheafify (J.over U) A]

/-- The canonical map from the constant sheaf on `J.over U` at `M` to the restriction of the
constant sheaf on `J` at `M`, adjoint to `M ⟶ M_C(U)`. -/
noncomputable def constantSheafOverHom (M : A) :
    (constantSheaf (J.over U) A).obj M ⟶ ((constantSheaf J A).obj M).over U :=
  ((constantSheafAdj (J.over U) A Over.mkIdTerminal).homEquiv M _).symm
    ((CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U))

/-- The adjunct of `constantSheafOverHom` is `M ⟶ M_C(U)`. -/
lemma constantSheafAdj_homEquiv_constantSheafOverHom (M : A) :
    (constantSheafAdj (J.over U) A Over.mkIdTerminal).homEquiv M _ (constantSheafOverHom J A U M) =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) :=
  Equiv.apply_symm_apply _ _

/-- The adjunct of a morphism out of a constant sheaf is the composite of the sheafification
map with the morphism on global sections. -/
lemma constantSheafAdj_homEquiv_apply {T : C} (hT : IsTerminal T) (M : A) (G : Sheaf J A)
    (ψ : (constantSheaf J A).obj M ⟶ G) :
    (constantSheafAdj J A hT).homEquiv M G ψ =
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op T) ≫ ψ.hom.app (op T) := by
  rw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp]

/-- **The canonical map is compatible with the sheafification maps**: on underlying presheaves,
`constantSheafOverHom` composed with the sheafification map of the constant presheaf on
`Over U` is the restriction to `Over U` of the sheafification map of the constant presheaf on
`C`. -/
lemma toSheafify_constantSheafOverHom_hom (M : A) :
    CategoryTheory.toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj M) ≫
        (constantSheafOverHom J A U M).hom =
      Functor.whiskerLeft (Over.forget U).op
        (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M)) := by
  apply ((constantPresheafAdj A (Over.mkIdTerminal (X := U))).homEquiv M _).injective
  have h := constantSheafAdj_homEquiv_constantSheafOverHom J A U M
  rw [constantSheafAdj_homEquiv_apply] at h
  simp only [Adjunction.homEquiv_unit, constantPresheafAdj_unit_app, evaluation_obj_map,
    Category.id_comp, NatTrans.comp_app, Functor.whiskerLeft_app]
  exact h

variable {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [J.WEqualsLocallyBijective A] [(J.over U).WEqualsLocallyBijective A]
  [hrefl : (CategoryTheory.forget A).ReflectsIsomorphisms]
  [hcomp : (J.over U).HasSheafCompose (CategoryTheory.forget A)]

include FA CA hrefl hcomp in
/-- **The restriction of a constant sheaf to a localized site is the constant sheaf**, through
the canonical map: its composite with the sheafification map of the constant presheaf is the
restriction of a locally bijective map, hence locally bijective, so the canonical map is
locally bijective, hence an isomorphism of sheaves. -/
instance isIso_constantSheafOverHom (M : A) : IsIso (constantSheafOverHom J A U M) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (constantSheafOverHom J A U M)]
  have h := toSheafify_constantSheafOverHom_hom J A U M
  have h₁ : Presheaf.IsLocallyInjective (J.over U) (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) _
  have h₂ : Presheaf.IsLocallySurjective (J.over U) (Functor.whiskerLeft (Over.forget U).op
      (CategoryTheory.toSheafify J ((Functor.const Cᵒᵖ).obj M))) :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) _
  rw [← h] at h₁ h₂
  have h₃ : Presheaf.IsLocallyInjective (J.over U)
      (CategoryTheory.toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj M)) :=
    ((J.over U).W_toSheafify _).isLocallyInjective
  have h₄ : Presheaf.IsLocallySurjective (J.over U)
      (CategoryTheory.toSheafify (J.over U) ((Functor.const (Over U)ᵒᵖ).obj M)) :=
    ((J.over U).W_toSheafify _).isLocallySurjective
  exact ⟨(Presheaf.comp_isLocallyInjective_iff _ _ _).mp h₁,
    (Presheaf.comp_isLocallySurjective_iff _ _ _).mp h₂⟩

include FA CA hrefl hcomp in
/-- The restriction of the constant sheaf at `M` to the localized site at `U` is the constant
sheaf at `M`, compatibly with the units `M ⟶ Γ`. -/
noncomputable def constantSheafOverIso (M : A) :
    (constantSheaf (J.over U) A).obj M ≅ ((constantSheaf J A).obj M).over U :=
  asIso (constantSheafOverHom J A U M)

end General

section ModuleCat

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {Λ : Type v'} [Ring Λ] [HasWeakSheafify J (ModuleCat.{v'} Λ)]
  [J.WEqualsLocallyBijective (ModuleCat.{v'} Λ)] {T : C}
  [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{v'} Λ)]

/-- **A morphism between constant sheaves of modules is locally induced by a linear map**:
for `φ : M_C ⟶ N_C` with `M` finitely generated and any object `T`, there is a covering sieve
`S` of `T` such that over every member `U` of `S` not covered by the empty sieve, the restriction
of `φ` to
`J.over U` is, through the canonical identifications `constantSheafOverHom`, the morphism of
constant sheaves induced by a `Λ`-linear map `f : M ⟶ N`. -/
theorem exists_mem_forall_exists_constantSheafOverHom_comp_map_eq (M N : ModuleCat.{v'} Λ)
    [Module.Finite Λ M]
    (φ : (constantSheaf J (ModuleCat.{v'} Λ)).obj M ⟶ (constantSheaf J (ModuleCat.{v'} Λ)).obj N) :
    ∃ S ∈ J T, ∀ ⦃U : C⦄ (g : U ⟶ T), S g → (⊥ : Sieve U) ∉ J U → ∃ f : M ⟶ N,
      constantSheafOverHom J _ U M ≫ (J.overPullback _ U).map φ =
        (constantSheaf (J.over U) _).map f ≫ constantSheafOverHom J _ U N := by
  obtain ⟨S, hS, h⟩ := exists_mem_forall_exists_linearMap J (T := T) M N φ
  refine ⟨S, hS, fun U g hg hU ↦ ?_⟩
  obtain ⟨f, hf⟩ := h g hg hU
  refine ⟨f, ((constantSheafAdj (J.over U) _ Over.mkIdTerminal).homEquiv M _).injective ?_⟩
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    constantSheafAdj_homEquiv_constantSheafOverHom, constantSheafAdj_homEquiv_constantSheafOverHom]
  ext m
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact hf m

end ModuleCat

end CategoryTheory

namespace CategoryTheory

section Kernel

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [Abelian A] [HasSheafify J A] (U : C) [HasSheafify (J.over U) A]
  [PreservesFiniteLimits (J.overPullback A U)] [PreservesFiniteColimits (J.overPullback A U)]
  [PreservesFiniteLimits (constantSheaf (J.over U) A)]
  {M N : A} (f : M ⟶ N) (φ : (constantSheaf J A).obj M ⟶ (constantSheaf J A).obj N)
  [IsIso (constantSheafOverHom J A U M)] [IsIso (constantSheafOverHom J A U N)]
  (h : constantSheafOverHom J A U M ≫ (J.overPullback A U).map φ =
    (constantSheaf (J.over U) A).map f ≫ constantSheafOverHom J A U N)

include h

/-- If the restriction of `φ : M_C ⟶ N_C` to `J.over U` is induced by `f : M ⟶ N`, the
restriction of its kernel is the constant sheaf at `kernel f`. -/
noncomputable def kernelOverIso :
    (kernel φ).over U ≅ (constantSheaf (J.over U) A).obj (kernel f) :=
  PreservesKernel.iso (J.overPullback A U) φ ≪≫
    kernel.mapIso _ ((constantSheaf (J.over U) A).map f) (asIso (constantSheafOverHom J A U M)).symm
      (asIso (constantSheafOverHom J A U N)).symm (by
        rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv,
          ← cancel_epi (constantSheafOverHom J A U M), IsIso.hom_inv_id_assoc, ← Category.assoc,
          h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]) ≪≫
    (PreservesKernel.iso (constantSheaf (J.over U) A) f).symm

/-- If the restriction of `φ : M_C ⟶ N_C` to `J.over U` is induced by `f : M ⟶ N`, the
restriction of its cokernel is the constant sheaf at `cokernel f`. -/
noncomputable def cokernelOverIso :
    (cokernel φ).over U ≅ (constantSheaf (J.over U) A).obj (cokernel f) :=
  have := (constantSheafAdj (J.over U) A Over.mkIdTerminal).leftAdjoint_preservesColimits
  PreservesCokernel.iso (J.overPullback A U) φ ≪≫
    cokernel.mapIso _ ((constantSheaf (J.over U) A).map f)
      (asIso (constantSheafOverHom J A U M)).symm (asIso (constantSheafOverHom J A U N)).symm (by
        rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv,
          ← cancel_epi (constantSheafOverHom J A U M), IsIso.hom_inv_id_assoc, ← Category.assoc,
          h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]) ≪≫
    (PreservesCokernel.iso (constantSheaf (J.over U) A) f).symm

omit [PreservesFiniteColimits (J.overPullback A U)] in
/-- The restriction of the kernel of `φ` to `J.over U` is constant. -/
lemma Sheaf.isConstant_kernel_over : ((kernel φ).over U).IsConstant (J.over U) :=
  Sheaf.isConstant_of_iso _ (kernelOverIso J A U f φ h)

omit [PreservesFiniteLimits (constantSheaf (J.over U) A)] in
/-- The restriction of the cokernel of `φ` to `J.over U` is constant. -/
lemma Sheaf.isConstant_cokernel_over : ((cokernel φ).over U).IsConstant (J.over U) :=
  Sheaf.isConstant_of_iso _ (cokernelOverIso J A U f φ h)

end Kernel

end CategoryTheory

namespace CategoryTheory

section Instances

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A]

/-- The constant sheaf functor is left exact, as the composite of the constant presheaf
functor and sheafification. -/
instance preservesFiniteLimits_constantSheaf [HasFiniteLimits A] [HasSheafify J A] :
    PreservesFiniteLimits (constantSheaf J A) :=
  have : PreservesFiniteLimits (Functor.const Cᵒᵖ : A ⥤ _) :=
    PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _
  comp_preservesFiniteLimits _ _

/-- The constant sheaf functor is right exact, as the composite of the constant presheaf
functor and sheafification, which is a left adjoint. -/
instance preservesFiniteColimits_constantSheaf [HasFiniteColimits A] [HasSheafify J A] :
    PreservesFiniteColimits (constantSheaf J A) :=
  have : PreservesFiniteColimits (Functor.const Cᵒᵖ : A ⥤ _) :=
    PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _
  comp_preservesFiniteColimits _ _

/-- The restriction of sheaves to a localized site preserves colimits: it is left adjoint to
the pushforward along the cocontinuous functor `Over.forget U`. -/
instance preservesColimits_overPullback (U : C)
    [∀ P : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension P] :
    PreservesColimitsOfSize.{v, u} (J.overPullback A U) :=
  ((Over.forget U).sheafAdjunctionCocontinuous A (J.over U) J).leftAdjoint_preservesColimits

instance preservesFiniteColimits_overPullback (U : C)
    [∀ P : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension P] :
    PreservesFiniteColimits (J.overPullback A U) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end Instances

end CategoryTheory
