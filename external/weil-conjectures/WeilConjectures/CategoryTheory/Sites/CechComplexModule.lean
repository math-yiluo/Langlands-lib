/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.CategoryTheory.Sites.CechInjectiveModule

/-!
# Čech complexes of sheaves of modules

Let `(C, J)` be a site and `R` a ring. We study the Čech complexes of the underlying abelian
presheaves of sheaves of `R`-modules, for arbitrary (not necessarily finite) families
`U : ι → Over V` generating a covering sieve.

A presheaf of abelian groups is *Čech-acyclic* (`CategoryTheory.Presheaf.IsCechAcyclic`) if all
these Čech complexes are exact in positive degrees. We show:

- the underlying abelian presheaf of an injective sheaf (or presheaf) of `R`-modules is
  Čech-acyclic: it is a direct summand of the cofree presheaf of `R`-modules
  `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` (`CategoryTheory.Presheaf.cofreeModule`), whose underlying abelian
  presheaf is `CategoryTheory.Presheaf.cofree`;
- in a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of `R`-modules with `A`
  Čech-acyclic, `B(V) ⟶ C(V)` is surjective for every `V`, and `C` is Čech-acyclic as soon as
  `B` is.

Since Čech-acyclicity only depends on the underlying abelian presheaf, these statements are the
input for comparing cohomology computed with different coefficient rings
(compare [Stacks, Tag 03FD]).

## Main statements

- `CategoryTheory.Presheaf.exactAt_cechComplex_forget₂_of_injective`
- `CategoryTheory.Presheaf.surjective_app_of_exactAt_cechComplex_one`
- `CategoryTheory.Sheaf.isCechAcyclic_of_injective`
- `CategoryTheory.Sheaf.surjective_app_of_isCechAcyclic`
- `CategoryTheory.Sheaf.isCechAcyclic_X₃`
-/

@[expose] public section

universe t v w u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C]

section Retract

variable {V : C} [HasFiniteProducts (Over V)] {ι : Type t} (U : ι → Over V)

/-- The Čech complex of an injective presheaf of `R`-modules is exact in positive degrees. -/
theorem exactAt_cechComplex_forget₂_of_injective {R : Type*} [Ring R]
    (P : Cᵒᵖ ⥤ ModuleCat.{max w v} R) [Injective P] (q : ℕ) :
    ((cechComplex U).obj (P ⋙ forget₂ _ AddCommGrpCat)).ExactAt (q + 1) :=
  exactAt_cechComplex_of_retract U (toCofree (P ⋙ forget₂ _ AddCommGrpCat))
    (Functor.whiskerRight (Injective.factorThru (𝟙 P) (toCofreeModule P))
      (forget₂ (ModuleCat R) AddCommGrpCat))
    ((congrArg (fun φ ↦ Functor.whiskerRight φ (forget₂ (ModuleCat R) AddCommGrpCat))
      (Injective.comp_factorThru (𝟙 P) (toCofreeModule P))).trans
      (Functor.whiskerRight_id _)) q (exactAt_cechComplex_cofree U _ q)

end Retract

section Surjective

variable {J : GrothendieckTopology C}

/-- Let `P₁ ⟶ P₂ ⟶ P₃` be morphisms of abelian presheaves which are sectionwise left exact, with
`P₂ ⟶ P₃` locally surjective and `P₂`, `P₃` sheaves. Let `V` be an object such that every
covering sieve of `V` contains a family `U` generating a covering sieve, on which the first Čech
cohomology of `P₁` vanishes. Then `P₂(V) → P₃(V)` is surjective. -/
theorem surjective_app_of_exactAt_cechComplex_one {P₁ P₂ P₃ : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}}
    (f : P₁ ⟶ P₂) (g : P₂ ⟶ P₃) (hfg : ∀ W x, g.app W (f.app W x) = 0)
    (hf : ∀ W, Function.Injective (f.app W))
    (hfg' : ∀ W x, g.app W x = 0 → ∃ y, f.app W y = x) [IsLocallySurjective J g]
    (h₂ : IsSheaf J P₂) (h₃ : IsSheaf J P₃) {V : C} [HasFiniteProducts (Over V)]
    (hV : ∀ R ∈ J V, ∃ (ι : Type t) (U : ι → Over V), (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V ∧
      ((cechComplex U).obj P₁).ExactAt 1) :
    Function.Surjective (g.app (op V)) := by
  intro s
  obtain ⟨ι, U, hR, hcov, hU⟩ := hV _ (Presheaf.imageSieve_mem J g s)
  choose t ht using hR
  let a : ((cechComplex U).obj P₂).X 0 := fun z ↦
    P₂.map (Pi.π (fun l ↦ U (z l)) 0).left.op (t (z 0))
  have ha (z : Fin 1 → ι) : ((cechComplex U).map g).f 0 a z =
      P₃.map (cechNerveObj U z).hom.op s := by
    rw [cechComplex_map_f_apply, NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp, Over.w]
  obtain ⟨e, he⟩ := exists_cechComplex_map_f_eq U f g hfg' _
    (((cechComplex U).obj P₂).d 0 1 a) (by
      rw [cechComplex_map_f_d_apply]
      exact cechComplex_d_zero_restrict U _ s _ ha)
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ 0).1 hU e
    (cechComplex_map_f_injective U _ hf _ (by
      rw [cechComplex_map_f_d_apply, he, map_zero, cechComplex_d_d_apply]))
  have hda : ((cechComplex U).obj P₂).d 0 1 (a - ((cechComplex U).map f).f 0 b) = 0 := by
    rw [map_sub, ← cechComplex_map_f_d_apply, hb, he, sub_self]
  -- the members of the Čech nerve in degree `0` generate a covering sieve
  have hcov' : Sieve.ofArrows (fun z : Fin 1 → ι ↦ (cechNerveObj U z).left)
      (fun z ↦ (cechNerveObj U z).hom) ∈ J V := by
    refine J.superset_covering (fun Y g hg ↦ ?_) hcov
    obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Sieve.mem_ofArrows_iff _ _ _).2
      ⟨fun _ ↦ i, h ≫ (Pi.lift fun _ ↦ 𝟙 (U i)).left, ?_⟩
    rw [Category.assoc, Over.w]
  obtain ⟨σ, hσ, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (Sheaf.isSheafFor_ofArrows ⟨P₂, h₂⟩ _ hcov')
    (fun z ↦ (a - ((cechComplex U).map f).f 0 b) z)
    fun z z' Z g₁ g₂ hg ↦ map_eq_of_cechComplex_d_zero U _ _ hda z z' g₁ g₂ hg
  refine ⟨σ, (Sheaf.isSheafFor_ofArrows ⟨P₃, h₃⟩ _ hcov').isSeparatedFor.ext
    fun Y h ⟨z⟩ ↦ ?_⟩
  change P₃.map _ (g.app _ σ) = P₃.map _ s
  rw [← NatTrans.naturality_apply]
  erw [hσ z]
  rw [cechComplex_sub_apply, map_sub, cechComplex_map_f_apply, hfg, sub_zero, ← ha]
  rfl

end Surjective

variable (J : GrothendieckTopology C) [∀ V : C, HasFiniteProducts (Over V)]

/-- A presheaf of abelian groups is *Čech-acyclic* for `J` if its Čech complexes on all the
families `U : ι → Over V` (with `ι : Type (max w v)`) generating a covering sieve of `V` are exact
in positive degrees. -/
def IsCechAcyclic (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}) : Prop :=
  ∀ (V : C) (ι : Type (max w v)) (U : ι → Over V),
    Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ q : ℕ, ((cechComplex U).obj P).ExactAt (q + 1)

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

open Presheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {R : Type*} [Ring R]

/-- The underlying abelian presheaf of a sheaf of `R`-modules is a sheaf. -/
lemma isSheaf_obj_comp_forget₂ (F : Sheaf J (ModuleCat.{max w v} R)) :
    Presheaf.IsSheaf J (F.obj ⋙ forget₂ _ AddCommGrpCat) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ F.property

variable [HasSheafify J (ModuleCat.{max w v} R)]

/-- The Čech complexes of an injective sheaf of `R`-modules are exact in positive degrees. -/
lemma isCechAcyclic_of_injective [∀ V : C, HasFiniteProducts (Over V)]
    (I : Sheaf J (ModuleCat.{max w v} R)) [Injective I] :
    IsCechAcyclic J (I.obj ⋙ forget₂ _ AddCommGrpCat) := fun _ _ U _ q ↦
  exactAt_cechComplex_forget₂_of_injective I U q

section

variable {S : ShortComplex (Sheaf J (ModuleCat.{max w v} R))}

omit [HasSheafify J (ModuleCat.{max w v} R)] in
/-- The composite of the two maps of a short complex of sheaves of modules vanishes on
sections. -/
lemma moduleCat_app_g_app_f (W : Cᵒᵖ) (x : S.X₁.obj.obj W) :
    S.g.hom.app W (S.f.hom.app W x) = 0 :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (congr_arg (fun φ ↦ φ.hom) S.zero) W) x

/-- In a short exact sequence of sheaves of modules, the first map is injective on sections. -/
lemma injective_moduleCat_app_f (hS : S.ShortExact) (W : Cᵒᵖ) :
    Function.Injective (S.f.hom.app W) := by
  have := hS.mono_f
  exact (ModuleCat.mono_iff_injective _).1
    ((sheafToPresheaf _ _ ⋙ (evaluation _ _).obj W).map_mono S.f)

/-- A short exact sequence of sheaves of modules is left exact on sections. -/
lemma exists_moduleCat_app_f_eq (hS : S.ShortExact) (W : Cᵒᵖ) (x : S.X₂.obj.obj W)
    (hx : S.g.hom.app W x = 0) : ∃ y, S.f.hom.app W y = x := by
  have := hS.mono_f
  exact (ShortComplex.moduleCat_exact_iff _).1 (hS.exact.map_of_mono_of_preservesKernel
    (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj W) inferInstance inferInstance) x hx

end

variable [J.WEqualsLocallyBijective (ModuleCat.{max w v} R)]
  [∀ V : C, HasFiniteProducts (Over V)]

/-- In a short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0` of sheaves of `R`-modules with `A`
Čech-acyclic, the map `B(V) ⟶ C(V)` is surjective for every object `V`. -/
theorem surjective_app_of_isCechAcyclic {S : ShortComplex (Sheaf J (ModuleCat.{max w v} R))}
    (hS : S.ShortExact) (h₁ : IsCechAcyclic J (S.X₁.obj ⋙ forget₂ _ AddCommGrpCat)) (V : C) :
    Function.Surjective (S.g.hom.app (op V)) := by
  have := hS.epi_g
  have : Sheaf.IsLocallySurjective S.g := (Sheaf.isLocallySurjective_iff_epi' _ S.g).2 this
  have : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight S.g.hom (forget₂ _ AddCommGrpCat)) :=
    ⟨fun s ↦ Presheaf.imageSieve_mem J S.g.hom s⟩
  refine Presheaf.surjective_app_of_exactAt_cechComplex_one
    (Functor.whiskerRight S.f.hom (forget₂ _ AddCommGrpCat))
    (Functor.whiskerRight S.g.hom (forget₂ _ AddCommGrpCat))
    (fun W x ↦ moduleCat_app_g_app_f W x)
    (injective_moduleCat_app_f hS) (exists_moduleCat_app_f_eq hS)
    (isSheaf_obj_comp_forget₂ S.X₂) (isSheaf_obj_comp_forget₂ S.X₃) (fun T hT ↦ ?_)
  exact ⟨T.arrows.category, fun a ↦ a.obj, fun a ↦ a.property,
    by rwa [Sieve.ofArrows_category], h₁ V _ _ (by rwa [Sieve.ofArrows_category]) 0⟩

/-- Čech-acyclic sheaves of `R`-modules are closed under cokernels of monomorphisms. -/
theorem isCechAcyclic_X₃ {S : ShortComplex (Sheaf J (ModuleCat.{max w v} R))}
    (hS : S.ShortExact) (h₁ : IsCechAcyclic J (S.X₁.obj ⋙ forget₂ _ AddCommGrpCat))
    (h₂ : IsCechAcyclic J (S.X₂.obj ⋙ forget₂ _ AddCommGrpCat)) :
    IsCechAcyclic J (S.X₃.obj ⋙ forget₂ _ AddCommGrpCat) := fun V ι U hU q ↦
  exactAt_cechComplex_of_sectionwise U
    (Functor.whiskerRight S.f.hom (forget₂ _ AddCommGrpCat))
    (Functor.whiskerRight S.g.hom (forget₂ _ AddCommGrpCat))
    (fun W x ↦ moduleCat_app_g_app_f W x) (injective_moduleCat_app_f hS)
    (exists_moduleCat_app_f_eq hS)
    (fun _ _ ↦ surjective_app_of_isCechAcyclic hS h₁ _) q (h₁ V ι U hU (q + 1)) (h₂ V ι U hU q)

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {R : Type*} [Ring R]

/-- A morphism of sheaves of modules which is surjective on all sections is an epimorphism. -/
lemma epi_of_surjective_app {F G : Sheaf J (ModuleCat.{v} R)} (φ : F ⟶ G)
    (h : ∀ W, Function.Surjective (φ.hom.app W)) : Epi φ := by
  have : Epi φ.hom := by
    have (W : Cᵒᵖ) : Epi (φ.hom.app W) := (ModuleCat.epi_iff_surjective _).2 (h W)
    exact NatTrans.epi_of_epi_app _
  refine ⟨fun a b hab ↦ ?_⟩
  refine Sheaf.hom_ext ?_
  exact (cancel_epi φ.hom).1 (by simpa using congrArg (fun ψ ↦ ψ.hom) hab)

end CategoryTheory.Sheaf
