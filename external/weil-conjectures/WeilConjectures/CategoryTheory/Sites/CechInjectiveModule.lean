/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.CategoryTheory.Sites.CechCriterion

/-!
# Injective sheaves of modules have no higher abelian cohomology

Let `R` be a ring and `I` an injective sheaf of `R`-modules on a site. Its underlying presheaf
is a direct summand of the cofree presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} I(Z)`, as `R`-modules
(`CategoryTheory.Presheaf.cofreeModule`), so the Čech complexes of the underlying abelian
presheaf of `I` are exact (`CategoryTheory.Sheaf.exactAt_cechComplex_forget₂_of_injective`). On
a site with enough finite covering families, the Čech criterion then shows that the underlying
abelian sheaf of `I` has no higher cohomology
(`CategoryTheory.Sheaf.subsingleton_H_succ_forget₂_of_injective`).

Consequently the cohomology of a sheaf of `R`-modules, computed in sheaves of `R`-modules, is
the cohomology of its underlying abelian sheaf, for every ring `R` (not only those which are
flat over `ℤ`): an injective resolution in sheaves of `R`-modules is an acyclic resolution of the
underlying abelian sheaf.
-/

@[expose] public section

universe t v w

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type w} [Category.{v} C]

section Retract

variable {V : C} [HasFiniteProducts (Over V)] {ι : Type t} (U : ι → Over V)

/-- Exactness of Čech complexes passes to retracts of presheaves. -/
theorem exactAt_cechComplex_of_retract {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{max w v}} (i : P ⟶ Q)
    (r : Q ⟶ P) (hir : i ≫ r = 𝟙 P) (q : ℕ) (hQ : ((cechComplex U).obj Q).ExactAt (q + 1)) :
    ((cechComplex U).obj P).ExactAt (q + 1) := by
  set ι' := (cechComplex U).map i
  set ρ := (cechComplex U).map r
  have hιρ (k : ℕ) (c : ((cechComplex U).obj P).X k) : ρ.f k (ι'.f k c) = c := by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.comp_f, ← Functor.map_comp, hir,
      CategoryTheory.Functor.map_id, HomologicalComplex.id_f, ConcreteCategory.id_apply]
  rw [exactAt_cechComplex_iff]
  intro c hc
  obtain ⟨b, hb⟩ := (exactAt_cechComplex_iff U _ q).1 hQ (ι'.f (q + 1) c)
    ((ConcreteCategory.congr_hom (ι'.comm (q + 1) (q + 2)) c).trans
      ((congrArg (ι'.f (q + 2)) hc).trans (map_zero _)))
  exact ⟨ρ.f q b, (ConcreteCategory.congr_hom (ρ.comm q (q + 1)) b).trans
    ((congrArg (ρ.f (q + 1)) hb).trans (hιρ _ c))⟩

end Retract

section Module

variable {R : Type*} [Ring R] (P : Cᵒᵖ ⥤ ModuleCat.{max w v} R)

/-- The cofree presheaf `Y ↦ ∏_{Z, g : Z ⟶ Y} P(Z)` of a presheaf of `R`-modules, as a presheaf
of `R`-modules. Its underlying presheaf of abelian groups is the cofree presheaf of the
underlying presheaf of `P` (`CategoryTheory.Presheaf.cofree`). -/
@[simps]
noncomputable def cofreeModule : Cᵒᵖ ⥤ ModuleCat.{max w v} R where
  obj Y := ModuleCat.of R (∀ (Z : C) (_ : Z ⟶ Y.unop), P.obj (op Z))
  map {Y Y'} h := ModuleCat.ofHom
    { toFun c Z g := c Z (g ≫ h.unop)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_id _ := by
    ext c Z g
    simp
  map_comp _ _ := by
    ext c Z g
    simp

/-- The embedding of a presheaf of `R`-modules into its cofree presheaf, `p ↦ (g ↦ P(g) p)`. -/
@[simps]
noncomputable def toCofreeModule : P ⟶ cofreeModule P where
  app Y := ModuleCat.ofHom
    { toFun p Z g := P.map g.op p
      map_add' _ _ := funext fun _ ↦ funext fun _ ↦ map_add _ _ _
      map_smul' _ _ := funext fun _ ↦ funext fun _ ↦ map_smul _ _ _ }
  naturality Y Y' h := by
    ext p
    funext Z g
    change P.map g.op (P.map h p) = P.map (g ≫ h.unop).op p
    rw [op_comp, P.map_comp]
    rfl

instance : Mono (toCofreeModule P) := by
  have (Y : Cᵒᵖ) : Mono ((toCofreeModule P).app Y) :=
    (ModuleCat.mono_iff_injective _).2 fun p p' h ↦ by
      have := congrFun (congrFun h Y.unop) (𝟙 _)
      change P.map (𝟙 _).op p = P.map (𝟙 _).op p' at this
      simpa using this
  exact NatTrans.mono_of_mono_app _

/-- The underlying abelian presheaf of an injective presheaf of `R`-modules is a retract of its
cofree presheaf. -/
lemma exists_retract_cofree_forget₂ [Injective P] :
    ∃ r : cofree (P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v}) ⟶
      P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v},
      toCofree (P ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v}) ≫ r = 𝟙 _ := by
  let r := Injective.factorThru (𝟙 P) (toCofreeModule P)
  have hr := Injective.comp_factorThru (𝟙 P) (toCofreeModule P)
  refine ⟨Functor.whiskerRight r (forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v}), ?_⟩
  ext Y p
  have := congrArg (fun φ ↦ (φ.app Y).hom p) hr
  exact this

end Module

end CategoryTheory.Presheaf

namespace CategoryTheory.Sheaf

variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C} {R : Type*} [Ring R]
  [HasSheafify J (ModuleCat.{max w v} R)]

/-- The Čech complexes of the underlying abelian presheaf of an injective sheaf of `R`-modules
are exact in positive degrees. -/
lemma exactAt_cechComplex_forget₂_of_injective (I : Sheaf J (ModuleCat.{max w v} R))
    [Injective I] {V : C} [HasFiniteProducts (Over V)] {ι : Type*} (U : ι → Over V) (q : ℕ) :
    ((Presheaf.cechComplex U).obj
      (I.obj ⋙ forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v})).ExactAt (q + 1) := by
  have : Injective I.obj := (sheafificationAdjunction _ _).map_injective I inferInstance
  obtain ⟨r, hr⟩ := Presheaf.exists_retract_cofree_forget₂ I.obj
  exact Presheaf.exactAt_cechComplex_of_retract U _ r hr q
    (Presheaf.exactAt_cechComplex_cofree U _ q)

variable [HasSheafify J AddCommGrpCat.{max w v}] [HasExt.{t} (Sheaf J AddCommGrpCat.{max w v})]
  [∀ V : C, HasFiniteProducts (Over V)] [EnoughInjectives (Sheaf J AddCommGrpCat.{max w v})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w v}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v})]

/-- **Injective sheaves of modules are acyclic as abelian sheaves.** On a site with a terminal
object `T` and a class `B` of objects as in the Čech criterion
(`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex`), the underlying abelian
sheaf of an injective sheaf of `R`-modules has no higher cohomology, for every ring `R`. -/
theorem subsingleton_H_succ_forget₂_of_injective {T : C} (hT : IsTerminal T) (B : C → Prop)
    (hBT : B T)
    (hcov : ∀ V, B V → ∀ S ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
        (∀ a, S (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (I : Sheaf J (ModuleCat.{max w v} R)) [Injective I] (q : ℕ) :
    Subsingleton (Sheaf.H ((sheafCompose J
      (forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v})).obj I) (q + 1)) :=
  subsingleton_H_succ_of_exactAt_cechComplex hT B hBT hcov
    ((sheafCompose J (forget₂ (ModuleCat.{max w v} R) AddCommGrpCat.{max w v})).obj I)
    (fun _ _ _ U _ _ q ↦ by
      have := exactAt_cechComplex_forget₂_of_injective I U q
      exact this) q

end CategoryTheory.Sheaf
