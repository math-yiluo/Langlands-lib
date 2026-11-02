import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque

/-! # Actual abelian sheaves: injective restrictions and flasque cohomology -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Langlands.Cohomology.AbelianSheafFlasque

section Site

variable {C : Type u} [Category.{v} C]

/-- The section equivalence for a free abelian presheaf on a representable. -/
def freeYonedaEquiv (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (U : C) :
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj (yoneda.obj U) ⟶ F) ≃
      F.obj (op U) :=
  ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ F).trans yonedaEquiv

/-- The free-representable section equivalence is natural in the open. -/
lemma freeYonedaEquiv_naturality {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}} {U V : C}
    (f : U ⟶ V)
    (g : ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).obj (yoneda.obj V) ⟶ F) :
    freeYonedaEquiv F U
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map f) ≫ g) =
      F.map f.op (freeYonedaEquiv F V g) := by
  have h := (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left
    (yoneda.map f) g
  exact (congrArg yonedaEquiv h).trans (yonedaEquiv_naturality _ _).symm

variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v}]

/-- Restriction along a monomorphism is surjective in an injective abelian sheaf. -/
lemma surjective_map_of_injective (F : Sheaf J AddCommGrpCat.{v}) [Injective F]
    {U V : C} (f : U ⟶ V) [Mono f] :
    Function.Surjective (F.obj.map f.op) := by
  intro t
  let adj := sheafificationAdjunction J AddCommGrpCat.{v}
  let L := (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.free
  let i := L.map (yoneda.map f)
  have : Mono i := inferInstance
  let φ : L.obj (yoneda.obj U) ⟶ F.obj := (freeYonedaEquiv F.obj U).symm t
  let m := (presheafToSheaf J AddCommGrpCat.{v}).map i
  have : Mono m := inferInstance
  let ψ := Injective.factorThru ((adj.homEquiv _ _).symm φ) m
  have hψ : m ≫ ψ = (adj.homEquiv _ _).symm φ := Injective.comp_factorThru _ _
  have h : i ≫ adj.homEquiv _ _ ψ = φ := by
    rw [← Adjunction.homEquiv_naturality_left]
    change adj.homEquiv _ _ (m ≫ ψ) = φ
    rw [hψ, Equiv.apply_symm_apply]
  refine ⟨freeYonedaEquiv F.obj V (adj.homEquiv _ _ ψ), ?_⟩
  have ht := congrArg (freeYonedaEquiv F.obj U) h
  rw [freeYonedaEquiv_naturality] at ht
  exact ht.trans (Equiv.apply_symm_apply _ _)

end Site

section Topological

variable {X : TopCat.{u}}

/-- Injective abelian sheaves on a topological space are flasque. -/
lemma isFlasque_of_injective (F : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective F] :
    TopCat.Sheaf.IsFlasque F where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    have : Injective (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) F := ‹_›
    exact surjective_map_of_injective F i.unop

/-- The short exact sequence given by the chosen injective embedding of a sheaf. -/
abbrev injectiveSc (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

lemma injectiveSc_shortExact (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (injectiveSc F).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
    inferInstance inferInstance

/-- The cokernel of a flasque sheaf in its chosen injective embedding is flasque. -/
lemma isFlasque_cokernel (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque (cokernel (Injective.ι F)) := by
  have : TopCat.Sheaf.IsFlasque (Injective.under F) :=
    isFlasque_of_injective (Injective.under F)
  exact TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (injectiveSc_shortExact F)

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero cohomology surjects onto the injective cokernel of a flasque sheaf. -/
lemma surjective_H_zero_map (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsFlasque F] :
    Function.Surjective (Sheaf.H.map (injectiveSc F).g 0 : Sheaf.H.{u} _ 0 → Sheaf.H.{u} _ 0) := by
  have hepi := TopCat.Sheaf.IsFlasque.epi_of_shortExact
    (injectiveSc_shortExact F) (U := ⊤)
  have hs := (AddCommGrpCat.epi_iff_surjective _).1 hepi
  intro x
  obtain ⟨t, ht⟩ := hs (Sheaf.H.equiv₀ _ (isTerminalTop (α := Opens X)) x)
  refine ⟨(Sheaf.H.equiv₀ _ (isTerminalTop (α := Opens X))).symm t, ?_⟩
  apply (Sheaf.H.equiv₀ _ (isTerminalTop (α := Opens X))).injective
  rw [← Sheaf.H.equiv₀_naturality]
  simpa only [AddEquiv.apply_symm_apply] using ht

set_option backward.isDefEq.respectTransparency false in
/-- The actual Ext-defined higher cohomology of a flasque abelian sheaf vanishes. -/
theorem H_eq_zero_of_isFlasque (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsFlasque F] (x : Sheaf.H.{u} F (n + 1)) : x = 0 := by
  induction n generalizing F with
  | zero =>
    let S := injectiveSc F
    have hS := injectiveSc_shortExact F
    obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS x
      (Subsingleton.elim _ _) rfl
    obtain ⟨z, hz⟩ := surjective_H_zero_map F y
    have hzero := ConcreteCategory.congr_hom (Sheaf.H.longSequence_exact hS 0 1 rfl |>.zero 1) z
    change Sheaf.H.δ hS 0 1 rfl (Sheaf.H.map S.g 0 z) = 0 at hzero
    rw [hz, hy] at hzero
    exact hzero
  | succ n ih =>
    let S := injectiveSc F
    have hS := injectiveSc_shortExact F
    obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS x
      (Subsingleton.elim _ _) rfl
    have : TopCat.Sheaf.IsFlasque (cokernel (Injective.ι F)) := isFlasque_cokernel F
    have hy0 : y = 0 := ih _ y
    rw [hy0, map_zero] at hy
    exact hy.symm

set_option backward.isDefEq.respectTransparency false in
/-- All actual higher cohomology groups of a flasque abelian sheaf are zero objects. -/
theorem isZero_H_succ_of_isFlasque (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    [TopCat.Sheaf.IsFlasque F] :
    IsZero (AddCommGrpCat.of (Sheaf.H.{u} F (n + 1))) := by
  have : Subsingleton (Sheaf.H.{u} F (n + 1)) :=
    subsingleton_of_forall_eq 0 (H_eq_zero_of_isFlasque n F)
  exact AddCommGrpCat.isZero_of_subsingleton _

end Topological

end Langlands.Cohomology.AbelianSheafFlasque
