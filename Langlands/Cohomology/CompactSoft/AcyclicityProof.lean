import Langlands.Cohomology.CompactSoft.ShortExactProof
import Langlands.Cohomology.RightDerivedSequence
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-! # Compact cohomology vanishing for c-soft module sheaves -/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Langlands.Sheaf.CompactSoft ZeroObject

universe u

namespace CompactSoft

variable {X : TopCat.{u}} {R : Type u} [CommRing R]

private def freeYonedaEquiv (F : X.Presheaf (ModuleCat.{u} R)) (U : Opens X) :
    (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)).obj (yoneda.obj U) ⟶ F) ≃
      F.obj (op U) :=
  (((ModuleCat.adj R).whiskerRight (Opens X)ᵒᵖ).homEquiv _ F).trans yonedaEquiv

private lemma freeYonedaEquiv_naturality {F : X.Presheaf (ModuleCat.{u} R)}
    {U V : Opens X} (f : U ⟶ V)
    (g : ((Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)).obj (yoneda.obj V) ⟶ F) :
    freeYonedaEquiv F U
        (((Functor.whiskeringRight _ _ _).obj (ModuleCat.free R)).map (yoneda.map f) ≫ g) =
      F.map f.op (freeYonedaEquiv F V g) := by
  have h := ((ModuleCat.adj R).whiskerRight (Opens X)ᵒᵖ).homEquiv_naturality_left
    (yoneda.map f) g
  exact (congrArg yonedaEquiv h).trans (yonedaEquiv_naturality _ _).symm

/-- An injective module sheaf has surjective restriction maps. -/
theorem isFlasque_of_injective (F : TopCat.Sheaf (ModuleCat.{u} R) X) [Injective F] :
    F.IsFlasque where
  epi {U V} f := by
    apply (ModuleCat.epi_iff_surjective _).2
    intro t
    let J := Opens.grothendieckTopology X
    let adj := sheafificationAdjunction J (ModuleCat.{u} R)
    let L := (Functor.whiskeringRight (Opens X)ᵒᵖ _ _).obj (ModuleCat.free R)
    let i := L.map (yoneda.map f.unop)
    have : Mono i := by
      have : ∀ W, Mono (i.app W) := by
        intro W
        apply (ModuleCat.mono_iff_injective _).2
        exact Finsupp.mapDomain_injective
          ((CategoryTheory.mono_iff_injective _).1
            (inferInstance : Mono ((yoneda.map f.unop).app W)))
      exact NatTrans.mono_of_mono_app i
    let φ : L.obj (yoneda.obj V.unop) ⟶ F.obj :=
      (freeYonedaEquiv F.obj V.unop).symm t
    let m := (presheafToSheaf J (ModuleCat.{u} R)).map i
    have : Mono m := inferInstance
    have : Injective (C := Sheaf J (ModuleCat.{u} R)) F := ‹_›
    let ψ := Injective.factorThru ((adj.homEquiv _ _).symm φ) m
    have hψ : m ≫ ψ = (adj.homEquiv _ _).symm φ := Injective.comp_factorThru _ _
    have h : i ≫ adj.homEquiv _ _ ψ = φ := by
      exact (adj.homEquiv_naturality_left i ψ).symm.trans
        ((congrArg (adj.homEquiv _ _) hψ).trans (Equiv.apply_symm_apply _ _))
    refine ⟨freeYonedaEquiv F.obj U.unop (adj.homEquiv _ _ ψ), ?_⟩
    have ht := congrArg (freeYonedaEquiv F.obj V.unop) h
    rw [freeYonedaEquiv_naturality] at ht
    exact ht.trans (Equiv.apply_symm_apply _ _)

/-- Injective module sheaves on locally compact Hausdorff spaces are c-soft. -/
theorem isCSoft_of_injective [T2Space X] [LocallyCompactSpace X]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) [Injective F] : IsCSoft F := by
  let : F.IsFlasque := isFlasque_of_injective F
  exact isCSoft_of_isFlasque F

end CompactSoft

/-- Positive right-derived compact sections vanish on a c-soft module sheaf. -/
theorem cSoftAcyclicity : CSoftAcyclicityStatement.{u} := by
  intro X _ _ R _ F hF n
  let := HasDerivedCategory.standard (TopCat.Sheaf (ModuleCat.{u} R) X)
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let T := Sheaf.CompactSupport.functor (X := X) (R := R)
  change IsZero ((T.rightDerived (n + 1)).obj F)
  induction n generalizing F with
  | zero =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have : Epi (T.map S.g) := (cSoftShortExact X R S hS hF).1.epi_g
    have he : (T.rightDerived 0).map S.g =
        T.rightDerivedZeroIsoSelf.hom.app S.X₂ ≫ T.map S.g ≫
          T.rightDerivedZeroIsoSelf.inv.app S.X₃ := by
      rw [← Category.assoc, ← T.rightDerivedZeroIsoSelf.hom.naturality,
        Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have : Epi ((T.rightDerived 0).map S.g) := by
      rw [he]
      infer_instance
    have : Epi (DerivedPlus.rightDerivedδ T hS 0 1 rfl) :=
      DerivedPlus.epi_rightDerivedδ_of_isZero T hS 0 1 rfl
        (T.isZero_rightDerived_obj_injective_succ 0 (Injective.under F))
    exact IsZero.of_epi_eq_zero _ (zero_of_epi_comp _
      (DerivedPlus.rightDerived_map_comp_δ T hS 0 1 rfl))
  | succ n ih =>
    let S := ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition _)
    have hS : S.ShortExact :=
      ShortComplex.ShortExact.mk'
        (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _))
        inferInstance inferInstance
    have hQ : IsCSoft S.X₃ :=
      (cSoftShortExact X R S hS hF).2
        (CompactSoft.isCSoft_of_injective (Injective.under F))
    have : Epi (DerivedPlus.rightDerivedδ T hS (n + 1) (n + 1 + 1) rfl) :=
      DerivedPlus.epi_rightDerivedδ_of_isZero T hS _ _ rfl
        (T.isZero_rightDerived_obj_injective_succ (n + 1) (Injective.under F))
    exact IsZero.of_epi (DerivedPlus.rightDerivedδ T hS (n + 1) (n + 1 + 1) rfl)
      (ih S.X₃ hQ)

end Langlands.Cohomology
