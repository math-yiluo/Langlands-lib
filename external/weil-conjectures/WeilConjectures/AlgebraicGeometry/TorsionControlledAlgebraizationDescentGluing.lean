/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.Topology.GlueSheavesOfModules
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationLocalDescent
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Gluing torsion-controlled triples -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem product_zero_of_iso {X : Scheme.{u}} {I : X.Modules}
    (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) {P Q : X.Modules}
    (e : P ≅ Q) (h : IsZero (Scheme.idealModuleProduct j Q)) :
    IsZero (Scheme.idealModuleProduct j P) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let f := MonoidalCategoryStruct.whiskerRight j P ≫
    (MonoidalCategoryStruct.leftUnitor P).hom
  let g := MonoidalCategoryStruct.whiskerRight j Q ≫
    (MonoidalCategoryStruct.leftUnitor Q).hom
  have hg : g = 0 := by
    rw [← image.fac g]
    rw [h.eq_zero_of_src (image.ι g), comp_zero]
  have hf : f = 0 := by
    apply (cancel_mono e.hom).mp
    rw [zero_comp]
    dsimp [f]
    calc
      _ = MonoidalCategoryStruct.whiskerRight j P ≫
          (MonoidalCategoryStruct.whiskerLeft
            (MonoidalCategoryStruct.tensorUnit X.Modules) e.hom ≫
              (MonoidalCategoryStruct.leftUnitor Q).hom) := by
        exact congrArg (MonoidalCategoryStruct.whiskerRight j P ≫ ·)
          (MonoidalCategory.leftUnitor_naturality e.hom).symm
      _ = MonoidalCategoryStruct.whiskerLeft I e.hom ≫ g := by
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ (MonoidalCategoryStruct.leftUnitor Q).hom)
            (MonoidalCategory.whisker_exchange j e.hom).symm).trans
              (Category.assoc _ _ _))
      _ = 0 := by rw [hg, comp_zero]
  change IsZero (image f)
  apply IsZero.of_mono_eq_zero (image.ι f)
  apply (cancel_epi (factorThruImage f)).mp
  rw [image.fac, comp_zero, hf]

private theorem restrict_arrow_bounds {X : Scheme.{u}} (J : X.IdealSheafData)
    {P Q : X.Modules} (a : P ⟶ Q) (U : X.Opens)
    {P' Q' : U.toScheme.Modules} (a' : P' ⟶ Q')
    (e : (Scheme.Modules.restrictFunctor U.ι).obj P ≅ P')
    (d : (Scheme.Modules.restrictFunctor U.ι).obj Q ≅ Q')
    (w : (Scheme.Modules.restrictFunctor U.ι).map a ≫ d.hom = e.hom ≫ a')
    (s : ℕ)
    (hk : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2 (kernel a')))
    (hc : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2 (cokernel a'))) :
    IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2
      ((Scheme.Modules.restrictFunctor U.ι).obj (kernel a))) ∧
    IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower (J.comap U.ι).toModulesι s).2
      ((Scheme.Modules.restrictFunctor U.ι).obj (cokernel a))) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let ek := PreservesKernel.iso R a ≪≫ kernel.mapIso (R.map a) a' e d w
  let ec := PreservesCokernel.iso R a ≪≫ cokernel.mapIso (R.map a) a' e d w
  exact ⟨product_zero_of_iso _ ek hk, product_zero_of_iso _ ec hc⟩


private theorem system_hom_glue {X : Scheme.{u}}
    (N M : ℕᵒᵖ ⥤ X.Modules) (ι : Type u) (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (f : ∀ i, N ⋙ SheafOfModules.overFunctor (moduleRings X.toRingedSpace) (U i) ⟶
      M ⋙ SheafOfModules.overFunctor (moduleRings X.toRingedSpace) (U i))
    (hf : ∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      ((f i).app n).val.app (op (Over.mk (homOfLE hi))) =
        ((f j).app n).val.app (op (Over.mk (homOfLE hj)))) :
    ∃ g : N ⟶ M, ∀ (n : ℕᵒᵖ) (i : ι), (g.app n).over (U i) = (f i).app n := by
  classical
  have ex (n : ℕᵒᵖ) : ∃ g : N.obj n ⟶ M.obj n,
      ∀ i, g.over (U i) = (f i).app n := by
    obtain ⟨g, hg, _⟩ :=
      (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).1
        (N.obj n) (M.obj n) (fun i => (f i).app n) (hf n)
    exact ⟨g, hg⟩
  choose g hg using ex
  let t : N ⟶ M :=
    { app := g
      naturality := by
        intro n m a
        apply (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.1
        intro i
        change (N.map a).over (U i) ≫ (g m).over (U i) =
          (g n).over (U i) ≫ (M.map a).over (U i)
        rw [hg m i, hg n i]
        exact (f i).naturality a }
  exact ⟨t, hg⟩

private theorem system_iso_glue {X : Scheme.{u}}
    (N M : ℕᵒᵖ ⥤ X.Modules) (ι : Type u) (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (e : ∀ i, N ⋙ SheafOfModules.overFunctor (moduleRings X.toRingedSpace) (U i) ≅
      M ⋙ SheafOfModules.overFunctor (moduleRings X.toRingedSpace) (U i))
    (he : ∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      ((e i).hom.app n).val.app (op (Over.mk (homOfLE hi))) =
        ((e j).hom.app n).val.app (op (Over.mk (homOfLE hj)))) :
    ∃ g : N ≅ M, ∀ (n : ℕᵒᵖ) (i : ι), (g.hom.app n).over (U i) = (e i).hom.app n := by
  have hinv : ∀ (n : ℕᵒᵖ) (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j),
      ((e i).inv.app n).val.app (op (Over.mk (homOfLE hi))) =
        ((e j).inv.app n).val.app (op (Over.mk (homOfLE hj))) := by
    intro n i j W hi hj
    let ei := (SheafOfModules.evaluation ((moduleRings X.toRingedSpace).over (U i))
      (op (Over.mk (homOfLE hi)))).mapIso ((e i).app n)
    let ej := (SheafOfModules.evaluation ((moduleRings X.toRingedSpace).over (U j))
      (op (Over.mk (homOfLE hj)))).mapIso ((e j).app n)
    exact (Iso.inv_eq_inv ei ej).mpr (he n i j W hi hj)
  obtain ⟨f, hf⟩ := system_hom_glue N M ι U hcover (fun i => (e i).hom) he
  obtain ⟨g, hg⟩ := system_hom_glue M N ι U hcover (fun i => (e i).inv) hinv
  refine ⟨⟨f, g, ?_, ?_⟩, hf⟩
  · apply NatTrans.ext
    funext n
    apply (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.1
    intro i
    change (f.app n).over (U i) ≫ (g.app n).over (U i) = 𝟙 _
    rw [hf n i, hg n i]
    exact (e i).hom_inv_id_app n
  · apply NatTrans.ext
    funext n
    apply (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.1
    intro i
    change (g.app n).over (U i) ≫ (f.app n).over (U i) = 𝟙 _
    rw [hg n i, hf n i]
    exact (e i).inv_hom_id_app n

/-- Local torsion-controlled triples glue to a global factorization whose actual
kernel and cokernel retain local annihilation bounds.

Source: Stacks Project, Tag 0889(1), uniqueness argument; Sheaves, Tags 00AL and 00AM.
(blueprint: new-stage3-torsion-controlled-algebraization-descent-gluing).

Proof: Choose supplied triples on each open. On each overlap use the normalized
quotient comparisons to identify completions. Lift the comparison and its inverse
by torsion-controlled hom lifting. Completion extensionality, together with
compatibility with the map to H, shows that both composites are identities and
that the lifted comparison is unique. Uniqueness proves the cocycle equation.
Apply sheaf-of-modules descent to glue the sources and maps. Coherence is local.
Glue formal comparison maps and inverses levelwise; their transition equations
and factorization equations hold locally, hence globally. Exact restriction
identifies the restrictions of the global kernel and cokernel with the kernels
and cokernels of the local maps, and ideal products commute with restriction.
Transport the supplied bounds across these identifications. For the empty scheme
all these modules are zero; for the unit ideal uniqueness uses the torsion
hypothesis and makes no assertion about arbitrary algebraizations. -/
theorem torsionControlled_algebraization_descent_gluing
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (ι : Type u) (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (Hlocal : ∀ i, CoherentModules (U i).toScheme)
    (hHlocal : ∀ i, (Hlocal i).obj = (Scheme.Modules.restrictFunctor (U i).ι).obj H.obj)
    (γ : ∀ i, ((completion X J).obj H).obj ⋙
      Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) (Hlocal i).obj)
    (hγ : ∀ (i : ι) (n : ℕ),
      (Scheme.Modules.restrictFunctor (U i).ι).map
          (formalModuleQuotientπ J (n + 1) H.obj) ≫ (γ i).hom.app (op n) =
        eqToHom (hHlocal i).symm ≫
          formalModuleQuotientπ (J.comap (U i).ι) (n + 1) (Hlocal i).obj)
    (hlocal : ∀ i, ∃ (F : CoherentModules (U i).toScheme) (a : F ⟶ Hlocal i)
      (β : N.obj ⋙ Scheme.Modules.restrictFunctor (U i).ι ≅
        formalCompletionSystem (J.comap (U i).ι) F.obj),
      Functor.whiskerRight δ.hom (Scheme.Modules.restrictFunctor (U i).ι) ≫ (γ i).hom =
        β.hom ≫ formalCompletionMap (J.comap (U i).ι) a.hom ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2 (cokernel a.hom)))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∀ i, ∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i).ι).obj (kernel a.hom))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower (J.comap (U i).ι).toModulesι s).2
          ((Scheme.Modules.restrictFunctor (U i).ι).obj (cokernel a.hom)))) := by
  obtain ⟨F, a, ε, hε, hδε, hlocalArrow⟩ :=
    torsionControlled_algebraization_local_descent
      J H N δ ι U hcover Hlocal hHlocal γ hγ hlocal
  obtain ⟨b, hb⟩ := system_iso_glue N.obj ((completion X J).obj F).obj
    ι U hcover ε hε
  let β : N ≅ (completion X J).obj F := ObjectProperty.isoMk _ b
  refine ⟨F, a, β, ?_, ?_⟩
  · apply InducedCategory.hom_ext
    apply NatTrans.ext
    funext n
    apply (glue_sheaves_of_modules.{u, u} X.toRingedSpace ι U hcover).2.1
    intro i
    change (δ.hom.app n).over (U i) =
      (b.hom.app n).over (U i) ≫ (((completion X J).map a).hom.app n).over (U i)
    rw [hb n i]
    exact hδε n i
  · intro i
    obtain ⟨Fi, ai, e, he, s, hs, hk, hc⟩ := hlocalArrow i
    refine ⟨s, hs, ?_⟩
    exact restrict_arrow_bounds J a.hom (U i) ai.hom e
      (eqToIso (hHlocal i).symm) he s hk hc

end AlgebraicGeometry
