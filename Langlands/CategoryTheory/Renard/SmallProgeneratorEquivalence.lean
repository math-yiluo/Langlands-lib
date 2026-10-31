import Langlands.CategoryTheory.Renard.SmallProgeneratorEquivalenceStatements
import Langlands.CategoryTheory.Renard.HomExactnessComparison
import Langlands.CategoryTheory.Renard.GeneratorPresentation
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Abelian.Projective.Basic
import Mathlib.CategoryTheory.Generator.Preadditive
import Mathlib.CategoryTheory.Preadditive.Yoneda.Projective

/-!
# Renard's small-progenerator equivalence theorem

For a small progenerator `P`, the actual right `End P`-module Hom functor
`preadditiveCoyonedaObj P` is faithful, full and essentially surjective.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace Langlands.Renard

section

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{v} C] {P : C}

/-- A small progenerator is projective in Mathlib's lifting sense. -/
theorem projective_of_homSmallProgenerator (hP : HomSmallProgenerator.{v} P) :
    Projective P :=
  (homProjectiveComparison P).mp hP.1.1

/-- The module-valued Hom functor of a small progenerator is faithful. -/
theorem preadditiveCoyonedaObj_faithful_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).Faithful :=
  (isSeparator_iff_faithful_preadditiveCoyonedaObj P).mp (homGenerator_isSeparator hP.2)

/-- The module-valued Hom functor of a small progenerator preserves coproducts indexed by
`Type v`. -/
theorem preadditiveCoyonedaObj_preservesCoproducts_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) (I : Type v) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyonedaObj P) := by
  have : PreservesColimitsOfShape (Discrete I)
      (preadditiveCoyonedaObj P ⋙ ModuleCat.restrictScalars (Int.castRingHom (End P)ᵐᵒᵖ)) :=
    hP.1.2 I
  have : ReflectsColimitsOfShape (Discrete I)
      (ModuleCat.restrictScalars.{v} (Int.castRingHom (End P)ᵐᵒᵖ)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves (preadditiveCoyonedaObj P)
    (ModuleCat.restrictScalars (Int.castRingHom (End P)ᵐᵒᵖ))

omit [HasCoproducts.{v} C] in
/-- Precomposition with an endomorphism is the module action on `Hom(P, X)`. -/
theorem preadditiveCoyonedaObj_comp_eq_smul {X : C} (f : P ⟶ P)
    (x : (preadditiveCoyonedaObj P).obj X) :
    (f ≫ x : (preadditiveCoyonedaObj P).obj X) = (MulOpposite.op f : (End P)ᵐᵒᵖ) • x :=
  rfl

omit [HasCoproducts.{v} C] in
/-- A module map out of `Hom(P, X)` commutes with precomposition by endomorphisms of `P`. -/
theorem preadditiveCoyonedaObj_hom_comp {X : C} {M : ModuleCat.{v} (End P)ᵐᵒᵖ}
    (φ : (preadditiveCoyonedaObj P).obj X ⟶ M) (f : P ⟶ P)
    (x : (preadditiveCoyonedaObj P).obj X) :
    φ (f ≫ x) = (MulOpposite.op f : (End P)ᵐᵒᵖ) • φ x := by
  rw [preadditiveCoyonedaObj_comp_eq_smul, map_smul]

/-- Module maps out of `Hom(P, ∐ P)` agree once they agree on the coprojections. -/
theorem preadditiveCoyonedaObj_sigma_hom_ext (hP : HomSmallProgenerator.{v} P) {I : Type v}
    {M : ModuleCat.{v} (End P)ᵐᵒᵖ}
    {φ ψ : (preadditiveCoyonedaObj P).obj (∐ fun _ : I => P) ⟶ M}
    (h : ∀ i, φ (Sigma.ι (fun _ : I => P) i) = ψ (Sigma.ι (fun _ : I => P) i)) : φ = ψ := by
  have := preadditiveCoyonedaObj_preservesCoproducts_of_homSmallProgenerator hP I
  refine (isColimitOfPreserves (preadditiveCoyonedaObj P)
    (coproductIsCoproduct fun _ : I => P)).hom_ext fun ⟨i⟩ => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun (f : P ⟶ P) => ?_)
  change φ (f ≫ Sigma.ι (fun _ : I => P) i) = ψ (f ≫ Sigma.ι (fun _ : I => P) i)
  exact (preadditiveCoyonedaObj_hom_comp φ f _).trans
    ((congrArg _ (h i)).trans (preadditiveCoyonedaObj_hom_comp ψ f _).symm)

/-- Every module map `Hom(P, ∐ P) → Hom(P, Y)` is postcomposition with a morphism. -/
theorem preadditiveCoyonedaObj_sigma_map_surjective (hP : HomSmallProgenerator.{v} P)
    {I : Type v} {Y : C}
    (ψ : (preadditiveCoyonedaObj P).obj (∐ fun _ : I => P) ⟶ (preadditiveCoyonedaObj P).obj Y) :
    ∃ g : (∐ fun _ : I => P) ⟶ Y, (preadditiveCoyonedaObj P).map g = ψ := by
  refine ⟨Sigma.desc fun i => ψ (Sigma.ι (fun _ : I => P) i),
    preadditiveCoyonedaObj_sigma_hom_ext hP fun i => ?_⟩
  change Sigma.ι (fun _ : I => P) i ≫ Sigma.desc _ = _
  exact Sigma.ι_comp_desc _ i

/-- The module-valued Hom functor of a small progenerator is full. -/
theorem preadditiveCoyonedaObj_full_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).Full where
  map_surjective {X Y} φ := by
    have hproj := projective_of_homSmallProgenerator hP
    have := preadditiveCoyonedaObj_faithful_of_homSmallProgenerator hP
    have := (Projective.projective_iff_preservesEpimorphisms_preadditiveCoyonedaObj P).mp hproj
    let π : (∐ fun _ : P ⟶ X => P) ⟶ X := Sigma.desc fun a : P ⟶ X => a
    have : Epi π := homGenerator_epi_evaluation hP.2 X
    obtain ⟨g₀, hg₀⟩ :=
      preadditiveCoyonedaObj_sigma_map_surjective hP ((preadditiveCoyonedaObj P).map π ≫ φ)
    have hk : kernel.ι π ≫ g₀ = 0 := by
      apply (preadditiveCoyonedaObj P).map_injective
      rw [Functor.map_comp, hg₀, ← Category.assoc, ← Functor.map_comp, kernel.condition,
        Functor.map_zero, Limits.zero_comp, Functor.map_zero]
    refine ⟨Abelian.epiDesc π g₀ hk, ?_⟩
    rw [← cancel_epi ((preadditiveCoyonedaObj P).map π), ← Functor.map_comp,
      Abelian.comp_epiDesc, hg₀]

/-- The module map `Hom(P, P) → M`, `f ↦ m · f`, determined by an element `m`. -/
noncomputable def preadditiveCoyonedaObjEvalHom (M : ModuleCat.{v} (End P)ᵐᵒᵖ) (m : M) :
    (preadditiveCoyonedaObj P).obj P ⟶ M :=
  ModuleCat.ofHom
    { toFun := fun f => (MulOpposite.op f : (End P)ᵐᵒᵖ) • m
      map_add' := fun f g => by
        rw [MulOpposite.op_add]
        exact add_smul _ _ m
      map_smul' := fun r f => by
        change (r * (MulOpposite.op f : (End P)ᵐᵒᵖ)) • m = r • (MulOpposite.op f : (End P)ᵐᵒᵖ) • m
        exact mul_smul _ _ m }

/-- Every right `End P`-module is a quotient of `Hom(P, ∐ P)` for a `Type v`-indexed
coproduct. -/
theorem preadditiveCoyonedaObj_exists_epi_sigma (hP : HomSmallProgenerator.{v} P)
    (M : ModuleCat.{v} (End P)ᵐᵒᵖ) :
    ∃ (I : Type v) (ε : (preadditiveCoyonedaObj P).obj (∐ fun _ : I => P) ⟶ M), Epi ε := by
  have := preadditiveCoyonedaObj_preservesCoproducts_of_homSmallProgenerator hP M
  let hc := isColimitOfPreserves (preadditiveCoyonedaObj P)
    (coproductIsCoproduct fun _ : M => P)
  let s : Cocone ((Discrete.functor fun _ : M => P) ⋙ preadditiveCoyonedaObj P) :=
    { pt := M
      ι := Discrete.natTrans fun m => preadditiveCoyonedaObjEvalHom M m.as }
  refine ⟨M, hc.desc s, (ModuleCat.epi_iff_surjective _).mpr fun m =>
    ⟨Sigma.ι (fun _ : M => P) m, ?_⟩⟩
  have h := congrArg (fun φ => φ (𝟙 P)) (hc.fac s ⟨m⟩)
  change hc.desc s (𝟙 P ≫ Sigma.ι (fun _ : M => P) m) =
    (MulOpposite.op (𝟙 P) : (End P)ᵐᵒᵖ) • m at h
  rw [Category.id_comp] at h
  rw [h]
  exact one_smul _ m

/-- The module-valued Hom functor of a small progenerator is essentially surjective. -/
theorem preadditiveCoyonedaObj_essSurj_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).EssSurj where
  mem_essImage M := by
    have := projective_of_homSmallProgenerator hP
    obtain ⟨I, ε, hε⟩ := preadditiveCoyonedaObj_exists_epi_sigma hP M
    obtain ⟨J, ε', hε'⟩ := preadditiveCoyonedaObj_exists_epi_sigma hP (kernel ε)
    obtain ⟨d, hd⟩ := preadditiveCoyonedaObj_sigma_map_surjective hP (ε' ≫ kernel.ι ε)
    exact ⟨cokernel d, ⟨PreservesCokernel.iso (preadditiveCoyonedaObj P) d ≪≫
      cokernelIsoOfEq hd ≪≫ cokernelEpiComp ε' (kernel.ι ε) ≪≫
      (cokernelIsCokernel (kernel.ι ε)).coconePointUniqueUpToIso
        (Abelian.epiIsCokernelOfKernel (Fork.ofι (kernel.ι ε)
          ((kernel.condition ε).trans comp_zero.symm)) (kernelIsKernel ε))⟩⟩

/-- The module-valued Hom functor of a small progenerator is an equivalence. -/
theorem preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator
    (hP : HomSmallProgenerator.{v} P) : (preadditiveCoyonedaObj P).IsEquivalence where
  faithful := preadditiveCoyonedaObj_faithful_of_homSmallProgenerator hP
  full := preadditiveCoyonedaObj_full_of_homSmallProgenerator hP
  essSurj := preadditiveCoyonedaObj_essSurj_of_homSmallProgenerator hP

end

/-- Renard A.VIII.2: the exact published small-progenerator equivalence statement. -/
theorem smallProgeneratorEquivalence (C : Type u) [Category.{v} C] [Abelian C]
    [HasCoproducts.{v} C] : SmallProgeneratorEquivalenceStatement.{v,u} C :=
  fun _ hP => preadditiveCoyonedaObj_isEquivalence_of_homSmallProgenerator hP

end Langlands.Renard
