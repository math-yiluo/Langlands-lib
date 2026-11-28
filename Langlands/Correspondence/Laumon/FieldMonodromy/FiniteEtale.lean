import Langlands.Correspondence.Laumon.FieldMonodromy.GaloisAut
import Langlands.Geometry.FieldEtaleModuleSheaves
import Langlands.Geometry.FieldEtaleStalkChange

/-!
# Proof of `FiniteEtaleFieldMonodromyStatement`

The three clauses come from three modules: `fieldGaloisToAut_isHomeomorph` (module
`Langlands.Correspondence.Laumon.FieldMonodromy.GaloisAut`), the equivalence
`Langlands.Geometry.FieldEtaleModuleSheaves.equivalence` with its stalk identification
`forgetIso` (module `Langlands.Geometry.FieldEtaleModuleSheaves`), and the stalk isomorphism
`Langlands.Geometry.FieldEtaleStalkChange.sheafFiberIso` for a `K`-embedding `Ω → Ω_L` (module
`Langlands.Geometry.FieldEtaleStalkChange`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Henniart.Laumon

open Langlands.Geometry

/-- **Finite étale monodromy of a field** (Laumon 1987, (2.1.2.1); Stacks Project, Lemma 58.6.3
and Theorem 59.56.3). -/
theorem finiteEtaleFieldMonodromy : FiniteEtaleFieldMonodromyStatement.{u} := by
  intro K Ω _ _ _ _
  refine ⟨fieldGaloisToAut_isHomeomorph K Ω, fun Λ _ ↦ ?_⟩
  have := IsSepClosure.sep_closed K (K := Ω)
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  refine ⟨FieldEtaleModuleSheaves.equivalence K Ω Λ, FieldEtaleModuleSheaves.forgetIso K Ω Λ,
    fun F σ X x x' hx z ↦ FieldEtaleModuleSheaves.forgetIso_hom_app_ρ K Ω Λ F σ X x x' hx z, ?_⟩
  intro L _ _ ΩL _ _ _ _ _ ι F
  have := IsSepClosure.sep_closed L (K := ΩL)
  refine ⟨(FieldEtaleStalkChange.sheafFiberIso K Ω ΩL ι (ModuleCat.{u + 1} Λ)).app F, ?_, ?_⟩
  · intro X x y hy z
    have h := ConcreteCategory.congr_hom
      (FieldEtaleStalkChange.toPresheafFiber_sheafFiberIso_hom_app K Ω ΩL ι _ F X x) z
    have hxy : (FieldEtaleStalkChange.fiberIso K Ω ΩL ι).hom.app X x = y :=
      Over.OverMorphism.ext hy.symm
    rw [hxy] at h
    exact h
  · intro τ σ hτσ X x y hy z
    have h1 := FieldEtaleModuleSheaves.forgetIso_hom_app_ρ K Ω Λ F σ X x
      (Scheme.galoisOverHom σ ≫ x) rfl z
    have h := ConcreteCategory.congr_hom
      (FieldEtaleStalkChange.toPresheafFiber_sheafFiberIso_hom_app K Ω ΩL ι _ F X
        (Scheme.galoisOverHom σ ≫ x)) z
    have hxy : (FieldEtaleStalkChange.fiberIso K Ω ΩL ι).hom.app X
        (Scheme.galoisOverHom σ ≫ x) = y := by
      refine Over.OverMorphism.ext ?_
      rw [hy]
      change Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
          x.left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
            Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ x.left
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext a
      exact hτσ a
    rw [hxy] at h
    exact (congrArg (fun v ↦
      ((FieldEtaleStalkChange.sheafFiberIso K Ω ΩL ι (ModuleCat.{u + 1} Λ)).app F).hom v) h1).trans h

end Langlands.Henniart.Laumon
