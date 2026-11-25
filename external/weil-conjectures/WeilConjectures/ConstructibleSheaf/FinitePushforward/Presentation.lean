/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.EtaleLowerShriekQcqs
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.FiniteSubsum
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape

/-!
# Presentations of constructible sheaves (Stacks 095N)

A constructible sheaf of `Λ`-modules on a quasi-compact quasi-separated scheme, `Λ` Noetherian,
is the cokernel of a map between finite sums of extensions by zero `v_! Λ` along étale maps from
affine schemes (`AlgebraicGeometry.Etale.exists_presentation_of_isConstructibleSheaf`). By 093C
it is a quotient of a sum of such `v_! Λ`, which are constructible (Stacks 03SA), hence of a
finite subsum (Stacks 095M); the kernel is again constructible, so the same applies to it.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
  [CompactSpace X] [QuasiSeparatedSpace X]

/-- A constructible sheaf is a quotient of a finite sum of extensions by zero `v_! Λ` along étale
maps from affine schemes. -/
lemma exists_epi_sigma_lowerShriekUnit (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (w : ∀ i, U i ⟶ X) (hw : ∀ i, Etale (w i))
      (_ : ∀ i, IsAffine (U i)) (π : (∐ fun i ↦ Etale.lowerShriekUnit (Λ := Λ) (w i) (hw i)) ⟶ F),
      Epi π := by
  classical
  let G : Etale.SectionIndex F → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    fun i ↦ Etale.lowerShriekUnit (Λ := Λ) i.1.1.hom i.1.1.prop
  have hG (i : Etale.SectionIndex F) : IsConstructibleSheaf (G i) :=
    have : IsAffine ((𝟭 Scheme).obj i.1.1.left) := i.1.2
    have : Etale i.1.1.hom := i.1.1.prop
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (X := X) i.1.1.hom
  have := Etale.epi_sigmaDesc_sectionHom F
  obtain ⟨S, hS⟩ :=
    exists_epi_finsetSigmaDesc G (fun i ↦ Etale.sectionHom F i.1.1.hom i.1.1.prop i.2)
  let e := S.equivFin.symm
  refine ⟨S.card, fun k ↦ (e k).1.1.1.left, fun k ↦ (e k).1.1.1.hom, fun k ↦ (e k).1.1.1.prop,
    fun k ↦ (e k).1.1.2, (Sigma.whiskerEquiv (f := fun k ↦ G (e k).1) (g := fun i : S ↦ G i.1) e
      fun _ ↦ Iso.refl _).hom ≫
      finsetSigmaDesc G (fun i ↦ Etale.sectionHom F i.1.1.hom i.1.1.prop i.2) S, ?_⟩
  exact epi_comp _ _

attribute [local instance] Abelian.hasFiniteBiproducts in
/-- **Stacks 095N.** A constructible sheaf of `Λ`-modules on a quasi-compact quasi-separated
scheme is the cokernel of a map between finite sums of extensions by zero `v_! Λ` along étale
maps from affine schemes. -/
@[stacks 095N]
theorem exists_presentation_of_isConstructibleSheaf [IsNoetherianRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F] :
    ∃ (m n : ℕ) (V : Fin m → Scheme.{u}) (v : ∀ j, V j ⟶ X) (hv : ∀ j, Etale (v j))
      (_ : ∀ j, IsAffine (V j)) (U : Fin n → Scheme.{u}) (w : ∀ i, U i ⟶ X)
      (hw : ∀ i, Etale (w i)) (_ : ∀ i, IsAffine (U i))
      (φ : (∐ fun j ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (v j) (hv j)).obj
        ((constantSheaf (V j).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
          (ModuleCat.of Λ Λ))) ⟶
        ∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (w i) (hw i)).obj
          ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ)))
      (π : (∐ fun i ↦ (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) (w i) (hw i)).obj
          ((constantSheaf (U i).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ Λ))) ⟶ F)
      (hφπ : φ ≫ π = 0), Nonempty (IsColimit (CokernelCofork.ofπ π hφπ)) := by
  obtain ⟨n, U, w, hw, hU, π, hπ⟩ := exists_epi_sigma_lowerShriekUnit (Λ := Λ) F
  have (i : Fin n) : IsConstructibleSheaf (Etale.lowerShriekUnit (Λ := Λ) (w i) (hw i)) :=
    have := hU i
    have := hw i
    isConstructibleSheaf_lowerShriekUnit_of_isAffine_source (w i)
  have := isConstructibleSheaf_sigma_fin fun i ↦ Etale.lowerShriekUnit (Λ := Λ) (w i) (hw i)
  have := IsConstructibleSheaf.kernel π
  obtain ⟨m, V, v, hv, hV, p, hp⟩ := exists_epi_sigma_lowerShriekUnit (Λ := Λ) (kernel π)
  refine ⟨m, n, V, v, hv, hV, U, w, hw, hU, p ≫ kernel.ι π, π, by simp, ⟨?_⟩⟩
  have hc0 := Abelian.epiIsCokernelOfKernel _ (kernelIsKernel π)
  refine CokernelCofork.IsColimit.ofπ π _ (fun g hg ↦ hc0.desc (CokernelCofork.ofπ g ?_))
    (fun g hg ↦ ?_) (fun g hg m hm ↦ ?_)
  · change kernel.ι π ≫ g = 0
    rw [← cancel_epi p, comp_zero, ← Category.assoc]
    exact hg
  · exact hc0.fac _ WalkingParallelPair.one
  · exact Cofork.IsColimit.hom_ext hc0 (hm.trans
      (hc0.fac (CokernelCofork.ofπ g _) WalkingParallelPair.one).symm)

end Etale

end AlgebraicGeometry
