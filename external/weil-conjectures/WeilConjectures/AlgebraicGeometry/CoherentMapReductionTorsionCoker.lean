/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
/-! Cokernel half of reduction torsion. -/
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
private theorem product_zero_of_epi {X : Scheme.{u}} {J F G : X.Modules}
    (ι : J ⟶ SheafOfModules.unit X.ringCatSheaf) (q : F ⟶ G) [Epi q]
    (hz : IsZero (Scheme.idealModuleProduct ι F)) :
    IsZero (Scheme.idealModuleProduct ι G) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  let a := MonoidalCategoryStruct.whiskerRight ι F ≫
    (MonoidalCategoryStruct.leftUnitor F).hom
  let b := MonoidalCategoryStruct.whiskerRight ι G ≫
    (MonoidalCategoryStruct.leftUnitor G).hom
  have ha : a = 0 := by
    rw [← image.fac a, hz.eq_zero_of_src (image.ι a), comp_zero]
  have : Epi ((MonoidalCategory.tensorLeft J).map q) :=
    (MonoidalCategory.tensorLeft J).map_epi q
  have hb : b = 0 := by
    apply (cancel_epi ((MonoidalCategory.tensorLeft J).map q)).1
    rw [comp_zero]
    change MonoidalCategoryStruct.whiskerLeft J q ≫
      (MonoidalCategoryStruct.whiskerRight ι G ≫
        (MonoidalCategoryStruct.leftUnitor G).hom) = 0
    rw [← Category.assoc]
    erw [MonoidalCategory.whisker_exchange]
    change MonoidalCategoryStruct.whiskerRight ι F ≫
      (MonoidalCategoryStruct.whiskerLeft (MonoidalCategoryStruct.tensorUnit X.Modules) q ≫
        (MonoidalCategoryStruct.leftUnitor G).hom) = 0
    have hcomp := (MonoidalCategory.leftUnitor_naturality q).symm
    rw [← hcomp]
    change a ≫ q = 0
    rw [ha, zero_comp]
  apply IsZero.of_mono_eq_zero (image.ι b)
  apply (cancel_epi (factorThruImage b)).1
  simpa only [image.fac, comp_zero] using hb

set_option linter.unusedVariables false in
/-- Cokernel part of the reduction torsion bound.
Source: Stacks Project, Remark 0888, final commutative algebra argument.
Proof: the quotient projection H → H/I^(n+1)H followed by the reduced cokernel
projection kills a, so factors through coker(a). This factor is epic because its
composite with the original cokernel projection is epic. Ideal annihilation descends
along epimorphisms: tensoring an epimorphism is epic, and multiplication is natural.
Thus K^t kills the reduced cokernel. The inclusion K^(2t) → K^t factors the associated
ideal-product inclusion, proving the claimed bound. Neither coherence nor the
kernel hypothesis is needed for this component.
(blueprint: lem-weil-pbc-coherent-map-reduction-torsion-coker) -/
theorem coherentMap_reduction_torsion_coker
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (F H : CoherentModules X) (a : F ⟶ H) (t : ℕ) (ht : 1 ≤ t)
    (hker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (kernel a.hom)))
    (hcoker : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι t).2
      (cokernel a.hom))) :
    ∀ n : ℕ, IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (2 * t)).2
      (cokernel (formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))))) := by
  intro n
  let b := formalModuleQuotientMap I a.hom (Nat.le_refl (n + 1))
  let q := formalModuleQuotientπ I (n + 1) H.obj ≫ cokernel.π b
  have hq : a.hom ≫ q = 0 := by
    change a.hom ≫ formalModuleQuotientπ I (n + 1) H.obj ≫ cokernel.π b = 0
    rw [← Category.assoc]
    have hb : formalModuleQuotientπ I (n + 1) F.obj ≫ b =
        a.hom ≫ formalModuleQuotientπ I (n + 1) H.obj := by
      simp [b, formalModuleQuotientπ, formalModuleQuotientMap]
    rw [← hb, Category.assoc, cokernel.condition, comp_zero]
  have : Epi q := by dsimp [q, formalModuleQuotientπ]; infer_instance
  let e := cokernel.desc a.hom q hq
  have : Epi e := by dsimp [e]; infer_instance
  have hz := product_zero_of_epi (Scheme.idealSheafPower K.toModulesι t).2 e hcoker
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K (𝟙 (cokernel b))
    (show t ≤ 2 * t by omega)
  have hi := hz.eq_zero_of_src
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι t).2 (cokernel b))
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have : Mono (Scheme.idealModuleProductι
      (Scheme.idealSheafPower K.toModulesι (2 * t)).2 (cokernel b)) := by
    dsimp [Scheme.idealModuleProductι]; infer_instance
  apply IsZero.of_mono_eq_zero (Scheme.idealModuleProductι
    (Scheme.idealSheafPower K.toModulesι (2 * t)).2 (cokernel b))
  simpa [hi] using hk
end AlgebraicGeometry
