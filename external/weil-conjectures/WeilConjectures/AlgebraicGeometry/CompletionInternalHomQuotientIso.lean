/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Finite-level internal Hom quotient isIso

Source: Stacks Project, Cohomology of Schemes, Tag 0882, comparison-map construction.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-isIso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the level-m source quotient is an internal-Hom
isomorphism into the level-n target quotient when n ≤ m.

Source: Stacks Project, Cohomology of Schemes, Tag 0882, construction of the
comparison map, and Section 0EHN, equation 0880. This finite-level cokernel
argument requires neither coherence nor a Noetherian scheme.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient-isIso).

Proof: Write Q = F/I^n F. Multiplication by I^n on Q is zero: the quotient
projection kills the image of multiplication I^n tensor F → F, and sections
of Q locally lift to F. Since n ≤ m, I^m is contained in I^n, so I^m also
annihilates Q. On any open U, an O_U-linear sheaf map G|U → Q|U therefore
kills I^m G|U: locally its generators ax map to a times the image of x,
which is zero. Restriction to U preserves cokernels of sheaves of modules,
so the cokernel universal property gives a unique map (G/I^m G)|U → Q|U
whose precomposition is the given map. Uniqueness makes these factorizations
compatible with restrictions, addition and scalar multiplication. Thus they
define a morphism between the internal-Hom sheaves in the reverse direction.
Precomposition after this morphism is the identity by its defining property;
the reverse composite is the identity by uniqueness in the cokernel property.
These two identities give the required isomorphism. -/
theorem completion_internal_hom_quotient_isIso {X : Scheme.{u}}
    (I : X.IdealSheafData) (F G : X.Modules) (m n : ℕ) (h : n ≤ m) :
    IsIso (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I m G) (𝟙 (formalModuleQuotient I n F))) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  let : SymmetricCategory X.Modules := SheafOfModules.symmetricCategory X.sheaf
  let : MonoidalClosed X.Modules := SheafOfModules.monoidalClosed (R := X.sheaf)
  let Q := formalModuleQuotient I n F
  let K := Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι m).2 G
  let q : G ⟶ cokernel K := cokernel.π K
  apply isIso_of_yoneda_map_bijective
  intro T
  change X.Modules at T
  let L := MonoidalCategory.tensorRight T
  have : Epi (L.map q) := L.map_epi (cokernel.π K)
  constructor
  · intro a b hab
    apply (SheafOfModules.tensorHomEquiv (R := X.sheaf) _ T Q).symm.injective
    apply (cancel_epi (L.map q)).1
    apply (SheafOfModules.tensorHomEquiv (R := X.sheaf) G T Q).injective
    change SheafOfModules.tensorHomEquiv (R := X.sheaf) G T Q
        (MonoidalCategoryStruct.whiskerRight q T ≫
          (SheafOfModules.tensorHomEquiv (R := X.sheaf) _ T Q).symm a) =
      SheafOfModules.tensorHomEquiv (R := X.sheaf) G T Q
        (MonoidalCategoryStruct.whiskerRight q T ≫
          (SheafOfModules.tensorHomEquiv (R := X.sheaf) _ T Q).symm b)
    rw [SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := X.sheaf) q,
      SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := X.sheaf) q,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hab
  · intro b
    let φ := (SheafOfModules.tensorHomEquiv (R := X.sheaf) G T Q).symm b
    have hz : L.map K ≫ φ = 0 := by
      let J := (Scheme.idealSheafPower I.toModulesι m).1
      let ι : J ⟶ MonoidalCategoryStruct.tensorUnit X.Modules :=
        (Scheme.idealSheafPower I.toModulesι m).2
      let Q := formalModuleQuotient I n F
      let q := formalModuleQuotientπ I n F
      let a (M : X.Modules) : MonoidalCategoryStruct.tensorObj J M ⟶ M :=
        MonoidalCategoryStruct.whiskerRight ι M ≫ (MonoidalCategoryStruct.leftUnitor M).hom
      have nat {M N : X.Modules} (f : M ⟶ N) :
          a M ≫ f = MonoidalCategoryStruct.whiskerLeft J f ≫ a N := by
        dsimp only [a]
        rw [Category.assoc, ← MonoidalCategory.leftUnitor_naturality f]
        exact (MonoidalCategory.whisker_exchange_assoc ι f _).symm
      have : Epi q := inferInstanceAs (Epi (cokernel.π _))
      have haQ : a Q = 0 := by
        apply (cancel_epi ((MonoidalCategory.tensorLeft J).map q)).1
        rw [comp_zero]
        change MonoidalCategoryStruct.whiskerLeft J q ≫ a Q = 0
        rw [← nat q]
        change a F ≫ q = 0
        rw [← image.fac (a F), Category.assoc]
        have hz := formalModuleQuotient_map_zero I (𝟙 F) h
        change Scheme.idealModuleProductι ι F ≫ q = 0 at hz
        change image.ι (a F) ≫ q = 0 at hz
        rw [hz, comp_zero]
      have ht : MonoidalCategoryStruct.whiskerRight (a G) T ≫ φ = 0 := by
        have he : MonoidalCategoryStruct.whiskerRight (a G) T =
            (MonoidalCategoryStruct.associator J G T).hom ≫
              a (MonoidalCategoryStruct.tensorObj G T) := by
          dsimp only [a]
          rw [MonoidalCategory.comp_whiskerRight, MonoidalCategory.leftUnitor_tensor_hom,
            ← Category.assoc,
            ← MonoidalCategory.associator_naturality_left]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
        rw [he, Category.assoc, nat φ, haQ, comp_zero, comp_zero]
      have : Epi ((MonoidalCategory.tensorRight T).map (factorThruImage (a G))) :=
        (MonoidalCategory.tensorRight T).map_epi _
      apply (cancel_epi ((MonoidalCategory.tensorRight T).map (factorThruImage (a G)))).1
      rw [comp_zero]
      change MonoidalCategoryStruct.whiskerRight (factorThruImage (a G)) T ≫
        MonoidalCategoryStruct.whiskerRight (image.ι (a G)) T ≫ φ = 0
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, image.fac]
      exact ht
    let d := (PreservesCokernel.iso L K).hom ≫ cokernel.desc (L.map K) φ hz
    refine ⟨SheafOfModules.tensorHomEquiv (R := X.sheaf) _ T Q d, ?_⟩
    change SheafOfModules.tensorHomEquiv (R := X.sheaf) _ T Q d ≫
      SheafOfModules.homObjMap (R := X.sheaf) q (𝟙 Q) = b
    refine (SheafOfModules.tensorHomEquiv_whiskerRight_comp
      (R := X.sheaf) q d).symm.trans ?_
    change SheafOfModules.tensorHomEquiv (R := X.sheaf) G T Q (L.map q ≫ d) = b
    dsimp only [d, q]
    rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]
    exact (SheafOfModules.tensorHomEquiv (R := X.sheaf) G T Q).apply_symm_apply b

end AlgebraicGeometry
