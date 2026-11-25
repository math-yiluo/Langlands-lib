/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleAnnihilated
import WeilConjectures.AlgebraicGeometry.TorsionControlledAlgebraizationConstruction
import WeilConjectures.AlgebraicGeometry.TorsionControlledCompletionHomLift

/-! # Torsion-controlled triples for easy algebraization

Source: Stacks Project, Tag 0889, part (1)
(blueprint: lem-weil-pbc-easy-algebraization-torsion-triple).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Easy algebraization with the torsion condition on the actual coherent map retained.
Uniqueness is among torsion-controlled triples. This restriction matters when the ideal
is the unit ideal: completion then forgets everything, and an unrestricted triple need
not be isomorphic to the chosen one.

Source: Stacks Project, Tag 0889, part (1), including condition (1)(b)
(blueprint: lem-weil-pbc-easy-algebraization-torsion-triple).

Proof:
Restrict to a finite affine cover. The coherent-formal-module affine equivalence turns
alpha into a map from a finite completed module to the completion of a finite module.
Remark 0888 converts the uniform component annihilation into annihilation of the limit
kernel and cokernel. The formal-gluing isogeny theorem constructs a module map with
ideal-power-torsion kernel and cokernel whose completion is this map. The finiteness
criterion for formal gluing makes its source finite. Formal gluing also gives unique
isomorphisms of any two such torsion-controlled triples, respecting both the map and
completion comparison. On overlaps those isomorphisms satisfy the cocycle identity by
uniqueness; glue the modules and their maps and completion comparisons. Finitely many
affines give a uniform positive exponent for the glued kernel and cokernel. The same
uniqueness glues isomorphisms of triples and proves the asserted global uniqueness.
-/
theorem grothendieckExistenceEasy_torsionTriple
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H : CoherentModules X) (N : CoherentFormalModule X J)
    (δ : N ⟶ (completion X J).obj H)
    (htorsion : ∃ t : ℕ, 1 ≤ t ∧ ∀ e : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (δ.hom.app (op e)))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (δ.hom.app (op e))))) :
    ∃ (F : CoherentModules X) (a : F ⟶ H) (β : N ≅ (completion X J).obj F),
      δ = β.hom ≫ (completion X J).map a ∧
      (∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel a.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel a.hom))) ∧
      ∀ (F' : CoherentModules X) (a' : F' ⟶ H)
        (β' : N ≅ (completion X J).obj F'),
        δ = β'.hom ≫ (completion X J).map a' →
        (∃ s : ℕ, 1 ≤ s ∧
          IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
            (kernel a'.hom)) ∧
          IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
            (cokernel a'.hom))) →
        ∃! γ : F ≅ F', γ.hom ≫ a' = a ∧
          β.hom ≫ (completion X J).map γ.hom = β'.hom := by
  have hlocal := ((coherentFormalModule_annihilated_iff X J J N
    ((completion X J).obj H) δ).out 1 2).mp htorsion
  obtain ⟨F, a, β, hδ, ha⟩ :=
    torsionControlled_algebraization_construction J H N δ hlocal
  refine ⟨F, a, β, hδ, ha, ?_⟩
  intro F' a' β' hδ' ha'
  let C := completion X J
  have hforward : (β.inv ≫ β'.hom) ≫ C.map a' = C.map a := by
    rw [Category.assoc, ← hδ', hδ, Iso.inv_hom_id_assoc]
  have hbackward : (β'.inv ≫ β.hom) ≫ C.map a = C.map a' := by
    rw [Category.assoc, ← hδ, hδ', Iso.inv_hom_id_assoc]
  obtain ⟨g, hg, _⟩ :=
    torsionControlled_completion_hom_lift J H F F' a a' ha ha' _ hforward
  obtain ⟨h, hh, _⟩ :=
    torsionControlled_completion_hom_lift J H F' F a' a ha' ha _ hbackward
  have identity_lift (G : CoherentModules X) (b : G ⟶ H)
      (hb : ∃ s : ℕ, 1 ≤ s ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (kernel b.hom)) ∧
        IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
          (cokernel b.hom)))
      (k : G ⟶ G) (hk : k ≫ b = b ∧ C.map k = 𝟙 _) : k = 𝟙 G := by
    obtain ⟨l, _, hl⟩ :=
      torsionControlled_completion_hom_lift J H G G b b hb hb (𝟙 _) (by simp)
    exact (hl k hk).trans (hl (𝟙 G) (by simp)).symm
  have hgh : g ≫ h = 𝟙 F := by
    apply identity_lift F a ha
    constructor
    · rw [Category.assoc, hh.1, hg.1]
    · rw [C.map_comp, hg.2, hh.2]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  have hhg : h ≫ g = 𝟙 F' := by
    apply identity_lift F' a' ha'
    constructor
    · rw [Category.assoc, hg.1, hh.1]
    · rw [C.map_comp, hh.2, hg.2]
      simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  let γ : F ≅ F' := ⟨g, h, hgh, hhg⟩
  have hβ : β.hom ≫ C.map g = β'.hom := by
    rw [hg.2, Iso.hom_inv_id_assoc]
  refine ⟨γ, ⟨hg.1, hβ⟩, ?_⟩
  intro γ' hγ'
  apply Iso.ext
  obtain ⟨l, _, hl⟩ :=
    torsionControlled_completion_hom_lift J H F F' a a' ha ha' _ hforward
  have hmap : C.map γ'.hom = β.inv ≫ β'.hom := by
    rw [← hγ'.2, Iso.inv_hom_id_assoc]
  exact (hl γ'.hom ⟨hγ'.1, hmap⟩).trans (hl g hg).symm

end AlgebraicGeometry
