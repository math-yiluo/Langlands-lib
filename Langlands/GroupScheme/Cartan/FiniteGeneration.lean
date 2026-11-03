import Langlands.GroupScheme.Cartan.GenerationStatement
import Langlands.GroupScheme.FiniteGeneration
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.Reductive.TorusGenerationStatement
import Langlands.GroupScheme.Torus.Geometry

/-! # The family of actual Cartan subgroups and conditional finite torus generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- An actual Cartan subgroup, with its group scheme, inclusion and Cartan proof.
This type indexes all presentations, without identifying isomorphic presentations. -/
structure CartanSubgroup (G : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  isCartan : IsCartanSubgroup inclusion

/-- Cartan generation and maximal-torus self-centralization supply finite torus
 generation. Pointed-image generation is discharged by its published proof. -/
theorem reductiveFiniteTorusGeneration_of_cartanGeneration
    (hCartan : CartanGenerationStatement.{u})
    (hcentralizer : MaximalTorusCentralizerStatement.{u}) :
    ReductiveFiniteTorusGenerationStatement.{u} := by
  intro k _ _ G hG
  classical
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let A : CartanSubgroup G → GroupScheme (Spec (CommRingCat.of k)) := fun C => C.group
  let a : ∀ C : CartanSubgroup G, A C ⟶ G := fun C => C.inclusion
  have hT : ∀ C : CartanSubgroup G, IsTorus (A C) := fun C =>
    C.isCartan.isTorus_of_centralizerStatement hcentralizer hG
  have hA : ∀ C : CartanSubgroup G,
      Smooth (A C).X.hom ∧ IsAffineHom (A C).X.hom ∧ ConnectedSpace (A C).X.left := by
    intro C
    refine ⟨(hT C).smooth, ?_, (hT C).connectedSpace⟩
    let : IsClosedImmersion (a C).hom.hom.left := C.isCartan.1
    change IsAffineHom C.group.X.hom
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  have hall : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G),
      IsClosedSubgroup i → (∀ C : CartanSubgroup G, FactorsThrough (a C).hom.hom i) →
        SubgroupFunctor.range i = ⊤ := by
    intro H i hi hfamily
    apply hCartan k G hG.smooth hG.isAffineHom hG.connectedSpace H i hi
    intro C c hc
    exact hfamily ⟨C, c, hc⟩
  obtain ⟨s, hs⟩ := FiniteGeneration.exists_finite_generating_subfamily_of_pointedImageGeneration
    (A := A) (a := a) ImageGeneration.pointedImageGeneration hA hall
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, (fun j => A (e j).val), (fun j => a (e j).val),
    (fun j => hT (e j).val), (fun j => (e j).val.isCartan.1), ?_⟩
  intro H i hi hfamily
  apply hs H i hi
  intro C hC
  have h := hfamily (e.symm ⟨C, hC⟩)
  change FactorsThrough (a (e (e.symm ⟨C, hC⟩)).val).hom.hom i at h
  rw [e.apply_symm_apply] at h
  exact h

end Langlands.GroupScheme
