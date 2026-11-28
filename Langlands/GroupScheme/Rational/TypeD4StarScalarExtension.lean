import Langlands.GroupScheme.Reductive.TitsPrescribedStabilizerField
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField

/-! # Persistence of a transitive D4 leaf action under scalar extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (E : IntermediateField k (SeparableClosure k))

local instance d4ScalarClosureAlgebra : Algebra E (SeparableClosure E) :=
  (separableClosure E (AlgebraicClosure E)).algebra

local instance d4ScalarExtensionAffine :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance d4ScalarExtensionFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- If the degree of an intermediate field is not divisible by three, no
trialitarian D4 leaf becomes fixed by its full absolute Galois group. -/
theorem prescribedStabilizerIndex_D4_of_not_three_dvd_finrank
    (e : d.Vertex ≃ Fin 4) (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a ≠ a)
    (hdeg : ¬ 3 ∣ Module.finrank k E) :
    let C := d.prescribedStabilizerIndexComparison E
    let eE := C.vertices.symm.trans e
    (∀ a b, C.index.cartan a b = CartanMatrix.D 4 (eE a) (eE b)) ∧
      ∀ a : C.index.Vertex, eE a ≠ 1 →
        ∃ τ : SeparableClosure E ≃ₐ[E] SeparableClosure E, C.index.star τ a ≠ a := by
  classical
  let C := d.prescribedStabilizerIndexComparison E
  let eE := C.vertices.symm.trans e
  refine ⟨?_, ?_⟩
  · intro a b
    simpa only [eE, Equiv.trans_apply, Equiv.apply_symm_apply] using
      (C.cartan_eq (C.vertices.symm a) (C.vertices.symm b)).trans
        (hD (C.vertices.symm a) (C.vertices.symm b))
  · intro x hx
    let a := C.vertices.symm x
    have ha : e a ≠ 1 := hx
    by_contra! hfixed
    have hsub : E.fixingSubgroup ≤ d.starVertexStabilizer a := by
      intro σ hσ
      let s : E.fixingSubgroup := ⟨σ, hσ⟩
      let e₀ := prescribedStabilizerClosureEquiv E
      let τ := (AlgEquiv.autCongr e₀).symm (IntermediateField.fixingSubgroupEquiv E s)
      have he : ((AlgEquiv.autCongr e₀ τ).restrictScalars k) = σ := by
        dsimp only [τ]
        rw [MulEquiv.apply_symm_apply]
        rfl
      apply (d.mem_starVertexStabilizer a σ).mpr
      apply C.vertices.injective
      have ht := C.star_eq τ a
      change C.vertices (d.star ((AlgEquiv.autCongr e₀ τ).restrictScalars k) a) =
        C.index.star τ (C.vertices a) at ht
      rw [he, show C.vertices a = x from C.vertices.apply_symm_apply x, hfixed] at ht
      exact ht.trans (C.vertices.apply_symm_apply x).symm
    have hle : d.starVertexField a ≤ E := by
      rw [← InfiniteGalois.fixedField_fixingSubgroup E]
      intro y hy
      change y ∈ IntermediateField.fixedField (d.starVertexStabilizer a) at hy
      exact (IntermediateField.mem_fixedField_iff _ _).mpr fun σ hσ =>
        (IntermediateField.mem_fixedField_iff _ _).mp hy σ (hsub hσ)
    have hn : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
        ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a = a := by
      rintro ⟨b, hb, hfix⟩
      obtain ⟨σ, hσ⟩ := hno b hb
      exact hσ (hfix σ)
    have h := IntermediateField.finrank_dvd_of_le_right hle
    rw [d.finrank_starVertexField_of_D4_no_fixed_leaf e hD hn a ha] at h
    exact hdeg h

/-- The transported Cartan numbering and its moving leaves over the extension. -/
theorem exists_D4_index_of_not_three_dvd_finrank
    (e : d.Vertex ≃ Fin 4) (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ∀ a : d.Vertex, e a ≠ 1 →
      ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a ≠ a)
    (hdeg : ¬ 3 ∣ Module.finrank k E) :
    ∃ (dE : TitsIndexData ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (eE : dE.Vertex ≃ Fin 4),
      (∀ a b, dE.cartan a b = CartanMatrix.D 4 (eE a) (eE b)) ∧
      ∀ a : dE.Vertex, eE a ≠ 1 →
        ∃ τ : SeparableClosure E ≃ₐ[E] SeparableClosure E, dE.star τ a ≠ a :=
  ⟨_, _, d.prescribedStabilizerIndex_D4_of_not_three_dvd_finrank E e hD hno hdeg⟩

end Langlands.GroupScheme.TitsIndexData
