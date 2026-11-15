import Langlands.CommutativeAlgebra.Popescu.FieldCaseStatement
import Langlands.CommutativeAlgebra.Popescu.CharZeroResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.CharPResolutionStatement
import Langlands.CommutativeAlgebra.Popescu.SingularIdealFactorizationStatement

/-! # Assembly of the field case of Popescu's theorem (Stacks 07GC, field case) -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

open TensorProduct

/-- Over a field `k`, a regular `k`-algebra is geometrically regular: it is the fibre over the
unique prime `⊥` of `k`, whose residue field is `k` itself. -/
theorem RegularAlgebra.geometricallyRegular_of_field {k : Type u} {Λ : Type*} [Field k]
    [CommRing Λ] [Algebra k Λ] (h : RegularAlgebra k Λ) : GeometricallyRegular k Λ := by
  have hb := h.2 ⊥
  let e : k ≃ₐ[k] (⊥ : Ideal k).ResidueField := (⊥ : Ideal k).algEquivResidueFieldOfField
  let eΛ : (⊥ : Ideal k).Fiber Λ ≃ₐ[k] Λ :=
    (Algebra.TensorProduct.congr e.symm AlgEquiv.refl).trans (Algebra.TensorProduct.lid k Λ)
  refine ⟨?_, ?_⟩
  · have := hb.1
    exact isNoetherianRing_of_ringEquiv _ eΛ.toRingEquiv
  · intro k' _ _ _ _
    let : Algebra (⊥ : Ideal k).ResidueField k' :=
      ((algebraMap k k').comp e.symm.toRingHom).toAlgebra
    have : IsScalarTower k (⊥ : Ideal k).ResidueField k' :=
      IsScalarTower.of_algebraMap_eq fun x => by
        show algebraMap k k' x = algebraMap k k' (e.symm (algebraMap k _ x))
        rw [e.symm.commutes, Algebra.algebraMap_self_apply]
    have : FiniteDimensional (⊥ : Ideal k).ResidueField k' :=
      Module.Finite.of_restrictScalars_finite k _ k'
    have : IsPurelyInseparable (⊥ : Ideal k).ResidueField k' :=
      IsPurelyInseparable.tower_top k _ k'
    have := hb.2 k'
    exact IsRegularRing.of_ringEquiv
      (Algebra.TensorProduct.cancelBaseChange k (⊥ : Ideal k).ResidueField k' k' Λ).toRingEquiv

/-- The field case of Popescu's theorem, assuming Stacks Lemma 2.8 (07EU) and the resolution
lemmas 10.3 (07FE, characteristic zero) and 11.4 (07FJ, characteristic `p`). The proof is the
Noetherian induction of Stacks 07GC: among all factorizations `A → B → Λ` with `B` finitely
presented, pick one whose ideal `h_B` is maximal. If `h_B = Λ`, Lemma 2.8 finishes; otherwise a
minimal prime over `h_B` can be resolved, contradicting maximality. -/
theorem fieldCase_of_resolutions (h3 : SingularIdealFactorizationStatement.{u})
    (h7 : CharZeroResolutionStatement.{u}) (h8 : CharPResolutionStatement.{u}) :
    PopescuFieldCaseStatement.{u} := by
  intro k Λ _ _ _ _ hreg A _ _ _ f
  have hgr : GeometricallyRegular k Λ := RegularAlgebra.geometricallyRegular_of_field hreg
  have : IsRegularRing Λ := hgr.isRegularRing
  have hres : ∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra.FinitePresentation k B]
      (h : B →ₐ[k] Λ) (q : Ideal Λ) [q.IsPrime], q ∈ (singularRadical k h).minimalPrimes →
      CanBeResolved k h q := by
    intro B _ _ _ h q _ hq
    rcases CharP.exists' k with hchar | ⟨p, _, _⟩
    · exact h7 k B Λ h q hq inferInstance
    · exact h8 k B Λ p hgr h q hq
  let S : Set (Ideal Λ) := {I | ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B),
      Algebra.FinitePresentation k B ∧ ∃ (g : A →ₐ[k] B) (h : B →ₐ[k] Λ), h.comp g = f ∧
        I = singularRadical k h}
  have hne : S.Nonempty :=
    ⟨_, A, inferInstance, inferInstance, inferInstance, AlgHom.id k A, f, AlgHom.comp_id f, rfl⟩
  obtain ⟨I, ⟨B, _, _, hB, g, h, hgh, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian Λ Λ) S hne
  have := hB
  by_cases htop : singularRadical k h = ⊤
  · have : (singularIdeal k B).map h = ⊤ := Ideal.radical_eq_top.mp htop
    obtain ⟨C, _, _, hC, g', h', hgh'⟩ := h3 k B Λ h this
    exact ⟨C, inferInstance, inferInstance, hC, g'.comp g, h', by
      rw [← AlgHom.comp_assoc, hgh', hgh]⟩
  · exfalso
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ htop
    obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
    have : q.IsPrime := hq.1.1
    obtain ⟨C, _, _, hC, g', h', hgh', hle', hnle⟩ := hres B h q hq
    refine hmax (singularRadical k h') ⟨C, inferInstance, inferInstance, hC, g'.comp g, h', ?_, rfl⟩
      (lt_of_le_of_ne hle' fun heq => hnle ?_)
    · rw [← AlgHom.comp_assoc, hgh', hgh]
    · rw [← heq]
      exact hq.1.2

end Langlands.CommutativeAlgebra.Popescu
