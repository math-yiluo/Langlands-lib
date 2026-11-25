import Langlands.Galois.RestrictedRamification.MaximalExtension

/-!
# The group `G_S` in two isomorphic extensions

For a number field `K`, a set `S` of finite places of `K` and an isomorphism `e : Ω ≃ₐ[K] Ω'` of
Galois extensions of `K` (for example two separable closures), `e` carries the maximal extension
of `K` in `Ω` unramified outside `S` onto the one in `Ω'`
(`maximalUnramifiedOutside_map_algEquiv`), and conjugation by `e` is an isomorphism of
topological groups `G_S(Ω) ≃ₜ* G_S(Ω')` (`galoisGroupUnramifiedOutsideCongr`) compatible with the
quotient maps from `Gal(Ω / K)` and `Gal(Ω' / K)` (`galoisGroupUnramifiedOutsideCongr_quotientMap`).

The algebraic input is that a prime is unramified exactly when its preimage under an isomorphism
of algebras is (`isUnramifiedAt_of_algEquiv`): an isomorphism is formally unramified, so is a
localization, and unramifiedness is transitive in a tower (`Algebra.IsUnramifiedAt.comp`). The
topological input is that conjugation by `e` carries the fixing subgroup of a finite
subextension to the fixing subgroup of its image (`fixingSubgroup_map_autCongr`), so it is
continuous for the Krull topologies (`continuous_autCongr`).
-/

noncomputable section

universe u v w

namespace Langlands.Galois

open Langlands.Galois IsDedekindDomain
open scoped NumberField

section Unramified

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- A prime `P` of `B` is unramified over `R` if its preimage under an isomorphism of
`R`-algebras `A ≃ₐ[R] B` is. -/
theorem isUnramifiedAt_of_algEquiv (ψ : A ≃ₐ[R] B) (P : Ideal B) [P.IsPrime]
    [Algebra.IsUnramifiedAt R (P.comap ψ)] : Algebra.IsUnramifiedAt R P := by
  let : Algebra A B := ψ.toRingHom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algHom ψ.toAlgHom
  have : P.LiesOver (P.comap ψ) := ⟨rfl⟩
  have : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId A B) ψ.surjective
  have : Algebra.IsUnramifiedAt A P :=
    Algebra.FormallyUnramified.comp A B (Localization.AtPrime P)
  exact Algebra.IsUnramifiedAt.comp (P.comap ψ) P

/-- A prime of `R` is unramified in `B` if it is unramified in an `R`-algebra isomorphic to
`B`. -/
theorem isUnramifiedIn_of_algEquiv (ψ : A ≃ₐ[R] B) {p : Ideal R}
    (h : Algebra.IsUnramifiedIn A p) : Algebra.IsUnramifiedIn B p := by
  intro P hP hPp
  have hQ : (P.comap ψ).LiesOver p := by
    refine ⟨?_⟩
    rw [hPp.over]
    ext r
    simp only [Ideal.under, Ideal.mem_comap, AlgEquiv.commutes]
  have := h (P.comap ψ) inferInstance hQ
  exact isUnramifiedAt_of_algEquiv ψ P

end Unramified

section Fields

variable {K : Type u} [Field K] [NumberField K] {Ω : Type v} {Ω' : Type w} [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra K Ω'] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- An isomorphism of extensions carries a finite subextension unramified outside `S` to one
unramified outside `S`. -/
theorem isUnramifiedOutside_map_algEquiv (e : Ω ≃ₐ[K] Ω') {E : IntermediateField K Ω}
    [FiniteDimensional K E] (hE : IsUnramifiedOutside S E) :
    IsUnramifiedOutside S (E.map e.toAlgHom) := by
  have : FiniteDimensional K (E.map e.toAlgHom) :=
    (IntermediateField.intermediateFieldMap e E).toLinearEquiv.finiteDimensional
  have := NumberField.of_module_finite K E
  have := NumberField.of_module_finite K (E.map e.toAlgHom)
  intro v hv
  exact isUnramifiedIn_of_algEquiv
    (NumberField.RingOfIntegers.mapAlgEquiv (IntermediateField.intermediateFieldMap e E)) (hE v hv)

/-- An isomorphism of Galois extensions carries the maximal extension unramified outside `S`
onto the maximal extension unramified outside `S`. -/
theorem maximalUnramifiedOutside_map_algEquiv [IsGalois K Ω] [IsGalois K Ω'] (e : Ω ≃ₐ[K] Ω') :
    (maximalUnramifiedOutside K Ω S).map e.toAlgHom = maximalUnramifiedOutside K Ω' S := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maximalUnramifiedOutside_iff S).1 hx
    have : FiniteDimensional K (E.map e.toAlgHom) :=
      (IntermediateField.intermediateFieldMap e E).toLinearEquiv.finiteDimensional
    exact le_maximalUnramifiedOutside S (isUnramifiedOutside_map_algEquiv S e hu) ⟨x, hxE, rfl⟩
  · intro x hx
    obtain ⟨E, hf, hu, hxE⟩ := (mem_maximalUnramifiedOutside_iff S).1 hx
    have : FiniteDimensional K (E.map e.symm.toAlgHom) :=
      (IntermediateField.intermediateFieldMap e.symm E).toLinearEquiv.finiteDimensional
    refine ⟨e.symm x, le_maximalUnramifiedOutside S (isUnramifiedOutside_map_algEquiv S e.symm hu)
      ⟨x, hxE, rfl⟩, ?_⟩
    simp

end Fields

section Krull

variable {B : Type*} {Ω₁ : Type*} {Ω₂ : Type*} [Field B] [Field Ω₁] [Field Ω₂] [Algebra B Ω₁]
  [Algebra B Ω₂]

/-- Conjugation by an isomorphism of extensions carries the fixing subgroup of an intermediate
field to the fixing subgroup of its image. -/
theorem fixingSubgroup_map_autCongr (e : Ω₁ ≃ₐ[B] Ω₂) (F : IntermediateField B Ω₁) :
    F.fixingSubgroup.map e.autCongr.toMonoidHom = (F.map e.toAlgHom).fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hτ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro _ ⟨x, hx, rfl⟩
    change e (τ (e.symm (e x))) = e x
    rw [e.symm_apply_apply, hτ x hx]
  · intro hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    refine ⟨e.autCongr.symm σ, ?_, e.autCongr.apply_symm_apply σ⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change e.symm (σ (e x)) = x
    rw [hσ (e x) ⟨x, hx, rfl⟩, e.symm_apply_apply]

open scoped Topology in
/-- Conjugation by an isomorphism of extensions is continuous for the Krull topologies. -/
theorem continuous_autCongr (e : Ω₁ ≃ₐ[B] Ω₂) : Continuous e.autCongr := by
  apply continuous_of_continuousAt_one e.autCongr
  change Filter.Tendsto e.autCongr (𝓝 1) (𝓝 (e.autCongr 1))
  rw [map_one]
  apply Filter.tendsto_def.mpr
  intro s hs
  obtain ⟨D, hD, hDs⟩ := (krullTopology_mem_nhds_one_iff B Ω₂ s).mp hs
  have : FiniteDimensional B D := hD
  have hC : FiniteDimensional B (D.map e.symm.toAlgHom) :=
    (IntermediateField.intermediateFieldMap e.symm D).toLinearEquiv.finiteDimensional
  apply (krullTopology_mem_nhds_one_iff B Ω₁ _).mpr
  refine ⟨D.map e.symm.toAlgHom, hC, fun σ hσ => hDs ?_⟩
  have h : e.autCongr σ ∈ ((D.map e.symm.toAlgHom).map e.toAlgHom).fixingSubgroup := by
    rw [← fixingSubgroup_map_autCongr]
    exact ⟨σ, hσ, rfl⟩
  rwa [IntermediateField.map_map, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id B Ω₂ from
    AlgHom.ext e.apply_symm_apply, IntermediateField.map_id] at h

/-- Conjugation by an isomorphism of extensions, as an isomorphism of topological groups for the
Krull topologies. -/
def autCongrContinuous (e : Ω₁ ≃ₐ[B] Ω₂) : (Ω₁ ≃ₐ[B] Ω₁) ≃ₜ* (Ω₂ ≃ₐ[B] Ω₂) where
  toMulEquiv := e.autCongr
  continuous_toFun := continuous_autCongr e
  continuous_invFun := continuous_autCongr e.symm

/-- The value of `autCongrContinuous e σ`: `e ∘ σ ∘ e⁻¹`. -/
theorem autCongrContinuous_apply (e : Ω₁ ≃ₐ[B] Ω₂) (σ : Ω₁ ≃ₐ[B] Ω₁) (x : Ω₂) :
    autCongrContinuous e σ x = e (σ (e.symm x)) :=
  rfl

end Krull

section GaloisGroup

variable {K : Type u} [Field K] [NumberField K] {Ω : Type v} {Ω' : Type w} [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra K Ω'] [IsGalois K Ω] [IsGalois K Ω'] (S : Set (HeightOneSpectrum (𝓞 K)))

/-- The isomorphism of the maximal extensions unramified outside `S` induced by an isomorphism
`e : Ω ≃ₐ[K] Ω'`. -/
def maximalUnramifiedOutsideAlgEquiv (e : Ω ≃ₐ[K] Ω') :
    maximalUnramifiedOutside K Ω S ≃ₐ[K] maximalUnramifiedOutside K Ω' S :=
  (IntermediateField.intermediateFieldMap e _).trans
    (IntermediateField.equivOfEq (maximalUnramifiedOutside_map_algEquiv S e))

/-- `maximalUnramifiedOutsideAlgEquiv S e` is `e` on elements. -/
theorem maximalUnramifiedOutsideAlgEquiv_apply (e : Ω ≃ₐ[K] Ω')
    (x : maximalUnramifiedOutside K Ω S) :
    ((maximalUnramifiedOutsideAlgEquiv S e x : maximalUnramifiedOutside K Ω' S) : Ω') = e x :=
  rfl

/-- Its inverse is `e⁻¹` on elements. -/
theorem maximalUnramifiedOutsideAlgEquiv_symm_apply (e : Ω ≃ₐ[K] Ω')
    (x : maximalUnramifiedOutside K Ω' S) :
    (((maximalUnramifiedOutsideAlgEquiv S e).symm x : maximalUnramifiedOutside K Ω S) : Ω) =
      e.symm x := by
  have h := maximalUnramifiedOutsideAlgEquiv_apply S e
    ((maximalUnramifiedOutsideAlgEquiv S e).symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  rw [← e.symm_apply_apply (((maximalUnramifiedOutsideAlgEquiv S e).symm x :
    maximalUnramifiedOutside K Ω S) : Ω), ← h]

/-- An isomorphism `e : Ω ≃ₐ[K] Ω'` of Galois extensions induces, by conjugation, an isomorphism
of topological groups `G_S(Ω) ≃ₜ* G_S(Ω')`. -/
def galoisGroupUnramifiedOutsideCongr (e : Ω ≃ₐ[K] Ω') :
    GaloisGroupUnramifiedOutside K Ω S ≃ₜ* GaloisGroupUnramifiedOutside K Ω' S :=
  autCongrContinuous (maximalUnramifiedOutsideAlgEquiv S e)

/-- The value of `galoisGroupUnramifiedOutsideCongr S e σ` on an element of `K_S ⊆ Ω'`. -/
theorem galoisGroupUnramifiedOutsideCongr_apply (e : Ω ≃ₐ[K] Ω')
    (σ : GaloisGroupUnramifiedOutside K Ω S) (x : maximalUnramifiedOutside K Ω' S) :
    ((galoisGroupUnramifiedOutsideCongr S e σ x : maximalUnramifiedOutside K Ω' S) : Ω') =
      e (σ ((maximalUnramifiedOutsideAlgEquiv S e).symm x)) :=
  rfl

/-- The isomorphism `G_S(Ω) ≃ₜ* G_S(Ω')` is compatible with the quotient maps from `Gal(Ω / K)`
and `Gal(Ω' / K)` and conjugation by `e`. -/
theorem galoisGroupUnramifiedOutsideCongr_quotientMap (e : Ω ≃ₐ[K] Ω') (σ : Gal(Ω/K)) :
    galoisGroupUnramifiedOutsideCongr S e (GaloisGroupUnramifiedOutside.quotientMap K Ω S σ) =
      GaloisGroupUnramifiedOutside.quotientMap K Ω' S (e.autCongr σ) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  rw [galoisGroupUnramifiedOutsideCongr_apply, GaloisGroupUnramifiedOutside.quotientMap_apply,
    GaloisGroupUnramifiedOutside.quotientMap_apply, maximalUnramifiedOutsideAlgEquiv_symm_apply]
  rfl

end GaloisGroup

end Langlands.Galois
