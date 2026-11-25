import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.Primary
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Internal.UnitLattice
import Langlands.ClassFieldTheory.Global.FinitePlaceConjugacy

/-!
# The places of `L` above `S` as a `Gal(L/K)`-set

Let `L ⊆ K_S` be finite Galois over the number field `K`, with group `Γ = Gal(L/K)` acting on the
places of `L` by transport of structure (`finitePlaceAction`). For an embedding `j : L → K̄_v`, the
place of `L` defined by `j ∘ σ⁻¹` is `σ` applied to the place defined by `j`
(`placeOfAlgHom_comp_inv`): the completion `L_{σw}` is carried to `L_w` by `σ⁻¹`
(`finiteCompletionAlgEquiv`). Hence, with `w_v` the place of `L` given by the chosen embedding
`ι_v` of `K_S` into `K̄_v`:

* the places of `L` above `v` form one orbit, that of `w_v` (`exists_galRestrict_smul_eq`);
* the stabilizer of `w_v` is the decomposition group `D_v`, the image of the local Galois group
  `Gal(K̄_v/K_v) → G_S → Γ` (`smul_basePlace_eq_iff`);

so that the places above `S` are `⊔_{v ∈ S} Γ/D_v` as a `Γ`-set (`placesAboveEquiv`).
-/

namespace Langlands.GaloisCohomology

open Langlands.Galois NumberField IsDedekindDomain Langlands.Global.AdelicFunctoriality
open scoped Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

noncomputable section

section Conjugate

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  {v : HeightOneSpectrum (𝓞 K)}

omit [NumberField K] in
/-- The place `σ • w` lies over the same place as `w`. -/
theorem liesOver_smul (σ : L ≃ₐ[K] L) (w : FinitePlacesAbove L v) :
    (σ • w.1).asIdeal.LiesOver v.asIdeal := by
  rw [liesOver_iff_eq_under, under_smul_finitePlace, ← liesOver_iff_eq_under]
  exact w.2

/-- **Conjugate places.** The place of `L` defined by `j ∘ σ⁻¹` is `σ` applied to the place
defined by `j`. -/
theorem placeOfAlgHom_comp_inv (j : L →ₐ[K] AlgebraicClosure (v.adicCompletion K)) (σ : L ≃ₐ[K] L) :
    ((placeOfAlgHom (j.comp ((σ⁻¹ : L ≃ₐ[K] L) : L →ₐ[K] L))).1 : HeightOneSpectrum (𝓞 L)) =
      σ • (placeOfAlgHom j).1 := by
  have : (placeOfAlgHom j).1.asIdeal.LiesOver v.asIdeal := (placeOfAlgHom j).2
  have hσw : (σ • (placeOfAlgHom j).1).asIdeal.LiesOver v.asIdeal := liesOver_smul σ _
  let w' : FinitePlacesAbove L v := ⟨σ • (placeOfAlgHom j).1, hσw⟩
  let c : w'.1.adicCompletion L →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K) :=
    (completionEmbeddingOfAlgHom j).comp
      (Langlands.ClassFieldTheory.Global.finiteCompletionAlgEquiv v (placeOfAlgHom j).1
        (σ⁻¹ : L ≃ₐ[K] L)).toAlgHom
  have hc : ∀ x : L, c (algebraMap L _ x) = (j.comp ((σ⁻¹ : L ≃ₐ[K] L) : L →ₐ[K] L)) x := fun x => by
    change completionEmbeddingOfAlgHom j
      (Langlands.ClassFieldTheory.Global.finiteCompletionAlgEquiv v (placeOfAlgHom j).1
        (σ⁻¹ : L ≃ₐ[K] L) (algebraMap L _ x)) = _
    rw [Langlands.ClassFieldTheory.Global.finiteCompletionAlgEquiv_coe,
      completionEmbeddingOfAlgHom_algebraMap]
    rfl
  exact (congrArg Subtype.val (eq_placeOfAlgHom _ c hc)).symm

end Conjugate

section Orbits

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {L : Type u} [Field L] [NumberField L] [Algebra K L]
  [Algebra L Ω] [IsScalarTower K L Ω]
  (hL : ∀ x : L, algebraMap L Ω x ∈ maximalUnramifiedOutside K Ω S) [IsGalois K L]
  (ι : PlaceEmbeddings K Ω)

attribute [local instance 2000] IsSepClosure.isGalois

/-- `x ↦ ι_v ∘ x⁻¹|_L` turns left multiplication into precomposition with the inverse. -/
theorem localEmbedding_mul_left (v : HeightOneSpectrum (𝓞 K))
    (σ x : GaloisGroupUnramifiedOutside K Ω S) :
    localEmbedding hL ι v (σ * x) =
      (localEmbedding hL ι v x).comp ((Galois.galRestrict hL σ)⁻¹ : L ≃ₐ[K] L).toAlgHom := by
  ext l
  rw [AlgHom.comp_apply, localEmbedding_apply, localEmbedding_apply, mul_inv_rev, AlgEquiv.mul_apply]
  congr 2
  rw [← map_inv, ← Galois.galRestrict_apply]
  rfl

/-- The place of `L` attached to `σ x` is `σ` applied to the place attached to `x`. -/
theorem localPlace_mul_left (v : HeightOneSpectrum (𝓞 K)) (σ x : GaloisGroupUnramifiedOutside K Ω S) :
    ((Langlands.Galois.localPlace hL ι v (σ * x)).1 : HeightOneSpectrum (𝓞 L)) =
      Galois.galRestrict hL σ • (Langlands.Galois.localPlace hL ι v x).1 := by
  rw [Langlands.Galois.localPlace, localEmbedding_mul_left]
  exact placeOfAlgHom_comp_inv _ _

/-- The base place `w_v` of `L` above `v`: the place of the embedding `ι_v`. -/
abbrev basePlace (v : HeightOneSpectrum (𝓞 K)) : FinitePlacesAbove L v :=
  Langlands.Galois.localPlace hL ι v 1

/-- The decomposition group of `v` in `Gal(L/K)`: the image of the local Galois group. -/
def decompositionGroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup (L ≃ₐ[K] L) :=
  ((Galois.galRestrict hL).comp (localizationHom ι S v).toMonoidHom).range

/-- Every place of `L` above `v` is in the orbit of the base place. -/
theorem exists_galRestrict_smul_eq (v : HeightOneSpectrum (𝓞 K)) (w : FinitePlacesAbove L v) :
    ∃ σ : GaloisGroupUnramifiedOutside K Ω S, Galois.galRestrict hL σ • (basePlace hL ι v).1 = w.1 := by
  obtain ⟨j, rfl⟩ := exists_placeOfAlgHom_eq w
  obtain ⟨x, rfl⟩ := exists_localEmbedding_eq hL ι v j
  refine ⟨x, ?_⟩
  rw [← localPlace_mul_left, mul_one]

/-- **The stabilizer of the base place is the decomposition group.** -/
theorem smul_basePlace_eq_iff (v : HeightOneSpectrum (𝓞 K)) (τ : L ≃ₐ[K] L) :
    τ • ((basePlace hL ι v).1 : HeightOneSpectrum (𝓞 L)) = (basePlace hL ι v).1 ↔
      τ ∈ decompositionGroup hL ι v := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := galRestrict_surjective hL τ
    rw [← localPlace_mul_left, mul_one] at h
    have h' : Langlands.Galois.localPlace hL ι v x = Langlands.Galois.localPlace hL ι v 1 := Subtype.ext h
    obtain ⟨g, hg⟩ := exists_algEquiv_of_placeOfAlgHom_eq _ _ h'.symm
    have hinjι : Function.Injective (ι.finite v) := (ι.finite v).toRingHom.injective
    have hinjL : Function.Injective (embeddingMaximalUnramifiedOutside hL) :=
      (embeddingMaximalUnramifiedOutside hL).toRingHom.injective
    have key : ∀ y : L, (x⁻¹ : GaloisGroupUnramifiedOutside K Ω S)
        (embeddingMaximalUnramifiedOutside hL y) =
        localizationHom ι S v g (embeddingMaximalUnramifiedOutside hL y) := fun y => by
      apply Subtype.ext
      apply hinjι
      have := hg y
      rw [localEmbedding_apply, localEmbedding_apply, inv_one, AlgEquiv.one_apply] at this
      rw [localizationHom_apply]
      exact this
    refine ⟨g⁻¹, ?_⟩
    apply AlgEquiv.ext
    intro l
    apply hinjL
    rw [MonoidHom.comp_apply, Galois.galRestrict_apply, Galois.galRestrict_apply]
    have h2 := key (Galois.galRestrict hL x l)
    rw [Galois.galRestrict_apply, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply] at h2
    change (localizationHom ι S v g⁻¹) _ = _
    conv_lhs => rw [h2]
    rw [map_inv, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  · rintro ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, ← localPlace_mul_left, mul_one]
    have := localPlace_mul hL ι v 1 (u := 1) (one_mem _) g
    rw [one_mul, one_mul] at this
    exact congrArg Subtype.val this

end Orbits

end

end Langlands.GaloisCohomology
