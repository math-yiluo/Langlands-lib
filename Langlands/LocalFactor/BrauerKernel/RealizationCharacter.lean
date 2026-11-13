import Langlands.LocalFactor.BrauerKernel.RealizationField
import Langlands.LocalFactor.BrauerKernel.ConjugateTransport
import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.Global.Factors.RelativeWeilLocalHecke
import Langlands.Global.HeckeNormPower
import Langlands.LocalFactor.CommonClosureRankOneSpectral
import Langlands.LocalFactor.BrauerKernel.TypeSplit

/-! # Characters of generators at the distinguished place of a global realization -/

noncomputable section

set_option autoImplicit false

universe uF

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum CommonClosure
open Langlands.Global.CompletionPadic Weil.Local
open scoped WithZero NNReal Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality.FiniteExtension (completionMap completionMap_coe)

section Norm

variable {𝕃 : Type} [Field 𝕃] [NumberField 𝕃] (u : HeightOneSpectrum (𝓞 𝕃))

/-- The norm of the completion `𝕃_u` is the residue-normalized absolute value of its
completion-topology realization. -/
theorem norm_eq_topologicalData_normalizedAbs (x : u.adicCompletion 𝕃) :
    ‖x‖ = (topologicalData u).normalizedAbs x := by
  by_cases hx : x = 0
  · rw [hx, norm_zero, (topologicalData u).normalizedAbs_zero]
  have hv : (Valued.v : Valuation (u.adicCompletion 𝕃) ℤᵐ⁰) x ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hx
  rw [(topologicalData u).normalizedAbs_of_ne_zero hx,
    Langlands.Global.HeckeEulerProduct.residueCardinality_eq,
    PadicField.TopologicalData.ord,
    Langlands.Global.AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation,
    NumberField.FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv,
    WithZero.toAdd_unzero_eq_log, neg_neg]
  push_cast
  rfl

/-- The norm of `𝕃_u` is the normalized absolute value of the canonical package of `𝕃_u`
over any prime equal to its residue prime. -/
theorem norm_eq_normalizedAbs_padicFieldAt {p : ℕ} [Fact p.Prime] (h : residuePrime u = p)
    (x : u.adicCompletion 𝕃) :
    ‖x‖ = (padicFieldAt u h).canonicalTopologicalData.normalizedAbs x := by
  subst h
  rw [norm_eq_topologicalData_normalizedAbs,
    PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree,
    PadicField.TopologicalData.normalizedAbs_eq_canonicalNorm_pow_degree]
  rfl

end Norm

section Conjugator

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  (v : HeightOneSpectrum (𝓞 k)) {F : PadicField.{uF} (residuePrime v)} (K : Extension F)
  [Normal F.Carrier K.field] (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))
  (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
  (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
  (hφ : @Continuous _ _ _ F.canonicalTopology φ)
  (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm)
  (hψ : @Continuous _ _ _ (K.asPadicField (p := residuePrime v)).canonicalTopology ψ)
  (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
    algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
  (L : Extension F)
  (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
  [u.asIdeal.LiesOver v.asIdeal]

/-- The embedding `K'_w → \bar{𝕃_u} ≅ \bar F` through Mathlib's chosen closure isomorphism
over the base embedding `F → 𝕃_u`. -/
def realizationClosureEmbedding : w.adicCompletion K' →+* AlgebraicClosure F.Carrier :=
  (extensionClosureEquiv F (towerPadicField v u)
      (realizationBaseAlgHom v u φ hφ')).symm.toRingHom.comp
    (ClassField.Global.RelativeWeilGroup.completionClosureEmbedding u w)

omit [w.asIdeal.LiesOver v.asIdeal] in
/-- On `𝕃_u` the closure embedding is the chosen embedding of the standalone field. -/
theorem realizationClosureEmbedding_completionMap (x : u.adicCompletion (realizationSubfield K θ L)) :
    realizationClosureEmbedding v K θ w φ hφ' L u (completionMap u w x) =
      extensionFieldEmbedding F (towerPadicField v u) (realizationBaseAlgHom v u φ hφ') x := by
  change (extensionClosureEquiv F (towerPadicField v u) (realizationBaseAlgHom v u φ hφ')).symm
      (ClassField.Global.RelativeWeilGroup.completionClosureEmbedding u w
        (algebraMap (u.adicCompletion (realizationSubfield K θ L)) (w.adicCompletion K') x)) = _
  rw [ClassField.Global.RelativeWeilGroup.completionClosureEmbedding_algebraMap]
  rfl

/-- The closure embedding composed with `ψ⁻¹`, as an `F`-algebra map `K → \bar F`. -/
def realizationClosureAlgHom :
    K.field →ₐ[F.Carrier] AlgebraicClosure F.Carrier where
  toRingHom := (realizationClosureEmbedding v K θ w φ hφ' L u).comp
    (ψ.symm : K.field →+* w.adicCompletion K')
  commutes' a := by
    have h1 : ψ.symm (algebraMap F.Carrier K.field a) = completionMap v w (φ.symm a) := by
      rw [RingEquiv.symm_apply_eq, realization_completionMap K v w φ ψ hφ hψ hcomp,
        RingEquiv.apply_symm_apply]
    change realizationClosureEmbedding v K θ w φ hφ' L u
      (ψ.symm (algebraMap F.Carrier K.field a)) = _
    rw [h1, ← ClassField.Global.CompletionTower.completionMap_comp v u w, RingHom.comp_apply,
      realizationClosureEmbedding_completionMap, ← realizationBaseAlgHom_apply v u φ hφ',
      extensionFieldEmbedding_comp]

include hφ hψ hcomp in
/-- **The conjugating Weil element.** There is `τ ∈ W_F` whose Galois projection carries the
closure embedding of `K'_w` to the realization `ψ`. -/
theorem exists_projection_realizationClosureEmbedding :
    ∃ τ : localWeilGroup F, ∀ z : w.adicCompletion K',
      AlgEquiv.toAlgHom (localProjection F τ)
          (realizationClosureEmbedding v K θ w φ hφ' L u z) =
        ((ψ z : K.field) : AlgebraicClosure F.Carrier) := by
  let A' := realizationClosureAlgHom v K θ w φ ψ hφ hφ' hψ hcomp L u
  let α : K.field ≃ₐ[F.Carrier] K.field := A'.restrictNormal' K.field
  obtain ⟨τ, hτ⟩ := galoisRestriction_surjective F K α⁻¹
  refine ⟨τ, fun z => ?_⟩
  have h1 : realizationClosureEmbedding v K θ w φ hφ' L u z =
      ((α (ψ z) : K.field) : AlgebraicClosure F.Carrier) := by
    have h2 := A'.restrictNormal_commutes K.field (ψ z)
    change _ = algebraMap K.field (AlgebraicClosure F.Carrier) (A'.restrictNormal K.field (ψ z))
    rw [h2]
    change _ = realizationClosureEmbedding v K θ w φ hφ' L u (ψ.symm (ψ z))
    rw [RingEquiv.symm_apply_apply]
  rw [h1, ← galoisRestriction_apply, hτ]
  change (((α.symm (α (ψ z))) : K.field) : AlgebraicClosure F.Carrier) = _
  rw [AlgEquiv.symm_apply_apply]

end Conjugator

section Galois

/-- Galois comparison for an abstract realization: if `τ ∈ W_F` carries the closure embedding
`Λ⁻¹ ∘ ĵ` of `K_w` (`Λ` Mathlib's closure isomorphism over `f : F → E`) to `ψ : K_w ≃ K`, and
`ρ ∈ Gal(K'/k)` acts on `K'` as `y ∈ W_E` acts through `ĵ`, then `τ y τ⁻¹` restricts on `K` to
`θ ρ`. -/
theorem galoisRestriction_conj_eq_of_closure {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (K : Extension F) [Normal F.Carrier K.field] {k K' Kw : Type*} [Field k] [Field K']
    [Field Kw] [Algebra k K'] (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))
    (j : K' →+* Kw) (ψ : Kw ≃+* K.field) (hθ : ∀ σ x, θ σ (ψ (j x)) = ψ (j (σ x)))
    {E : PadicField.{0} p} (f : F.Carrier →ₐ[Padic p] E.Carrier)
    (ĵ : Kw →+* AlgebraicClosure E.Carrier) (τ : localWeilGroup F)
    (hτ : ∀ z, AlgEquiv.toAlgHom (localProjection F τ) ((extensionClosureEquiv F E f).symm (ĵ z)) =
      ((ψ z : K.field) : AlgebraicClosure F.Carrier))
    (y : localWeilGroup E) (ρ : K' ≃ₐ[k] K')
    (hρ : ∀ x, ĵ (j (ρ x)) = AlgEquiv.toAlgHom (localProjection E y) (ĵ (j x))) :
    galoisRestriction F K (τ * extensionWeilMap F E f y * τ⁻¹) = θ ρ := by
  have hinv : ∀ z, AlgEquiv.toAlgHom (localProjection F τ)⁻¹
      ((ψ z : K.field) : AlgebraicClosure F.Carrier) =
      (extensionClosureEquiv F E f).symm (ĵ z) := by
    intro z
    rw [← hτ z]
    exact AlgEquiv.symm_apply_apply (localProjection F τ) _
  have h1 : ∀ x, AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E y))
      ((extensionClosureEquiv F E f).symm (ĵ (j x))) =
      (extensionClosureEquiv F E f).symm (ĵ (j (ρ x))) := by
    intro x
    apply (extensionClosureEquiv F E f).injective
    have hg := extensionClosureLift_galoisMap F E f (localProjection E y)
      ((extensionClosureEquiv F E f).symm (ĵ (j x)))
    change extensionClosureEquiv F E f _ = _ at hg
    rw [hg, ← extensionClosureEquiv_apply, RingEquiv.apply_symm_apply,
      RingEquiv.apply_symm_apply]
    exact (hρ x).symm
  have key : ∀ x : K', ((galoisRestriction F K (τ * extensionWeilMap F E f y * τ⁻¹)
      (ψ (j x)) : K.field) : AlgebraicClosure F.Carrier) =
      ((ψ (j (ρ x)) : K.field) : AlgebraicClosure F.Carrier) := by
    intro x
    rw [galoisRestriction_apply]
    have hW : localProjection F (τ * extensionWeilMap F E f y * τ⁻¹) = localProjection F τ *
        extensionGaloisMap F E f (localProjection E y) * (localProjection F τ)⁻¹ := by
      simp only [map_mul, map_inv, localProjection_extensionWeilMap]
    rw [hW]
    change AlgEquiv.toAlgHom (localProjection F τ)
      (AlgEquiv.toAlgHom (extensionGaloisMap F E f (localProjection E y))
        (AlgEquiv.toAlgHom (localProjection F τ)⁻¹
          ((ψ (j x) : K.field) : AlgebraicClosure F.Carrier))) = _
    rw [hinv, h1]
    exact hτ _
  rw [← θ.apply_symm_apply (galoisRestriction F K (τ * extensionWeilMap F E f y * τ⁻¹))]
  congr 1
  apply AlgEquiv.ext
  intro x
  apply j.injective
  apply ψ.injective
  apply Subtype.ext
  rw [← hθ, θ.apply_symm_apply]
  exact key x

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  [IsGalois k K']
  (v : HeightOneSpectrum (𝓞 k)) {F : PadicField.{uF} (residuePrime v)} (K : Extension F)
  [Normal F.Carrier K.field] (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))
  (w : HeightOneSpectrum (𝓞 K'))
  (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
  (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm)
  (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
    ψ (algebraMap K' (w.adicCompletion K') (σ x)))
  (L : Extension F)
  (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
  [u.asIdeal.LiesOver v.asIdeal] {c : ClassField.Global.FundamentalClass.ClassFamily.{0}}

include hθ in
/-- **Galois comparison at the distinguished place.** Let `τ ∈ W_F` carry the closure embedding
of `K'_w` to `ψ`, and let `ι : W_{𝕃_u} → W_{K'/𝕃}` satisfy the projection clause of a local
relative Weil map. Then the restriction to `K` of `τ y τ⁻¹`, for `y ∈ W_{𝕃_u}` viewed in `W_F`,
is `θ` of the Galois projection of `ι y`. -/
theorem galoisRestriction_conj_extensionWeilMap (τ : localWeilGroup F)
    (hτ : ∀ z, AlgEquiv.toAlgHom (localProjection F τ)
        (realizationClosureEmbedding v K θ w φ hφ' L u z) =
      ((ψ z : K.field) : AlgebraicClosure F.Carrier))
    (ι : localWeilGroup (towerPadicField v u) →
      ClassField.Global.RelativeWeilGroup c (realizationSubfield K θ L) K')
    (hι : ∀ (g : localWeilGroup (towerPadicField v u)) (x : K'),
      ClassField.Global.RelativeWeilGroup.completionClosureEmbedding u w
          (algebraMap K' (w.adicCompletion K')
            (ClassField.Global.RelativeWeilGroup.projection c (realizationSubfield K θ L) K'
              (ι g) x)) =
        AlgEquiv.toAlgHom (localProjection (towerPadicField v u) g)
          (ClassField.Global.RelativeWeilGroup.completionClosureEmbedding u w
            (algebraMap K' (w.adicCompletion K') x)))
    (y : localWeilGroup (towerPadicField v u)) :
    galoisRestriction F K (τ * extensionWeilMap F (towerPadicField v u)
        (realizationBaseAlgHom v u φ hφ') y * τ⁻¹) =
      θ ((ClassField.Global.RelativeWeilGroup.projection c (realizationSubfield K θ L) K'
        (ι y)).restrictScalars k) :=
  galoisRestriction_conj_eq_of_closure K θ (algebraMap K' (w.adicCompletion K')) ψ hθ
    (realizationBaseAlgHom v u φ hφ')
    (ClassField.Global.RelativeWeilGroup.completionClosureEmbedding u w) τ hτ y _ (hι y)

end Galois

section Character

open ClassField.Global ClassField.Global.RelativeWeilGroup LocalClassField

attribute [local instance] relativeGaloisTopology

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  [IsGalois k K']
  (v : HeightOneSpectrum (𝓞 k)) {F : PadicField.{uF} (residuePrime v)} (K : Extension F)
  [Normal F.Carrier K.field] (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))
  (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
  (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
  (hφ : @Continuous _ _ _ F.canonicalTopology φ)
  (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm)
  (hψ : @Continuous _ _ _ (K.asPadicField (p := residuePrime v)).canonicalTopology ψ)
  (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
    algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
  (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
    ψ (algebraMap K' (w.adicCompletion K') (σ x)))
  (L : Extension F) (hL : L.field ≤ K.field)
  (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
  [u.asIdeal.LiesOver v.asIdeal] {c : FundamentalClass.ClassFamily.{0}}

set_option maxHeartbeats 1000000 in
/-- **The characters of a generator at the distinguished place.** Let `e` be normalized and
`χ` a field character of `L ⊆ K` whose twisted Weil character `χ ∘ e_L · ω_{-t}` is the
inflation of a character `θL` of the Galois image of `W_L`. Let `ι : W_{𝕃_u} → W_{K'/𝕃}`
satisfy the projection clause of a local relative Weil map and have transfer inverse to the
transported candidate `e'` of `𝕃_u`. Let `Θ` be a Hecke character of `𝕃` whose reciprocity
character is the inflation of `θL` through `θ`, and `α` a Hecke character of `k` trivial on
`k_v^×`. Then `χ` is the transport along the generator-field isomorphism of the component at
`u` of `(α ∘ N) · ‖·‖^t · Θ`. -/
theorem fieldCharacter_eq_realizationTransport (e : ReciprocityFamily F)
    (he : NormalizedReciprocity F e) (χ : FieldCharacter F L) (t : ℂ)
    (θL : galoisImage F K L →* ℂˣ)
    (hspec : ∀ x : weilSubgroup F L,
      θL (toGaloisImage F K L x) = twistedWeilCharacter F e L χ t x)
    (ι : localWeilGroup (towerPadicField v u) →
      RelativeWeilGroup c (realizationSubfield K θ L) K')
    (hι : ∀ (g : localWeilGroup (towerPadicField v u)) (x : K'),
      completionClosureEmbedding u w
          (algebraMap K' (w.adicCompletion K')
            (projection c (realizationSubfield K θ L) K' (ι g) x)) =
        AlgEquiv.toAlgHom (localProjection (towerPadicField v u) g)
          (completionClosureEmbedding u w (algebraMap K' (w.adicCompletion K') x)))
    (hιt : ∀ y, transfer c (realizationSubfield K θ L) K' (ι y) =
      (IdeleClassGroup.ofAdicCompletion (𝓞 (realizationSubfield K θ L))
        (realizationSubfield K θ L) u
        (RankOne.reciprocityUnits (towerPadicField v u)
          (extensionReciprocityCandidate F (towerPadicField v u)
            (realizationBaseAlgHom v u φ hφ') e) y))⁻¹)
    (α : Langlands.Global.HeckeCharacter k) (hα : α.finiteComponent v = 1)
    (Θ : Langlands.Global.HeckeCharacter (realizationSubfield K θ L))
    (hΘ : ∀ x, ∃ hx : θ ((projection c (realizationSubfield K θ L) K' x).restrictScalars k) ∈
        galoisImage F K L,
      continuousReciprocityCharacter c (realizationSubfield K θ L) K' Θ x = θL ⟨_, hx⟩) :
    χ = PadicField.ConductorTransport.quasicharacter (towerPadicField v u)
      (L.asPadicField (p := residuePrime v))
      (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u)
      (quasicharacterAt u (residuePrime_eq v u)
        ((Langlands.Global.HeckeCharacter.normComp α *
          Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t *
          Θ).finiteComponent u)) := by
  let := (towerPadicField v u).algebra
  let : Algebra (Padic (residuePrime v)) L.field := (L.asPadicField (p := residuePrime v)).algebra
  obtain ⟨τ, hτ⟩ := exists_projection_realizationClosureEmbedding v K θ w φ ψ hφ hφ' hψ hcomp L u
  have hσ : ∀ x, ((realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u x : L.field) :
      AlgebraicClosure F.Carrier) = ((ψ (completionMap u w x) : K.field) :
        AlgebraicClosure F.Carrier) :=
    realizationGeneratorEquiv_apply v K θ w φ ψ hφ hψ hcomp hθ L hL u
  have hw : ∀ x, AlgEquiv.toAlgHom (localProjection F τ)
      (extensionFieldEmbedding F (towerPadicField v u) (realizationBaseAlgHom v u φ hφ') x) =
      ((realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u x : L.field) :
        AlgebraicClosure F.Carrier) := by
    intro x
    rw [hσ, ← realizationClosureEmbedding_completionMap v K θ w φ hφ' L u]
    exact hτ _
  have hb : ∀ z, z ∈ L.field ↔ ∃ x,
      ((realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u x : L.field) :
        AlgebraicClosure F.Carrier) = z := by
    intro z
    constructor
    · intro hz
      obtain ⟨x, hx⟩ := (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u).surjective
        (show (L.asPadicField (p := residuePrime v)).Carrier from (⟨z, hz⟩ : L.field))
      exact ⟨x, congrArg (fun t : L.field => (t : AlgebraicClosure F.Carrier)) hx⟩
    · rintro ⟨x, rfl⟩
      exact (show L.field from
        realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u x).2
  have hL' := conj_extensionFiniteIntermediate_field F L _ hb τ hw
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨y, hy⟩ := rankOne_reciprocityUnits_surjective
    (extensionReciprocityCandidate F (towerPadicField v u) (realizationBaseAlgHom v u φ hφ') e)
    (Units.mapEquiv (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u).symm.toMulEquiv x)
  have hσy : realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u
      (RankOne.reciprocityUnits (towerPadicField v u)
        (extensionReciprocityCandidate F (towerPadicField v u)
          (realizationBaseAlgHom v u φ hφ') e) y : (towerPadicField v u).Carrier) =
      (x : (L.asPadicField (p := residuePrime v)).Carrier) := by
    rw [hy]
    exact AlgEquiv.apply_symm_apply _ _
  let W : weilSubgroup F L := ⟨τ * extensionWeilMap F (towerPadicField v u)
    (realizationBaseAlgHom v u φ hφ') y * τ⁻¹, conj_extensionWeilMap_mem F L τ hL' y⟩
  have hrec : reciprocityUnits F e L W = x := by
    apply Units.ext
    apply Subtype.ext
    rw [reciprocityUnits_conj_extension F e he L _ τ hw hL' y]
    exact congrArg (fun t : L.field => (t : AlgebraicClosure F.Carrier)) hσy
  have hL1 : ((χ x : ℂˣ) : ℂ) = (CommonClosureSpectral.character F L t W : ℂ) *
      (θL (toGaloisImage F K L W) : ℂ) := by
    rw [← hrec]
    change (weilCharacter F e L χ W : ℂ) = _
    rw [weilCharacter_eq_twisted F e L χ t W, hspec W]
  have hchar : (CommonClosureSpectral.character F L t W : ℂ) =
      Complex.exp (t * (Real.log ((L.asPadicField (p := residuePrime v)).canonicalTopologicalData.normalizedAbs
        (x : L.field)) : ℂ)) := by
    rw [CommonClosureSpectralAnalytic.character_eq_norm_exp F e L he t W, hrec]
    rfl
  have hn : (padicFieldAt u (residuePrime_eq v u)).canonicalTopologicalData.normalizedAbs
      (RankOne.reciprocityUnits (towerPadicField v u)
        (extensionReciprocityCandidate F (towerPadicField v u)
          (realizationBaseAlgHom v u φ hφ') e) y : (towerPadicField v u).Carrier) =
      (L.asPadicField (p := residuePrime v)).canonicalTopologicalData.normalizedAbs
        (x : L.field) := by
    rw [← PadicField.CanonicalTransport.normalizedAbs_map (towerPadicField v u)
      (L.asPadicField (p := residuePrime v))
      (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u), hσy]
  have hnorm : ∀ a : (u.adicCompletion (realizationSubfield K θ L))ˣ,
      ((Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t).finiteComponent u
        a : ℂ) = Complex.exp (t * (Real.log
          ((padicFieldAt u (residuePrime_eq v u)).canonicalTopologicalData.normalizedAbs
            (a : u.adicCompletion (realizationSubfield K θ L))) : ℂ)) := by
    intro a
    rw [Langlands.Global.HeckeCharacter.normPower_finiteComponent,
      norm_eq_normalizedAbs_padicFieldAt u (residuePrime_eq v u)]
  have hα' : ∀ a : (u.adicCompletion (realizationSubfield K θ L))ˣ,
      (((Langlands.Global.HeckeCharacter.normComp
        (L := realizationSubfield K θ L) α).finiteComponent u a : ℂˣ) : ℂ) = 1 := by
    intro a
    rw [Langlands.Global.HeckeCharacter.normComp_finiteComponent α v ⟨u, inferInstance⟩, hα]
    rfl
  have hΘ' : ((Θ.finiteComponent u
      (RankOne.reciprocityUnits (towerPadicField v u)
        (extensionReciprocityCandidate F (towerPadicField v u)
          (realizationBaseAlgHom v u φ hφ') e) y) : ℂˣ) : ℂ) =
      (θL (toGaloisImage F K L W) : ℂ) := by
    have h1 := continuousReciprocityCharacter_apply_of_transfer_eq Θ ι
      (fun y => RankOne.reciprocityUnits (towerPadicField v u)
        (extensionReciprocityCandidate F (towerPadicField v u)
          (realizationBaseAlgHom v u φ hφ') e) y) hιt y
    obtain ⟨hx, h2⟩ := hΘ (ι y)
    have h3 := h1.symm.trans h2
    refine (congrArg Units.val h3).trans ?_
    refine congrArg (fun s => ((θL s : ℂˣ) : ℂ)) (Subtype.ext ?_)
    exact (galoisRestriction_conj_extensionWeilMap v K θ w φ ψ hφ' hθ L u τ hτ ι hι y).symm
  have hq : ((PadicField.ConductorTransport.quasicharacter (towerPadicField v u)
      (L.asPadicField (p := residuePrime v))
      (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u)
      (quasicharacterAt u (residuePrime_eq v u)
        ((Langlands.Global.HeckeCharacter.normComp α *
          Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t *
          Θ).finiteComponent u)) x : ℂˣ) : ℂ) =
      (((Langlands.Global.HeckeCharacter.normComp α *
          Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t *
          Θ).finiteComponent u
        (Units.mapEquiv
          (realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u).symm.toMulEquiv x) :
          ℂˣ) : ℂ) := rfl
  have hq2 := congrArg (fun a : (u.adicCompletion (realizationSubfield K θ L))ˣ =>
    (((Langlands.Global.HeckeCharacter.normComp α *
          Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t *
          Θ).finiteComponent u a : ℂˣ) : ℂ)) hy.symm
  have hsplit : ∀ a : (u.adicCompletion (realizationSubfield K θ L))ˣ,
      (((Langlands.Global.HeckeCharacter.normComp α *
          Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t *
          Θ).finiteComponent u a : ℂˣ) : ℂ) =
      (((Langlands.Global.HeckeCharacter.normComp (L := realizationSubfield K θ L) α).finiteComponent u
          a : ℂˣ) : ℂ) *
        (((Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t).finiteComponent u
          a : ℂˣ) : ℂ) * ((Θ.finiteComponent u a : ℂˣ) : ℂ) := by
    intro a
    rw [Langlands.Global.HeckeCharacter.finiteComponent_mul,
      Langlands.Global.HeckeCharacter.finiteComponent_mul, ContinuousMonoidHom.mul_apply,
      ContinuousMonoidHom.mul_apply, Units.val_mul, Units.val_mul]
  have e2 : (((Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t).finiteComponent u
      (RankOne.reciprocityUnits (towerPadicField v u)
        (extensionReciprocityCandidate F (towerPadicField v u)
          (realizationBaseAlgHom v u φ hφ') e) y) : ℂˣ) : ℂ) =
      Complex.exp (t * (Real.log ((L.asPadicField (p := residuePrime v)).canonicalTopologicalData.normalizedAbs
        (x : L.field)) : ℂ)) :=
    (hnorm _).trans (congrArg (fun r : ℝ => Complex.exp (t * (Real.log r : ℂ))) hn)
  have eR : (((Langlands.Global.HeckeCharacter.normComp (L := realizationSubfield K θ L) α).finiteComponent u
        (RankOne.reciprocityUnits (towerPadicField v u)
          (extensionReciprocityCandidate F (towerPadicField v u)
            (realizationBaseAlgHom v u φ hφ') e) y) : ℂˣ) : ℂ) *
      (((Langlands.Global.HeckeCharacter.normPower (realizationSubfield K θ L) t).finiteComponent u
        (RankOne.reciprocityUnits (towerPadicField v u)
          (extensionReciprocityCandidate F (towerPadicField v u)
            (realizationBaseAlgHom v u φ hφ') e) y) : ℂˣ) : ℂ) *
      ((Θ.finiteComponent u
        (RankOne.reciprocityUnits (towerPadicField v u)
          (extensionReciprocityCandidate F (towerPadicField v u)
            (realizationBaseAlgHom v u φ hφ') e) y) : ℂˣ) : ℂ) =
      (CommonClosureSpectral.character F L t W : ℂ) * (θL (toGaloisImage F K L W) : ℂ) := by
    rw [hα', e2, hΘ', hchar, one_mul]
  apply Units.ext
  exact hL1.trans (hq.trans (hq2.trans ((hsplit _).trans eR))).symm

end Character

end Langlands.LocalFactor.NonabelianBrauer
