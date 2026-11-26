import Langlands.ClassFieldTheory.Global.LocalRelativeWeilMapConjugacyProof
import Langlands.ClassFieldTheory.Global.CohomologyMaps
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Weil.Local.ExtensionNormReciprocity
import Langlands.Weil.Local.FiniteGaloisTower
import Langlands.Weil.Local.FiniteGaloisAbsoluteConjugation

/-!
# Conjugacy of local-to-relative Weil maps at different places

Two local-to-relative Weil maps `W_{F_v} → W_{E/F}` at places `w`, `w'` above `v`, for
geometric reciprocity candidates of `E_w` and `E_{w'}`, are conjugate in `W_{E/F}`.
-/

noncomputable section

namespace Langlands.ClassFieldTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Topology Filter
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

universe u

/-- Two embeddings of a normal extension differ by an automorphism. -/
theorem exists_algEquiv_comp_eq_of_normal {F E Ω : Type*} [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Normal F E] (j j' : E →ₐ[F] Ω) :
    ∃ σ : E ≃ₐ[F] E, ∀ x, j (σ x) = j' x := by
  let _ : Algebra E Ω := j.toRingHom.toAlgebra
  have : IsScalarTower F E Ω := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  exact ⟨j'.restrictNormal' E, fun x => j'.restrictNormal_commutes E x⟩

namespace RelativeWeilGroup

section Embedding

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : Langlands.Global.FinitePlace F) (w : Langlands.Global.FinitePlace E)
  [w.asIdeal.LiesOver v.asIdeal]

/-- The embedding `E → \bar{F_v}` through `E_w`, as an `F`-algebra map. -/
def globalClosureEmbedding : E →ₐ[F] AlgebraicClosure (v.adicCompletion F) where
  toRingHom := (completionClosureEmbedding v w).comp (algebraMap E (w.adicCompletion E))
  commutes' a := by
    have h1 : algebraMap E (w.adicCompletion E) (algebraMap F E a) =
        algebraMap (v.adicCompletion F) (w.adicCompletion E)
          (algebraMap F (v.adicCompletion F) a) :=
      (FiniteExtension.completionMap_coe v w a).symm
    change completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) (algebraMap F E a)) = _
    rw [h1, completionClosureEmbedding_algebraMap]
    exact (IsScalarTower.algebraMap_apply F (v.adicCompletion F) _ a).symm

theorem globalClosureEmbedding_apply (x : E) :
    globalClosureEmbedding v w x =
      completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x) := rfl

/-- Every intermediate field of `\bar{F_v}/F_v` containing the image of `E` contains the
image of `E_w`: `E_w` is spanned over `F_v` by `E`. -/
theorem completionClosureEmbedding_mem_of_global
    (K : IntermediateField (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)))
    (h : ∀ x : E, completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x) ∈ K)
    (z : w.adicCompletion E) : completionClosureEmbedding v w z ∈ K := by
  classical
  let q : FinitePlacesAbove E v := ⟨w, inferInstance⟩
  have key : ∀ t, completionClosureEmbedding v w (finiteTensorMap (L := E) v t q) ∈ K := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul a y =>
      rw [finiteTensorMap_tmul, map_mul]
      refine K.mul_mem ?_ (h y)
      have ha := completionClosureEmbedding_algebraMap v w a
      change completionClosureEmbedding v w
        (algebraMap (v.adicCompletion F) (w.adicCompletion E) a) ∈ K
      rw [ha]
      exact K.algebraMap_mem a
    | add s t hs ht =>
      rw [map_add, Pi.add_apply, map_add]
      exact K.add_mem hs ht
  obtain ⟨t, ht⟩ := finiteTensorMap_surjective (L := E) v
    (Function.update (0 : (r : FinitePlacesAbove E v) → r.1.adicCompletion E) q z)
  have hz : finiteTensorMap (L := E) v t q = z := by
    rw [ht, Function.update_self]
  rw [← hz]
  exact key t

end Embedding


section Comparison

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Langlands.Global.FinitePlace F} {w w' : Langlands.Global.FinitePlace E}
  [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
  (σ : E ≃ₐ[F] E)
  (hσ : ∀ x, globalClosureEmbedding v w (σ x) = globalClosureEmbedding v w' x)

include hσ in
/-- The image of `E_{w'}` in `\bar{F_v}` lies in the image of `E_w`. -/
theorem exists_completionClosureEmbedding_eq (z : w'.adicCompletion E) :
    ∃ u : w.adicCompletion E,
      completionClosureEmbedding v w u = completionClosureEmbedding v w' z := by
  have hK := completionClosureEmbedding_mem_of_global v w'
    (Weil.Local.extensionIntermediateField (padicField v) (towerPadicField v w)
      (completionPadicAlgHom v w)) (fun x => (Weil.Local.mem_extensionIntermediateField _ _ _ _).mpr
        ⟨algebraMap E (w.adicCompletion E) (σ x), hσ x⟩) z
  exact (Weil.Local.mem_extensionIntermediateField _ _ _ _).mp hK

/-- A preimage in `E_w` of the image of an element of `E_{w'}`. -/
def completionComparisonFun (z : w'.adicCompletion E) : w.adicCompletion E :=
  Classical.choose (exists_completionClosureEmbedding_eq σ hσ z)

theorem completionComparisonFun_spec (z : w'.adicCompletion E) :
    completionClosureEmbedding v w (completionComparisonFun σ hσ z) =
      completionClosureEmbedding v w' z :=
  Classical.choose_spec (exists_completionClosureEmbedding_eq σ hσ z)

/-- The comparison map `E_{w'} → E_w` over the common image in `\bar{F_v}`. -/
def completionComparison : w'.adicCompletion E →+* w.adicCompletion E where
  toFun := completionComparisonFun σ hσ
  map_one' := (completionClosureEmbedding v w).injective (by
    rw [completionComparisonFun_spec, map_one, map_one])
  map_mul' a b := (completionClosureEmbedding v w).injective (by
    rw [map_mul, completionComparisonFun_spec, completionComparisonFun_spec,
      completionComparisonFun_spec, map_mul])
  map_zero' := (completionClosureEmbedding v w).injective (by
    rw [completionComparisonFun_spec, map_zero, map_zero])
  map_add' a b := (completionClosureEmbedding v w).injective (by
    rw [map_add, completionComparisonFun_spec, completionComparisonFun_spec,
      completionComparisonFun_spec, map_add])

theorem completionClosureEmbedding_completionComparison (z : w'.adicCompletion E) :
    completionClosureEmbedding v w (completionComparison σ hσ z) =
      completionClosureEmbedding v w' z :=
  completionComparisonFun_spec σ hσ z

/-- The comparison map is `F_v`-linear. -/
theorem completionComparison_algebraMap (a : v.adicCompletion F) :
    completionComparison σ hσ (algebraMap (v.adicCompletion F) (w'.adicCompletion E) a) =
      algebraMap (v.adicCompletion F) (w.adicCompletion E) a := by
  apply (completionClosureEmbedding v w).injective
  rw [completionClosureEmbedding_completionComparison, completionClosureEmbedding_algebraMap,
    completionClosureEmbedding_algebraMap]

/-- On `E`, the comparison map is `σ`. -/
theorem completionComparison_global (x : E) :
    completionComparison σ hσ (algebraMap E (w'.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (σ x) := by
  apply (completionClosureEmbedding v w).injective
  rw [completionClosureEmbedding_completionComparison]
  exact (hσ x).symm

/-- The comparison map is continuous. -/
theorem continuous_completionComparison : Continuous (completionComparison σ hσ) := by
  let _ : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  have := FiniteExtension.local_finite v w'
  let ψL : w'.adicCompletion E →ₗ[v.adicCompletion F] w.adicCompletion E :=
    { toFun := completionComparison σ hσ
      map_add' := map_add _
      map_smul' := fun a z => by
        simp only [Algebra.smul_def, map_mul, completionComparison_algebraMap,
          RingHom.id_apply] }
  exact ψL.continuous_of_finiteDimensional

include hσ in
/-- `σ` maps the prime of `w'` into the prime of `w`. -/
theorem mapRingEquiv_mem_of_comparison (x : 𝓞 E) (hx : x ∈ w'.asIdeal) :
    RingOfIntegers.mapRingEquiv σ.toRingEquiv x ∈ w.asIdeal := by
  rw [← valuation_lt_one_iff_mem (K := E), ← valuedAdicCompletion_eq_valuation'] at hx ⊢
  change Valued.v (algebraMap E (w'.adicCompletion E) (algebraMap (𝓞 E) E x)) < 1 at hx
  change Valued.v (algebraMap E (w.adicCompletion E) (σ (algebraMap (𝓞 E) E x))) < 1
  rw [valued_lt_one_iff_tendsto w'] at hx
  rw [valued_lt_one_iff_tendsto w]
  have h := ((continuous_completionComparison σ hσ).tendsto 0).comp hx
  rw [map_zero] at h
  refine h.congr fun n => ?_
  simp only [Function.comp_apply, map_pow, completionComparison_global]

include hσ in
/-- `σ` carries the place `w'` to `w`. -/
theorem finitePlaceEquiv_eq_of_comparison : finitePlaceEquiv σ.toRingEquiv w = w' := by
  have hσ' : ∀ x, globalClosureEmbedding v w' (σ.symm x) = globalClosureEmbedding v w x :=
    fun x => by rw [← hσ, σ.apply_symm_apply]
  apply HeightOneSpectrum.ext
  ext x
  rw [finitePlaceEquiv_mem]
  constructor
  · intro hx
    have h := mapRingEquiv_mem_of_comparison (w := w') (w' := w) σ.symm hσ' _ hx
    convert h using 1
    ext
    simp
  · exact mapRingEquiv_mem_of_comparison σ hσ x

end Comparison

section Reciprocity

open LocalFactor.RankOne LocalClassField Weil.Local

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : Langlands.Global.FinitePlace F} {w w' : Langlands.Global.FinitePlace E}
  [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]
  (σ : E ≃ₐ[F] E)
  (hσ : ∀ x, globalClosureEmbedding v w (σ x) = globalClosureEmbedding v w' x)

/-- The comparison map as a homomorphism of `p`-adic fields. -/
def completionComparisonPadic :
    letI := (towerPadicField v w').algebra
    letI := (towerPadicField v w).algebra
    (towerPadicField v w').Carrier →ₐ[Padic (residuePrime v)] (towerPadicField v w).Carrier :=
  letI := (padicField v).algebra
  letI := (towerPadicField v w').algebra
  letI := (towerPadicField v w).algebra
  { toRingHom := completionComparison σ hσ
    commutes' := fun r => by
      have h1 := (completionPadicAlgHom v w').commutes r
      have h2 := (completionPadicAlgHom v w).commutes r
      rw [completionPadicAlgHom_apply] at h1 h2
      change completionComparison σ hσ _ = _
      rw [← h1, ← h2]
      exact completionComparison_algebraMap σ hσ _ }

theorem completionComparisonPadic_apply (z : w'.adicCompletion E) :
    completionComparisonPadic σ hσ z = completionComparison σ hσ z := rfl

theorem completionComparisonPadic_comp :
    letI := (padicField v).algebra
    letI := (towerPadicField v w').algebra
    letI := (towerPadicField v w).algebra
    (completionComparisonPadic σ hσ).comp (completionPadicAlgHom v w') =
      completionPadicAlgHom v w :=
  letI := (padicField v).algebra
  letI := (towerPadicField v w').algebra
  letI := (towerPadicField v w).algebra
  AlgHom.ext fun a => completionComparison_algebraMap σ hσ a

include hσ in
/-- The comparison map is surjective. -/
theorem completionComparison_surjective : Function.Surjective (completionComparison σ hσ) := by
  have hσ' : ∀ x, globalClosureEmbedding v w' (σ.symm x) = globalClosureEmbedding v w x :=
    fun x => by rw [← hσ, σ.apply_symm_apply]
  intro u
  obtain ⟨u', hu'⟩ := exists_completionClosureEmbedding_eq (w := w') (w' := w) σ.symm hσ' u
  refine ⟨u', (completionClosureEmbedding v w).injective ?_⟩
  rw [completionClosureEmbedding_completionComparison, hu']

/-- Along the comparison map, which has degree one, the norm is its inverse. -/
theorem completionComparisonPadic_norm (z : w.adicCompletion E) :
    letI := extensionAlgebra (towerPadicField v w') (towerPadicField v w)
      (completionComparisonPadic σ hσ)
    completionComparisonPadic σ hσ (Algebra.norm (towerPadicField v w').Carrier z) = z := by
  let _ := extensionAlgebra (towerPadicField v w') (towerPadicField v w)
    (completionComparisonPadic σ hσ)
  have hsurj : ∀ z : (towerPadicField v w).Carrier, ∃ c : (towerPadicField v w').Carrier,
      c • (1 : (towerPadicField v w).Carrier) = z := fun z => by
    obtain ⟨c, hc⟩ := completionComparison_surjective σ hσ z
    exact ⟨c, by rw [Algebra.smul_def, mul_one]; exact hc⟩
  have hrank : Module.finrank (towerPadicField v w').Carrier (towerPadicField v w).Carrier = 1 :=
    (finrank_eq_one_iff_of_nonzero' (1 : (towerPadicField v w).Carrier) one_ne_zero).mpr hsurj
  obtain ⟨c, rfl⟩ := completionComparison_surjective σ hσ z
  change completionComparisonPadic σ hσ (Algebra.norm (towerPadicField v w').Carrier
    (algebraMap (towerPadicField v w').Carrier (towerPadicField v w).Carrier c)) = _
  rw [Algebra.norm_algebraMap, hrank, pow_one]
  rfl

/-- The tower correction of the comparison map fixes the image of `E_{w'}`. -/
theorem towerCorrection_completionComparison (z : w'.adicCompletion E) :
    AlgEquiv.toAlgHom (FiniteGaloisTower.towerCorrection (padicField v) (towerPadicField v w')
        (towerPadicField v w) (completionPadicAlgHom v w') (completionComparisonPadic σ hσ))
      (completionClosureEmbedding v w' z) = completionClosureEmbedding v w' z := by
  apply (FiniteGaloisTower.compositeClosureEquiv (padicField v) (towerPadicField v w')
    (towerPadicField v w) (completionPadicAlgHom v w') (completionComparisonPadic σ hσ)).injective
  have hL : extensionClosureEquiv (padicField v) (towerPadicField v w) (completionPadicAlgHom v w)
      (completionClosureEmbedding v w' z) =
        algebraMap (w.adicCompletion E) (AlgebraicClosure (w.adicCompletion E))
          (completionComparison σ hσ z) := by
    rw [← completionClosureEmbedding_completionComparison σ hσ z, extensionClosureEquiv_apply]
    exact extensionClosureLift_fieldEmbedding _ _ _ _
  have hR : FiniteGaloisTower.compositeClosureEquiv (padicField v) (towerPadicField v w')
      (towerPadicField v w) (completionPadicAlgHom v w') (completionComparisonPadic σ hσ)
        (completionClosureEmbedding v w' z) =
        algebraMap (w.adicCompletion E) (AlgebraicClosure (w.adicCompletion E))
          (completionComparison σ hσ z) := by
    change extensionClosureEquiv (towerPadicField v w') (towerPadicField v w)
      (completionComparisonPadic σ hσ) (extensionClosureEquiv (padicField v)
        (towerPadicField v w') (completionPadicAlgHom v w')
          (extensionFieldEmbedding _ _ (completionPadicAlgHom v w') z)) = _
    rw [extensionClosureEquiv_apply _ _ (completionPadicAlgHom v w'),
      extensionClosureLift_fieldEmbedding, extensionClosureEquiv_apply,
      extensionClosureLift_algebraMap]
    rfl
  rw [FiniteGaloisTower.compositeClosureEquiv_towerCorrection, completionComparisonPadic_comp,
    hL, hR]

/-- The restriction of the tower correction to `E_{w'}` is the identity. -/
theorem finiteGaloisRestriction_towerCorrection
    (hGal : @IsGalois (padicField v).Carrier _ (towerPadicField v w').Carrier _
      (extensionAlgebra (padicField v) (towerPadicField v w') (completionPadicAlgHom v w')))
    (z : w'.adicCompletion E) :
    letI := extensionAlgebra (padicField v) (towerPadicField v w') (completionPadicAlgHom v w')
    finiteGaloisRestriction (padicField v) (towerPadicField v w') (completionPadicAlgHom v w') hGal
      (FiniteGaloisTower.towerCorrection (padicField v) (towerPadicField v w')
        (towerPadicField v w) (completionPadicAlgHom v w') (completionComparisonPadic σ hσ)) z =
      z := by
  let _ := extensionAlgebra (padicField v) (towerPadicField v w') (completionPadicAlgHom v w')
  apply (completionClosureEmbedding v w').injective
  exact (finiteGaloisRestriction_apply (padicField v) (towerPadicField v w')
    (completionPadicAlgHom v w') hGal _ z).trans (towerCorrection_completionComparison σ hσ z)

variable [IsGalois F E]

/-- **Reciprocity transport.** If `y ∈ W_{E_w}` and `y' ∈ W_{E_{w'}}` have the same image in
`W_{F_v}`, the comparison map carries the reciprocity value of `y'` to that of `y`. -/
theorem reciprocityUnits_completionComparison
    {e : ReciprocityCandidate (towerPadicField v w)}
    (he : GeometricWeilReciprocityRelation (towerPadicField v w)
      (towerPadicField v w).canonicalTopologicalData e)
    {e' : ReciprocityCandidate (towerPadicField v w')}
    (he' : GeometricWeilReciprocityRelation (towerPadicField v w')
      (towerPadicField v w').canonicalTopologicalData e')
    (y : localWeilGroup (towerPadicField v w)) (y' : localWeilGroup (towerPadicField v w'))
    (hy : completionWeilMap v w y = completionWeilMap v w' y') :
    completionComparison σ hσ (reciprocityUnits (towerPadicField v w') e' y' :
        w'.adicCompletion E) =
      (reciprocityUnits (towerPadicField v w) e y : w.adicCompletion E) := by
  have hGal : @IsGalois (padicField v).Carrier _ (towerPadicField v w').Carrier _
      (extensionAlgebra (padicField v) (towerPadicField v w') (completionPadicAlgHom v w')) :=
    isGalois_adicCompletion v w'
  let κ := FiniteGaloisTower.towerCorrection (padicField v) (towerPadicField v w')
    (towerPadicField v w) (completionPadicAlgHom v w') (completionComparisonPadic σ hσ)
  have hconj : extensionWeilMap (towerPadicField v w') (towerPadicField v w)
      (completionComparisonPadic σ hσ) y =
      finiteGaloisAbsoluteConjugation (padicField v) (towerPadicField v w')
        (completionPadicAlgHom v w') hGal κ y' := by
    apply extensionWeilMap_injective (padicField v) (towerPadicField v w')
      (completionPadicAlgHom v w')
    rw [FiniteGaloisTower.extensionWeilMap_comp, completionComparisonPadic_comp,
      extensionWeilMap_finiteGaloisAbsoluteConjugation]
    exact congrArg _ hy
  have step1 : (reciprocityUnits (towerPadicField v w') e'
      (extensionWeilMap (towerPadicField v w') (towerPadicField v w)
        (completionComparisonPadic σ hσ) y) : w'.adicCompletion E) =
      reciprocityUnits (towerPadicField v w') e' y' := by
    rw [hconj, reciprocityUnits_finiteGaloisAbsoluteConjugation (padicField v)
      (towerPadicField v w') (completionPadicAlgHom v w') hGal e' he' κ y']
    exact finiteGaloisRestriction_towerCorrection σ hσ hGal _
  have step2 := congrArg Units.val (reciprocityUnits_extensionWeilMap (towerPadicField v w')
    (towerPadicField v w) (completionComparisonPadic σ hσ) e' he' e he y)
  rw [← step1]
  change completionComparisonPadic σ hσ _ = _
  rw [step2, Units.coe_map]
  exact completionComparisonPadic_norm σ hσ _

end Reciprocity

section Assembly

open LocalFactor.RankOne LocalClassField

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}
  {v : Langlands.Global.FinitePlace F} {w w' : Langlands.Global.FinitePlace E}
  [w.asIdeal.LiesOver v.asIdeal] [w'.asIdeal.LiesOver v.asIdeal]

/-- Conjugation of a local map by an element of `W_{E/F}`. -/
def conjugateLocalMap (s : RelativeWeilGroup c F E)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E) :
    Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E where
  toMonoidHom := (MulAut.conj s).toMonoidHom.comp ι.toMonoidHom
  continuous_toFun := by
    obtain ⟨f, hf⟩ : ∃ f : Weil.Local.localWeilGroup (padicField v) → RelativeWeilGroup c F E,
        f = fun g => ι g := ⟨_, rfl⟩
    have hι : Continuous f := by
      rw [hf]
      exact ι.continuous
    change Continuous (fun g => s * ι g * s⁻¹)
    rw [show (fun g => s * ι g * s⁻¹) = fun g => s * f g * s⁻¹ by rw [hf]]
    revert hι
    rw [show krullTopology F E = relativeGaloisTopology F E from DiscreteTopology.eq_bot]
    intro hι
    let _ := relativeGaloisTopology F E
    exact (continuous_const.mul hι).mul continuous_const

theorem conjugateLocalMap_apply (s : RelativeWeilGroup c F E)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (g : Weil.Local.localWeilGroup (padicField v)) :
    conjugateLocalMap s ι g = s * ι g * s⁻¹ := rfl

omit [IsGalois F E] [w.asIdeal.LiesOver v.asIdeal] in
/-- The image of `W_{E_{w'}}` fixes the image of `E_{w'}`. -/
theorem completionWeilMap_fixes (y' : Weil.Local.localWeilGroup (towerPadicField v w'))
    (z : w'.adicCompletion E) :
    AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField v) (completionWeilMap v w' y'))
      (completionClosureEmbedding v w' z) = completionClosureEmbedding v w' z := by
  have hmem : Weil.Local.extensionGaloisMap (padicField v) (towerPadicField v w')
      (completionPadicAlgHom v w') (Weil.Local.localProjection _ y') ∈
      (Weil.Local.extensionIntermediateField (padicField v) (towerPadicField v w')
        (completionPadicAlgHom v w')).fixingSubgroup := by
    rw [← Weil.Local.extensionGaloisMap_range]
    exact ⟨Weil.Local.localProjection _ y', rfl⟩
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hmem _
    ((Weil.Local.mem_extensionIntermediateField _ _ _ _).2 ⟨z, rfl⟩)

/-- Conjugating a local map at `(w, e)` by a lift of `σ⁻¹` gives a local map at `(w', e')`. -/
theorem isLocalRelativeWeilMap_conjugate
    {e : ReciprocityCandidate (towerPadicField v w)}
    {e' : ReciprocityCandidate (towerPadicField v w')}
    {ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap v w e ι)
    (he' : GeometricWeilReciprocityRelation (towerPadicField v w')
      (towerPadicField v w').canonicalTopologicalData e')
    (σ : E ≃ₐ[F] E)
    (hσ : ∀ x, globalClosureEmbedding v w (σ x) = globalClosureEmbedding v w' x)
    (s : RelativeWeilGroup c F E) (hs : projection c F E s = σ⁻¹) :
    IsLocalRelativeWeilMap v w' e' (conjugateLocalMap s ι) := by
  refine ⟨he', fun g x => ?_, fun y' => ?_⟩
  · have hp : projection c F E (conjugateLocalMap s ι g) =
        σ⁻¹ * projection c F E (ι g) * σ := by
      rw [conjugateLocalMap_apply, map_mul, map_mul, map_inv, hs, inv_inv]
    rw [hp]
    change globalClosureEmbedding v w' ((σ⁻¹ * projection c F E (ι g) * σ) x) =
      AlgEquiv.toAlgHom (Weil.Local.localProjection (padicField v) g)
        (globalClosureEmbedding v w' x)
    rw [← hσ, ← hσ]
    have h1 : σ ((σ⁻¹ * projection c F E (ι g) * σ) x) = projection c F E (ι g) (σ x) := by
      simp only [AlgEquiv.mul_apply]
      exact σ.apply_symm_apply _
    rw [h1]
    exact hι.2.1 g (σ x)
  · -- The element lies in the image of `W_{E_w}`.
    obtain ⟨y, hy⟩ : completionWeilMap v w' y' ∈ (completionWeilMap v w).toMonoidHom.range := by
      apply mem_range_completionWeilMap_of_fixes v w
      intro x
      have hx : completionClosureEmbedding v w (algebraMap E (w.adicCompletion E) x) =
          completionClosureEmbedding v w' (algebraMap E (w'.adicCompletion E) (σ.symm x)) := by
        have := hσ (σ.symm x)
        rw [σ.apply_symm_apply] at this
        exact this
      rw [hx]
      exact completionWeilMap_fixes y' _
    have hy' : completionWeilMap v w y = completionWeilMap v w' y' := hy
    -- Transport of the idele class.
    have hrec := reciprocityUnits_completionComparison σ hσ hι.1 he' y y' hy'
    have hidele := ideleClassEquiv_ofAdicCompletion_of_eq σ.toRingEquiv w w'
      (finitePlaceEquiv_eq_of_comparison σ hσ) (completionComparison σ hσ)
      (continuous_completionComparison σ hσ) (completionComparison_global σ hσ)
      (reciprocityUnits (towerPadicField v w') e' y')
    have hunit : Units.map (completionComparison σ hσ).toMonoidHom
        (reciprocityUnits (towerPadicField v w') e' y') =
        reciprocityUnits (towerPadicField v w) e y := Units.ext hrec
    rw [hunit] at hidele
    have hinv : ∀ X, ideleClassEquiv (σ⁻¹).toRingEquiv (ideleClassEquiv σ.toRingEquiv X) = X :=
      fun X => by
        change relativeIdeleClassAut F E σ⁻¹ (relativeIdeleClassAut F E σ X) = X
        rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
    rw [conjugateLocalMap_apply, ← hy', hι.2.2 y, ← hidele]
    rw [show ∀ a : RelativeWeilGroup c F E, s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ from
      fun a => by group, conjugation, hs, hinv]

/-- **Conjugacy at different places.** Two local-to-relative Weil maps at places `w`, `w'`
above `v`, for geometric reciprocity candidates of `E_w` and `E_{w'}`, are conjugate in
`W_{E/F}`. -/
theorem exists_conj_of_isLocalRelativeWeilMap
    {e : ReciprocityCandidate (towerPadicField v w)}
    {e' : ReciprocityCandidate (towerPadicField v w')}
    {ι ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap v w e ι) (hι' : IsLocalRelativeWeilMap v w' e' ι') :
    ∃ t : RelativeWeilGroup c F E, ∀ g, ι' g = t * ι g * t⁻¹ := by
  obtain ⟨σ, hσ⟩ := exists_algEquiv_comp_eq_of_normal (globalClosureEmbedding v w)
    (globalClosureEmbedding v w')
  obtain ⟨s, hs⟩ := projection_surjective c F E σ⁻¹
  obtain ⟨b, hb⟩ := localRelativeWeilMapConjugacy F E c v w' e' (conjugateLocalMap s ι) ι'
    (isLocalRelativeWeilMap_conjugate hι hι'.1 σ hσ s hs) hι'
  refine ⟨inclusion c F E b * s, fun g => ?_⟩
  rw [hb g, conjugateLocalMap_apply]
  group

end Assembly

end RelativeWeilGroup

end Langlands.ClassFieldTheory.Global
