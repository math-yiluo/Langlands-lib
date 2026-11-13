import Langlands.LocalFactor.BrauerKernel.RealizationPlace
import Langlands.LocalFactor.BrauerKernel.GaloisType
import Langlands.ClassField.Global.CompletionTower

/-! # Generator fields at the distinguished place of a global realization -/

noncomputable section

set_option autoImplicit false

universe uF

namespace Langlands.LocalFactor.NonabelianBrauer

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum _root_.Topology CommonClosure
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

section Galois

variable {k K' F K : Type*} [Field k] [Field K'] [Field F] [Field K] [Algebra k K'] [Algebra F K]
  (θ : (K' ≃ₐ[k] K') ≃* (K ≃ₐ[F] K)) (j : K' →+* K) (hθ : ∀ σ x, θ σ (j x) = j (σ x))
  (H : Subgroup (K ≃ₐ[F] K))

include hθ in
/-- An embedding compatible with a Galois comparison `θ` sends the fixed field of `θ⁻¹ H` into
the fixed field of `H`. -/
theorem map_mem_fixedField_comap {x : K'}
    (hx : x ∈ IntermediateField.fixedField (H.comap θ.toMonoidHom)) :
    j x ∈ IntermediateField.fixedField H := by
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro τ hτ
  obtain ⟨σ, rfl⟩ := θ.surjective τ
  rw [hθ, hx σ hτ]

include hθ in
/-- An intermediate field `M` of the finite Galois extension `K / F` containing the image of the
fixed field of `θ⁻¹ H` contains the fixed field of `H`. -/
theorem fixedField_le_of_map_mem [FiniteDimensional k K'] [FiniteDimensional F K] [IsGalois F K]
    (M : IntermediateField F K)
    (hM : ∀ x ∈ IntermediateField.fixedField (H.comap θ.toMonoidHom), j x ∈ M) :
    IntermediateField.fixedField H ≤ M := by
  have hle : M.fixingSubgroup ≤ H := by
    intro τ hτ
    obtain ⟨σ, rfl⟩ := θ.surjective τ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hτ
    have hσ : σ ∈ (IntermediateField.fixedField (H.comap θ.toMonoidHom)).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      apply j.injective
      rw [← hθ]
      exact hτ _ (hM x hx)
    rw [IntermediateField.fixingSubgroup_fixedField] at hσ
    exact hσ
  calc IntermediateField.fixedField H ≤ IntermediateField.fixedField M.fixingSubgroup :=
        IntermediateField.fixedField_antitone hle
    _ = M := IsGalois.fixedField_fixingSubgroup M

end Galois

section GaloisImage

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (K : Extension F)
  [Normal F.Carrier K.field]

/-- For `L ⊆ K`, the Galois image of `W_L` in `Gal(K/F)` is the subgroup fixing `L`. -/
theorem mem_galoisImage_iff (L : Extension F) (hL : L.field ≤ K.field)
    (σ : K.field ≃ₐ[F.Carrier] K.field) :
    σ ∈ galoisImage F K L ↔
      ∀ x : K.field, (x : AlgebraicClosure F.Carrier) ∈ L.field → σ x = x := by
  obtain ⟨w, rfl⟩ := galoisRestriction_surjective F K σ
  rw [galoisRestriction_mem_galoisImage_iff F K L hL]
  change Weil.Local.localProjection F w ∈ IntermediateField.fixingSubgroup L.field ↔ _
  refine (IntermediateField.mem_fixingSubgroup_iff (K := L.field) _).trans ?_
  constructor
  · intro h x hx
    apply Subtype.ext
    rw [galoisRestriction_apply]
    exact h _ hx
  · intro h x hx
    have h1 := congrArg Subtype.val (h ⟨x, hL hx⟩ hx)
    rw [galoisRestriction_apply] at h1
    exact h1

/-- For `L ⊆ K`, the fixed field of the Galois image of `W_L` is `L`. -/
theorem fixedField_galoisImage (L : Extension F) (hL : L.field ≤ K.field) :
    IntermediateField.fixedField (galoisImage F K L) = IntermediateField.restrict hL := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier K.field := ⟨⟩
  have h : galoisImage F K L = (IntermediateField.restrict hL).fixingSubgroup := by
    ext σ
    rw [mem_galoisImage_iff F K L hL, IntermediateField.mem_fixingSubgroup_iff]
    exact ⟨fun h x hx => h x ((IntermediateField.mem_restrict hL x).mp hx),
      fun h x hx => h x ((IntermediateField.mem_restrict hL x).mpr hx)⟩
  rw [h, IsGalois.fixedField_fixingSubgroup]

end GaloisImage

section Realization

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (K : Extension F)

/-- The canonical topology of a finite intermediate field of the common closure is Hausdorff. -/
theorem realizationField_t2Space :
    @T2Space K.field (K.asPadicField (p := p)).canonicalTopology := by
  have h := (K.asPadicField (p := p)).canonicalTopologicalData.fieldT2
  rwa [PadicField.canonicalTopologicalData_topology] at h

/-- `F`-algebra maps between finite intermediate fields of the common closure are continuous
for the canonical topologies. -/
theorem continuous_algHom_field (L : Extension F) (τ : K.field →ₐ[F.Carrier] L.field) :
    @Continuous _ _ (K.asPadicField (p := p)).canonicalTopology
      (L.asPadicField (p := p)).canonicalTopology τ := by
  let : Algebra (Padic p) K.field := (K.asPadicField (p := p)).algebra
  let : Algebra (Padic p) L.field := (L.asPadicField (p := p)).algebra
  let : Module (Padic p) K.field := Algebra.toModule
  let : Module (Padic p) L.field := Algebra.toModule
  let : TopologicalSpace K.field := (K.asPadicField (p := p)).canonicalTopology
  let : TopologicalSpace L.field := (L.asPadicField (p := p)).canonicalTopology
  have : IsModuleTopology (Padic p) K.field := ⟨rfl⟩
  have : IsModuleTopology (Padic p) L.field := ⟨rfl⟩
  let g : K.field →ₗ[Padic p] L.field :=
    { toFun := τ
      map_add' := map_add τ
      map_smul' := fun c x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact τ.commutes (algebraMap (Padic p) F.Carrier c) }
  have : ContinuousAdd L.field := IsModuleTopology.toContinuousAdd (Padic p) L.field
  exact IsModuleTopology.continuous_of_linearMap g

/-- The structure map `F → K` is continuous for the canonical topologies. -/
theorem continuous_algebraMap_field :
    @Continuous _ _ F.canonicalTopology (K.asPadicField (p := p)).canonicalTopology
      (algebraMap F.Carrier K.field) := by
  let : Algebra (Padic p) K.field := (K.asPadicField (p := p)).algebra
  let : Module (Padic p) K.field := Algebra.toModule
  let : TopologicalSpace K.field := (K.asPadicField (p := p)).canonicalTopology
  let : TopologicalSpace F.Carrier := F.canonicalTopology
  have : IsModuleTopology (Padic p) K.field := ⟨rfl⟩
  have : IsModuleTopology (Padic p) F.Carrier := ⟨rfl⟩
  let g : F.Carrier →ₗ[Padic p] K.field :=
    { toFun := algebraMap F.Carrier K.field
      map_add' := map_add _
      map_smul' := fun c x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have : ContinuousAdd K.field := IsModuleTopology.toContinuousAdd (Padic p) K.field
  exact IsModuleTopology.continuous_of_linearMap g

end Realization

section Place

open Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (K : Extension F)

/-- On the completion of `k` at `v`, a global realization `ψ` restricts to `φ`: both sides are
continuous and agree on the dense image of `k`. -/
theorem realization_completionMap (v : HeightOneSpectrum (𝓞 k))
    (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
    (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
    (hφ : @Continuous _ _ _ F.canonicalTopology φ)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := p)).canonicalTopology ψ)
    (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
      algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
    (x : v.adicCompletion k) :
    ψ (completionMap v w x) = algebraMap F.Carrier K.field (φ x) := by
  let := F.canonicalTopology
  let := (K.asPadicField (p := p)).canonicalTopology
  have := realizationField_t2Space K
  have h1 : Continuous fun x => ψ (completionMap v w x) :=
    hψ.comp (continuous_completionMap v w)
  have h2 : Continuous fun x => algebraMap F.Carrier K.field (φ x) :=
    (continuous_algebraMap_field K).comp hφ
  have heq := (denseRange_algebraMap (K := k) (v := v)).equalizer h1 h2 (funext fun x => by
    simp only [Function.comp_apply, completionMap_coe]
    exact hcomp x)
  exact congrFun heq x

/-- An `F`-automorphism of `K` fixing the realization of a subfield `𝕃 ⊆ K'` fixes the
realization of its completion, by continuity and density. -/
theorem realization_fixes_completion {𝕃 : Type} [Field 𝕃] [NumberField 𝕃] [Algebra 𝕃 K']
    (u : HeightOneSpectrum (𝓞 𝕃)) (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver u.asIdeal]
    (ψ : w.adicCompletion K' ≃+* K.field)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := p)).canonicalTopology ψ)
    (τ : K.field ≃ₐ[F.Carrier] K.field)
    (hτ : ∀ y : 𝕃, τ (ψ (algebraMap K' (w.adicCompletion K') (algebraMap 𝕃 K' y))) =
      ψ (algebraMap K' (w.adicCompletion K') (algebraMap 𝕃 K' y)))
    (y : u.adicCompletion 𝕃) :
    τ (ψ (completionMap u w y)) = ψ (completionMap u w y) := by
  let := (K.asPadicField (p := p)).canonicalTopology
  have := realizationField_t2Space K
  have h0 : Continuous fun y => ψ (completionMap u w y) :=
    hψ.comp (continuous_completionMap u w)
  have h1 : Continuous fun y => τ (ψ (completionMap u w y)) :=
    (continuous_algHom_field K K τ.toAlgHom).comp h0
  have heq := (denseRange_algebraMap (K := 𝕃) (v := u)).equalizer h1 h0 (funext fun y => by
    simp only [Function.comp_apply, completionMap_coe]
    exact hτ y)
  exact congrFun heq y

end Place

section GeneratorField

open Langlands.Global.AdelicFunctoriality.FiniteExtension

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (K : Extension F) [Normal F.Carrier K.field]
  (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))

/-- The fixed field in `K'` of the subgroup corresponding under `θ` to the Galois image of `L`. -/
abbrev realizationSubfield (L : Extension F) : IntermediateField k K' :=
  IntermediateField.fixedField ((galoisImage F K L).comap θ.toMonoidHom)

/-- A realization `ψ` compatible with `θ` sends the completion of the fixed field of
`θ⁻¹ (Gal(K/L))` into `L`. -/
theorem realization_completion_mem (w : HeightOneSpectrum (𝓞 K'))
    (ψ : w.adicCompletion K' ≃+* K.field)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := p)).canonicalTopology ψ)
    (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
      ψ (algebraMap K' (w.adicCompletion K') (σ x)))
    (L : Extension F) (hL : L.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
    (y : u.adicCompletion (realizationSubfield K θ L)) :
    ((ψ (completionMap u w y) : K.field) : AlgebraicClosure F.Carrier) ∈ L.field := by
  have h : ψ (completionMap u w y) ∈ IntermediateField.fixedField (galoisImage F K L) := by
    rw [IntermediateField.mem_fixedField_iff]
    intro τ hτ
    refine realization_fixes_completion K u w ψ hψ τ (fun x => ?_) y
    have hx := map_mem_fixedField_comap θ
      ((ψ : w.adicCompletion K' →+* K.field).comp (algebraMap K' (w.adicCompletion K')))
      (fun σ x => hθ σ x) (galoisImage F K L) x.2
    rw [IntermediateField.mem_fixedField_iff] at hx
    exact hx τ hτ
  rw [fixedField_galoisImage F K L hL] at h
  exact (IntermediateField.mem_restrict hL _).mp h

/-- The realization of the completion of the fixed field of `θ⁻¹ (Gal(K/L))`, as a ring
homomorphism into `L`. -/
def realizationCompletionHom (w : HeightOneSpectrum (𝓞 K'))
    (ψ : w.adicCompletion K' ≃+* K.field)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := p)).canonicalTopology ψ)
    (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
      ψ (algebraMap K' (w.adicCompletion K') (σ x)))
    (L : Extension F) (hL : L.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal] :
    u.adicCompletion (realizationSubfield K θ L) →+* L.field :=
  RingHom.codRestrict (((K.field.val : K.field →ₐ[F.Carrier] AlgebraicClosure F.Carrier) :
      K.field →+* AlgebraicClosure F.Carrier).comp
    ((ψ : w.adicCompletion K' →+* K.field).comp (completionMap u w))) L.field
    (realization_completion_mem K θ w ψ hψ hθ L hL u)

theorem realizationCompletionHom_apply (w : HeightOneSpectrum (𝓞 K'))
    (ψ : w.adicCompletion K' ≃+* K.field)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := p)).canonicalTopology ψ)
    (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
      ψ (algebraMap K' (w.adicCompletion K') (σ x)))
    (L : Extension F) (hL : L.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
    (y : u.adicCompletion (realizationSubfield K θ L)) :
    ((realizationCompletionHom K θ w ψ hψ hθ L hL u y : L.field) :
        AlgebraicClosure F.Carrier) =
      ((ψ (completionMap u w y) : K.field) : AlgebraicClosure F.Carrier) :=
  rfl

/-- The realization of the completion of the fixed field of `θ⁻¹ (Gal(K/L))` is all of `L`:
its image is an intermediate field of `K / F` (it contains `F` because `ψ` restricts to `φ`)
containing the realization of the fixed field, hence the fixed field of the Galois image. -/
theorem realizationCompletionHom_surjective (v : HeightOneSpectrum (𝓞 k))
    (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
    (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
    (hφ : @Continuous _ _ _ F.canonicalTopology φ)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := p)).canonicalTopology ψ)
    (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
      algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
    (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
      ψ (algebraMap K' (w.adicCompletion K') (σ x)))
    (L : Extension F) (hL : L.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] :
    Function.Surjective (realizationCompletionHom K θ w ψ hψ hθ L hL u) := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  have : IsGalois F.Carrier K.field := ⟨⟩
  let f : u.adicCompletion (realizationSubfield K θ L) →+* K.field :=
    (ψ : w.adicCompletion K' →+* K.field).comp (completionMap u w)
  let M : IntermediateField F.Carrier K.field :=
    f.fieldRange.toIntermediateField (fun a => RingHom.mem_fieldRange.mpr
      ⟨completionMap v u (φ.symm a), by
        change ψ (completionMap u w (completionMap v u (φ.symm a))) = _
        rw [← RingHom.comp_apply (completionMap u w),
          ClassField.Global.CompletionTower.completionMap_comp v u w,
          realization_completionMap K v w φ ψ hφ hψ hcomp, RingEquiv.apply_symm_apply]⟩)
  have hle : IntermediateField.fixedField (galoisImage F K L) ≤ M := by
    refine fixedField_le_of_map_mem θ
      ((ψ : w.adicCompletion K' →+* K.field).comp (algebraMap K' (w.adicCompletion K')))
      (fun σ x => hθ σ x) (galoisImage F K L) M ?_
    intro x hx
    refine RingHom.mem_fieldRange.mpr
      ⟨algebraMap (realizationSubfield K θ L) (u.adicCompletion (realizationSubfield K θ L))
        ⟨x, hx⟩, ?_⟩
    change ψ (completionMap u w (algebraMap _ _ _)) = _
    rw [completionMap_coe]
    rfl
  rw [fixedField_galoisImage F K L hL] at hle
  intro z
  obtain ⟨y, hy⟩ := RingHom.mem_fieldRange.mp
    (hle ((IntermediateField.mem_restrict hL ⟨z, hL z.2⟩).mpr z.2))
  refine ⟨y, Subtype.ext ?_⟩
  have h2 : ((f y : K.field) : AlgebraicClosure F.Carrier) = z :=
    congrArg (fun t : K.field => (t : AlgebraicClosure F.Carrier)) hy
  exact h2

end GeneratorField

section GeneratorEquiv

open Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- The structure map `ℚ_p → F` is continuous for the canonical topology. -/
theorem continuous_algebraMap_padicField {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    @Continuous _ _ _ F.canonicalTopology (algebraMap (Padic p) F.Carrier) := by
  let := F.canonicalTopology
  have : IsModuleTopology (Padic p) F.Carrier := ⟨rfl⟩
  have : ContinuousAdd F.Carrier := IsModuleTopology.toContinuousAdd (Padic p) F.Carrier
  exact IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (Padic p) F.Carrier)

/-- The canonical topology of a p-adic field is Hausdorff. -/
theorem padicField_t2Space {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    @T2Space F.Carrier F.canonicalTopology := by
  have h := F.canonicalTopologicalData.fieldT2
  rwa [PadicField.canonicalTopologicalData_topology] at h

variable {k K' : Type} [Field k] [Field K'] [NumberField k] [NumberField K'] [Algebra k K']
  (v : HeightOneSpectrum (𝓞 k)) {F : PadicField.{uF} (residuePrime v)} (K : Extension F)
  [Normal F.Carrier K.field] (θ : (K' ≃ₐ[k] K') ≃* (K.field ≃ₐ[F.Carrier] K.field))

/-- A continuous isomorphism `φ : k_v ≃ F` fixes `ℚ_p`. -/
theorem realization_padicMap (φ : v.adicCompletion k ≃+* F.Carrier)
    (hφ : @Continuous _ _ _ F.canonicalTopology φ) (a : Padic (residuePrime v)) :
    φ (padicMap v a) = algebraMap (Padic (residuePrime v)) F.Carrier a := by
  let := (padicField v).algebra
  let := F.canonicalTopology
  have := padicField_t2Space F
  exact ringHom_algebraMap_of_continuous (A := v.adicCompletion k) (continuous_padicMap v)
    (continuous_algebraMap_padicField F) (φ : v.adicCompletion k →+* F.Carrier) hφ a

/-- The embedding `F ≅ k_v → 𝕃_u` of `ℚ_p`-algebras, for a place `u` of `𝕃 / k` above `v`. -/
def realizationBaseAlgHom {𝕃 : Type} [Field 𝕃] [NumberField 𝕃] [Algebra k 𝕃]
    (u : HeightOneSpectrum (𝓞 𝕃)) [u.asIdeal.LiesOver v.asIdeal]
    (φ : v.adicCompletion k ≃+* F.Carrier)
    (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm) :
    letI := (towerPadicField v u).algebra
    F.Carrier →ₐ[Padic (residuePrime v)] (towerPadicField v u).Carrier :=
  letI := (padicField v).algebra
  letI := F.canonicalTopology
  letI := (towerPadicField v u).algebra
  (ClassField.Global.RelativeWeilGroup.completionPadicAlgHom v u).comp
    (algHomOfContinuous (A := F.Carrier) (B := v.adicCompletion k)
      (continuous_algebraMap_padicField F) (continuous_padicMap v)
      (φ.symm : F.Carrier →+* v.adicCompletion k) hφ')

theorem realizationBaseAlgHom_apply {𝕃 : Type} [Field 𝕃] [NumberField 𝕃] [Algebra k 𝕃]
    (u : HeightOneSpectrum (𝓞 𝕃)) [u.asIdeal.LiesOver v.asIdeal]
    (φ : v.adicCompletion k ≃+* F.Carrier)
    (hφ' : @Continuous _ _ F.canonicalTopology _ φ.symm) (a : F.Carrier) :
    realizationBaseAlgHom v u φ hφ' a = completionMap v u (φ.symm a) :=
  rfl

/-- **The generator-field isomorphism.** The realization `ψ` restricted to the completion of
the fixed field of `θ⁻¹ (Gal(K/L))` is an isomorphism of `ℚ_p`-algebras onto `L`. -/
def realizationGeneratorEquiv (w : HeightOneSpectrum (𝓞 K')) [w.asIdeal.LiesOver v.asIdeal]
    (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
    (hφ : @Continuous _ _ _ F.canonicalTopology φ)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := residuePrime v)).canonicalTopology ψ)
    (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
      algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
    (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
      ψ (algebraMap K' (w.adicCompletion K') (σ x)))
    (L : Extension F) (hL : L.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] :
    letI := (towerPadicField v u).algebra
    letI : Algebra (Padic (residuePrime v)) L.field :=
      (L.asPadicField (p := residuePrime v)).algebra
    (towerPadicField v u).Carrier ≃ₐ[Padic (residuePrime v)]
      (L.asPadicField (p := residuePrime v)).Carrier :=
  letI := (towerPadicField v u).algebra
  letI : Algebra (Padic (residuePrime v)) L.field :=
    (L.asPadicField (p := residuePrime v)).algebra
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective
      (realizationCompletionHom K θ w ψ hψ hθ L hL u)
      ⟨(realizationCompletionHom K θ w ψ hψ hθ L hL u).injective,
        realizationCompletionHom_surjective K θ v w φ ψ hφ hψ hcomp hθ L hL u⟩)
    (fun a => by
      apply Subtype.ext
      change ((ψ (completionMap u w (padicMapAt u (residuePrime_eq v u) a)) : K.field) :
        AlgebraicClosure F.Carrier) = _
      rw [← completionMap_comp_padicMap v u, RingHom.comp_apply,
        ← RingHom.comp_apply (completionMap u w),
        ClassField.Global.CompletionTower.completionMap_comp v u w,
        realization_completionMap K v w φ ψ hφ hψ hcomp, realization_padicMap v φ hφ a]
      rfl)

theorem realizationGeneratorEquiv_apply (w : HeightOneSpectrum (𝓞 K'))
    [w.asIdeal.LiesOver v.asIdeal]
    (φ : v.adicCompletion k ≃+* F.Carrier) (ψ : w.adicCompletion K' ≃+* K.field)
    (hφ : @Continuous _ _ _ F.canonicalTopology φ)
    (hψ : @Continuous _ _ _ (K.asPadicField (p := residuePrime v)).canonicalTopology ψ)
    (hcomp : ∀ x : k, ψ (algebraMap K' (w.adicCompletion K') (algebraMap k K' x)) =
      algebraMap F.Carrier K.field (φ (algebraMap k (v.adicCompletion k) x)))
    (hθ : ∀ σ x, θ σ (ψ (algebraMap K' (w.adicCompletion K') x)) =
      ψ (algebraMap K' (w.adicCompletion K') (σ x)))
    (L : Extension F) (hL : L.field ≤ K.field)
    (u : HeightOneSpectrum (𝓞 (realizationSubfield K θ L))) [w.asIdeal.LiesOver u.asIdeal]
    [u.asIdeal.LiesOver v.asIdeal] (y : u.adicCompletion (realizationSubfield K θ L)) :
    ((realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u y : L.field) :
        AlgebraicClosure F.Carrier) =
      ((ψ (completionMap u w y) : K.field) : AlgebraicClosure F.Carrier) :=
  rfl

/-- The generator-field isomorphism lies over `F`: composed with the base embedding
`realizationBaseAlgHom`, it is the inclusion of `F` in the common closure. -/
theorem realizationGeneratorEquiv_base (w : HeightOneSpectrum (𝓞 K'))
    [w.asIdeal.LiesOver v.asIdeal]
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
    [u.asIdeal.LiesOver v.asIdeal] (a : F.Carrier) :
    ((realizationGeneratorEquiv v K θ w φ ψ hφ hψ hcomp hθ L hL u
        (realizationBaseAlgHom v u φ hφ' a) : L.field) : AlgebraicClosure F.Carrier) =
      algebraMap F.Carrier (AlgebraicClosure F.Carrier) a := by
  rw [realizationGeneratorEquiv_apply, realizationBaseAlgHom_apply,
    ← RingHom.comp_apply (completionMap u w),
    ClassField.Global.CompletionTower.completionMap_comp v u w,
    realization_completionMap K v w φ ψ hφ hψ hcomp, RingEquiv.apply_symm_apply]
  rfl

end GeneratorEquiv

end Langlands.LocalFactor.NonabelianBrauer
