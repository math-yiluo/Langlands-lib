import Langlands.Global.Arithmetic.GaloisModelRealization
import Langlands.Global.Arithmetic.HarrisSetup

/-!
# Places and completions of a tower of number fields from dense local embeddings

Dense embeddings `E → F₀`, `E' → F₁`, `L → F₂` of a tower of number fields into a tower of
finite extensions of `ℚ_[p]`, compatible along both towers, determine primes `v | v' | ṽ`,
completion isomorphisms continuous in both directions for the module topologies, and the
commuting completion diagrams. A Galois comparison `Gal(L / E) ≃* Gal(F₂ / F₀)` compatible with
the embeddings makes `ṽ` the unique prime of `L` above `v`, matches the degrees, and makes `L` a
normal closure of `E' / E` when `F₂` is one of `F₁ / F₀`. The last section specializes this to
Harris's `PlaceDatum` for a `p`-adic field `F`, an extension `F'` and `F̃ = galoisClosure F F'`
with the canonical topologies; the conjugation and distinctness lemmas transport places along
field automorphisms and separate places cut out by different embeddings.
-/

namespace Langlands.Global.FieldRealization

open IntermediateField NumberField IsDedekindDomain AdelicFunctoriality

section Normed

variable {K : Type*} [Field K] [NumberField K]
  {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]

/-- The completion of `K` at the prime of a dense embedding `j : K →+* F` is identified with
`F`, continuously in both directions and extending `j`. -/
theorem exists_densePrime_completion (j : K →+* F) (hj : DenseRange j) :
    ∃ φ : (densePrime j hj).adicCompletion K ≃+* F,
      Continuous φ ∧ Continuous φ.symm ∧ ∀ x : K, φ (algebraMap K _ x) = j x := by
  obtain ⟨v, φ, hv, hφ, hφs, hφK⟩ := exists_adicCompletion_ringEquiv j hj
  obtain rfl : v = densePrime j hj := HeightOneSpectrum.ext (Ideal.ext hv)
  exact ⟨φ, hφ, hφs, hφK⟩

/-- The completion of `K` at a prime `v` cut out by a dense embedding `j : K →+* F` is identified
with `F`, continuously in both directions and extending `j`. -/
theorem exists_completion_of_mem_iff (j : K →+* F) (hj : DenseRange j)
    (v : HeightOneSpectrum (𝓞 K)) (hv : ∀ a : 𝓞 K, a ∈ v.asIdeal ↔ ‖j a‖ < 1) :
    ∃ φ : v.adicCompletion K ≃+* F,
      Continuous φ ∧ Continuous φ.symm ∧ ∀ x : K, φ (algebraMap K _ x) = j x := by
  obtain ⟨v₀, φ, hv₀, hφ, hφs, hφK⟩ := exists_adicCompletion_ringEquiv j hj
  obtain rfl : v₀ = v := HeightOneSpectrum.ext (Ideal.ext fun a => (hv₀ a).trans (hv a).symm)
  exact ⟨φ, hφ, hφs, hφK⟩

omit [CompleteSpace F] in
/-- Compatible dense embeddings along norm-preserving algebra maps give primes lying over each
other. -/
theorem liesOver_densePrime {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {F' : Type*} [NontriviallyNormedField F'] [IsUltrametricDist F'] [Algebra F F']
    (j : K →+* F) (hj : DenseRange j) (j' : L →+* F') (hj' : DenseRange j')
    (hnorm : ∀ x : F, ‖algebraMap F F' x‖ = ‖x‖)
    (hcomp : ∀ x : K, j' (algebraMap K L x) = algebraMap F F' (j x)) :
    (densePrime j' hj').asIdeal.LiesOver (densePrime j hj).asIdeal :=
  ⟨Ideal.ext fun a => by
    rw [Ideal.mem_under, mem_densePrime, mem_densePrime]
    change _ ↔ ‖j' (algebraMap K L a)‖ < 1
    rw [hcomp, hnorm]⟩

end Normed

/-- Two continuous maps out of the completion of `K` at `v` agreeing on `K` coincide; this
gives the commuting completion diagram of compatible completion isomorphisms. -/
theorem completionMap_comm {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] {A B : Type*} [Field A] [Field B] [TopologicalSpace A]
    [TopologicalSpace B] [T2Space B] [Algebra A B] (hAB : Continuous (algebraMap A B))
    (j : K →+* A) (j' : L →+* B) (hcomp : ∀ x : K, j' (algebraMap K L x) = algebraMap A B (j x))
    (φ : v.adicCompletion K ≃+* A) (φ' : w.adicCompletion L ≃+* B) (hφ : Continuous φ)
    (hφ' : Continuous φ') (hφK : ∀ x : K, φ (algebraMap K _ x) = j x)
    (hφL : ∀ y : L, φ' (algebraMap L _ y) = j' y) (x : v.adicCompletion K) :
    φ' (FiniteExtension.completionMap v w x) = algebraMap A B (φ x) := by
  have h := (HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    (hφ'.comp (FiniteExtension.continuous_completionMap v w)) (hAB.comp hφ)
    (funext fun x => by
      simp only [Function.comp_apply, FiniteExtension.completionMap_coe, hφK, hφL, hcomp])
  exact congrFun h x

/-- Two completion isomorphisms at the same prime agree on elements sent into the image of
`ℚ_[p]`: their quotient is a continuous automorphism, hence fixes `ℚ_[p]`. -/
theorem eq_of_completion_eq (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) {A : Type*} [Field A] [TopologicalSpace A] [T2Space A]
    [Algebra ℚ_[p] A] [ContinuousSMul ℚ_[p] A] (j₁ j₂ : K →+* A)
    (φ₁ φ₂ : v.adicCompletion K ≃+* A) (hφ₁ : Continuous φ₁.symm) (hφ₂ : Continuous φ₂)
    (h₁ : ∀ x : K, φ₁ (algebraMap K _ x) = j₁ x) (h₂ : ∀ x : K, φ₂ (algebraMap K _ x) = j₂ x)
    {x : K} {r : ℚ_[p]} (hx : j₁ x = algebraMap ℚ_[p] A r) : j₂ x = j₁ x := by
  let ψ : A ≃+* A := φ₁.symm.trans φ₂
  have hψ : Continuous ψ := hφ₂.comp hφ₁
  have hQ : (ψ : A → A) ∘ algebraMap ℚ_[p] A = algebraMap ℚ_[p] A :=
    (Padic.denseRange_ratCast p).equalizer (hψ.comp (continuous_algebraMap ℚ_[p] A))
      (continuous_algebraMap ℚ_[p] A) (funext fun q => by simp only [Function.comp_apply,
        map_ratCast])
  have hψx : ψ (j₁ x) = j₂ x := by
    change φ₂ (φ₁.symm (j₁ x)) = _
    rw [← h₁, RingEquiv.symm_apply_apply, h₂]
  rw [← hψx, hx]
  exact congrFun hQ r

section GaloisComparison

variable {E E' L : Type*} [Field E] [Field E'] [Field L] [Algebra E E'] [Algebra E L]
  [Algebra E' L] [IsScalarTower E E' L] [FiniteDimensional E L] [IsGalois E L]
  {F₀ F₁ F₂ : Type*} [Field F₀] [Field F₁] [Field F₂] [Algebra F₀ F₁] [Algebra F₀ F₂]
  [Algebra F₁ F₂] [IsScalarTower F₀ F₁ F₂] [FiniteDimensional F₀ F₂] [IsGalois F₀ F₂]
  (j₁ : E' →+* F₁) (j₂ : L →+* F₂) (h₁ : Algebra.adjoin F₀ (Set.range j₁) = ⊤)
  (hc₁ : ∀ y : E', j₂ (algebraMap E' L y) = algebraMap F₁ F₂ (j₁ y))
  (θ : (L ≃ₐ[E] L) ≃* (F₂ ≃ₐ[F₀] F₂)) (hθ : ∀ σ x, θ σ (j₂ x) = j₂ (σ x))

omit [FiniteDimensional F₀ F₂] [IsGalois F₀ F₂] in
include h₁ in
/-- An automorphism of `F₂ / F₀` fixing the image under `ρ` of a generating embedding
`E' → F₁` fixes the image of `F₁` under `ρ`. -/
private theorem fixes_of_fixes_range (ρ τ : F₂ ≃ₐ[F₀] F₂)
    (h : ∀ y : E', τ (ρ (algebraMap F₁ F₂ (j₁ y))) = ρ (algebraMap F₁ F₂ (j₁ y))) (z : F₁) :
    τ (ρ (algebraMap F₁ F₂ z)) = ρ (algebraMap F₁ F₂ z) := by
  have := AlgHom.ext_of_adjoin_eq_top h₁
    (φ₁ := (τ.toAlgHom.comp ρ.toAlgHom).comp (IsScalarTower.toAlgHom F₀ F₁ F₂))
    (φ₂ := ρ.toAlgHom.comp (IsScalarTower.toAlgHom F₀ F₁ F₂))
    (by rintro _ ⟨y, rfl⟩; exact h y)
  exact AlgHom.congr_fun this z

omit [FiniteDimensional E L] [IsGalois E L] [FiniteDimensional F₀ F₂] [IsGalois F₀ F₂] in
include h₁ hc₁ hθ in
/-- The Galois comparison carries the fixing subgroup of `E'` onto that of `F₁`. -/
private theorem mem_fixingSubgroup_iff_comparison (σ : L ≃ₐ[E] L) :
    σ ∈ (IsScalarTower.toAlgHom E E' L).fieldRange.fixingSubgroup ↔
      θ σ ∈ (IsScalarTower.toAlgHom F₀ F₁ F₂).fieldRange.fixingSubgroup := by
  simp only [IntermediateField.mem_fixingSubgroup_iff, AlgHom.mem_fieldRange,
    IsScalarTower.toAlgHom_apply, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h z
    simpa using fixes_of_fixes_range j₁ h₁ 1 (θ σ)
      (fun y => by rw [AlgEquiv.one_apply, ← hc₁, hθ, h]) z
  · intro h y
    apply j₂.injective
    rw [← hθ, hc₁, h]

include h₁ hc₁ hθ in
/-- A Galois comparison `Gal(L / E) ≃* Gal(F₂ / F₀)` compatible with embeddings `E' → F₁`
(generating `F₁` over `F₀`) and `L → F₂` matches the degrees of `E' / E` and `F₁ / F₀` and of
`L / E` and `F₂ / F₀`, and makes `L` a normal closure of `E' / E` when `F₂` is a normal closure
of `F₁ / F₀`. -/
theorem finrank_isNormalClosure_of_galoisEquiv [IsNormalClosure F₀ F₁ F₂] :
    Module.finrank E E' = Module.finrank F₀ F₁ ∧ Module.finrank E L = Module.finrank F₀ F₂ ∧
      IsNormalClosure E E' L := by
  have hL : Module.finrank E L = Module.finrank F₀ F₂ := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr θ.toEquiv
  have hMN : Module.finrank (IsScalarTower.toAlgHom E E' L).fieldRange L =
      Module.finrank (IsScalarTower.toAlgHom F₀ F₁ F₂).fieldRange F₂ := by
    rw [← IsGalois.card_fixingSubgroup_eq_finrank, ← IsGalois.card_fixingSubgroup_eq_finrank]
    exact Nat.card_congr
      (θ.toEquiv.subtypeEquiv (mem_fixingSubgroup_iff_comparison j₁ j₂ h₁ hc₁ θ hθ))
  have hE' : Module.finrank E E' = Module.finrank F₀ F₁ := by
    rw [(AlgHom.equivFieldRange (IsScalarTower.toAlgHom E E' L)).toLinearEquiv.finrank_eq,
      (AlgHom.equivFieldRange (IsScalarTower.toAlgHom F₀ F₁ F₂)).toLinearEquiv.finrank_eq]
    have h₁₂ := Module.finrank_mul_finrank E (IsScalarTower.toAlgHom E E' L).fieldRange L
    rw [hL, ← Module.finrank_mul_finrank F₀ (IsScalarTower.toAlgHom F₀ F₁ F₂).fieldRange F₂,
      hMN] at h₁₂
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h₁₂
  have : FiniteDimensional E E' := FiniteDimensional.left E E' L
  have : FiniteDimensional F₀ F₁ := FiniteDimensional.left F₀ F₁ F₂
  refine ⟨hE', hL, Algebra.IsAlgebraic.isNormalClosure_iff.mpr ⟨fun x => ?_, ?_⟩⟩
  · simpa only [minpoly.algebraMap_eq (algebraMap E' L).injective] using
      (IsGalois.to_normal (F := E) (E := L)).splits (algebraMap E' L x)
  have hbot : (normalClosure E E' L).fixingSubgroup = ⊥ := by
    refine eq_bot_iff.mpr fun σ hσ => ?_
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    rw [Subgroup.mem_bot, ← θ.map_eq_one_iff]
    have key (g : F₁ →ₐ[F₀] F₂) : g.fieldRange ≤ fixedField (Subgroup.zpowers (θ σ)) := by
      rw [IntermediateField.le_iff_le, Subgroup.zpowers_le,
        IntermediateField.mem_fixingSubgroup_iff]
      obtain ⟨ρ, hρ⟩ : ∃ ρ : F₂ ≃ₐ[F₀] F₂, ∀ z, ρ (algebraMap F₁ F₂ z) = g z :=
        ⟨AlgEquiv.ofBijective (g.liftNormal F₂) (AlgHom.normal_bijective F₀ F₂ F₂ _),
          fun z => g.liftNormal_commutes F₂ z⟩
      intro x hx
      obtain ⟨z, rfl⟩ := AlgHom.mem_fieldRange.mp hx
      rw [← hρ]
      obtain ⟨τ, rfl⟩ := θ.surjective ρ
      refine fixes_of_fixes_range j₁ h₁ (θ τ) (θ σ) (fun y => ?_) z
      rw [← hc₁, hθ, hθ, hσ]
      exact ((τ.toAlgHom.comp (IsScalarTower.toAlgHom E E' L)).fieldRange_le_normalClosure
        ⟨y, rfl⟩)
    have htop := normalClosure_le_iff.mpr key
    rw [(Algebra.IsAlgebraic.isNormalClosure_iff.mp ‹IsNormalClosure F₀ F₁ F₂›).2,
      IntermediateField.le_iff_le, Subgroup.zpowers_le, IntermediateField.fixingSubgroup_top]
      at htop
    exact htop
  rw [← IsGalois.fixedField_fixingSubgroup (normalClosure E E' L), hbot,
    IntermediateField.fixedField_bot]

end GaloisComparison

section Spectral

variable (p : ℕ) [Fact p.Prime]
  {E E' L : Type*} [Field E] [Field E'] [Field L] [NumberField E] [NumberField E']
  [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]
  [IsGalois E L]
  (F₀ F₁ F₂ : Type*) [Field F₀] [Field F₁] [Field F₂]
  [Algebra ℚ_[p] F₀] [Algebra ℚ_[p] F₁] [Algebra ℚ_[p] F₂]
  [FiniteDimensional ℚ_[p] F₀] [FiniteDimensional ℚ_[p] F₁] [FiniteDimensional ℚ_[p] F₂]
  [Algebra F₀ F₁] [Algebra F₀ F₂] [Algebra F₁ F₂] [IsScalarTower F₀ F₁ F₂]
  [IsScalarTower ℚ_[p] F₀ F₁] [IsScalarTower ℚ_[p] F₀ F₂] [IsScalarTower ℚ_[p] F₁ F₂]

/-- The place data of a tower of number fields with generating compatible embeddings into a
tower of finite extensions of `ℚ_[p]` and a compatible Galois comparison, for the module
topologies over `ℚ_[p]`. -/
theorem exists_placeData (j₀ : E →+* F₀) (j₁ : E' →+* F₁) (j₂ : L →+* F₂)
    (h₀ : Algebra.adjoin ℚ_[p] (Set.range j₀) = ⊤)
    (h₁ : Algebra.adjoin ℚ_[p] (Set.range j₁) = ⊤)
    (h₂ : Algebra.adjoin ℚ_[p] (Set.range j₂) = ⊤)
    (hc₀ : ∀ x : E, j₂ (algebraMap E L x) = algebraMap F₀ F₂ (j₀ x))
    (hc₁ : ∀ y : E', j₂ (algebraMap E' L y) = algebraMap F₁ F₂ (j₁ y))
    (θ : (L ≃ₐ[E] L) ≃* (F₂ ≃ₐ[F₀] F₂)) (hθ : ∀ σ x, θ σ (j₂ x) = j₂ (σ x)) :
    letI := moduleTopology ℚ_[p] F₀
    letI := moduleTopology ℚ_[p] F₁
    letI := moduleTopology ℚ_[p] F₂
    ∃ (v : HeightOneSpectrum (𝓞 E)) (v' : HeightOneSpectrum (𝓞 E'))
      (w : HeightOneSpectrum (𝓞 L)) (_ : v'.asIdeal.LiesOver v.asIdeal)
      (_ : w.asIdeal.LiesOver v'.asIdeal) (_ : w.asIdeal.LiesOver v.asIdeal)
      (ψ₀ : v.adicCompletion E ≃+* F₀) (ψ₁ : v'.adicCompletion E' ≃+* F₁)
      (ψ₂ : w.adicCompletion L ≃+* F₂),
      (∀ a : 𝓞 E, a ∈ v.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j₀ a) < 1) ∧
      Harris.HasUniquePlaceAbove L v ∧
      Continuous ψ₀ ∧ Continuous ψ₀.symm ∧ Continuous ψ₁ ∧ Continuous ψ₁.symm ∧
      Continuous ψ₂ ∧ Continuous ψ₂.symm ∧
      (∀ x : E, ψ₀ (algebraMap E _ x) = j₀ x) ∧
      (∀ x, ψ₁ (FiniteExtension.completionMap v v' x) = algebraMap F₀ F₁ (ψ₀ x)) ∧
      (∀ y, ψ₂ (FiniteExtension.completionMap v' w y) = algebraMap F₁ F₂ (ψ₁ y)) ∧
      (∀ x, ψ₂ (FiniteExtension.completionMap v w x) = algebraMap F₀ F₂ (ψ₀ x)) ∧
      ∀ (σ : L ≃ₐ[E] L) (x : L),
        θ σ (ψ₂ (algebraMap L (w.adicCompletion L) x)) =
          ψ₂ (algebraMap L (w.adicCompletion L) (σ x)) := by
  -- Replace the field and algebra structures by spectral-normed ones.
  obtain ⟨n₀, e₀, hn₀⟩ := exists_spectralNormedField p F₀
  obtain ⟨n₁, e₁, hn₁⟩ := exists_spectralNormedField p F₁
  obtain ⟨n₂, e₂, hn₂⟩ := exists_spectralNormedField p F₂
  subst e₀ e₁ e₂
  obtain ⟨a₀, f₀⟩ := exists_spectralNormedAlgebra p F₀ hn₀
  obtain ⟨a₁, f₁⟩ := exists_spectralNormedAlgebra p F₁ hn₁
  obtain ⟨a₂, f₂⟩ := exists_spectralNormedAlgebra p F₂ hn₂
  subst f₀ f₁ f₂
  have : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : IsUltrametricDist F₁ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : IsUltrametricDist F₂ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CompleteSpace F₀ := FiniteDimensional.complete ℚ_[p] F₀
  have : CompleteSpace F₁ := FiniteDimensional.complete ℚ_[p] F₁
  have : CompleteSpace F₂ := FiniteDimensional.complete ℚ_[p] F₂
  have hd₀ := denseRange_of_adjoin_eq_top p j₀ h₀
  have hd₁ := denseRange_of_adjoin_eq_top p j₁ h₁
  have hd₂ := denseRange_of_adjoin_eq_top p j₂ h₂
  have hn₀₁ : ∀ x : F₀, ‖algebraMap F₀ F₁ x‖ = ‖x‖ := fun x => by
    rw [hn₁, hn₀]; exact (spectralNorm.eq_of_tower (K := ℚ_[p]) (L := F₁) x).symm
  have hn₀₂ : ∀ x : F₀, ‖algebraMap F₀ F₂ x‖ = ‖x‖ := fun x => by
    rw [hn₂, hn₀]; exact (spectralNorm.eq_of_tower (K := ℚ_[p]) (L := F₂) x).symm
  have hn₁₂ : ∀ x : F₁, ‖algebraMap F₁ F₂ x‖ = ‖x‖ := fun x => by
    rw [hn₂, hn₁]; exact (spectralNorm.eq_of_tower (K := ℚ_[p]) (L := F₂) x).symm
  have hinv : ∀ (σ : L ≃ₐ[E] L) (x : L), ‖j₂ (σ x)‖ = ‖j₂ x‖ := fun σ x => by
    rw [← hθ, hn₂, hn₂]
    exact (spectralNorm_eq_of_equiv ((θ σ).restrictScalars ℚ_[p]) (j₂ x)).symm
  have hc₀₁ : ∀ x : E, j₁ (algebraMap E E' x) = algebraMap F₀ F₁ (j₀ x) := fun x => by
    apply (algebraMap F₁ F₂).injective
    rw [← hc₁, ← IsScalarTower.algebraMap_apply, hc₀, IsScalarTower.algebraMap_apply F₀ F₁ F₂]
  have : (densePrime j₁ hd₁).asIdeal.LiesOver (densePrime j₀ hd₀).asIdeal :=
    liesOver_densePrime j₀ hd₀ j₁ hd₁ hn₀₁ hc₀₁
  have : (densePrime j₂ hd₂).asIdeal.LiesOver (densePrime j₁ hd₁).asIdeal :=
    liesOver_densePrime j₁ hd₁ j₂ hd₂ hn₁₂ hc₁
  have : (densePrime j₂ hd₂).asIdeal.LiesOver (densePrime j₀ hd₀).asIdeal :=
    liesOver_densePrime j₀ hd₀ j₂ hd₂ hn₀₂ hc₀
  obtain ⟨ψ₀, hψ₀, hψ₀s, hψ₀E⟩ := exists_densePrime_completion j₀ hd₀
  obtain ⟨ψ₁, hψ₁, hψ₁s, hψ₁E⟩ := exists_densePrime_completion j₁ hd₁
  obtain ⟨ψ₂, hψ₂, hψ₂s, hψ₂E⟩ := exists_densePrime_completion j₂ hd₂
  have hcont₀₁ : Continuous (algebraMap F₀ F₁) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap F₀ F₁) hn₀₁).continuous
  have hcont₀₂ : Continuous (algebraMap F₀ F₂) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap F₀ F₂) hn₀₂).continuous
  have hcont₁₂ : Continuous (algebraMap F₁ F₂) :=
    (AddMonoidHomClass.isometry_of_norm (algebraMap F₁ F₂) hn₁₂).continuous
  have : IsModuleTopology ℚ_[p] F₀ := isModuleTopologyOfFiniteDimensional
  have : IsModuleTopology ℚ_[p] F₁ := isModuleTopologyOfFiniteDimensional
  have : IsModuleTopology ℚ_[p] F₂ := isModuleTopologyOfFiniteDimensional
  have hτ₀ := eq_moduleTopology ℚ_[p] F₀
  have hτ₁ := eq_moduleTopology ℚ_[p] F₁
  have hτ₂ := eq_moduleTopology ℚ_[p] F₂
  refine ⟨densePrime j₀ hd₀, densePrime j₁ hd₁, densePrime j₂ hd₂, inferInstance, inferInstance,
    inferInstance, ψ₀, ψ₁, ψ₂, fun a => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hψ₀E,
    completionMap_comm _ _ hcont₀₁ j₀ j₁ hc₀₁ ψ₀ ψ₁ hψ₀ hψ₁ hψ₀E hψ₁E,
    completionMap_comm _ _ hcont₁₂ j₁ j₂ hc₁ ψ₁ ψ₂ hψ₁ hψ₂ hψ₁E hψ₂E,
    completionMap_comm _ _ hcont₀₂ j₀ j₂ hc₀ ψ₀ ψ₂ hψ₀ hψ₂ hψ₀E hψ₂E, fun σ x => ?_⟩
  · rw [mem_densePrime, hn₀]
  · intro w w' hw hw'
    rw [prime_unique_of_norm_invariant j₂ _ (mem_densePrime j₂ hd₂) hinv _ w hw,
      prime_unique_of_norm_invariant j₂ _ (mem_densePrime j₂ hd₂) hinv _ w' hw']
  · rw [← hτ₀]; exact hψ₀
  · rw [← hτ₀]; exact hψ₀s
  · rw [← hτ₁]; exact hψ₁
  · rw [← hτ₁]; exact hψ₁s
  · rw [← hτ₂]; exact hψ₂
  · rw [← hτ₂]; exact hψ₂s
  · rw [hψ₂E, hψ₂E, hθ]

end Spectral

/-- Two `ℚ_[p]`-generating embeddings `E → F₀` cutting out the same prime of `E` (through the
spectral norm) agree on every element that one of them sends into the image of `ℚ_[p]`. -/
theorem eq_of_place_eq (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [NumberField E]
    {F₀ : Type*} [Field F₀] [Algebra ℚ_[p] F₀] [FiniteDimensional ℚ_[p] F₀] (j j' : E →+* F₀)
    (h : Algebra.adjoin ℚ_[p] (Set.range j) = ⊤) (h' : Algebra.adjoin ℚ_[p] (Set.range j') = ⊤)
    (v : HeightOneSpectrum (𝓞 E))
    (hv : ∀ a : 𝓞 E, a ∈ v.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j a) < 1)
    (hv' : ∀ a : 𝓞 E, a ∈ v.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j' a) < 1)
    {x : E} {r : ℚ_[p]} (hx : j x = algebraMap ℚ_[p] F₀ r) : j' x = j x := by
  obtain ⟨n, e, hn⟩ := exists_spectralNormedField p F₀
  subst e
  obtain ⟨a, f⟩ := exists_spectralNormedAlgebra p F₀ hn
  subst f
  have : IsUltrametricDist F₀ := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CompleteSpace F₀ := FiniteDimensional.complete ℚ_[p] F₀
  obtain ⟨φ, -, hφs, hφE⟩ := exists_completion_of_mem_iff j (denseRange_of_adjoin_eq_top p j h) v
    fun a => by rw [hv, hn]
  obtain ⟨φ', hφ', -, hφ'E⟩ :=
    exists_completion_of_mem_iff j' (denseRange_of_adjoin_eq_top p j' h') v fun a => by
      rw [hv', hn]
  exact eq_of_completion_eq p v j j' φ φ' hφs hφ' hφE hφ'E hx

/-- Two `ℚ_[p]`-generating embeddings `E → F₀` that differ at an element sent by the first into
the image of `ℚ_[p]` cut out different primes of `E`. -/
theorem ne_of_place_eq (p : ℕ) [Fact p.Prime] {E : Type*} [Field E] [NumberField E]
    {F₀ : Type*} [Field F₀] [Algebra ℚ_[p] F₀] [FiniteDimensional ℚ_[p] F₀] (j j' : E →+* F₀)
    (h : Algebra.adjoin ℚ_[p] (Set.range j) = ⊤) (h' : Algebra.adjoin ℚ_[p] (Set.range j') = ⊤)
    {v v' : HeightOneSpectrum (𝓞 E)}
    (hv : ∀ a : 𝓞 E, a ∈ v.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j a) < 1)
    (hv' : ∀ a : 𝓞 E, a ∈ v'.asIdeal ↔ spectralNorm ℚ_[p] F₀ (j' a) < 1)
    {x : E} {r : ℚ_[p]} (hx : j x = algebraMap ℚ_[p] F₀ r) (hne : j' x ≠ j x) : v ≠ v' := by
  rintro rfl
  exact hne (eq_of_place_eq p j j' h h' v hv hv' hx)

/-- Generation over an intermediate ring `K` gives generation over the base `R` when `K` is
generated over `R` by elements carried into the generating set. -/
theorem adjoin_eq_top_of_adjoin_base {R K A : Type*} [CommRing R] [CommRing K] [CommRing A]
    [Algebra R K] [Algebra R A] [Algebra K A] [IsScalarTower R K A] {s : Set K} {t : Set A}
    (hs : Algebra.adjoin R s = ⊤) (ht : Algebra.adjoin K t = ⊤)
    (hst : algebraMap K A '' s ⊆ t) : Algebra.adjoin R t = ⊤ := by
  have hK : (IsScalarTower.toAlgHom R K A).range ≤ Algebra.adjoin R t := by
    rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin]
    exact Algebra.adjoin_mono hst
  refine eq_top_iff.mpr fun z hz' => ?_
  clear hz'
  have hz : z ∈ Algebra.adjoin K t := ht ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r => exact hK (AlgHom.mem_range_self _ r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

section Conjugation

variable {E L : Type*} [Field E] [Field L] [NumberField E] [NumberField L] [Algebra E L]

omit [NumberField E] in
/-- A field automorphism `e` of `E` that cuts `v` out through `N ∘ j` cuts `finitePlaceEquiv e v`
out through `N ∘ j ∘ e`. -/
theorem mem_finitePlaceEquiv_iff {A : Type*} [Ring A] (e : E ≃+* E) (j : E →+* A) (N : A → ℝ)
    {v : HeightOneSpectrum (𝓞 E)} (hv : ∀ a : 𝓞 E, a ∈ v.asIdeal ↔ N (j a) < 1) (a : 𝓞 E) :
    a ∈ (finitePlaceEquiv e v).asIdeal ↔ N (j.comp e.toRingHom a) < 1 := by
  rw [finitePlaceEquiv_mem, hv]
  rfl

omit [NumberField E] in
/-- Composing with a field automorphism does not change the image of an embedding. -/
theorem range_comp_ringEquiv {A : Type*} [Ring A] (e : E ≃+* E) (j : E →+* A) :
    Set.range (j.comp e.toRingHom) = Set.range j := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.symm x, by simp⟩

omit [NumberField E] in
/-- A rational integer lies in `finitePlaceEquiv e v` exactly when it lies in `v`. -/
theorem natCast_mem_finitePlaceEquiv (e : E ≃+* E) (v : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    (n : 𝓞 E) ∈ (finitePlaceEquiv e v).asIdeal ↔ (n : 𝓞 E) ∈ v.asIdeal := by
  rw [finitePlaceEquiv_mem, map_natCast]

/-- Uniqueness of the place of `L` above `v` transfers to `finitePlaceEquiv cE v` when `cE`
extends to an automorphism `cL` of `L`. -/
theorem hasUniquePlaceAbove_finitePlaceEquiv (cE : E ≃+* E) (cL : L ≃+* L)
    (hc : ∀ x : E, cL (algebraMap E L x) = algebraMap E L (cE x))
    {v : HeightOneSpectrum (𝓞 E)} (hv : Harris.HasUniquePlaceAbove L v) :
    Harris.HasUniquePlaceAbove L (finitePlaceEquiv cE v) := by
  have key (w : HeightOneSpectrum (𝓞 L))
      (hw : w.asIdeal.LiesOver (finitePlaceEquiv cE v).asIdeal) :
      (finitePlaceEquiv cL.symm w).asIdeal.LiesOver v.asIdeal := by
    refine ⟨Ideal.ext fun a => ?_⟩
    have h : RingOfIntegers.mapRingEquiv cL.symm (algebraMap (𝓞 E) (𝓞 L) a) =
        algebraMap (𝓞 E) (𝓞 L) (RingOfIntegers.mapRingEquiv cE.symm a) := by
      apply RingOfIntegers.ext
      change cL.symm (algebraMap E L (a : E)) = algebraMap E L (cE.symm (a : E))
      rw [RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]
    have h' : RingOfIntegers.mapRingEquiv cE (RingOfIntegers.mapRingEquiv cE.symm a) = a :=
      RingOfIntegers.ext (by simp)
    rw [Ideal.mem_under, finitePlaceEquiv_mem, h, ← Ideal.mem_under, ← hw.over,
      finitePlaceEquiv_mem, h']
  intro w w' hw hw'
  exact (finitePlaceEquiv cL.symm).injective (hv _ _ (key w hw) (key w' hw'))

end Conjugation

section Harris

open Harris LocalFactor.CommonClosure GeneralPosition

variable {p : ℕ} [Fact p.Prime] (F : PadicField p) (F' : Extension F)
  {E E' L : Type*} [Field E] [Field E'] [Field L] [NumberField E] [NumberField E']
  [NumberField L] [Algebra E E'] [Algebra E L] [Algebra E' L] [IsScalarTower E E' L]
  [IsGalois E L]

/-- Harris's place datum from embeddings `E → F`, `E' → F'`, `L → F̃` of a tower of number
fields, compatible along both towers in the common algebraic closure, generating `F` over
`ℚ_[p]` and `F'`, `F̃` over `F`, together with a compatible Galois comparison
`Gal(L / E) ≃* Gal(F̃ / F)`. All topologies are those of the target statement. -/
theorem exists_harrisPlaceDatum (jE : E →+* F.Carrier) (jE' : E' →+* F'.field)
    (jL : L →+* (galoisClosure F F').field) (hE : Algebra.adjoin ℚ_[p] (Set.range jE) = ⊤)
    (hE' : Algebra.adjoin F.Carrier (Set.range jE') = ⊤)
    (hL : Algebra.adjoin F.Carrier (Set.range jL) = ⊤)
    (hcE : ∀ x : E,
      jL (algebraMap E L x) = algebraMap F.Carrier (galoisClosure F F').field (jE x))
    (hcE' : ∀ y : E', ((jL (algebraMap E' L y) : (galoisClosure F F').field) :
      AlgebraicClosure F.Carrier) = ((jE' y : F'.field) : AlgebraicClosure F.Carrier))
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field))
    (hθ : ∀ σ x, θ σ (jL x) = jL (σ x)) :
    letI := F.canonicalTopology
    letI := (fieldData F F').topology
    letI := (fieldData F (galoisClosure F F')).topology
    ∃ (P : PlaceDatum F F' E E' L) (φ : FiniteCompletion E' P.v' ≃+* F'.field),
      (∀ a : 𝓞 E, a ∈ P.v.asIdeal ↔ spectralNorm ℚ_[p] F.Carrier (jE a) < 1) ∧
      (∀ x : E, P.iso (algebraMap E _ x) = jE x) ∧
      (p : 𝓞 E) ∈ P.v.asIdeal ∧ HasUniquePlaceAbove L P.v ∧ P.IsCompatible ∧
      Continuous P.iso ∧ Continuous P.iso.symm ∧
      Continuous P.isoTilde ∧ Continuous P.isoTilde.symm ∧
      (∀ (σ : L ≃ₐ[E] L) (x : L),
        θ σ (P.isoTilde (algebraMap L (FiniteCompletion L P.vTilde) x)) =
          P.isoTilde (algebraMap L (FiniteCompletion L P.vTilde) (σ x))) ∧
      Continuous φ ∧ Continuous φ.symm ∧
      (∀ x : FiniteCompletion E P.v,
        φ (FiniteExtension.completionMap P.v P.v' x) =
          algebraMap F.Carrier F'.field (P.iso x)) ∧
      ∀ y : FiniteCompletion E' P.v',
        ((φ y : F'.field) : AlgebraicClosure F.Carrier) =
          ((P.isoTilde (FiniteExtension.completionMap P.v' P.vTilde y) :
            (galoisClosure F F').field) : AlgebraicClosure F.Carrier) := by
  -- The `ℚ_[p]`-algebra structures of `F'` and `F̃` underlying their canonical topologies.
  let a₁ : Algebra ℚ_[p] F'.field := (F'.asPadicField (p := p)).algebra
  let a₂ : Algebra ℚ_[p] (galoisClosure F F').field :=
    ((galoisClosure F F').asPadicField (p := p)).algebra
  let a₁₂ : Algebra F'.field (galoisClosure F F').field :=
    (IntermediateField.inclusion (le_galoisClosure F F')).toAlgebra
  have : IsScalarTower ℚ_[p] F.Carrier F'.field := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower F.Carrier F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := (F'.asPadicField (p := p)).finiteDimensional
  have := ((galoisClosure F F').asPadicField (p := p)).finiteDimensional
  have hc₀₁ (x : E) : jE' (algebraMap E E' x) = algebraMap F.Carrier F'.field (jE x) := by
    apply Subtype.ext
    rw [← hcE', ← IsScalarTower.algebraMap_apply, hcE]
    rfl
  have hc₁ (y : E') : jL (algebraMap E' L y) =
      algebraMap F'.field (galoisClosure F F').field (jE' y) := Subtype.ext (hcE' y)
  have h₁ : Algebra.adjoin ℚ_[p] (Set.range jE') = ⊤ :=
    adjoin_eq_top_of_adjoin_base hE hE' (by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨algebraMap E E' x, hc₀₁ x⟩)
  have h₂ : Algebra.adjoin ℚ_[p] (Set.range jL) = ⊤ :=
    adjoin_eq_top_of_adjoin_base hE hL (by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨algebraMap E L x, hcE x⟩)
  obtain ⟨v, v', w, _, _, _, ψ₀, ψ₁, ψ₂, hv, huniq, hψ₀, hψ₀s, hψ₁, hψ₁s, hψ₂, hψ₂s, hψ₀E,
    h₀₁, h₁₂, h₀₂, hθ'⟩ :=
    exists_placeData p F.Carrier F'.field (galoisClosure F F').field jE jE' jL hE h₁ h₂ hcE hc₁
      θ hθ
  have hτ₁ : (fieldData F F').topology = (F'.asPadicField (p := p)).canonicalTopology :=
    PadicField.canonicalTopologicalData_topology _
  have hτ₂ : (fieldData F (galoisClosure F F')).topology =
      ((galoisClosure F F').asPadicField (p := p)).canonicalTopology :=
    PadicField.canonicalTopologicalData_topology _
  have hp : (p : 𝓞 E) ∈ v.asIdeal := by
    rw [hv, show jE ((p : 𝓞 E) : E) = algebraMap ℚ_[p] F.Carrier (p : ℚ_[p]) by simp,
      spectralNorm_extends, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr (Fact.out : p.Prime).one_lt)
  refine ⟨⟨v, v', w, ψ₀, ψ₂⟩, ψ₁, hv, hψ₀E, hp, huniq, ⟨h₀₂, ?_⟩, hψ₀, hψ₀s, ?_, ?_, hθ', ?_, ?_,
    h₀₁, fun y => ?_⟩
  · ext z
    simp only [Set.mem_range, h₁₂, SetLike.mem_coe]
    refine ⟨?_, fun hz => ⟨ψ₁.symm ⟨z, hz⟩, ?_⟩⟩
    · rintro ⟨y, rfl⟩
      exact (ψ₁ y).2
    · rw [RingEquiv.apply_symm_apply]
      rfl
  · rw [hτ₂]; exact hψ₂
  · rw [hτ₂]; exact hψ₂s
  · rw [hτ₁]; exact hψ₁
  · rw [hτ₁]; exact hψ₁s
  · dsimp only
    rw [h₁₂]
    rfl

omit [NumberField E'] in
/-- The degrees and the normal closure of Harris's setup from compatible embeddings
`E' → F'`, `L → F̃` (the first generating `F'` over `F`) and a compatible Galois comparison
`Gal(L / E) ≃* Gal(F̃ / F)`. -/
theorem harrisDegrees (jE' : E' →+* F'.field) (jL : L →+* (galoisClosure F F').field)
    (hE' : Algebra.adjoin F.Carrier (Set.range jE') = ⊤)
    (hcE' : ∀ y : E', ((jL (algebraMap E' L y) : (galoisClosure F F').field) :
      AlgebraicClosure F.Carrier) = ((jE' y : F'.field) : AlgebraicClosure F.Carrier))
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field))
    (hθ : ∀ σ x, θ σ (jL x) = jL (σ x)) :
    Module.finrank E E' = Module.finrank F.Carrier F'.field ∧
      Module.finrank E L = Module.finrank F.Carrier (galoisClosure F F').field ∧
      IsNormalClosure E E' L := by
  let : Algebra F'.field (galoisClosure F F').field :=
    (IntermediateField.inclusion (le_galoisClosure F F')).toAlgebra
  have : IsScalarTower F.Carrier F'.field (galoisClosure F F').field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := Algebra.charZero_of_charZero ℚ_[p] F.Carrier
  have : IsGalois F.Carrier (galoisClosure F F').field :=
    inferInstanceAs (IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier)))
  have : IsNormalClosure F.Carrier F'.field (galoisClosure F F').field :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun _ => IsAlgClosed.splits _
  exact finrank_isNormalClosure_of_galoisEquiv jE' jL hE' (fun y => Subtype.ext (hcE' y)) θ hθ

end Harris

end Langlands.Global.FieldRealization
