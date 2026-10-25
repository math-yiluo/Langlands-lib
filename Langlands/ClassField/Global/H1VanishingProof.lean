import Langlands.ClassField.Global.CohomologyMaps
import Langlands.ClassField.Global.CocycleRestriction
import Langlands.ClassField.Global.FundamentalClassStatement
import Langlands.ClassField.Global.IdeleClassGaloisDescentProof
import Langlands.ClassField.Global.IdeleClassNormGaloisProductProof
import Langlands.ClassField.Global.CyclicH2NormIndexComparisonProof
import Langlands.ClassField.Global.CyclicIdeleClassHerbrandAssembly
import Langlands.Global.AdelicFunctoriality.IdeleClassSecondInequalityProof
import Langlands.Cohomology.PrimeSectionH1Proof

/-! # Vanishing of the first idele-class cohomology -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open scoped NumberField
open Langlands.Global.AdelicFunctoriality

universe u

namespace H1VanishingProof

section Cyclic

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- **Cyclic vanishing.** For a cyclic Galois extension of number fields,
`H¹(Gal(E/F), C_E) = 0`, from the Herbrand quotient and the second inequality. -/
theorem subsingleton_H1_of_isCyclic (hA : IdeleClassGaloisDescent.{u, u})
    (hC : IdeleClassNormGaloisProduct.{u, u}) (hD : CyclicIdeleClassHerbrandQuotient.{u, u})
    (hE : IdeleClassSecondInequality.{u, u}) [IsCyclic (E ≃ₐ[F] E)] :
    Subsingleton (relativeIdeleClassCohomology F E 1 : Type u) := by
  obtain ⟨h1, -, hcard⟩ := hD F E
  have hdvd := (cyclicH2NormIndexComparison hA hC F E).trans (hE F E)
  rw [hcard] at hdvd
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have h1' : Nat.card (relativeIdeleClassCohomology F E 1 : Type u) ∣ 1 :=
    (Nat.mul_dvd_mul_iff_left hn).1 (by simpa using hdvd)
  exact (Nat.card_eq_one_iff_unique.1 (Nat.dvd_one.1 h1')).1

end Cyclic

section Section

variable (hA : IdeleClassGaloisDescent.{u, u}) (hC : IdeleClassNormGaloisProduct.{u, u})
  (hD : CyclicIdeleClassHerbrandQuotient.{u, u}) (hE : IdeleClassSecondInequality.{u, u})

include hA hC hD hE

/-- **Prime sections, Galois form.** Let `E/K` be Galois and `M` an intermediate field,
Galois over `K` of prime degree. A (multiplicative) `1`-cocycle of `Gal(E/K)` with values in
`C_E` which is trivial on `Gal(E/M)` is a coboundary. -/
theorem exists_coboundary_of_prime_card {K E : Type u} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [IsGalois K E] (M : IntermediateField K E) [IsGalois K M]
    (hM : (Nat.card (M ≃ₐ[K] M)).Prime) (f : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E)
    (hf : ∀ σ τ, f (σ * τ) = f σ * relativeIdeleClassAut K E σ (f τ))
    (h0 : ∀ n ∈ M.fixingSubgroup, f n = 1) :
    ∃ c : IdeleClassGroup (𝓞 E) E, ∀ σ, f σ = relativeIdeleClassAut K E σ c / c := by
  classical
  -- `f` is constant on the cosets of `Gal(E/M)`, and its values are fixed by `Gal(E/M)`.
  have hcoset : ∀ σ n, n ∈ M.fixingSubgroup → f (σ * n) = f σ := fun σ n hn => by
    rw [hf, h0 n hn, map_one]
    exact mul_one (f σ)
  have hnormal : M.fixingSubgroup.Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact MonoidHom.normal_ker _
  have hval : ∀ σ, ∀ n ∈ M.fixingSubgroup, relativeIdeleClassAut K E n (f σ) = f σ :=
    fun σ n hn => by
      have h2 : σ⁻¹ * n * σ ∈ M.fixingSubgroup := by
        simpa using hnormal.conj_mem n hn σ⁻¹
      have h3 := hf n σ
      rw [h0 n hn, show n * σ = σ * (σ⁻¹ * n * σ) by group, hcoset σ _ h2] at h3
      exact (h3.trans (one_mul (relativeIdeleClassAut K E n (f σ)))).symm
  -- Hence every value descends to `C_M`.
  have hfixM : ∀ σ (τ : E ≃ₐ[M] E), relativeIdeleClassAut M E τ (f σ) = f σ := fun σ τ => by
    rw [← relativeIdeleClassAut_restrictScalars (K := K)]
    refine hval σ _ ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_)
    exact τ.commutes ⟨x, hx⟩
  choose g₀ hg₀ using fun σ => ((hA M E).2 (f σ)).1 (hfixM σ)
  have hinj := (hA M E).1
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom M : (E ≃ₐ[K] E) → M ≃ₐ[K] M) :=
    AlgEquiv.restrictNormalHom_surjective E
  let lift := Function.surjInv hsurj
  have hlift : ∀ τ, AlgEquiv.restrictNormalHom M (lift τ) = τ := Function.surjInv_eq hsurj
  have hfib : ∀ σ σ', AlgEquiv.restrictNormalHom M σ = AlgEquiv.restrictNormalHom M σ' →
      f σ = f σ' := fun σ σ' h => by
    have : σ⁻¹ * σ' ∈ M.fixingSubgroup := by
      rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, h,
        inv_mul_cancel]
    rw [← mul_inv_cancel_left σ σ', hcoset σ _ this]
  have hact : ∀ (σ : E ≃ₐ[K] E) (a : IdeleClassGroup (𝓞 M) M),
      ideleClassInclusion (K := M) (L := E)
          (relativeIdeleClassAut K M (AlgEquiv.restrictNormalHom M σ) a) =
        relativeIdeleClassAut K E σ (ideleClassInclusion a) :=
    fun σ a => ideleClassInclusion_relativeIdeleClassAut σ a
  -- The descended function on `Gal(M/K)` is a cocycle.
  have hg : ∀ τ₁ τ₂, g₀ (lift (τ₁ * τ₂)) =
      g₀ (lift τ₁) * relativeIdeleClassAut K M τ₁ (g₀ (lift τ₂)) := by
    intro τ₁ τ₂
    have e1 : f (lift (τ₁ * τ₂)) = f (lift τ₁ * lift τ₂) :=
      hfib _ _ (by rw [map_mul, hlift, hlift, hlift])
    have e2 := hact (lift τ₁) (g₀ (lift τ₂))
    rw [hlift] at e2
    apply hinj
    rw [map_mul, e2, hg₀, hg₀, hg₀, e1, hf]
  -- Apply the cyclic case to `M/K`.
  have : Fact (Nat.card (M ≃ₐ[K] M)).Prime := ⟨hM⟩
  have : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card rfl
  have hsub := subsingleton_H1_of_isCyclic (F := K) (E := M) hA hC hD hE
  let B := relativeIdeleClassRepresentation K M
  let φ : (M ≃ₐ[K] M) → B := fun τ =>
    (Additive.ofMul (g₀ (lift τ)) : Additive (IdeleClassGroup (𝓞 M) M))
  have hmem : φ ∈ groupCohomology.cocycles₁ B := by
    rw [groupCohomology.mem_cocycles₁_iff]
    intro τ₁ τ₂
    have h := congrArg Additive.ofMul ((hg τ₁ τ₂).trans (mul_comm (g₀ (lift τ₁)) _))
    exact h
  have hzero : groupCohomology.H1π B ⟨_, hmem⟩ = 0 := Subsingleton.elim _ _
  rw [groupCohomology.H1π_eq_zero_iff] at hzero
  obtain ⟨d, hd⟩ := hzero
  let c : IdeleClassGroup (𝓞 M) M := Additive.toMul (α := IdeleClassGroup (𝓞 M) M) d
  have hdτ : ∀ τ, g₀ (lift τ) = relativeIdeleClassAut K M τ c / c := fun τ => by
    have h := congrArg (Additive.toMul (α := IdeleClassGroup (𝓞 M) M)) (congrFun hd τ)
    exact h.symm
  refine ⟨ideleClassInclusion (K := M) (L := E) c, fun σ => ?_⟩
  rw [hfib σ (lift (AlgEquiv.restrictNormalHom M σ)) (hlift _).symm, ← hg₀, hdτ, map_div, hact]

/-- **Prime sections, subgroup form.** A `1`-cocycle of `Gal(E/K)` with values in `C_E`
which is trivial on a normal subgroup of prime index is a coboundary. -/
theorem exists_coboundary_of_prime_index {K E : Type u} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [IsGalois K E] (N : Subgroup (E ≃ₐ[K] E)) [N.Normal]
    (hN : N.index.Prime) (f : (E ≃ₐ[K] E) → IdeleClassGroup (𝓞 E) E)
    (hf : ∀ σ τ, f (σ * τ) = f σ * relativeIdeleClassAut K E σ (f τ))
    (h0 : ∀ n ∈ N, f n = 1) :
    ∃ c : IdeleClassGroup (𝓞 E) E, ∀ σ, f σ = relativeIdeleClassAut K E σ c / c := by
  have hcard : Nat.card (IntermediateField.fixedField N ≃ₐ[K] IntermediateField.fixedField N) =
      N.index :=
    (Nat.card_congr (IsGalois.normalAutEquivQuotient N).toEquiv).symm
  refine exists_coboundary_of_prime_card hA hC hD hE (IntermediateField.fixedField N)
    (hcard ▸ hN) f hf ?_
  rw [IntermediateField.fixingSubgroup_fixedField]
  exact h0

/-- **Prime sections for the actual idele class group.** For a subgroup `H ≤ Gal(E/F)` and a
normal subgroup `N` of `H` of prime index, `H¹(H/N, C_E^N) = 0`. -/
theorem subsingleton_H1_quotientToInvariants {F E : Type u} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (H : Subgroup (E ≃ₐ[F] E))
    (N : Subgroup H) [N.Normal] (hN : N.index.Prime) :
    Subsingleton (groupCohomology
      ((Rep.res H.subtype (relativeIdeleClassRepresentation F E)).quotientToInvariants N) 1) := by
  classical
  let A := relativeIdeleClassRepresentation F E
  let X := (Rep.res H.subtype A).quotientToInvariants N
  let K' : IntermediateField F E := IntermediateField.fixedField H
  have hH : K'.fixingSubgroup = H := IntermediateField.fixingSubgroup_fixedField H
  let e : (E ≃ₐ[K'] E) ≃* H :=
    (IntermediateField.fixingSubgroupEquiv K').symm.trans (MulEquiv.subgroupCongr hH)
  have he : ∀ σ, ((e σ : H) : E ≃ₐ[F] E) = σ.restrictScalars F := fun _ => rfl
  let N' : Subgroup (E ≃ₐ[K'] E) := N.comap e.toMonoidHom
  have : N'.Normal := Subgroup.Normal.comap inferInstance _
  have hN' : N'.index.Prime := by
    rw [Subgroup.index_comap_of_surjective _ e.surjective]
    exact hN
  refine subsingleton_of_forall_eq 0 fun x => ?_
  induction x using groupCohomology.H1_induction_on with
  | h z =>
  rw [groupCohomology.H1π_eq_zero_iff]
  let f : (E ≃ₐ[K'] E) → IdeleClassGroup (𝓞 E) E := fun σ =>
    Additive.toMul ((z (QuotientGroup.mk (e σ) : H ⧸ N) : X).1 : A)
  have hz := (groupCohomology.mem_cocycles₁_iff (z : H ⧸ N → X)).1 z.2
  have hf : ∀ σ τ, f (σ * τ) = f σ * relativeIdeleClassAut K' E σ (f τ) := by
    intro σ τ
    have := congrArg (fun v : X => Additive.toMul (v.1 : A))
      (hz (QuotientGroup.mk (e σ)) (QuotientGroup.mk (e τ)))
    rw [← QuotientGroup.mk_mul, ← map_mul] at this
    change Additive.toMul ((z (QuotientGroup.mk (e (σ * τ)) : H ⧸ N) : X).1 : A) = _
    rw [this]
    exact mul_comm (relativeIdeleClassAut K' E σ (f τ)) (f σ)
  have h0 : ∀ n ∈ N', f n = 1 := by
    intro n hn
    have h1 : (QuotientGroup.mk (e n) : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hn
    simp only [f, h1, groupCohomology.cocycles₁_map_one]
    rfl
  obtain ⟨c, hc⟩ := exists_coboundary_of_prime_index hA hC hD hE N' hN' f hf h0
  have hcinv : (Additive.ofMul c : A) ∈
      Representation.invariants ((Rep.res H.subtype A).ρ.comp N.subtype) := by
    rintro ⟨n, hn⟩
    obtain ⟨σ, rfl⟩ := e.surjective n
    have h1 := hc σ
    rw [h0 σ hn, eq_comm, div_eq_one] at h1
    exact congrArg Additive.ofMul h1
  refine ⟨⟨Additive.ofMul c, hcinv⟩, funext fun q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H h =>
  obtain ⟨σ, rfl⟩ := e.surjective h
  apply Subtype.ext
  change Additive.ofMul (relativeIdeleClassAut K' E σ c) - Additive.ofMul c =
    Additive.ofMul (f σ)
  rw [hc σ]
  rfl

/-- **Conditional vanishing.** The four child statements and the generic prime-section
reduction give `H¹(Gal(E/F), C_E) = 0`. -/
theorem ideleClassH1Vanishing_of (hP : Langlands.Cohomology.PrimeSectionH1Vanishing.{u}) :
    FundamentalClass.IdeleClassH1Vanishing.{u} := by
  intro F _ _ E _ _ _ _
  exact hP _ _ (relativeIdeleClassRepresentation F E)
    fun H N _ hN => subsingleton_H1_quotientToInvariants hA hC hD hE H N hN

end Section

/-- **Remaining hypotheses.** With the published proofs `ideleClassNormGaloisProduct` and
`Langlands.Cohomology.primeSectionH1Vanishing`, only descent, the cyclic Herbrand quotient and
the second inequality remain as hypotheses. -/
theorem ideleClassH1Vanishing_of_descent (hA : IdeleClassGaloisDescent.{u, u})
    (hD : CyclicIdeleClassHerbrandQuotient.{u, u}) (hE : IdeleClassSecondInequality.{u, u}) :
    FundamentalClass.IdeleClassH1Vanishing.{u} :=
  ideleClassH1Vanishing_of hA ideleClassNormGaloisProduct hD hE
    Langlands.Cohomology.primeSectionH1Vanishing

/-- **Remaining inequalities.** With the published descent proof `ideleClassGaloisDescent`
also plugged in, only the cyclic Herbrand quotient and the second inequality remain. -/
theorem ideleClassH1Vanishing_of_inequalities (hD : CyclicIdeleClassHerbrandQuotient.{u, u})
    (hE : IdeleClassSecondInequality.{u, u}) : FundamentalClass.IdeleClassH1Vanishing.{u} :=
  ideleClassH1Vanishing_of_descent ideleClassGaloisDescent.{u, u} hD hE

/-- **Remaining second inequality.** With the published first-inequality proof
`cyclicIdeleClassHerbrandQuotient` also plugged in, only the second inequality remains. -/
theorem ideleClassH1Vanishing_of_secondInequality (hE : IdeleClassSecondInequality.{u, u}) :
    FundamentalClass.IdeleClassH1Vanishing.{u} :=
  ideleClassH1Vanishing_of_inequalities cyclicIdeleClassHerbrandQuotient.{u, u} hE

end H1VanishingProof

/-- **Vanishing of `H¹` of the idele class group.** For every finite Galois extension `E/F`
of number fields, `H¹(Gal(E/F), C_E) = 0`. -/
theorem ideleClassH1Vanishing : FundamentalClass.IdeleClassH1Vanishing.{u} :=
  H1VanishingProof.ideleClassH1Vanishing_of_secondInequality ideleClassSecondInequality.{u, u}

end Langlands.ClassField.Global
