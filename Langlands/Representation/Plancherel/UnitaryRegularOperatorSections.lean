import Langlands.Representation.Plancherel.UnitaryRegularOperatorExpansion
import Langlands.Representation.Plancherel.FiniteSmoothFamilyTransport
import Langlands.Representation.Plancherel.ProductInducedOrbitSections
import Langlands.Representation.Plancherel.UnramifiedOperatorTranslation

/-! # Smooth orbit sections from regular operators

Three generic steps for constructing an actual smooth orbit section whose compact picture is a
regular operator applied to another smooth family:

* `unitaryRegularOperator_mem_finiteSmoothFamilies` and its monomial version: a regular operator
  `d⁻¹ N` with polynomial numerator and a denominator nonzero on the unitary torus, applied to a
  finite smooth family, is a finite smooth family;
* `regular_smul_mul_eq_of_isOpen` and `regular_inv_smul_mul_eq_of_isOpen`: a covariance
  identity `c(zτ) ∘ P = Q ∘ c(z)` on the interior of a translation-stable domain extends to the
  numerator, and to the values `d⁻¹ N` wherever the denominator is nonzero, given the identity
  principle for polynomial families;
* `exists_productInducedSmoothOrbitSection`: a finite smooth compact family with the stabilizer
  covariance is the compact picture of an actual smooth orbit section.
-/

noncomputable section

open CategoryTheory Langlands.Aubert.General Langlands.Induction
open scoped NNReal ContDiff TensorProduct

namespace Langlands.Plancherel

open UnramifiedOperatorFamily

universe uG uI uJ uK uV uW

/-! ### Regular operators on finite smooth families -/

section Smooth

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} (ν : I → (G →* ℝ≥0ˣ))
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

set_option hygiene false in
local notation "χ" z => (⟨(e.symm z).val, (e.symm z).property.1⟩ : unramifiedCharacters ν)

/-- A regular operator `z ↦ d(z)⁻¹ N(z)` with polynomial numerator and a denominator nonzero on
the unitary torus maps a finite smooth family `R` to the finite smooth family
`z ↦ d(z)⁻¹ N(z) (R z)`. -/
theorem unitaryRegularOperator_mem_finiteSmoothFamilies
    (he : HasLaurentUnitaryCoordinates ν e)
    (d : unramifiedRegularFunctions ν) (hd : ∀ z : J → Circle, d.val (χ z) ≠ 0)
    (A : unramifiedCharacters ν → V →ₗ[ℂ] W)
    (hA : IsPolynomialOperatorOn Set.univ (fun z => A z.val))
    {R : (J → Circle) → V} (hR : R ∈ finiteSmoothFamilies J V) :
    (fun z => unitaryRegularOperator ν e d A z (R z)) ∈ finiteSmoothFamilies J W := by
  classical
  obtain ⟨n, f, v, hRf⟩ := (mem_finiteSmoothFamilies_iff J V R).mp hR
  choose N b w hbw using fun i : Fin n => hA (v i)
  have hdinv : IsSmoothFiniteTorusFunction (fun z => (d.val (χ z))⁻¹) :=
    (isSmoothFiniteTorusFunction_unramifiedRegularFunction ν e he d).inv
      (fun θ => hd (finiteTorusExp θ))
  have hf (i : Fin n) : IsSmoothFiniteTorusFunction (f i).val := (f i).property
  let c (i : Fin n) (j : Fin (N i)) : smoothFiniteTorusFunctions J :=
    ⟨fun z => (f i).val z * ((d.val (χ z))⁻¹ * (b i j).val (χ z)),
      (hf i).mul
        (hdinv.mul (isSmoothFiniteTorusFunction_unramifiedRegularFunction ν e he (b i j)))⟩
  have hsum : (fun z => unitaryRegularOperator ν e d A z (R z)) =
      ∑ i, ∑ j, (fun z => (c i j).val z • w i j) := by
    funext z
    simp only [Finset.sum_apply]
    change (d.val (χ z))⁻¹ • A (χ z) (R z) = _
    rw [hRf z, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hval : A (χ z) (v i) = ∑ j, (b i j).val (χ z) • w i j :=
      hbw i ⟨χ z, Set.mem_univ _⟩
    rw [map_smul, hval, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [c, smul_smul]
    congr 1
    ring
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.subset_span ⟨c i j, w i j, rfl⟩

/-- The same after an integer monomial change of the torus coordinates. -/
theorem unitaryRegularOperator_comp_monomial_mem_finiteSmoothFamilies
    (he : HasLaurentUnitaryCoordinates ν e)
    (d : unramifiedRegularFunctions ν) (hd : ∀ z : J → Circle, d.val (χ z) ≠ 0)
    (A : unramifiedCharacters ν → V →ₗ[ℂ] W)
    (hA : IsPolynomialOperatorOn Set.univ (fun z => A z.val))
    {R : (J → Circle) → V} (hR : R ∈ finiteSmoothFamilies J V)
    {K : Type uK} [Fintype K] (a : J → K → ℤ) :
    (fun w => unitaryRegularOperator ν e d A (finiteTorusMonomial a w)
      (R (finiteTorusMonomial a w))) ∈ finiteSmoothFamilies K W :=
  mem_finiteSmoothFamilies_comp_monomial
    (unitaryRegularOperator_mem_finiteSmoothFamilies ν e he d hd A hA hR) a

end Smooth

/-! ### Covariance identities by the identity principle -/

section Identity

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {I : Type uI} {ν : I → (G →* ℝ≥0ˣ)}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Translation by `τ` of a polynomial family is polynomial. -/
theorem isPolynomialOn_mul_translate {f : unramifiedCharacters ν → W}
    (hf : IsPolynomialOn Set.univ (fun χ => f χ.val)) (τ : unramifiedCharacters ν) :
    IsPolynomialOn Set.univ (fun χ => f (χ.val * τ)) := by
  obtain ⟨n, b, v, hb⟩ := hf
  refine ⟨n, fun i => unramifiedRegularTranslation ν τ (b i), v, fun χ => ?_⟩
  have h := hb ⟨χ.val * τ, Set.mem_univ _⟩
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  change (b i).val (χ.val * τ) • v i = (b i).val (τ * χ.val) • v i
  rw [mul_comm χ.val τ]

/-- Multiplication by a translated regular function preserves polynomiality. -/
theorem isPolynomialOn_regular_mul_translate_smul {f : unramifiedCharacters ν → W}
    (hf : IsPolynomialOn Set.univ (fun χ => f χ.val)) (d : unramifiedRegularFunctions ν)
    (τ : unramifiedCharacters ν) :
    IsPolynomialOn Set.univ (fun χ => d.val (χ.val * τ) • f χ.val) := by
  obtain ⟨n, b, v, hb⟩ := hf.regular_smul (unramifiedRegularTranslation ν τ d)
  refine ⟨n, b, v, fun χ => (Eq.trans ?_ (hb χ))⟩
  change d.val (χ.val * τ) • f χ.val = d.val (τ * χ.val) • f χ.val
  rw [mul_comm χ.val τ]

/-- Translation by `τ` preserves the interior of a set that is stable under translation by `τ`. -/
theorem mul_mem_interior_of_forall_mul_mem [ContinuousMul (unramifiedCharacters ν)]
    {D : Set (unramifiedCharacters ν)} (τ : unramifiedCharacters ν)
    (hD : ∀ z ∈ D, z * τ ∈ D) {z : unramifiedCharacters ν} (hz : z ∈ interior D) :
    z * τ ∈ interior D := by
  have hopen : IsOpen ((fun x => x * τ⁻¹) ⁻¹' interior D) :=
    (continuous_id.mul continuous_const).isOpen_preimage _ isOpen_interior
  have hsub : (fun x => x * τ⁻¹) ⁻¹' interior D ⊆ D := by
    intro x hx
    have h := hD _ (interior_subset hx)
    simpa only [inv_mul_cancel_right] using h
  exact interior_maximal hsub hopen (by simpa only [Set.mem_preimage, mul_inv_cancel_right] using hz)

/-- **Covariance of a regular family by the identity principle.** Let `N = d · c` on the
interior `D°` of the domain `D` of `c`, with `N` polynomial and `D°` nonempty and stable under
translation by `τ`. If `c(zτ) ∘ P = Q ∘ c(z)` whenever `z, zτ ∈ D`, then
`d(z) N(zτ)(P X) = d(zτ) Q(N(z) X)` for every `z`, provided polynomial families vanishing on a
nonempty open set vanish (`hId`). -/
theorem regular_smul_mul_eq_of_isOpen
    (hId : ∀ f : unramifiedCharacters ν → W, IsPolynomialOn Set.univ (fun χ => f χ.val) →
      ∀ {D : Set (unramifiedCharacters ν)}, IsOpen D → D.Nonempty → (∀ χ ∈ D, f χ = 0) →
        ∀ χ, f χ = 0)
    {D : Set (unramifiedCharacters ν)} (hD : (interior D).Nonempty)
    (d : unramifiedRegularFunctions ν) (N : unramifiedCharacters ν → V →ₗ[ℂ] W)
    (hN : IsPolynomialOperatorOn Set.univ (fun χ => N χ.val))
    (c : D → V →ₗ[ℂ] W)
    (hc : ∀ z (hz : z ∈ interior D), N z = d.val z • c ⟨z, interior_subset hz⟩)
    (τ : unramifiedCharacters ν) (hτ : ∀ z ∈ interior D, z * τ ∈ interior D)
    (P : V →ₗ[ℂ] V) (Q : W →ₗ[ℂ] W)
    (hcov : ∀ z (hz : z ∈ D) (hzτ : z * τ ∈ D) X, c ⟨z * τ, hzτ⟩ (P X) = Q (c ⟨z, hz⟩ X))
    (X : V) (z : unramifiedCharacters ν) :
    d.val z • N (z * τ) (P X) = d.val (z * τ) • Q (N z X) := by
  have hpoly : IsPolynomialOn Set.univ (fun χ : (Set.univ : Set (unramifiedCharacters ν)) =>
      d.val χ.val • N (χ.val * τ) (P X) - d.val (χ.val * τ) • Q (N χ.val X)) :=
    IsPolynomialOn.sub
      ((isPolynomialOn_mul_translate (f := fun χ => N χ (P X)) (hN (P X)) τ).regular_smul d)
      (isPolynomialOn_regular_mul_translate_smul (f := fun χ => Q (N χ X))
        ((hN X).linearMap Q) d τ)
  have hzero : ∀ χ ∈ interior D,
      d.val χ • N (χ * τ) (P X) - d.val (χ * τ) • Q (N χ X) = 0 := by
    intro χ hχ
    have hχτ := hτ χ hχ
    rw [hc χ hχ, hc (χ * τ) hχτ, LinearMap.smul_apply, LinearMap.smul_apply,
      hcov χ (interior_subset hχ) (interior_subset hχτ) X, map_smul, smul_smul, smul_smul,
      mul_comm, sub_self]
  exact sub_eq_zero.mp
    (hId (fun χ => d.val χ • N (χ * τ) (P X) - d.val (χ * τ) • Q (N χ X)) hpoly
      isOpen_interior hD hzero z)

/-- The values `d⁻¹ N` satisfy the covariance wherever both denominators are nonzero. -/
theorem regular_inv_smul_mul_eq_of_isOpen
    (hId : ∀ f : unramifiedCharacters ν → W, IsPolynomialOn Set.univ (fun χ => f χ.val) →
      ∀ {D : Set (unramifiedCharacters ν)}, IsOpen D → D.Nonempty → (∀ χ ∈ D, f χ = 0) →
        ∀ χ, f χ = 0)
    {D : Set (unramifiedCharacters ν)} (hD : (interior D).Nonempty)
    (d : unramifiedRegularFunctions ν) (N : unramifiedCharacters ν → V →ₗ[ℂ] W)
    (hN : IsPolynomialOperatorOn Set.univ (fun χ => N χ.val))
    (c : D → V →ₗ[ℂ] W)
    (hc : ∀ z (hz : z ∈ interior D), N z = d.val z • c ⟨z, interior_subset hz⟩)
    (τ : unramifiedCharacters ν) (hτ : ∀ z ∈ interior D, z * τ ∈ interior D)
    (P : V →ₗ[ℂ] V) (Q : W →ₗ[ℂ] W)
    (hcov : ∀ z (hz : z ∈ D) (hzτ : z * τ ∈ D) X, c ⟨z * τ, hzτ⟩ (P X) = Q (c ⟨z, hz⟩ X))
    (X : V) (z : unramifiedCharacters ν) (hz : d.val z ≠ 0) (hzτ : d.val (z * τ) ≠ 0) :
    (d.val (z * τ))⁻¹ • N (z * τ) (P X) = Q ((d.val z)⁻¹ • N z X) := by
  have h := regular_smul_mul_eq_of_isOpen hId hD d N hN c hc τ hτ P Q hcov X z
  calc (d.val (z * τ))⁻¹ • N (z * τ) (P X)
      = (d.val (z * τ))⁻¹ • (d.val z)⁻¹ • (d.val z • N (z * τ) (P X)) := by
        rw [smul_smul (d.val z)⁻¹, inv_mul_cancel₀ hz, one_smul]
    _ = (d.val (z * τ))⁻¹ • (d.val z)⁻¹ • (d.val (z * τ) • Q (N z X)) := by rw [h]
    _ = Q ((d.val z)⁻¹ • N z X) := by
        rw [smul_smul (d.val z)⁻¹, smul_smul, mul_comm (d.val z)⁻¹, ← mul_assoc,
          inv_mul_cancel₀ hzτ, one_mul, map_smul]

end Identity

/-! ### Compact self-twist operators at equal characters -/

section SelfTwist

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (A : SmoothRep.{0, uG, uV} ℂ M)
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U) (K : OpenSubgroup G)
  (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)

/-- For an admissible irreducible `A`, the compact self-twist operators of two self-twists by equal
characters coincide (Schur, `productCompactSelfTwistEquiv_independent`). -/
theorem productCompactSelfTwistEquiv_eq_of_eq (hA : A.IsAdmissible)
    (hi : A.representation.IsIrreducible) {χ₁ χ₂ : unramifiedCharacters ν} (hχ : χ₁ = χ₂)
    (e₁ : A.representation.Equiv
      (A.twist χ₁.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ₁)).representation)
    (e₂ : A.representation.Equiv
      (A.twist χ₂.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ₂)).representation) :
    productCompactSelfTwistEquiv ν A h K hP hK hν hr χ₁ e₁ =
      productCompactSelfTwistEquiv ν A h K hP hK hν hr χ₂ e₂ := by
  subst hχ
  exact productCompactSelfTwistEquiv_independent ν A h K hP hK hν hr hA hi χ₁ e₁ e₂

end SelfTwist

/-! ### Smooth orbit sections with a prescribed compact picture -/

section Sections

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [LocallyCompactSpace G]
  {M : Subgroup G} {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {J : Type uJ} (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)) [Fintype J]

/-- **A smooth orbit section with prescribed compact picture.** A finite smooth family `Fc` of
compact pictures with the covariance `Fc(z · s) = s · Fc(z)` under the unitary stabilizer is the
compact restriction of the parameter pullback of an actual smooth orbit section. -/
theorem exists_productInducedSmoothOrbitSection
    (Fc : (J → Circle) → ProductInducedCompactPicture h K π.obj)
    (hFc : Fc ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj))
    (hcov : ∀ (s : unitaryClassTwistStabilizer ν (Quotient.mk _ π)) (z : J → Circle),
      Fc (z * unitaryStabilizerTorusHom ν e (Quotient.mk _ π) s) =
        unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π s (Fc z)) :
    ∃ Ψ : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
      productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        (productInducedOrbitPullback ν π e h hU Ψ.val) = Fc := by
  let F : productInducedSmoothFamilies ν e h K hP hK hν hr hU hPK π :=
    ⟨(productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).symm Fc, by
      change productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
        ((productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj).symm Fc) ∈
          finiteSmoothEquivariantFamilies J (ProductInducedCompactPicture h K π.obj)
            (unitaryStabilizerTorusHom ν e (Quotient.mk _ π))
            (unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π)
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨hFc, hcov⟩⟩
  refine ⟨productInducedSmoothOrbitExtension ν π e h hU K hP hK hν hr hPK F, ?_⟩
  change productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
    (productInducedOrbitPullback ν π e h hU
      (productInducedOrbitExtension ν π e h hU K hP hK hν hr hPK F)) = Fc
  rw [productInducedOrbitPullback_extension]
  exact LinearEquiv.apply_symm_apply _ Fc

end Sections

end Langlands.Plancherel
