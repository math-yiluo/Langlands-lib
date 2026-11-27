import Langlands.CommutativeAlgebra.SmoothDvrPrimeLocalization
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes

/-! # Stalks of smooth schemes over a DVR at generic points of the closed fibre -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AlgebraicGeometry.SmoothDvrStalk

variable (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of V))

/-- The structure map from the ring to a stalk of a scheme over its spectrum. -/
noncomputable def stalkStructureMap (x : T) : CommRingCat.of V ⟶ T.presheaf.stalk x :=
  ((Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫
    (Spec (CommRingCat.of V)).presheaf.germ ⊤ (t.base x) trivial) ≫ t.stalkMap x

omit [IsDomain V] [IsDiscreteValuationRing V] in
theorem fromSpecStalk_comp (x : T) :
    T.fromSpecStalk x ≫ t = Spec.map (stalkStructureMap V t x) := by
  rw [stalkStructureMap, Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk t,
    Spec.fromSpecStalk_eq]

/-- At a generic point of the closed fibre of a smooth scheme over a discrete valuation
ring, the stalk is a discrete valuation ring of ramification index one over the base. -/
theorem stalk_isRamificationIndexOne [Smooth t] (η : T)
    (hηs : t.base η = closedPoint V)
    (hgen : ∀ y : T, y ⤳ η → t.base y = closedPoint V → y = η)
    [Algebra V (T.presheaf.stalk η)]
    (hφ : algebraMap V (T.presheaf.stalk η) = (stalkStructureMap V t η).hom) :
    ∃ _ : IsLocalHom (algebraMap V (T.presheaf.stalk η)),
      IsRamificationIndexOne V (T.presheaf.stalk η) := by
  classical
  let O := T.presheaf.stalk η
  let φ := stalkStructureMap V t η
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfac : T.fromSpecStalk η ≫ t = Spec.map φ := fromSpecStalk_comp V t η
  have hbase : ∀ 𝔮 : PrimeSpectrum O,
      t.base ((T.fromSpecStalk η).base 𝔮) = (Spec.map φ).base 𝔮 := fun 𝔮 => by
    rw [← hfac]; rfl
  have hcomap : ∀ 𝔮 : PrimeSpectrum O,
      ((Spec.map φ).base 𝔮).asIdeal = 𝔮.asIdeal.comap φ.hom := fun _ => rfl
  -- Primes of the stalk containing the uniformizer are maximal.
  have key : ∀ 𝔮 : PrimeSpectrum O, φ.hom π ∈ 𝔮.asIdeal → 𝔮 = closedPoint O := by
    intro 𝔮 hπ𝔮
    have hy : t.base ((T.fromSpecStalk η).base 𝔮) = closedPoint V := by
      rw [hbase]
      apply PrimeSpectrum.ext
      change ((Spec.map φ).base 𝔮).asIdeal = maximalIdeal V
      rw [hcomap]
      have hne : 𝔮.asIdeal.comap φ.hom ≠ ⊥ := by
        intro h
        have hmem : π ∈ 𝔮.asIdeal.comap φ.hom := hπ𝔮
        rw [h] at hmem
        exact hπ.ne_zero (Ideal.mem_bot.mp hmem)
      exact IsLocalRing.eq_maximalIdeal
        (Ring.DimensionLEOne.maximalOfPrime hne (Ideal.comap_isPrime φ.hom 𝔮.asIdeal))
    have hyη : (T.fromSpecStalk η).base 𝔮 ⤳ η := by
      have hmem : (T.fromSpecStalk η).base 𝔮 ∈ Set.range (T.fromSpecStalk η).base :=
        ⟨𝔮, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    have heq := hgen _ hyη hy
    apply (T.fromSpecStalk η).isEmbedding.injective
    rw [heq, Scheme.fromSpecStalk_closedPoint]
  -- The structure map pulls back the maximal ideal to the maximal ideal.
  have hmax : (maximalIdeal O).comap φ.hom = maximalIdeal V := by
    have h1 : ((Spec.map φ).base (closedPoint O)).asIdeal = maximalIdeal V := by
      rw [← hbase, Scheme.fromSpecStalk_closedPoint, hηs]; rfl
    rw [← h1, hcomap]; rfl
  -- An affine open neighbourhood and its coordinate ring.
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  let A := Γ(T, U)
  let ψ : CommRingCat.of V ⟶ Γ(T, U) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ t.appLE ⊤ U le_top
  let : Algebra V A := ψ.hom.toAlgebra
  have : Algebra.Smooth V A := by
    have h1 : (t.appLE ⊤ U le_top).hom.Smooth :=
      t.smooth_appLE (isAffineOpen_top _) hU le_top
    have h2 : ψ.hom.Smooth := RingHom.Smooth.comp
      (RingHom.Smooth.of_bijective
        (Scheme.ΓSpecIso (CommRingCat.of V)).symm.commRingCatIsoToRingEquiv.bijective) h1
    exact RingHom.smooth_algebraMap.mp h2
  let : Algebra A O := T.presheaf.algebra_section_stalk ⟨η, hηU⟩
  have hloc : IsLocalization.AtPrime O (hU.primeIdealOf ⟨η, hηU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨η, hηU⟩
  let p := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal
  -- The structure map factors through the coordinate ring.
  have hfacA : φ = ψ ≫ T.presheaf.germ U η hηU := by
    simp only [φ, ψ, stalkStructureMap, Category.assoc, Scheme.Hom.appLE,
      TopCat.Presheaf.germ_res]
    congr 1
    exact Scheme.Hom.germ_stalkMap t ⊤ η trivial
  have : IsScalarTower V A O := IsScalarTower.of_algebraMap_eq' (by
    rw [hφ]
    change φ.hom = (T.presheaf.germ U η hηU).hom.comp ψ.hom
    rw [hfacA]
    rfl)
  have hp : (maximalIdeal V).map (algebraMap V A) ≤ p := by
    rw [Ideal.map_le_iff_le_comap]
    intro v hv
    rw [Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff O p,
      ← IsScalarTower.algebraMap_apply, hφ]
    have h : v ∈ (maximalIdeal O).comap φ.hom := hmax ▸ hv
    exact h
  have hmin : ∀ q : Ideal A, q.IsPrime → (maximalIdeal V).map (algebraMap V A) ≤ q → q ≤ p →
      q = p := by
    intro q hq hmq hqp
    have hdisj : Disjoint (p.primeCompl : Set A) q :=
      Set.disjoint_left.mpr fun a ha haq => ha (hqp haq)
    have hQ : (q.map (algebraMap A O)).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint p.primeCompl O q hq hdisj
    have hπQ : φ.hom π ∈ q.map (algebraMap A O) := by
      have h1 : algebraMap V A π ∈ q :=
        hmq (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit))
      have h2 := Ideal.mem_map_of_mem (algebraMap A O) h1
      rwa [← IsScalarTower.algebraMap_apply, hφ] at h2
    have hQm : q.map (algebraMap A O) = maximalIdeal O :=
      congrArg PrimeSpectrum.asIdeal (key ⟨_, hQ⟩ hπQ)
    calc q = (q.map (algebraMap A O)).comap (algebraMap A O) :=
          (IsLocalization.under_map_of_isPrime_disjoint p.primeCompl O hq hdisj).symm
      _ = (maximalIdeal O).comap (algebraMap A O) := by rw [hQm]
      _ = p := IsLocalization.AtPrime.under_maximalIdeal O p
  have hlh : IsLocalHom (algebraMap V O) :=
    CommutativeAlgebra.SmoothDvrPrimeLocalization.isLocalHom_algebraMap (O := O) p hp
  exact ⟨hlh, CommutativeAlgebra.SmoothDvrPrimeLocalization.isRamificationIndexOne p hp hmin⟩

end Langlands.AlgebraicGeometry.SmoothDvrStalk
