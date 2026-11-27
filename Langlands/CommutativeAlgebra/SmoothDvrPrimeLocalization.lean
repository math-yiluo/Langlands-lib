import Langlands.AlgebraicGeometry.DvrSmootheningStatement
import Langlands.CommutativeAlgebra.SmoothDVRUniformizerDivision
import Langlands.CommutativeAlgebra.SeparablyClosedRationalPointProof
import Langlands.AlgebraicGeometry.PointTopology.SeparablyClosedDensity

/-! # Localizations of smooth algebras over a DVR at generic points of the special fibre -/

universe u

open scoped TensorProduct
open IsLocalRing

namespace Langlands.CommutativeAlgebra.SmoothDvrPrimeLocalization

variable {V A O : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [CommRing A] [Algebra V A]
  [CommRing O] [Algebra A O] [Algebra V O] [IsScalarTower V A O]
  (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime O p] [IsLocalRing O]

include p in
/-- The structure map to the localization is local when `p` lies over the maximal ideal. -/
theorem isLocalHom_algebraMap (hp : (maximalIdeal V).map (algebraMap V A) ≤ p) :
    IsLocalHom (algebraMap V O) := by
  refine ⟨fun x hx => ?_⟩
  by_contra hxu
  have hxm : x ∈ maximalIdeal V := hxu
  have hA : algebraMap V A x ∈ p := hp (Ideal.mem_map_of_mem _ hxm)
  have hO : algebraMap A O (algebraMap V A x) ∈ maximalIdeal O :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff O p _).mpr hA
  rw [← IsScalarTower.algebraMap_apply] at hO
  exact hO hx

variable [Algebra.Smooth V A]

include p in
/-- The maximal ideal of the discrete valuation ring generates the maximal ideal of the
localization at a prime which is minimal over it. -/
theorem maximalIdeal_map_eq (hp : (maximalIdeal V).map (algebraMap V A) ≤ p)
    (hmin : ∀ q : Ideal A, q.IsPrime → (maximalIdeal V).map (algebraMap V A) ≤ q → q ≤ p →
      q = p) :
    (maximalIdeal V).map (algebraMap V O) = maximalIdeal O := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmV : maximalIdeal V = Ideal.span {π} := hπ.maximalIdeal_eq
  have hmapA : (maximalIdeal V).map (algebraMap V A) = Ideal.span {algebraMap V A π} := by
    rw [hmV, Ideal.map_span, Set.image_singleton]
  have hmapO : (maximalIdeal V).map (algebraMap V O) = Ideal.span {algebraMap V O π} := by
    rw [hmV, Ideal.map_span, Set.image_singleton]
  have hπO : algebraMap V O π = algebraMap A O (algebraMap V A π) :=
    IsScalarTower.algebraMap_apply V A O π
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply V A O]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff O p _).mpr
      (hp (Ideal.mem_map_of_mem _ hx))
  · intro y hy
    rw [hmapO]
    -- Every prime of `O` containing the uniformizer is the maximal ideal.
    have hprime : ∀ P : Ideal O, P.IsPrime → algebraMap V O π ∈ P → P = maximalIdeal O := by
      intro P hP hπP
      let q := P.comap (algebraMap A O)
      have hq : q.IsPrime := Ideal.comap_isPrime _ _
      have hqp : q ≤ p := by
        intro a ha
        by_contra hap
        have hu : IsUnit (algebraMap A O a) :=
          IsLocalization.map_units O (⟨a, hap⟩ : p.primeCompl)
        exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
      have hπq : (maximalIdeal V).map (algebraMap V A) ≤ q := by
        rw [hmapA, Ideal.span_le, Set.singleton_subset_iff]
        change algebraMap A O (algebraMap V A π) ∈ P
        rw [← hπO]
        exact hπP
      have hqeq : q = p := hmin q hq hπq hqp
      calc P = q.map (algebraMap A O) := (IsLocalization.map_under p.primeCompl O P).symm
        _ = p.map (algebraMap A O) := by rw [hqeq]
        _ = maximalIdeal O := IsLocalization.AtPrime.map_eq_maximalIdeal p O
    -- Hence `y` lies in the radical of `(π)`.
    have hrad : y ∈ (Ideal.span {algebraMap V O π}).radical := by
      rw [Ideal.radical_eq_sInf]
      refine Submodule.mem_sInf.mpr fun P hP => ?_
      obtain ⟨hle, hPp⟩ := hP
      rw [hprime P hPp (hle (Ideal.subset_span rfl))]
      exact hy
    obtain ⟨n, hn⟩ := hrad
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp hn
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
    obtain ⟨⟨b, t⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl z
    -- Clear denominators in `(b / t) * π = (a / s) ^ n`.
    simp only at hz hy
    have h2 : IsLocalization.mk' O (algebraMap V A π * b) t =
        IsLocalization.mk' O (a ^ n) (s ^ n) := by
      rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_pow, ← hz, ← hπO, mul_comm]
    have heq := (IsLocalization.mk'_eq_iff_eq).mp h2
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl O).mp heq
    -- The element `c t a` lies in every prime containing `π`.
    have hdvd : algebraMap V A π ∣ (c : A) * t * a := by
      apply SmoothDVRUniformizerDivision.dvd_of_forall_mem_prime hπ
      intro P hP hπP
      have hmem : (c : A) * ((t : A) * a ^ n) ∈ P := by
        rw [← hc]
        exact P.mul_mem_left _ (P.mul_mem_left _ (P.mul_mem_right _ hπP))
      rcases hP.mem_or_mem hmem with hcP | hatP
      · exact P.mul_mem_right _ (P.mul_mem_right _ hcP)
      rcases hP.mem_or_mem hatP with htP | haP
      · exact P.mul_mem_right _ (P.mul_mem_left _ htP)
      · exact P.mul_mem_left _ (hP.mem_of_pow_mem n haP)
    obtain ⟨e, he⟩ := hdvd
    refine Ideal.mem_span_singleton'.mpr ⟨IsLocalization.mk' O e (c * t * s), ?_⟩
    rw [mul_comm, hπO, IsLocalization.mul_mk'_eq_mk'_of_mul, ← he, IsLocalization.mk'_eq_iff_eq]
    congr 1
    push_cast
    ring

include p in
/-- The residue field of the localization at a prime minimal over the maximal ideal of the
discrete valuation ring is a geometrically reduced extension of the residue field of the
discrete valuation ring. -/
theorem isGeometricallyReduced_residueField [IsLocalHom (algebraMap V O)]
    (hp : (maximalIdeal V).map (algebraMap V A) ≤ p)
    (hmin : ∀ q : Ideal A, q.IsPrime → (maximalIdeal V).map (algebraMap V A) ≤ q → q ≤ p →
      q = p) :
    Algebra.IsGeometricallyReduced (ResidueField V) (ResidueField O) := by
  classical
  let k := ResidueField V
  let B := k ⊗[V] A
  let θ : A →ₐ[V] B := Algebra.TensorProduct.includeRight
  have hθ : Function.Surjective θ :=
    Algebra.TensorProduct.includeRight_surjective A residue_surjective
  have : Algebra.IsGeometricallyReduced k B :=
    Langlands.AlgebraicGeometry.PointTopology.isGeometricallyReduced_of_smooth k B
  have : IsReduced B := Algebra.isReduced_of_isGeometricallyReduced (k := k)
  -- The kernel of `A → k ⊗ A` is the ideal generated by the maximal ideal of `V`.
  have hker : RingHom.ker θ ≤ (maximalIdeal V).map (algebraMap V A) := by
    intro x hx
    have hx' : θ x = 0 := hx
    let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor A (maximalIdeal V)
    have he : e (Ideal.Quotient.mk _ x) = θ x := rfl
    have h0 : e (Ideal.Quotient.mk _ x) = 0 := by rw [he]; exact hx'
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((map_eq_zero_iff e e.injective).mp h0)
  have hkerp : RingHom.ker θ ≤ p := hker.trans hp
  let pB : Ideal B := p.map θ
  have hpB : pB.IsPrime := Ideal.map_isPrime_of_surjective hθ hkerp
  have hcomap : pB.comap θ = p := by
    show Ideal.comap θ (Ideal.map θ p) = p
    rw [Ideal.comap_map_of_surjective' θ hθ]
    exact sup_eq_left.mpr hkerp
  -- `pB` is a minimal prime of `B`.
  have hmB : pB ∈ minimalPrimes B := by
    refine ⟨⟨hpB, bot_le⟩, fun q hq hqp => ?_⟩
    obtain ⟨hqprime, -⟩ := hq
    have h1 : (q.comap θ).IsPrime := Ideal.comap_isPrime _ _
    have h2 : (maximalIdeal V).map (algebraMap V A) ≤ q.comap θ := by
      rw [Ideal.map_le_iff_le_comap]
      intro v hv
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have : θ (algebraMap V A v) = 0 := by
        rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
          show algebraMap V k v = 0 from (Ideal.Quotient.eq_zero_iff_mem).mpr hv,
          TensorProduct.zero_tmul]
      rw [this]
      exact q.zero_mem
    have h3 : q.comap θ ≤ p := by
      rw [← hcomap]
      exact Ideal.comap_mono hqp
    have h4 := hmin _ h1 h2 h3
    have hq : q = pB :=
      calc q = (q.comap θ).map θ := (Ideal.map_comap_of_surjective θ hθ q).symm
        _ = pB := by rw [h4]
    exact hq.symm.le
  -- The localization of `B` at `pB` is a geometrically reduced field.
  let L := Localization.AtPrime pB
  have : Ring.KrullDimLE 0 L := .of_isLocalization pB hmB L
  have hLfield : IsField L := Ring.KrullDimLE.isField_of_isReduced
  have : Algebra.IsGeometricallyReduced k L :=
    SeparablyClosedRationalPointProof.isGeometricallyReduced_localization pB.primeCompl
  -- The residue field of `O` is that field.
  let κ := ResidueField O
  let g : A →ₐ[V] κ := (IsScalarTower.toAlgHom V O κ).comp (IsScalarTower.toAlgHom V A O)
  let ρ : B →ₐ[k] κ :=
    Algebra.TensorProduct.lift (Algebra.ofId k κ) g (fun _ _ => Commute.all _ _)
  have hρθ : ∀ a : A, ρ (θ a) = residue O (algebraMap A O a) := by
    intro a
    show ρ (1 ⊗ₜ a) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hunit : ∀ y : pB.primeCompl, IsUnit (ρ y) := by
    rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := hθ y
    have ha : a ∉ p := fun ha => hy (Ideal.mem_map_of_mem θ ha)
    rw [hρθ, isUnit_iff_ne_zero, Ne, residue_eq_zero_iff]
    exact fun h => ha ((IsLocalization.AtPrime.to_map_mem_maximal_iff O p a).mp h)
  let ψ : L →ₐ[k] κ := IsLocalization.liftAlgHom hunit
  have hψinj : Function.Injective ψ := by
    let := hLfield.toField
    exact ψ.toRingHom.injective
  have hψsurj : Function.Surjective ψ := by
    intro w
    obtain ⟨y, rfl⟩ := residue_surjective w
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl y
    have hs : θ s ∈ pB.primeCompl := by
      intro h
      have h' : (s : A) ∈ Ideal.comap θ pB := h
      rw [hcomap] at h'
      exact s.2 h'
    refine ⟨IsLocalization.mk' L (θ a) ⟨θ s, hs⟩, ?_⟩
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_mk'_spec]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hρθ]
    rw [← map_mul, IsLocalization.mk'_spec']
  let e := AlgEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩
  exact Algebra.IsGeometricallyReduced.of_injective e.symm.toAlgHom e.symm.injective

include p in
/-- The localization of a smooth algebra over a discrete valuation ring at a prime minimal
over the maximal ideal has ramification index one over the discrete valuation ring. -/
theorem isRamificationIndexOne [IsLocalHom (algebraMap V O)]
    (hp : (maximalIdeal V).map (algebraMap V A) ≤ p)
    (hmin : ∀ q : Ideal A, q.IsPrime → (maximalIdeal V).map (algebraMap V A) ≤ q → q ≤ p →
      q = p) :
    Langlands.AlgebraicGeometry.IsRamificationIndexOne V O :=
  ⟨maximalIdeal_map_eq p hp hmin, isGeometricallyReduced_residueField p hp hmin⟩

end Langlands.CommutativeAlgebra.SmoothDvrPrimeLocalization
