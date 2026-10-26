import Langlands.Representation.Classification.MaximalConeSelection
import Langlands.Representation.Classification.MaximalConeQuotient
import Langlands.Representation.Classification.MaximalConeLifting
import Langlands.Representation.Exponents.RealPartExistence
import Langlands.Representation.Classification.ParabolicConeSubgroupProof
import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyStatement
import Langlands.Representation.Twist.AdmissibilityProof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.Representation.Shahidi.IntertwiningPadic
import Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationStatement

/-!
# Assembly of the maximal-cone selection

The maximal-cone statement follows from four published propositions: finiteness
of dual exponents, existence of block cones, finite generation of opposite
Jacquet modules, and the dual-opposite tempered sufficiency criterion on product
Levis.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric
open scoped BigOperators

universe uF uV

namespace MaximalConeAssembly

variable {n : ℕ}

/-- The numerical cone conditions are the fields of `MaximalConePolygon.IsCone`. -/
theorem isCone_of_numerical {B C : BlockShape n} {r : Fin B.length → ℝ}
    {q : Fin B.length → Fin C.length} {t : Fin C.length → ℝ}
    (h : GLBlockConeNumericalConditions B C r q t) : MaximalConePolygon.IsCone B r C q t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Precomposition with a map of block indices, as a homomorphism. -/
def precomp {ℓ m : ℕ} {M : Type*} [Monoid M] (q : Fin ℓ → Fin m) :
    (Fin m → M) →* (Fin ℓ → M) where
  toFun a := a ∘ q
  map_one' := rfl
  map_mul' _ _ := rfl

end MaximalConeAssembly

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}

/-- The whole normalized opposite Jacquet module of an irreducible admissible
representation along a dual exponent has an irreducible admissible quotient on
which the block scalars act by that exponent. Finite generation of the opposite
Jacquet module is an explicit hypothesis. -/
theorem exists_irreducible_oppositeJacquet_quotient
    (hfg : Parabolic.OppositeJacquetFiniteGenerationStatement.{uF, uV})
    {C : BlockShape n} {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)}
    (hi : Representation.IsIrreducible A.ρ) (ha : letI := T.topology; IsAdmissible A.ρ)
    {χC : (Fin C.length → F.Carrierˣ) →* ℂˣ} (h : T.IsDualJacquetExponent C A χC) :
    letI := T.topology
    ∃ S : Rep.{uV} ℂ (C.Levi F.Carrier), Representation.IsIrreducible S.ρ ∧
      IsAdmissible S.ρ ∧
      Classification.HasScalarCharacter S.ρ (C.blockScalarLevi F.Carrier) χC ∧
      ∃ f : (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ.IntertwiningMap S.ρ,
        Function.Surjective f := by
  let := T.topology
  have := T.leviTopologicalGroup C
  obtain ⟨-, hne⟩ := h
  obtain ⟨φ, hφ, hne⟩ := (Subrepresentation.ne_bot_iff_exists _).mp hne
  have hfinA : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) A.ρ.asModule := by
    let := hi
    infer_instance
  have hfin := hfg p F T n C A ha.1 hfinA
  have hadm : IsAdmissible (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ :=
    Parabolic.standardOppositeJacquetAdmissibility p F T n C A A.ρ ha
  let ψ : Module.Dual ℂ (CuspidalJacquetMultiplicity.oppositeJacquet T C A) := φ
  refine MaximalConeQuotient.exists_irreducible_quotient (T.leviCompactOpenCofinal C)
    (C.blockScalarLevi F.Carrier) ?_ χC _ hfin hadm ψ ?_ ?_
  · intro c g
    exact (Subgroup.mem_center_iff.mp (C.blockScalarLevi_mem_center F.Carrier c) g).symm
  · intro h0
    apply hne
    exact h0
  · intro c v
    have := (mem_commutativeCharacterSpace_one _ _ _).mp hφ c
    exact LinearMap.congr_fun this v

/-- The tempered-sufficiency test for the twisted quotient: every dual
eigencharacter of a refined opposite Jacquet module has nonpositive partial real
parts inside each outer block, provided no cone of an exponent of `A` strictly
dominates `(C, t)`. -/
theorem prefix_nonpos_of_maximal (hcone : GLBlockConeExistenceStatement)
    {A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)} {C : BlockShape n} {t : Fin C.length → ℝ}
    (hmax : ∀ (B' : BlockShape n) (χ' : (Fin B'.length → F.Carrierˣ) →* ℂˣ)
      (r' : Fin B'.length → ℝ) (C' : BlockShape n) (q' : Fin B'.length → Fin C'.length)
      (t' : Fin C'.length → ℝ), T.IsDualJacquetExponent B' A χ' → T.IsRealPartOf χ' r' →
      MaximalConePolygon.IsCone B' r' C' q' t' → ¬ GLBlockPositivePartStrictlyDominates C' t' C t)
    {S : Rep.{uV} ℂ (C.Levi F.Carrier)}
    (f : (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ.IntertwiningMap S.ρ)
    (hf : Function.Surjective f) {ω : (Fin C.length → F.Carrierˣ) →* ℂˣ}
    (hω : Classification.HasScalarCharacter (T.leviRealPowerTwist C (-t) S.ρ)
      (C.blockScalarLevi F.Carrier) ω)
    (hunit : ∀ a, ‖(ω a : ℂ)‖ = 1) (D : BlockRefinement C)
    (ψ : (Fin (C.flatten D).length → F.Carrierˣ) →* ℂˣ) (s : Fin (C.flatten D).length → ℝ)
    (φ : Module.Dual ℂ (RefinedOppositeJacquetModule C D (T.leviRealPowerTwist C (-t) S.ρ)))
    (hψ : letI := T.topology; IsOpen (ψ.ker : Set (Fin (C.flatten D).length → F.Carrierˣ)))
    (hφ : φ ≠ 0)
    (heig : ∀ (a : Fin (C.flatten D).length → F.Carrierˣ) (v : S),
      φ (T.normalizedRefinedOppositeJacquet C D (T.leviRealPowerTwist C (-t) S.ρ)
          (flattenedLeviEquiv F.Carrier C D ((C.flatten D).blockScalarLevi F.Carrier a))
          (refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ) v)) =
        (ψ a : ℂ) * φ (refinedOppositeJacquetMk C D (T.leviRealPowerTwist C (-t) S.ρ) v))
    (hs : T.IsRealPartOf ψ s) (j : Fin C.length) (i : Fin (D j).length) :
    (∑ k ∈ Finset.univ.filter (fun k : Fin (D j).length => k ≤ i),
      s (C.flattenBlockEquiv D ⟨j, k⟩)) ≤ 0 := by
  set tp : Fin (C.flatten D).length → ℝ := fun k => t (C.flattenOuter D k) with htp
  have hexp := T.isDualJacquetExponent_flatten_of_quotient C D f hf t hψ hφ heig
  have hr := T.isRealPartOf_mul_leviRealPowerCharacter (C.flatten D) hs tp
  obtain ⟨C'', q'', t'', hc''⟩ := hcone n (C.flatten D)
    (fun k => s k + ((C.flatten D).size k : ℝ) * tp k)
  have hnot := hmax _ _ _ C'' q'' t'' hexp hr (MaximalConeAssembly.isCone_of_numerical hc'')
  have hfib := T.sum_fibre_eq_zero_of_unitary C D _ hω hunit hφ heig hs
  have hptot : ∀ j' : Fin C.length,
      (∑ k ∈ Finset.univ.filter (fun k => C.flattenOuter D k = j'),
        (s k + ((C.flatten D).size k : ℝ) * tp k)) = (C.size j' : ℝ) * t j' := by
    intro j'
    rw [Finset.sum_add_distrib, hfib j', zero_add, C.size_eq_sum_flattenOuter D j',
      Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    rw [htp]
    simp only [hk]
  have hres := MaximalConePolygon.residual_nonpos_of_not_strictlyDominates
    (C.flattenOuter_mono D) (C.size_eq_sum_flattenOuter D) hptot
    (MaximalConeAssembly.isCone_of_numerical hc'') hnot (C.flattenBlockEquiv D ⟨j, i⟩)
  rw [← C.sum_filter_flattenOuter_le D s j i]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k hk => ?_) hres
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  rw [htp]
  simp only [hk.1]
  ring

end PadicField.TopologicalData

/-- The maximal-cone selection, from finiteness of dual exponents, existence of
block cones, finite generation of opposite Jacquet modules and the dual-opposite
tempered sufficiency criterion. -/
theorem glMaximalConeJacquetQuotient_of
    (hfin : GLDualJacquetFinitenessStatement.{uF, uV})
    (hcone : GLBlockConeExistenceStatement)
    (hfg : Parabolic.OppositeJacquetFiniteGenerationStatement.{uF, uV})
    (htemp : GLProductLeviDualOppositeTemperedSufficiencyStatement.{uF, uV}) :
    GLMaximalConeJacquetQuotientStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n hn A hi ha
  classical
  let R : (B : BlockShape n) → Set (Fin B.length → ℝ) := fun B =>
    {r | ∃ χ, T.IsDualJacquetExponent B A χ ∧ T.IsRealPartOf χ r}
  have hR : ∀ B, (R B).Finite := by
    intro B
    let g : ((Fin B.length → F.Carrierˣ) →* ℂˣ) → (Fin B.length → ℝ) := fun χ =>
      if h : ∃ r, T.IsRealPartOf χ r then h.choose else 0
    refine ((hfin p F T n hn B A hi ha).1.image g).subset ?_
    rintro r ⟨χ, hχ, hr⟩
    refine ⟨χ, hχ, ?_⟩
    have h : ∃ r, T.IsRealPartOf χ r := ⟨r, hr⟩
    simp only [g, h, ↓reduceDIte]
    exact h.choose_spec.eq hr
  have hne : ∃ (B : BlockShape n) (r : Fin B.length → ℝ) (C : BlockShape n)
      (q : Fin B.length → Fin C.length) (t : Fin C.length → ℝ),
      r ∈ R B ∧ MaximalConePolygon.IsCone B r C q t := by
    let B₁ : BlockShape n :=
      { length := 1, size := fun _ => n, positive := fun _ => hn, sum_eq := by simp }
    obtain ⟨χ₁, hχ₁⟩ := T.exists_isDualJacquetExponent_of_length_eq_one (B := B₁) rfl hi ha
    obtain ⟨r₁, hr₁⟩ := T.exists_isRealPartOf χ₁ hχ₁.1
    obtain ⟨C, q, t, hc⟩ := hcone n B₁ r₁
    exact ⟨B₁, r₁, C, q, t, ⟨χ₁, hχ₁, hr₁⟩, MaximalConeAssembly.isCone_of_numerical hc⟩
  obtain ⟨B, r, C, q, t, ⟨χ, hχ, hr⟩, hc, hmax⟩ :=
    MaximalConePolygon.exists_maximal_cone R hR hne
  let χC : (Fin C.length → F.Carrierˣ) →* ℂˣ := χ.comp (MaximalConeAssembly.precomp q)
  have hχC : ∀ a, χC a = χ (a ∘ q) := fun a => rfl
  have hexpC : T.IsDualJacquetExponent C A χC :=
    T.isDualJacquetExponent_coarsen hc.mono hc.size_eq hχ hχC
  have hrealC : T.IsRealPartOf χC (fun j => (C.size j : ℝ) * t j) :=
    T.isRealPartOf_coarsen hr hχC _ hc.total
  have hsub := glBlockCoarseningSubgroups.{uF} n B C q hc.mono hc.surj hc.size_eq F.Carrier
  obtain ⟨S, hSi, hSa, hSsc, f, hf⟩ := T.exists_irreducible_oppositeJacquet_quotient hfg hi ha hexpC
  have hmax' : ∀ (B' : BlockShape n) (χ' : (Fin B'.length → F.Carrierˣ) →* ℂˣ)
      (r' : Fin B'.length → ℝ) (C' : BlockShape n) (q' : Fin B'.length → Fin C'.length)
      (t' : Fin C'.length → ℝ), T.IsDualJacquetExponent B' A χ' → T.IsRealPartOf χ' r' →
      MaximalConePolygon.IsCone B' r' C' q' t' →
      ¬ GLBlockPositivePartStrictlyDominates C' t' C t :=
    fun B' χ' r' C' q' t' h1 h2 h3 => hmax B' r' C' q' t' ⟨χ', h1, h2⟩ h3
  let ω : (Fin C.length → F.Carrierˣ) →* ℂˣ :=
    χC * (T.leviRealPowerCharacter C (-t)).comp (C.blockScalarLevi F.Carrier)
  have hω : Classification.HasScalarCharacter (T.leviRealPowerTwist C (-t) S.ρ)
      (C.blockScalarLevi F.Carrier) ω := by
    intro a v
    rw [T.leviRealPowerTwist_apply, hSsc a v, smul_smul]
    simp only [ω, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul, mul_comm]
  have hunit : ∀ a, ‖(ω a : ℂ)‖ = 1 := by
    intro a
    rw [T.isRealPartOf_mul_leviRealPowerCharacter C hrealC (-t) a]
    refine Finset.prod_eq_one fun j _ => ?_
    simp
  refine ⟨B, χ, r, C, q, t, χC, S, hχ, hr, hc.mono, hc.surj, hc.size_eq, hc.anti, hc.total,
    hc.prefix_le, hsub.1, hsub.2, hχC, hexpC, hrealC, hSi, hSa, hSsc, ⟨f, hf⟩, ?_, ?_⟩
  · intro _ _ _ μ _
    exact htemp p F T n hn C (Rep.of (T.leviRealPowerTwist C (-t) S.ρ)) ω
      ((isIrreducible_twist_iff _ _).mpr hSi)
      ((isAdmissible_twist_iff _ _ (T.isOpen_ker_leviRealPowerCharacter C (-t))).mpr hSa)
      hω hunit
      (fun D ψ s φ hψ hφ heig hs j i =>
        T.prefix_nonpos_of_maximal hcone hmax' f hf hω hunit D ψ s φ hψ hφ heig hs j i) μ
  intro B' χ' r' C' q' t' h1 h2 h3 h4 h5 h6 h7 h8
  exact hmax' B' χ' r' C' q' t' h1 h2 ⟨h3, h4, h5, h6, h7, h8⟩

end Langlands
