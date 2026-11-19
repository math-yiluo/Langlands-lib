import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionFixedTensor
import Langlands.Representation.Plancherel.SmoothFamilyPrescribedValues
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! # Finitely many fixed-level sections realizing every fiber basis -/

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

open Langlands.Plancherel Langlands.Aubert.General Langlands.Induction
open scoped NNReal ContDiff

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ uB

/-- An equivariant family can equal a prescribed vector throughout a common
open neighborhood of a given parameter. The neighborhood is independent of the vector. -/
private theorem exists_local_equivariant_family
    {J : Type*} [Fintype J] {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S : Type*} [Group S] [Finite S]
    (τ : S →* (J → Circle)) (D : Representation ℂ S V) (hτ : Function.Injective τ)
    (z₀ : J → Circle) :
    ∃ O : Set (J → Circle), IsOpen O ∧ z₀ ∈ O ∧
      ∃ F : V → ((J → Circle) → V), ∀ v,
        F v ∈ finiteSmoothEquivariantFamilies J V τ D ∧ ∀ z ∈ O, F v z = v := by
  classical
  let : Fintype S := Fintype.ofFinite S
  let Z := Set.range fun s : S => z₀ * (τ s)⁻¹
  obtain ⟨p, hp, hp1, hp0⟩ := exists_isSmoothFiniteTorusFunction_lagrange Z (Set.finite_range _) z₀
  have hpz (s : S) (hs : s ≠ 1) : p (z₀ * (τ s)⁻¹) = 0 := by
    refine hp0 _ ⟨s, rfl⟩ fun h => hs (hτ ?_)
    have h' : (τ s)⁻¹ = 1 := by simpa using h
    rw [inv_eq_one.mp h', map_one]
  let cut (z : J → Circle) : ℂ := (Real.smoothTransition (4 * (p z).re - 2) : ℂ)
  have hcut : IsSmoothFiniteTorusFunction cut := by
    change ContDiff ℝ ∞ (fun x => (Real.smoothTransition (4 * (p (finiteTorusExp x)).re - 2) : ℂ))
    exact Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (Complex.reCLM.contDiff.comp hp)).sub contDiff_const))
  let O := {z : J → Circle | (3 : ℝ) / 4 < (p z).re} ∩
    ⋂ s : {s : S // s ≠ 1}, {z : J → Circle | (p (z * (τ s.val)⁻¹)).re < (1 : ℝ) / 2}
  have hO : IsOpen O := (isOpen_lt continuous_const (Complex.continuous_re.comp hp.continuous)).inter
    (isOpen_iInter_of_finite fun s => isOpen_lt
      (Complex.continuous_re.comp (hp.continuous.comp (continuous_id.mul continuous_const))) continuous_const)
  have hOz : z₀ ∈ O := by
    refine ⟨?_, Set.mem_iInter.mpr fun s => ?_⟩
    · change (3 : ℝ) / 4 < (p z₀).re
      rw [hp1, Complex.one_re]
      norm_num
    · change (p (z₀ * (τ s.val)⁻¹)).re < (1 : ℝ) / 2
      rw [hpz s.val s.property, Complex.zero_re]
      norm_num
  let F (v : V) (z : J → Circle) := ∑ s : S, cut (z * (τ s)⁻¹) • D s v
  refine ⟨O, hO, hOz, F, fun v => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · have hsum : F v = ∑ s : S, fun z => cut (z * (τ s)⁻¹) • D s v := by
      funext z
      simp only [F, Finset.sum_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun s _ => Submodule.subset_span
      ⟨⟨fun z => cut (z * (τ s)⁻¹), (isSmoothFiniteTorusFunction_mul_const_iff cut _).mpr hcut⟩,
        D s v, rfl⟩
  · intro t z
    change ∑ s : S, cut (z * τ t * (τ s)⁻¹) • D s v =
      D t (∑ s : S, cut (z * (τ s)⁻¹) • D s v)
    rw [map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft t⁻¹) _ _ fun s => ?_
    change cut (z * τ t * (τ s)⁻¹) • D s v =
      D t (cut (z * (τ (t⁻¹ * s))⁻¹) • D (t⁻¹ * s) v)
    rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul τ,
      map_inv, mul_inv_rev, inv_inv, mul_comm (τ s)⁻¹, ← mul_assoc]
  · intro z hz
    change ∑ s : S, cut (z * (τ s)⁻¹) • D s v = v
    rw [Fintype.sum_eq_single 1]
    · have hz1 : (3 : ℝ) / 4 < (p z).re := hz.1
      have hc : cut z = 1 := by
        simp only [cut, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4 * (p z).re - 2),
          Complex.ofReal_one]
      simp [hc]
    · intro s hs
      have hz0 : (p (z * (τ s)⁻¹)).re < (1 : ℝ) / 2 := (Set.mem_iInter.mp hz.2) ⟨s, hs⟩
      have hc : cut (z * (τ s)⁻¹) = 0 := by
        simp only [cut, Real.smoothTransition.zero_of_nonpos (by linarith : 4 * (p (z * (τ s)⁻¹)).re - 2 ≤ 0),
          Complex.ofReal_zero]
      rw [hc, zero_smul]

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (H : OpenSubgroup G) (hHK : H ≤ K)

set_option hygiene false in
local notation "CompactPicture" => ProductInducedCompactPicture h K π.obj
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK H
set_option hygiene false in
local notation "Fixed" => orbitSectionFixedCoefficients h K π H
set_option hygiene false in
local notation "fixedRestriction" => orbitSectionLevelFixedRestriction h K π ν e hU hP hK hν hr hPK H hHK
set_option hygiene false in
local notation "restriction" => productInducedSmoothOrbitCompactRestriction h hU ν π K hP hK hν hr hPK e
set_option hygiene false in
local notation "Stab" => unitaryClassTwistStabilizer ν (Quotient.mk _ π)
set_option hygiene false in
local notation "τ" => unitaryStabilizerTorusHom ν e (Quotient.mk _ π)
set_option hygiene false in
local notation "action" => unitaryStabilizerCompactRepresentation ν h K hP hK hν hr π

/-- The self-twist action preserves the actual fixed coefficient space. -/
private def levelStabilizerRepresentation : Representation ℂ Stab Fixed :=
  Representation.subrepresentation action Fixed (fun s v hv => by
    have hfix := (mem_orbitSectionFixedCoefficients_iff h K π H hHK _).mp hv
    refine (mem_orbitSectionFixedCoefficients_iff h K π H hHK _).mpr fun x => ?_
    have e := unramifiedStabilizerCompactRepresentation_action ν π h K hP hK hν hr
      (unitaryClassStabilizerInclusion ν (Quotient.mk _ π) s)
      ⟨x.val, hHK x.property.1, hHK x.property.2⟩ v
    rw [hfix x] at e
    exact e.symm)

set_option hygiene false in
local notation "levelAction" => levelStabilizerRepresentation h hP K hK ν π hν hr H hHK

/-- A finite smooth equivariant family with values in the fixed compact coefficient
space lifts to an actual smooth section at precisely that level. -/
private theorem exists_level_of_fixed_equivariantFamily
    (F : (J → Circle) → Fixed) (hF : F ∈ finiteSmoothEquivariantFamilies J Fixed τ levelAction) :
    ∃ q : SectionLevel, ∀ z, fixedRestriction q z = F z := by
  let E := productInducedSmoothFamilyRestriction h hU hP K hK hPK π ν hν hr e
  let A := productInducedSmoothOrbitFamilyEquiv ν π e h hU K hP hK hν hr hPK
  let v : finiteSmoothEquivariantFamilies J CompactPicture τ action :=
    ⟨fun z => (F z).val, ⟨mem_finiteSmoothFamilies_linearMap hF.1
        (orbitSectionFixedCoefficients h K π H).subtype,
      fun s z => congrArg Subtype.val (hF.2 s z)⟩⟩
  let q := A.symm (E.symm v)
  have hv : restriction q = v.val := by
    change (E (A q)).val = v.val
    rw [show A q = E.symm v from A.apply_symm_apply _, E.apply_symm_apply]
  have hlevel : q.val ∈ orbitSectionLevelSubmodule ν π e h hU K hP hK hν hr hPK H := by
    refine ⟨q.property, fun x => ?_⟩
    let k : K.prod K := ⟨x.val, hHK x.property.1, hHK x.property.2⟩
    let D := productInducedSmoothOrbitCompactRepresentation h hU ν π K hP hK hν hr hPK e
    have hfix : D k q = q := by
      apply productInducedSmoothOrbitCompactRestriction_injective h hU ν π K hP hK hν hr hPK e
      funext z
      have hcomp := productInducedOrbitRepresentation_restriction h hU ν π K hP hK hν hr hPK e k q.val z
      change restriction (D k q) z = productInducedCompactRepresentation h K π.obj k (restriction q z) at hcomp
      rw [hcomp, hv]
      exact (mem_orbitSectionFixedCoefficients_iff h K π H hHK _).mp (F z).property x
    exact congrArg Subtype.val hfix
  refine ⟨⟨q.val, hlevel⟩, fun z => Subtype.ext ?_⟩
  exact congrFun hv z

/-- A single finite collection of level sections realizes every vector of a
specified finite coefficient basis at every parameter. -/
def HasOrbitSectionLevelFiberGenerators {B : Type uB} (b : Module.Basis B ℂ Fixed) : Prop :=
  ∃ t : Finset SectionLevel, ∀ (z : J → Circle) (i : B),
    ∃ q ∈ t, fixedRestriction q z = b i

/-- For any finite basis of the fixed coefficient space, finitely many actual
level sections realize each basis vector at every parameter. -/
theorem exists_finite_orbitSectionLevel_fiber_generators [Finite Stab]
    {B : Type uB} [Fintype B] (b : Module.Basis B ℂ Fixed) :
    HasOrbitSectionLevelFiberGenerators h hU hP K hK hPK ν π hν hr e H hHK b := by
  classical
  choose O hO hpoint F hF hloc using fun z =>
    exists_local_equivariant_family τ levelAction (unitaryStabilizerTorusHom_injective ν e _) z
  obtain ⟨s, hs⟩ := (isCompact_univ : IsCompact (Set.univ : Set (J → Circle))).elim_finite_subcover
    O hO (fun z _ => Set.mem_iUnion.mpr ⟨z, hpoint z⟩)
  choose q hq using fun (z : J → Circle) (i : B) =>
    exists_level_of_fixed_equivariantFamily h hU hP K hK hPK ν π hν hr e H hHK
      (F z (b i)) (hF z (b i))
  refine ⟨(s.product Finset.univ).image fun p => q p.1 p.2, fun z i => ?_⟩
  obtain ⟨p, hp, hz⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ z))
  exact ⟨q p i, Finset.mem_image.mpr ⟨(p, i), Finset.mem_product.mpr ⟨hp, Finset.mem_univ _⟩, rfl⟩,
    (hq p i z).trans (hloc p (b i) z hz)⟩

section Estimates

variable {B : Type uB} (b : Module.Basis B ℂ Fixed)
  (hgen : HasOrbitSectionLevelFiberGenerators h hU hP K hK hPK ν π hν hr e H hHK b)
  {X : Type*} (L : (J → Circle) → X → (Fixed →ₗ[ℂ] ℂ))

include hgen in
/-- A per-section vanishing threshold for a fiberwise linear expression gives
one threshold for the entire fixed coefficient space. -/
theorem exists_uniform_fiber_zero_threshold
    (U : ℝ → Set X) (hUanti : Antitone U)
    (hzero : ∀ q : SectionLevel, ∃ t > 0, ∀ z x, x ∈ U t → L z x (fixedRestriction q z) = 0) :
    ∃ t > 0, ∀ z x, x ∈ U t → L z x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hgen
  choose t ht h using hzero
  let T := 1 + ∑ q ∈ s, |t q|
  have hT : 0 < T := by
    dsimp only [T]
    linarith [Finset.sum_nonneg (s := s) fun q _ => abs_nonneg (t q)]
  refine ⟨T, hT, fun z x hx => b.ext fun i => ?_⟩
  obtain ⟨q, hq, hqv⟩ := hs z i
  have hle : t q ≤ T := (le_abs_self _).trans
    ((Finset.single_le_sum (fun q _ => abs_nonneg (t q)) hq).trans
      (le_add_of_nonneg_left zero_le_one))
  rw [← hqv, LinearMap.zero_apply]
  exact h q z x ((hUanti hle) hx)

include hgen in
/-- A per-section exponential bound gives one rate and coefficient bound on
every vector of the fixed basis, uniformly in the parameter. -/
theorem exists_uniform_fiber_basis_exponential_bound
    (U : Set X) (Ξ N : X → ℝ) (hΞ : ∀ x ∈ U, 0 ≤ Ξ x) (hN : ∀ x ∈ U, 0 ≤ N x)
    (hbound : ∀ q : SectionLevel, ∃ ε > 0, ∃ C : ℝ≥0, ∀ z x, x ∈ U →
      ‖L z x (fixedRestriction q z)‖ ≤ (C : ℝ) * Ξ x * Real.exp (-(ε * N x))) :
    ∃ ε > 0, ∃ C : ℝ≥0, ∀ i z x, x ∈ U →
      ‖L z x (b i)‖ ≤ (C : ℝ) * Ξ x * Real.exp (-(ε * N x)) := by
  classical
  obtain ⟨s, hs⟩ := hgen
  choose ε hε C hC using hbound
  let rates := insert 1 (s.image ε)
  let hp : rates.Nonempty := Finset.insert_nonempty _ _
  let rate := rates.min' hp
  have hrate : 0 < rate := by
    change 0 < rates.min' hp
    have hmem := rates.min'_mem hp
    rcases Finset.mem_insert.mp hmem with he | he
    · rw [he]
      exact zero_lt_one
    · obtain ⟨q, _, heq⟩ := Finset.mem_image.mp he
      rw [← heq]
      exact hε q
  refine ⟨rate, hrate, ∑ q ∈ s, C q, fun i z x hx => ?_⟩
  obtain ⟨q, hq, hqv⟩ := hs z i
  have hle : rate ≤ ε q :=
    rates.min'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq))
  have hcoe : (C q : ℝ) ≤ (↑(∑ q ∈ s, C q) : ℝ) := by
    exact_mod_cast (Finset.single_le_sum (f := C) (fun _ _ => bot_le) hq)
  have hexp : Real.exp (-(ε q * N x)) ≤ Real.exp (-(rate * N x)) :=
    Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hle (hN x hx)))
  rw [← hqv]
  exact (hC q z x hx).trans (mul_le_mul
    (mul_le_mul_of_nonneg_right hcoe (hΞ x hx)) hexp (Real.exp_nonneg _)
    (mul_nonneg (by positivity) (hΞ x hx)))

end Estimates

end Langlands.HarishChandraSchwartz
