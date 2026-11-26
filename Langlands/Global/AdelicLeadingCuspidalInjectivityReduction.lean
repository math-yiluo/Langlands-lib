import Langlands.Global.AdelicCuspidalExponentAscentStatement
import Langlands.Global.AdelicLeadingCuspidalInjectivityStatement
import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicStandardTopAutomorphy
import Langlands.Global.AdelicStandardConstantTerm
import Langlands.Global.AdelicHarishChandraDecomposition
import Langlands.Automorphic.GroupSchemeInvariantFormsSubmodule
import Langlands.GroupScheme.Rational.LanglandsSimpleRootBasis
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.Geometry.Building.RealTorusInvariantForm
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Leading cuspidal injectivity from the vanishing criterion and exponent ascent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RealTorusSpace

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

section Roots

omit [NumberField F] in
/-- The real exponent of a parameter of `P_J` is annihilated by the coroots of the simple
roots in `J`. -/
theorem realExponent_mem_corootAnnihilator (J : Idx)
    (lam : ComplexCharacterParameter F (𝓕.P J)) :
    𝓕.realExponent J lam ∈ corootAnnihilator 𝓕.i 𝓕.coroots J.1 := by
  have hp := (𝓕.isCompatible J).parabolic.isClosedSubgroup
  have hLevi := (𝓕.isCompatible J).levi.isClosedSubgroup.comp hp
  let : Mono (𝓕.l J ≫ 𝓕.p J).hom.hom.left := hLevi.mono
  have hrep : (standardLevi 𝓕.i 𝓕.ν J.1).IsRepresentedBy (𝓕.l J ≫ 𝓕.p J) :=
    ⟨Over.mono_of_mono_left _, (𝓕.isCompatible J).levi_eq⟩
  have hAnn := standardLeviCharacterAnnihilator F G 𝓕.connectedReductive 𝓕.T 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic J.1 J.2 (𝓕.M J) (𝓕.l J ≫ 𝓕.p J) hLevi hrep (𝓕.torus J)
    (𝓕.torus_comp J) 𝓕.coroots
  rw [← hAnn]
  have hcomp : ∀ x : RealCharacterParameter F (𝓕.P J),
      rationalCharacterRestrictReal (𝓕.torus J) (rationalCharacterRestrictReal (𝓕.l J) x) =
        realParameterRestriction (𝓕.torus J ≫ 𝓕.l J) x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s χ =>
      change s ⊗ₜ[ℤ] characterRestrict (𝓕.torus J) (characterRestrict (𝓕.l J) χ) =
        s ⊗ₜ[ℤ] characterRestrict (𝓕.torus J ≫ 𝓕.l J) χ
      rw [characterRestrict_comp, AddMonoidHom.comp_apply]
    | add y z hy hz => simp only [map_add, hy, hz]
  exact ⟨rationalCharacterRestrictReal (𝓕.l J) (parameterRealPart F (𝓕.P J) lam),
    hcomp _⟩

omit [NumberField F] in
/-- `⟨Re λ, b^∨⟩ = 0` for every simple root `b` of the Levi of `P_J`. -/
theorem pair_realExponent_coroot_eq_zero (J : Idx)
    (lam : ComplexCharacterParameter F (𝓕.P J)) (b : relativeRoots 𝓕.i) (hb : b.1 ∈ J.1) :
    pair 𝓕.T (𝓕.realExponent J lam) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot b) = 0 :=
  (mem_corootAnnihilator 𝓕.i 𝓕.coroots J.1 _).mp
    (𝓕.realExponent_mem_corootAnnihilator J lam) b hb

omit [NumberField F] in
/-- Let `z` lie in the real span of a set `R` of simple roots, with `⟨z, b^∨⟩ ≤ 0` for every
`b ∈ R` and `⟨z, α^∨⟩ < 0` for some `α ∈ R`. Then `⟨z, ν⟩ < 0` for the generic cocharacter `ν`
defining the minimal parabolic. -/
theorem pair_generic_neg_of_antidominant (R : Set (characterLattice 𝓕.T))
    (hR : R ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν) {z : Vstar 𝓕.T} (hz : z ∈ 𝓕.rootSpanReal R)
    (hle : ∀ b : relativeRoots 𝓕.i, b.1 ∈ R →
      pair 𝓕.T z ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot b) ≤ 0)
    (α : relativeRoots 𝓕.i)
    (hlt : pair 𝓕.T z ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot α) < 0) :
    pair 𝓕.T z ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.ν) < 0 := by
  classical
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.isSplitSubtorus.1
  have hfinite : (relativeRoots 𝓕.i).Finite := hT.finite_relativeRoots 𝓕.i
  have : Finite (relativeWeylGroup 𝓕.i) :=
    𝓕.connectedReductive.finite_relativeWeylGroup 𝓕.i 𝓕.maximalSplit
  let := Fintype.ofFinite (relativeWeylGroup 𝓕.i)
  let B := relativeWeylInvariantForm 𝓕.i hT
  have hB : IsWeylInvariantInnerProduct 𝓕.i B :=
    ⟨relativeWeylInvariantForm_symm 𝓕.i hT,
      fun _ => relativeWeylInvariantForm_pos 𝓕.i hT,
      relativeWeylInvariantForm_invariant 𝓕.i hT⟩
  let e : characterLattice 𝓕.T → Vstar 𝓕.T := fun x => (1 : ℝ) ⊗ₜ[ℤ] x
  have hrel : ∀ x ∈ R, x ∈ relativeRoots 𝓕.i := fun x hx =>
    simpleRelativeRoots_subset_relativeRoots 𝓕.i 𝓕.ν (hR hx)
  -- the inner product of `z` with a root of `R` is nonpositive
  have hBz : ∀ x (hx : x ∈ R), B z (e x) ≤ 0 := by
    intro x hx
    have h := 𝓕.coroots.coroot_mul_form 𝓕.i B hB ⟨x, hrel x hx⟩ z
    have hpos := hB.2.1 _ (𝓕.coroots.one_tmul_ne_zero 𝓕.i ⟨x, hrel x hx⟩)
    have hle' := hle ⟨x, hrel x hx⟩ hx
    change pair 𝓕.T z ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot ⟨x, hrel x hx⟩) * B (e x) (e x) =
      2 * B z (e x) at h
    nlinarith
  -- distinct roots of `R` are obtuse
  have hobtuse : ∀ x (hx : x ∈ R) y (hy : y ∈ R), x ≠ y → B (e x) (e y) ≤ 0 := by
    intro x hx y hy hxy
    exact 𝓕.coroots.simple_form_nonpos 𝓕.i 𝓕.ν hT hfinite 𝓕.generic B hB ⟨x, hR hx⟩ ⟨y, hR hy⟩
      (fun h => hxy (congrArg Subtype.val h))
  obtain ⟨c, hc, rfl⟩ := Finsupp.mem_span_image_iff_linearCombination ℝ |>.mp hz
  have hsupp : ∀ x ∈ c.support, x ∈ R := fun x hx => hc hx
  let Spos := c.support.filter fun x => 0 < c x
  let Sneg := c.support.filter fun x => c x < 0
  let p := ∑ x ∈ Spos, c x • e x
  let n := ∑ x ∈ Sneg, (-c x) • e x
  have hzpn : Finsupp.linearCombination ℝ e c = p - n := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    have hsplit := Finset.sum_filter_add_sum_filter_not c.support (fun x => 0 < c x)
      (fun x => c x • e x)
    have hneg : c.support.filter (fun x => ¬ 0 < c x) = Sneg := by
      ext x
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, Sneg, not_lt]
      constructor
      · rintro ⟨h0, hle⟩
        exact ⟨h0, lt_of_le_of_ne hle h0⟩
      · rintro ⟨h0, hlt⟩
        exact ⟨h0, hlt.le⟩
    rw [← hsplit, hneg]
    simp only [p, n, neg_smul, Finset.sum_neg_distrib, sub_neg_eq_add]
    rfl
  set z := Finsupp.linearCombination ℝ e c with hzdef
  have hBzp : B z p ≤ 0 := by
    simp only [p, map_sum, map_smul, smul_eq_mul]
    apply Finset.sum_nonpos
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact mul_nonpos_of_nonneg_of_nonpos hx'.2.le (hBz x (hsupp x hx'.1))
  have hBnp : B n p ≤ 0 := by
    simp only [p, n, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    apply Finset.sum_nonpos
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    apply mul_nonpos_of_nonneg_of_nonpos hy'.2.le
    apply Finset.sum_nonpos
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hxy : x ≠ y := fun h => by
      rw [h] at hx'
      exact lt_asymm hy'.2 hx'.2
    exact mul_nonpos_of_nonneg_of_nonpos (neg_nonneg.mpr hx'.2.le)
      (hobtuse x (hsupp x hx'.1) y (hsupp y hy'.1) hxy)
  have hp0 : p = 0 := by
    by_contra hp
    have hpos := hB.2.1 p hp
    have hpzn : p = z + n := by rw [hzpn]; abel
    have hpp : B p p = B z p + B n p := by
      calc B p p = B (z + n) p := by rw [← hpzn]
        _ = B z p + B n p := by rw [map_add, LinearMap.add_apply]
    linarith
  have hzn : z = -n := by rw [hzpn, hp0, zero_sub]
  -- the negative part is nonzero
  have hSneg : Sneg.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hz0 : z = 0 := by
      rw [hzn]
      simp [n, he]
    rw [hz0, map_zero, LinearMap.zero_apply] at hlt
    exact lt_irrefl _ hlt
  have hpair : pair 𝓕.T z ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.ν) =
      -∑ x ∈ Sneg, (-c x) * (latticePairing 𝓕.T x 𝓕.ν : ℝ) := by
    rw [hzn]
    simp only [n, map_neg, map_sum, map_smul, LinearMap.neg_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, e, pair_tmul_tmul, one_mul]
  rw [hpair, neg_neg_iff_pos]
  apply Finset.sum_pos _ hSneg
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  have hposx : 0 < latticePairing 𝓕.T x 𝓕.ν := (hR (hsupp x hx'.1)).1.2
  exact mul_pos (neg_pos.mpr hx'.2) (by exact_mod_cast hposx)

end Roots

section Linearity

/-- The constant term is additive on inputs with integrable constant-term integrands. -/
theorem constantTerm_sub_of_integrable {Q : Idx} {f h : AdelicGroupPoints F G → ℂ}
    (hf : 𝓕.HasIntegrableConstantTerm Q f) (hh : 𝓕.HasIntegrableConstantTerm Q h) :
    𝓕.constantTerm Q (f - h) = 𝓕.constantTerm Q f - 𝓕.constantTerm Q h := by
  funext g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  exact integral_sub (hf g) (hh g)

section Projection

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

theorem leviPairingIntegrand_sub (P : Idx) (f h : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M P) → ℂ) :
    𝓕.leviPairingIntegrand P (f - h) g ψ =
      𝓕.leviPairingIntegrand P f g ψ - 𝓕.leviPairingIntegrand P h g ψ := by
  funext x
  simp only [leviPairingIntegrand, Pi.sub_apply, sub_mul]

theorem isAutomorphicOn_sub {P : Idx} {f h : AdelicGroupPoints F G → ℂ}
    (hf : 𝓕.IsAutomorphicOn hsmooth Kinf rho P f) (hh : 𝓕.IsAutomorphicOn hsmooth Kinf rho P h) :
    𝓕.IsAutomorphicOn hsmooth Kinf rho P (f - h) :=
  (automorphicFunctionsOn (parabolicQuotientSubgroup F (𝓕.p P) (𝓕.iU P) (𝓕.l P)) Kinf rho
    hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)).sub_mem hf hh

/-- Cuspidal projections of two inputs give a cuspidal projection of their difference. -/
theorem IsCuspidalProjection.sub {P : Idx} {f f' fc fc' : AdelicGroupPoints F G → ℂ}
    (h₁ : 𝓕.IsCuspidalProjection hsmooth Kinf rho P f fc)
    (h₂ : 𝓕.IsCuspidalProjection hsmooth Kinf rho P f' fc') :
    𝓕.IsCuspidalProjection hsmooth Kinf rho P (f - f') (fc - fc') := by
  refine ⟨𝓕.isAutomorphicOn_sub hsmooth Kinf rho h₁.1 h₂.1,
    𝓕.isCuspidalAlong_sub hsmooth Kinf rho P h₁.1 h₂.1 h₁.2.1 h₂.2.1, ?_⟩
  intro ψ hψ g
  obtain ⟨i₁, j₁, e₁⟩ := h₁.2.2 ψ hψ g
  obtain ⟨i₂, j₂, e₂⟩ := h₂.2.2 ψ hψ g
  refine ⟨?_, ?_, ?_⟩
  · rw [𝓕.leviPairingIntegrand_sub]
    exact i₁.sub i₂
  · rw [𝓕.leviPairingIntegrand_sub]
    exact j₁.sub j₂
  · unfold leviPairing at e₁ e₂ ⊢
    rw [𝓕.leviPairingIntegrand_sub, 𝓕.leviPairingIntegrand_sub]
    simp only [Pi.sub_apply]
    rw [integral_sub i₁ i₂, integral_sub j₁ j₂, e₁, e₂]

/-- Extension by zero of a family of components outside a finite index set. -/
def padComponents {Q : Idx} (t : Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) :
    ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ :=
  open Classical in fun lam => if lam ∈ t then c lam else 0

theorem sum_padComponents {Q : Idx} {t S : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    (hts : t ⊆ S) (c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) :
    ∑ lam ∈ S, 𝓕.padComponents t c lam = ∑ lam ∈ t, c lam := by
  classical
  simp only [padComponents, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hts]

theorem leadingSum_padComponents {Q : Idx} {t S : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    (hts : t ⊆ S) (c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) :
    𝓕.leadingSum Q S (𝓕.padComponents t c) = 𝓕.leadingSum Q t c := by
  classical
  unfold leadingSum
  have hinter : S.filter (𝓕.IsLeadingExponent Q) ∩ t = t.filter (𝓕.IsLeadingExponent Q) := by
    ext lam
    simp only [Finset.mem_inter, Finset.mem_filter]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hts h.1, h.2⟩, h.1⟩⟩
  simp only [padComponents, Finset.sum_ite_mem, hinter]

theorem leadingSum_sub {Q : Idx} (S : Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c c' : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) :
    𝓕.leadingSum Q S (fun lam => c lam - c' lam) = 𝓕.leadingSum Q S c - 𝓕.leadingSum Q S c' := by
  unfold leadingSum
  rw [Finset.sum_sub_distrib]

theorem isAutomorphicOn_padComponents {Q : Idx} {t : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    {c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ}
    (hc : ∀ lam ∈ t, 𝓕.IsAutomorphicOn hsmooth Kinf rho Q (c lam))
    (lam : ComplexCharacterParameter F (𝓕.P Q)) :
    𝓕.IsAutomorphicOn hsmooth Kinf rho Q (𝓕.padComponents t c lam) := by
  classical
  unfold padComponents
  split_ifs with h
  · exact hc lam h
  · exact 𝓕.isAutomorphicOn_zero hsmooth Kinf rho Q

theorem isCuspidalAlong_padComponents {Q : Idx} {t : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    {c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ}
    (hc : ∀ lam ∈ t, 𝓕.IsCuspidalAlong Q (c lam))
    (lam : ComplexCharacterParameter F (𝓕.P Q)) :
    𝓕.IsCuspidalAlong Q (𝓕.padComponents t c lam) := by
  classical
  unfold padComponents
  split_ifs with h
  · exact hc lam h
  · exact 𝓕.isCuspidalAlong_zero Q

theorem hasUnnormalizedExponent_padComponents {Q : Idx}
    {t : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    {c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ}
    (hc : ∀ lam ∈ t, 𝓕.HasUnnormalizedExponent Q lam (c lam))
    (lam : ComplexCharacterParameter F (𝓕.P Q)) :
    𝓕.HasUnnormalizedExponent Q lam (𝓕.padComponents t c lam) := by
  classical
  unfold padComponents
  split_ifs with h
  · exact hc lam h
  · exact 𝓕.hasUnnormalizedExponent_zero Q lam

open Classical in
/-- Exponent decompositions of two functions give one of their difference, indexed by the
union of the exponent sets. -/
theorem IsExponentDecomposition.sub {Q : Idx} {f f' : AdelicGroupPoints F G → ℂ}
    {s s' : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    {c c' : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ}
    (h : 𝓕.IsExponentDecomposition hsmooth Kinf rho Q f s c)
    (h' : 𝓕.IsExponentDecomposition hsmooth Kinf rho Q f' s' c') :
    𝓕.IsExponentDecomposition hsmooth Kinf rho Q (f - f') (s ∪ s')
      (fun lam => 𝓕.padComponents s c lam - 𝓕.padComponents s' c' lam) := by
  classical
  refine ⟨?_, fun lam _ => ?_, fun lam _ => ?_, fun lam _ => ?_⟩
  · rw [Finset.sum_sub_distrib, 𝓕.sum_padComponents Finset.subset_union_left,
      𝓕.sum_padComponents Finset.subset_union_right, ← h.sum_eq, ← h'.sum_eq]
  · exact 𝓕.isAutomorphicOn_sub hsmooth Kinf rho
      (𝓕.isAutomorphicOn_padComponents hsmooth Kinf rho h.automorphic lam)
      (𝓕.isAutomorphicOn_padComponents hsmooth Kinf rho h'.automorphic lam)
  · exact 𝓕.isCuspidalAlong_sub hsmooth Kinf rho Q
      (𝓕.isAutomorphicOn_padComponents hsmooth Kinf rho h.automorphic lam)
      (𝓕.isAutomorphicOn_padComponents hsmooth Kinf rho h'.automorphic lam)
      (𝓕.isCuspidalAlong_padComponents h.cuspidal lam)
      (𝓕.isCuspidalAlong_padComponents h'.cuspidal lam)
  · exact 𝓕.hasUnnormalizedExponent_sub Q
      (𝓕.hasUnnormalizedExponent_padComponents h.exponent lam)
      (𝓕.hasUnnormalizedExponent_padComponents h'.exponent lam)

end Projection

end Linearity

section Core

theorem finite_standardIndex : Finite Idx :=
  (Set.Finite.finite_subsets 𝓕.finite_simpleRoots).to_subtype

theorem finite_index_set (Q : Idx) : Q.1.Finite := 𝓕.finite_simpleRoots.subset Q.2

/-- The combinatorial core of Bernstein–Lapid §6.5: for a family of cuspidal projections and
exponent decompositions of the constant terms of an automorphic form, all of whose leading
sums vanish, every component vanishes, given the exponent ascent of Corollary 6.5. -/
theorem components_eq_zero_of_leadingSum_eq_zero
    (hasc : CuspidalExponentAscentStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ}
    (hauto : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (φc : Idx → AdelicGroupPoints F G → ℂ)
    (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ)
    (hdata : 𝓕.IsCuspidalExponentFamily hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho
      φ φc s c)
    (hlead : ∀ Q : Idx, 𝓕.leadingSum Q (s Q) (c Q) = 0) :
    ∀ (Q : Idx), ∀ lam ∈ s Q, c Q lam = 0 := by
  classical
  have : Finite Idx := 𝓕.finite_standardIndex
  let := Fintype.ofFinite Idx
  by_contra hne
  push Not at hne
  -- the finite set of cuspidal exponents of the family
  let E : Finset (Σ Q : Idx, ComplexCharacterParameter F (𝓕.P Q)) :=
    (Finset.univ.sigma s).filter fun x => c x.1 x.2 ≠ 0
  have hmemE : ∀ x, x ∈ E ↔ x.2 ∈ s x.1 ∧ c x.1 x.2 ≠ 0 := by
    intro x
    simp [E, Finset.mem_sigma]
  have hrank : ∃ r : ℕ, ∃ x ∈ E, x.1.1.ncard = r := by
    obtain ⟨Q, lam, hlam, hc⟩ := hne
    exact ⟨_, ⟨Q, lam⟩, (hmemE _).mpr ⟨hlam, hc⟩, rfl⟩
  let r0 := Nat.find hrank
  have hr0 : ∃ x ∈ E, x.1.1.ncard = r0 := Nat.find_spec hrank
  let E0 := E.filter fun x => x.1.1.ncard = r0
  have hE0 : E0.Nonempty := by
    obtain ⟨x, hx, hxr⟩ := hr0
    exact ⟨x, Finset.mem_filter.mpr ⟨hx, hxr⟩⟩
  let f : (Σ Q : Idx, ComplexCharacterParameter F (𝓕.P Q)) → ℝ := fun x =>
    pair 𝓕.T (𝓕.realExponent x.1 x.2) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.ν)
  obtain ⟨⟨P, lam⟩, hx0, hmax⟩ := E0.exists_max_image f hE0
  obtain ⟨hxE, hxr⟩ := Finset.mem_filter.mp hx0
  obtain ⟨hlam, hclam⟩ := (hmemE _).mp hxE
  change P.1.ncard = r0 at hxr
  -- minimality of the rank of `P`
  have hminimal : ∀ Q : Idx, Q.1.ncard < P.1.ncard → ∀ mu ∈ s Q, c Q mu = 0 := by
    intro Q hQ mu hmu
    by_contra hcm
    have := Nat.find_min hrank (m := Q.1.ncard) (by rw [hxr] at hQ; exact hQ)
    exact this ⟨⟨Q, mu⟩, (hmemE _).mpr ⟨hmu, hcm⟩, rfl⟩
  -- the exponent `λ` is not leading
  have hnotlead : ¬ 𝓕.IsLeadingExponent P lam := by
    intro hl
    have hsum := hlead P
    unfold leadingSum at hsum
    have hz := 𝓕.eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent P
      ((s P).filter (𝓕.IsLeadingExponent P)) (c P)
      (fun mu hmu => ((hdata P).2.exponent mu (Finset.mem_filter.mp hmu).1)) hsum lam
      (Finset.mem_filter.mpr ⟨hlam, hl⟩)
    exact hclam hz
  unfold IsLeadingExponent closedPositiveChamber at hnotlead
  simp only [Set.mem_ofPred_eq, not_forall, not_le] at hnotlead
  obtain ⟨α, hαs, hαneg⟩ := hnotlead
  change pair 𝓕.T (𝓕.realExponent P lam) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot α) < 0 at hαneg
  have hαP : α.1 ∉ P.1 := by
    intro h
    rw [𝓕.pair_realExponent_coroot_eq_zero P lam α h] at hαneg
    exact lt_irrefl _ hαneg
  obtain ⟨Q, β, hβQ, hins, mu, hmu, hcmu, hβpos, hspan⟩ :=
    hasc F G 𝓕 K hK hKmin hKlevi rho hsmooth hrho φ hauto φc s c hdata P lam hlam hclam
      hminimal α hαs hαP hαneg
  -- `Q` has the rank of `P`
  have hcardQ : Q.1.ncard = P.1.ncard := by
    have h1 := Set.ncard_insert_of_notMem hβQ (𝓕.finite_index_set Q)
    have h2 := Set.ncard_insert_of_notMem hαP (𝓕.finite_index_set P)
    rw [hins] at h1
    omega
  have hQE0 : (⟨Q, mu⟩ : Σ Q : Idx, ComplexCharacterParameter F (𝓕.P Q)) ∈ E0 :=
    Finset.mem_filter.mpr ⟨(hmemE _).mpr ⟨hmu, hcmu⟩, by change Q.1.ncard = r0; omega⟩
  have hle := hmax _ hQE0
  -- the antidominance computation
  have hR : insert α.1 P.1 ⊆ simpleRelativeRoots 𝓕.i 𝓕.ν :=
    Set.insert_subset hαs P.2
  have hlamle : ∀ b : relativeRoots 𝓕.i, b.1 ∈ insert α.1 P.1 →
      pair 𝓕.T (𝓕.realExponent P lam) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot b) ≤ 0 := by
    intro b hb
    rcases hb with hb | hb
    · rw [show b = α from Subtype.ext hb]
      exact hαneg.le
    · exact (𝓕.pair_realExponent_coroot_eq_zero P lam b hb).le
  have hmuge : ∀ b : relativeRoots 𝓕.i, b.1 ∈ insert α.1 P.1 →
      0 ≤ pair 𝓕.T (𝓕.realExponent Q mu) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot b) := by
    intro b hb
    rw [← hins] at hb
    rcases hb with hb | hb
    · rw [show b = β from Subtype.ext hb]
      exact hβpos
    · exact (𝓕.pair_realExponent_coroot_eq_zero Q mu b hb).ge
  have hneg := 𝓕.pair_generic_neg_of_antidominant (insert α.1 P.1) hR hspan
    (fun b hb => by
      rw [map_sub, LinearMap.sub_apply]
      linarith [hlamle b hb, hmuge b hb])
    α
    (by
      rw [map_sub, LinearMap.sub_apply]
      linarith [hmuge α (Set.mem_insert _ _)])
  rw [map_sub, LinearMap.sub_apply] at hneg
  change f ⟨Q, mu⟩ ≤ f ⟨P, lam⟩ at hle
  simp only [f] at hle
  linarith

end Core

section RankZero

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem bijective_algebraMap_coordinateRing_fin_zero :
    Function.Bijective (algebraMap (CommRingCat.of F)
      (GeneralLinear.CoordinateRing (Fin 0) (CommRingCat.of F))) := by
  have : IsEmpty (GeneralLinear.Coordinate (Fin 0)) :=
    ⟨fun x => by cases x <;> exact Fin.elim0 ‹_›⟩
  have : Nontrivial (GeneralLinear.CoordinateRing (Fin 0) (CommRingCat.of F)) :=
    (GeneralLinear.classify (R := CommRingCat.of F) (S := F)
      (1 : GL (Fin 0) F)).toRingHom.domain_nontrivial
  refine ⟨RingHom.injective _, fun a => ?_⟩
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨MvPolynomial.isEmptyAlgEquiv (CommRingCat.of F) (GeneralLinear.Coordinate (Fin 0)) q, ?_⟩
  conv_rhs => rw [← (MvPolynomial.isEmptyAlgEquiv (CommRingCat.of F)
    (GeneralLinear.Coordinate (Fin 0))).symm_apply_apply q]
  rw [MvPolynomial.isEmptyAlgEquiv_symm_apply]
  rfl

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The general linear group scheme of rank zero has at most one point over every base. -/
theorem subsingleton_hom_groupScheme_fin_zero (X : Over (Spec (CommRingCat.of F))) :
    Subsingleton (X ⟶ (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)).X) := by
  have hiso : IsIso (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)).X.hom := by
    rw [GeneralLinear.groupScheme_hom]
    exact isIso_SpecMap_iff.mpr bijective_algebraMap_coordinateRing_fin_zero
  constructor
  intro x y
  apply Over.OverMorphism.ext
  rw [← cancel_mono (GeneralLinear.groupScheme (Fin 0) (CommRingCat.of F)).X.hom, Over.w x,
    Over.w y]

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- A closed subgroup of the rank-zero general linear group has at most one point over every
base. -/
theorem subsingleton_hom_of_rank_zero {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : MatrixRepresentation H (Fin 0)) (hj : IsClosedSubgroup j)
    (X : Over (Spec (CommRingCat.of F))) : Subsingleton (X ⟶ H.X) := by
  have := subsingleton_hom_groupScheme_fin_zero (F := F) X
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact ⟨fun x y => (cancel_mono j.hom.hom).mp (Subsingleton.elim _ _)⟩

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- If the plot-smooth functions on the infinite adelic points form a finite-dimensional space,
a function all of whose infinite slices equal one plot-smooth function is finite under the
center of the enveloping algebra. -/
theorem isCenterFiniteFunction_of_finiteDimensional {H : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine H.X.left] {e : ℕ} (hs : SmoothOfRelativeDimension e H.X.hom)
    (hc : AdelicDifferentialCommutator F H hs)
    [FiniteDimensional ℂ (InfinitePlotSmoothFunctions F H)]
    (v : InfinitePlotSmoothFunctions F H) (f : AdelicGroupPoints F H → ℂ)
    (hf : ∀ b, functionInfiniteSlice F H f b = v.val) :
    IsCenterFiniteFunction F H hs hc f := by
  let L : AdelicEnvelopingCenter F H hs →ₗ[ℂ] InfinitePlotSmoothFunctions F H :=
    { toFun := fun z => InfiniteAdelicGroupPoints.plotSmoothCenterAction F H hs hc z v
      map_add' := fun _ _ => by simp [map_add, LinearMap.add_apply]
      map_smul' := fun _ _ => by simp [map_smul, LinearMap.smul_apply] }
  let J : Ideal (AdelicEnvelopingCenter F H hs) :=
    { carrier := {z | InfiniteAdelicGroupPoints.plotSmoothCenterAction F H hs hc z v = 0}
      zero_mem' := by simp
      add_mem' := fun hz hw => by simp_all
      smul_mem' := fun a z hz => by
        change InfiniteAdelicGroupPoints.plotSmoothCenterAction F H hs hc (a * z) v = 0
        rw [map_mul, Module.End.mul_apply, hz, map_zero] }
  refine ⟨J, ?_, fun z hz b h => ?_⟩
  · change Module.Finite ℂ (AdelicEnvelopingCenter F H hs ⧸ LinearMap.ker L)
    have : Module.Finite ℂ (LinearMap.range L) := FiniteDimensional.finiteDimensional_submodule _
    exact (Module.Finite.equiv_iff L.quotKerEquivRange).mpr this
  · have hv : (⟨functionInfiniteSlice F H f b, h⟩ : InfinitePlotSmoothFunctions F H) = v :=
      Subtype.ext (hf b)
    rw [hv]
    exact hz

/-- For a closed embedding into the rank-zero general linear group, the constant function `1` is
a cusp form on the Levi of the full standard index. -/
theorem isLeviCuspForm_one_of_rank_zero (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) :
    𝓕.IsLeviCuspForm Kinf rho 𝓕.top (fun _ => 1) := by
  classical
  have hp := (𝓕.isCompatible 𝓕.top).parabolic.isClosedSubgroup
  have hj : IsClosedSubgroup (𝓕.l 𝓕.top ≫ 𝓕.p 𝓕.top ≫ rho) := by
    rw [← Category.assoc]
    exact ((𝓕.isCompatible 𝓕.top).levi.isClosedSubgroup.comp hp).comp hrho
  have hsub : ∀ X : Over (Spec (CommRingCat.of F)), Subsingleton (X ⟶ (𝓕.M 𝓕.top).X) :=
    subsingleton_hom_of_rank_zero _ hj
  have : Subsingleton (AdelicGroupPoints F (𝓕.M 𝓕.top)) := hsub _
  have : Subsingleton (InfiniteAdelicGroupPoints F (𝓕.M 𝓕.top)) := hsub _
  have : Finite (AdelicGroupPoints F (𝓕.M 𝓕.top)) := Finite.of_subsingleton
  have : Finite (InfiniteAdelicGroupPoints F (𝓕.M 𝓕.top)) := Finite.of_subsingleton
  refine ⟨⟨fun _ _ _ => rfl, ⟨continuous_const, fun b => ?_, ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩⟩,
    ?_, ?_, ⟨1, one_pos, 0, fun g => by simp⟩⟩, ?_⟩
  · exact (𝓕.M 𝓕.top).isPlotSmooth_const _ _ 1
  · exact FiniteDimensional.finiteDimensional_submodule _
  · have : FiniteDimensional ℂ (InfinitePlotSmoothFunctions F (𝓕.M 𝓕.top)) :=
      FiniteDimensional.finiteDimensional_submodule _
    exact isCenterFiniteFunction_of_finiteDimensional _ _
      ⟨fun _ => 1, (𝓕.M 𝓕.top).isPlotSmooth_const _ _ 1⟩ _ (fun _ => rfl)
  · intro P' U' p' r _ _ _ _ hne
    exfalso
    apply hne
    apply SubgroupFunctor.ext
    intro X
    rw [SubgroupFunctor.top_carrier]
    have := hsub X
    refine eq_top_iff.mpr fun x _ => ?_
    rw [Subsingleton.elim x 1]
    exact Subgroup.one_mem _

end RankZero

section Assembly

/-- An Iwasawa compact for the minimal standard parabolic serves every standard parabolic. -/
theorem isIwasawaCompact_of_minimal {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K) (Q : Idx) :
    IsIwasawaCompact (𝓕.p Q) K := by
  refine ⟨hK.isCompact, Set.eq_univ_of_univ_subset ?_⟩
  rw [← hK.range_mul]
  apply Set.mul_subset_mul_right
  rintro _ ⟨x, rfl⟩
  have hx : x ≫ (𝓕.p ⟨∅, Set.empty_subset _⟩).hom.hom ∈
      (SubgroupFunctor.range (𝓕.p ⟨∅, Set.empty_subset _⟩)).carrier _ :=
    SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp
    ((𝓕.le_iff_range_le ⟨∅, Set.empty_subset _⟩ Q).mp (Set.empty_subset _) _ hx)
  exact ⟨y, by simpa [AdelicGroupPoints.map_apply] using hy⟩

/-- Rational invariance and continuity give integrable constant-term integrands along every
standard parabolic. -/
theorem hasIntegrableConstantTerm_of_rational {f : AdelicGroupPoints F G → ℂ}
    (hinv : IsLeftInvariantUnder F G (rationalSubgroup F G) f) (hf : Continuous f) (Q : Idx) :
    𝓕.HasIntegrableConstantTerm Q f := by
  intro g
  refine 𝓕.integrable_constantTermIntegrand_of_le 𝓕.top Q (𝓕.le_top Q) hf ?_ g
  rw [𝓕.parabolicQuotientSubgroup_top]
  exact hinv

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

/-- Two automorphic forms with a common family of leading cuspidal components: their difference
has a family of cuspidal projections and exponent decompositions with vanishing leading sums. -/
theorem exists_difference_family {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) Kinf rho φ)
    (hψ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) Kinf rho ψ)
    {L : Idx → AdelicGroupPoints F G → ℂ}
    (hLφ : 𝓕.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho φ L)
    (hLψ : 𝓕.IsGlobalLeadingCuspidalComponents hsmooth Kinf rho ψ L) :
    ∃ (δc : Idx → AdelicGroupPoints F G → ℂ)
      (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
      (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ),
      𝓕.IsCuspidalExponentFamily hsmooth Kinf rho (φ - ψ) δc s c ∧
        ∀ Q : Idx, 𝓕.leadingSum Q (s Q) (c Q) = 0 := by
  classical
  choose φc hφc sφ cφ hφd hφl using hLφ
  choose ψc hψc sψ cψ hψd hψl using hLψ
  refine ⟨fun Q => φc Q - ψc Q, fun Q => sφ Q ∪ sψ Q,
    fun Q lam => 𝓕.padComponents (sφ Q) (cφ Q) lam - 𝓕.padComponents (sψ Q) (cψ Q) lam,
    fun Q => ⟨?_, ?_⟩, fun Q => ?_⟩
  · have hct : 𝓕.constantTerm Q (φ - ψ) = 𝓕.constantTerm Q φ - 𝓕.constantTerm Q ψ :=
      𝓕.constantTerm_sub_of_integrable
        (𝓕.hasIntegrableConstantTerm_of_rational hφ.1 hφ.2.1.1 Q)
        (𝓕.hasIntegrableConstantTerm_of_rational hψ.1 hψ.2.1.1 Q)
    rw [hct]
    exact (hφc Q).sub 𝓕 hsmooth Kinf rho (hψc Q)
  · convert (hφd Q).sub 𝓕 hsmooth Kinf rho (hψd Q)
  · rw [𝓕.leadingSum_sub, 𝓕.leadingSum_padComponents Finset.subset_union_left,
      𝓕.leadingSum_padComponents Finset.subset_union_right, ← hφl Q, ← hψl Q, sub_self]

/-- Theorem 6.3 of Bernstein–Lapid for a closed embedding of positive size, from the vanishing
criterion (8.1) and the exponent ascent of Corollary 6.4. -/
theorem eq_of_leadingCuspidalComponents_of_pos
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (hasc : CuspidalExponentAscentStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (hψ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho ψ)
    {L : Idx → AdelicGroupPoints F G → ℂ}
    (hLφ : 𝓕.IsGlobalLeadingCuspidalComponents hsmooth (K.comap (ofInfinite F G).toMonoidHom)
      rho φ L)
    (hLψ : 𝓕.IsGlobalLeadingCuspidalComponents hsmooth (K.comap (ofInfinite F G).toMonoidHom)
      rho ψ L) :
    φ = ψ := by
  set Kinf := K.comap (ofInfinite F G).toMonoidHom
  obtain ⟨δc, s, c, hdata, hlead⟩ := 𝓕.exists_difference_family hsmooth Kinf rho hφ hψ hLφ hLψ
  have hδ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) Kinf rho (φ - ψ) :=
    (automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth)).sub_mem hφ hψ
  have hzero := 𝓕.components_eq_zero_of_leadingSum_eq_zero hasc K hK hKmin hKlevi rho hsmooth
    hrho hδ δc s c hdata hlead
  have hδc : ∀ Q, δc Q = 0 := fun Q => by
    rw [(hdata Q).2.sum_eq]
    exact Finset.sum_eq_zero (hzero Q)
  have hann : ∀ Q : Idx, Q ≤ 𝓕.top →
      𝓕.InCuspidalAnnihilator Kinf rho Q (𝓕.constantTerm Q (φ - ψ)) := by
    intro Q _ ψ' hψ' g
    obtain ⟨hi, -, he⟩ := (hdata Q).1.2.2 ψ' hψ' g
    refine ⟨hi, ?_⟩
    rw [he, hδc Q]
    have hz : 𝓕.leviPairingIntegrand Q 0 g ψ' = 0 := by
      funext x
      simp [leviPairingIntegrand]
    simp [leviPairing, hz]
  have hmod : 𝓕.IsModerateContinuousOnParabolic rho 𝓕.top (φ - ψ) := by
    refine ⟨?_, hδ.2.1.1, hδ.2.2.2.2⟩
    rw [𝓕.parabolicQuotientSubgroup_top]
    exact hδ.1
  exact sub_eq_zero.mp (hvan F G 𝓕 K hK (𝓕.isIwasawaCompact_of_minimal hKmin) rho hN hrho
    𝓕.top (φ - ψ) hmod hann)

/-- Theorem 6.3 of Bernstein–Lapid for a closed embedding into the rank-zero general linear
group, from the exponent ascent of Corollary 6.4. The cusp form `1` of the trivial Levi replaces
the vanishing criterion. -/
theorem eq_of_leadingCuspidalComponents_of_rank_zero
    (hasc : CuspidalExponentAscentStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    {d : ℕ} (rho : MatrixRepresentation G (Fin 0))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φ ψ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (hψ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho ψ)
    {L : Idx → AdelicGroupPoints F G → ℂ}
    (hLφ : 𝓕.IsGlobalLeadingCuspidalComponents hsmooth (K.comap (ofInfinite F G).toMonoidHom)
      rho φ L)
    (hLψ : 𝓕.IsGlobalLeadingCuspidalComponents hsmooth (K.comap (ofInfinite F G).toMonoidHom)
      rho ψ L) :
    φ = ψ := by
  set Kinf := K.comap (ofInfinite F G).toMonoidHom
  obtain ⟨δc, s, c, hdata, hlead⟩ := 𝓕.exists_difference_family hsmooth Kinf rho hφ hψ hLφ hLψ
  have hδ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) Kinf rho (φ - ψ) :=
    (automorphicFunctionsOn (rationalSubgroup F G) Kinf rho hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth)).sub_mem hφ hψ
  have hzero := 𝓕.components_eq_zero_of_leadingSum_eq_zero hasc K hK hKmin hKlevi rho hsmooth
    hrho hδ δc s c hdata hlead
  have hδc : δc 𝓕.top = 0 := by
    rw [(hdata 𝓕.top).2.sum_eq]
    exact Finset.sum_eq_zero (hzero 𝓕.top)
  have : Subsingleton (AdelicGroupPoints F G) := subsingleton_hom_of_rank_zero rho hrho _
  funext g
  obtain ⟨hi, -, he⟩ := (hdata 𝓕.top).1.2.2 (fun _ => 1)
    (𝓕.isLeviCuspForm_one_of_rank_zero Kinf rho hrho) g
  have hint : 𝓕.leviPairingIntegrand 𝓕.top (𝓕.constantTerm 𝓕.top (φ - ψ)) g (fun _ => 1) =
      fun _ => φ g - ψ g := by
    funext x
    simp only [leviPairingIntegrand, 𝓕.constantTerm_top, map_one, mul_one, Pi.sub_apply]
    rw [Subsingleton.elim (map F (𝓕.M 𝓕.top) G (𝓕.l 𝓕.top ≫ 𝓕.p 𝓕.top) _ * g) g]
  have hz : 𝓕.leviPairingIntegrand 𝓕.top 0 g (fun _ => 1) = 0 := by
    funext x
    simp [leviPairingIntegrand]
  rw [hint] at hi
  unfold leviPairing at he
  rw [hint, hδc, hz] at he
  simp only [Pi.zero_apply, integral_zero, integral_const, smul_eq_zero] at he
  rcases integrable_const_iff.mp hi with h | h
  · exact sub_eq_zero.mp h
  · rcases he with h' | h'
    · exfalso
      have hu : normOneRationalQuotientHaarMeasure F (𝓕.M 𝓕.top) Set.univ = 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h'
      exact normOneRationalQuotientHaarMeasure_ne_zero F (𝓕.M 𝓕.top)
        (Measure.measure_univ_eq_zero.mp hu)
    · exact sub_eq_zero.mp h'

end Assembly

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

/-- Bernstein–Lapid, Theorem 6.3 (injectivity of the leading cuspidal components), from the
vanishing criterion (8.1) and the exponent ascent of Corollary 6.4. -/
def LeadingCuspidalInjectivityReductionStatement : Prop :=
  ParabolicCuspidalVanishingStatement.{u} → CuspidalExponentAscentStatement.{u} →
    LeadingCuspidalInjectivityStatement.{u}

/-- The reduction: the vanishing criterion (8.1) and Corollary 6.4 imply Theorem 6.3, for
closed embeddings of every size. -/
theorem leadingCuspidalInjectivityReduction :
    LeadingCuspidalInjectivityReductionStatement.{u} := by
  intro hvan hasc F _ _ G _ _ _ fam K hK hKmin hKlevi N d rho hsmooth hrho Kinf hcalc φ ψ L hφ hψ
    hLφ hLψ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact fam.eq_of_leadingCuspidalComponents_of_rank_zero hasc K hK hKmin hKlevi rho hsmooth hrho
      hφ hψ hLφ hLψ
  · exact fam.eq_of_leadingCuspidalComponents_of_pos hvan hasc K hK hKmin hKlevi rho hN hsmooth
      hrho hφ hψ hLφ hLψ

end Langlands.Global
