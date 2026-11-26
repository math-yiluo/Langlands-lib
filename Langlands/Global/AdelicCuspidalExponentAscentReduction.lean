import Langlands.Global.AdelicCuspidalExponentNonexistenceStatement
import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Global.AdelicCuspidalAnnihilator
import Langlands.Global.AdelicConstantTermAutomorphyStatement
import Langlands.Global.AdelicLeadingExponentDirectness
import Langlands.Global.AdelicStandardTopAutomorphy
import Langlands.Global.AdelicPositiveTorusSplitComponentProof
import Langlands.Global.AdelicHarishChandraDecomposition
import Langlands.GroupScheme.Rational.RelativeRealCorootStatements
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # The exponent ascent of Bernstein–Lapid, Corollary 6.4, from the lemma of §6.4 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  RealTorusSpace PositiveRealTorus

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

section Geometry

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The absolute value of `x^μ` at the image of a torus point `t` with logarithm `v`. -/
theorem norm_parameterPower_map_torus {T : CommGroupScheme (Spec (CommRingCat.of F))}
    {H : GroupScheme (Spec (CommRingCat.of F))} (j : T.toGrp ⟶ H)
    (mu : ComplexCharacterParameter F H) (t : AdelicGroupPoints F T.toGrp) (v : V T)
    (ht : characterLog F T.toGrp t = cocharacterFunctional v) :
    ‖parameterPower F H mu (map F T.toGrp H j t)‖ =
      Real.exp (pair T (realParameterRestriction j (parameterRealPart F H mu)) v) := by
  rw [parameterPower, Complex.norm_exp, characterLog_map, ht]
  congr 1
  induction mu using TensorProduct.inductionOn with
  | tmul s χ =>
    rw [complexParameterPairing_tmul, parameterRealPart_tmul]
    change (s * ((cocharacterFunctional v (GroupScheme.characterRestrict j χ) : ℝ) : ℂ)).re =
      pair T (s.re ⊗ₜ[ℤ] _) v
    rw [Complex.re_mul_ofReal, cocharacterFunctional_apply,
      show s.re ⊗ₜ[ℤ] _ = s.re • ((1 : ℝ) ⊗ₜ[ℤ] _) by rw [TensorProduct.smul_tmul', smul_eq_mul,
        mul_one], map_smul, LinearMap.smul_apply, smul_eq_mul]
    rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, Complex.add_re, hx, hy]

/-- Every real cocharacter annihilated by the simple roots of `R` is the logarithm of a positive
torus point whose image in `G(𝔸)` lies in the positive split component of `P_R`. -/
theorem exists_positiveSplitComponent_torus_log (R : Idx) {v : V 𝓕.T}
    (hv : v ∈ rootAnnihilator 𝓕.T R.1) :
    ∃ (a : 𝓕.positiveSplitComponent R) (t : AdelicGroupPoints F 𝓕.T.toGrp),
      map F (𝓕.P R) G (𝓕.p R) a = map F 𝓕.T.toGrp G 𝓕.i t ∧
      characterLog F 𝓕.T.toGrp t = cocharacterFunctional v := by
  have hc := 𝓕.isCompatible R
  have : IsAffineHom (𝓕.M R).X.hom := hc.levi.isConnectedReductive.isAffineHom
  have hjc : IsClosedSubgroup (𝓕.l R ≫ 𝓕.p R) :=
    hc.levi.isClosedSubgroup.comp hc.parabolic.isClosedSubgroup
  let : IsClosedImmersion (𝓕.l R ≫ 𝓕.p R).hom.hom.left := hjc
  have hrep : (standardLevi 𝓕.i 𝓕.ν R.1).IsRepresentedBy (𝓕.l R ≫ 𝓕.p R) :=
    ⟨Over.mono_of_mono_left _, hc.levi_eq⟩
  obtain ⟨_, f, hf, _, _, hrange, _⟩ :=
    (standardLeviCentralDirections.2 F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit 𝓕.ν
      𝓕.generic R.1 R.2 (𝓕.M R) (𝓕.l R ≫ 𝓕.p R) hjc hrep).2 (𝓕.A R) (𝓕.a R)
      hc.splitComponent
  have hA : IsSplitTorus (𝓕.A R).toGrp := hc.splitComponent.1.1.1
  rw [← hrange] at hv
  obtain ⟨w, rfl⟩ := hv
  obtain ⟨a', ha', hlog⟩ := exists_characterLog_eq hA (cocharacterFunctional w)
  refine ⟨⟨map F (𝓕.A R).toGrp (𝓕.P R) (𝓕.a R ≫ 𝓕.l R) a', a', ha', rfl⟩,
    map F (𝓕.A R).toGrp 𝓕.T.toGrp (CommGroupScheme.groupHom f) a', ?_, ?_⟩
  · change map F (𝓕.P R) G (𝓕.p R) (map F (𝓕.A R).toGrp (𝓕.P R) (𝓕.a R ≫ 𝓕.l R) a') = _
    simp only [map_apply, GroupScheme.affinePointsTarget_apply]
    rw [Category.assoc, Category.assoc]
    congr 1
    have h := congrArg (fun z : (𝓕.A R).toGrp ⟶ G => z.hom.hom) hf
    simpa [Category.assoc] using h.symm
  · rw [characterLog_map, hlog, ← cocharacterFunctional_cocharacterMapReal]

/-- If a point of `𝔄_R` is the image of a torus point `t`, its chosen lift to `𝔄_Q` is the
image of `t` in `P_Q(𝔸)`. -/
theorem splitLift_eq_map_torus {Q R : Idx} (hQR : Q ≤ R) (a : 𝓕.positiveSplitComponent R)
    (t : AdelicGroupPoints F 𝓕.T.toGrp)
    (ht : map F (𝓕.P R) G (𝓕.p R) a = map F 𝓕.T.toGrp G 𝓕.i t) :
    ((𝓕.splitLift hQR a : 𝓕.positiveSplitComponent Q) : AdelicGroupPoints F (𝓕.P Q)) =
      map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) t := by
  let := (𝓕.isCompatible Q).parabolic.isClosedSubgroup.mono
  have : Mono (𝓕.p Q).hom.hom := Over.mono_of_mono_left _
  have h1 : map F (𝓕.P Q) G (𝓕.p Q) (𝓕.splitLift hQR a) =
      map F (𝓕.P Q) G (𝓕.p Q) (map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) t) := by
    rw [𝓕.map_splitLift hQR a, ht, ← map_comp_apply_of_hom, Category.assoc, 𝓕.torus_comp]
  simp only [map_apply, GroupScheme.affinePointsTarget_apply] at h1
  exact (cancel_mono _).mp h1

/-- Bernstein–Lapid §6.1–6.2: if the absolute values of `μ` along `Q ⊆ R` and of `λ` along
`P ⊆ R` agree on `𝔄_R`, then `Re λ - Re μ` lies in the real span of the simple roots of `R`. -/
theorem realExponent_sub_mem_rootSpanReal {P Q R : Idx} (hPR : P ≤ R) (hQR : Q ≤ R)
    (lam : ComplexCharacterParameter F (𝓕.P P)) (mu : ComplexCharacterParameter F (𝓕.P Q))
    (h : ∀ a : 𝓕.positiveSplitComponent R,
      ‖parameterPower F (𝓕.P Q) mu (𝓕.splitLift hQR a)‖ =
        ‖parameterPower F (𝓕.P P) lam (𝓕.splitLift hPR a)‖) :
    𝓕.realExponent P lam - 𝓕.realExponent Q mu ∈ 𝓕.rootSpanReal R.1 := by
  have hT : IsSplitTorus 𝓕.T.toGrp := 𝓕.maximalSplit.1.1
  unfold rootSpanReal
  rw [← characterAnnihilator_cocharacterAnnihilator hT
    (Submodule.span ℝ ((fun x : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] x) '' R.1)),
    ← rootAnnihilator_eq_cocharacterAnnihilator, mem_characterAnnihilator]
  intro v hv
  obtain ⟨a, t, hat, ht⟩ := 𝓕.exists_positiveSplitComponent_torus_log R hv
  have hQ := 𝓕.splitLift_eq_map_torus hQR a t hat
  have hP := 𝓕.splitLift_eq_map_torus hPR a t hat
  have he := h a
  rw [hQ, hP, norm_parameterPower_map_torus _ _ _ v ht,
    norm_parameterPower_map_torus _ _ _ v ht, Real.exp_eq_exp] at he
  rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
  exact he.symm

end Geometry

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
private theorem subsingleton_hom_groupScheme_fin_zero (X : Over (Spec (CommRingCat.of F))) :
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
/-- A closed subgroup of the general linear group of rank zero has at most one point over
every base. -/
private theorem subsingleton_hom_of_fin_zero {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : MatrixRepresentation H (Fin 0)) (hj : IsClosedSubgroup j)
    (X : Over (Spec (CommRingCat.of F))) : Subsingleton (X ⟶ H.X) := by
  have := subsingleton_hom_groupScheme_fin_zero (F := F) X
  have : IsClosedImmersion j.hom.hom.left := hj
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  exact ⟨fun x y => (cancel_mono j.hom.hom).mp (Subsingleton.elim _ _)⟩

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem isCenterFiniteFunction_of_finiteDimensional'
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] {e : ℕ}
    (hs : SmoothOfRelativeDimension e H.X.hom) (hc : AdelicDifferentialCommutator F H hs)
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

/-- For a closed embedding into the general linear group of rank zero, the constant function
`1` is a cusp form on every standard Levi. -/
private theorem isLeviCuspForm_one_of_fin_zero (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) (J : Idx) :
    𝓕.IsLeviCuspForm Kinf rho J (fun _ => 1) := by
  classical
  have hp := (𝓕.isCompatible J).parabolic.isClosedSubgroup
  have hj : IsClosedSubgroup (𝓕.l J ≫ 𝓕.p J ≫ rho) := by
    rw [← Category.assoc]
    exact ((𝓕.isCompatible J).levi.isClosedSubgroup.comp hp).comp hrho
  have hsub : ∀ X : Over (Spec (CommRingCat.of F)), Subsingleton (X ⟶ (𝓕.M J).X) :=
    subsingleton_hom_of_fin_zero _ hj
  have : Subsingleton (AdelicGroupPoints F (𝓕.M J)) := hsub _
  have : Subsingleton (InfiniteAdelicGroupPoints F (𝓕.M J)) := hsub _
  have : Finite (AdelicGroupPoints F (𝓕.M J)) := Finite.of_subsingleton
  have : Finite (InfiniteAdelicGroupPoints F (𝓕.M J)) := Finite.of_subsingleton
  refine ⟨⟨fun _ _ _ => rfl, ⟨continuous_const, fun b => ?_, ⟨⊤, isOpen_univ, fun _ _ _ => rfl⟩⟩,
    ?_, ?_, ⟨1, one_pos, 0, fun g => by simp⟩⟩, ?_⟩
  · exact (𝓕.M J).isPlotSmooth_const _ _ 1
  · exact FiniteDimensional.finiteDimensional_submodule _
  · have : FiniteDimensional ℂ (InfinitePlotSmoothFunctions F (𝓕.M J)) :=
      FiniteDimensional.finiteDimensional_submodule _
    exact isCenterFiniteFunction_of_finiteDimensional' _ _
      ⟨fun _ => 1, (𝓕.M J).isPlotSmooth_const _ _ 1⟩ _ (fun _ => rfl)
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

section Uniqueness

/-- An Iwasawa compact for the minimal standard parabolic serves every standard parabolic. -/
private theorem isIwasawaCompact_of_minimal' {K : Subgroup (AdelicGroupPoints F G)}
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

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (rho : MatrixRepresentation G (Fin N))

/-- A cuspidal projection of the zero function vanishes: by the vanishing criterion (8.1) for
a closed embedding of positive size, and by the cusp form `1` of the trivial Levi for a closed
embedding into the general linear group of rank zero. -/
theorem eq_zero_of_isCuspidalProjection_zero (hvan : ParabolicCuspidalVanishingStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K) (hrho : IsClosedSubgroup rho)
    {Q : Idx} {ψ : AdelicGroupPoints F G → ℂ}
    (hp : 𝓕.IsCuspidalProjection hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho Q 0 ψ) :
    ψ = 0 := by
  set Kinf := K.comap (ofInfinite F G).toMonoidHom
  have h0 : ∀ (g : AdelicGroupPoints F G) (t : AdelicGroupPoints F (𝓕.M Q) → ℂ),
      𝓕.leviPairing Q 0 g t = 0 := by
    intro g t
    have hz : 𝓕.leviPairingIntegrand Q 0 g t = 0 := by
      funext x
      simp [leviPairingIntegrand]
    simp [leviPairing, hz]
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have : Subsingleton (AdelicGroupPoints F G) := subsingleton_hom_of_fin_zero rho hrho _
    funext g
    obtain ⟨-, hi, he⟩ := hp.2.2 (fun _ => 1) (𝓕.isLeviCuspForm_one_of_fin_zero Kinf rho hrho Q) g
    have hint : 𝓕.leviPairingIntegrand Q ψ g (fun _ => 1) = fun _ => ψ g := by
      funext x
      simp only [leviPairingIntegrand, map_one, mul_one]
      rw [Subsingleton.elim (map F (𝓕.M Q) G (𝓕.l Q ≫ 𝓕.p Q) _ * g) g]
    rw [h0] at he
    unfold leviPairing at he
    rw [hint] at hi he
    simp only [integral_const] at he
    rcases integrable_const_iff.mp hi with h | h
    · exact h
    · rcases mul_eq_zero.mp he.symm with h' | h'
      · exfalso
        have hu : normOneRationalQuotientHaarMeasure F (𝓕.M Q) Set.univ = 0 :=
          (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
            (Complex.ofReal_eq_zero.mp h')
        exact normOneRationalQuotientHaarMeasure_ne_zero F (𝓕.M Q)
          (Measure.measure_univ_eq_zero.mp hu)
      · exact h'
  · apply hvan F G 𝓕 K hK (𝓕.isIwasawaCompact_of_minimal' hKmin) rho hN hrho Q ψ
      ⟨hp.1.1, hp.1.2.1.1, hp.1.2.2.2.2⟩
    intro Q' hQ'
    rcases eq_or_ne Q' Q with rfl | hne
    · rw [𝓕.constantTerm_eq_self_of_automorphicOn Q' hp.1]
      intro t ht g
      obtain ⟨-, hi, he⟩ := hp.2.2 t ht g
      exact ⟨hi, he.symm.trans (h0 g t)⟩
    · rw [hp.2.1 Q' (lt_of_le_of_ne hQ' hne)]
      exact (𝓕.cuspidalAnnihilator Kinf rho Q').zero_mem

end Uniqueness

section Linearity

private theorem constantTerm_sub_of_integrable' {Q : Idx} {f h : AdelicGroupPoints F G → ℂ}
    (hf : 𝓕.HasIntegrableConstantTerm Q f) (hh : 𝓕.HasIntegrableConstantTerm Q h) :
    𝓕.constantTerm Q (f - h) = 𝓕.constantTerm Q f - 𝓕.constantTerm Q h := by
  funext g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  exact integral_sub (hf g) (hh g)

private theorem constantTerm_zero' (Q : Idx) : 𝓕.constantTerm Q 0 = 0 := by
  funext g
  unfold constantTerm AdelicGroupPoints.subgroupConstantTerm
  exact integral_zero _ _

variable {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))

private theorem leviPairingIntegrand_sub' (P : Idx) (f h : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (ψ : AdelicGroupPoints F (𝓕.M P) → ℂ) :
    𝓕.leviPairingIntegrand P (f - h) g ψ =
      𝓕.leviPairingIntegrand P f g ψ - 𝓕.leviPairingIntegrand P h g ψ := by
  funext x
  simp only [leviPairingIntegrand, Pi.sub_apply, sub_mul]

/-- Cuspidal projections of two inputs give a cuspidal projection of their difference. -/
private theorem isCuspidalProjection_sub' {P : Idx} {f f' fc fc' : AdelicGroupPoints F G → ℂ}
    (h₁ : 𝓕.IsCuspidalProjection hsmooth Kinf rho P f fc)
    (h₂ : 𝓕.IsCuspidalProjection hsmooth Kinf rho P f' fc') :
    𝓕.IsCuspidalProjection hsmooth Kinf rho P (f - f') (fc - fc') := by
  refine ⟨(𝓕.automorphicSubmodule hsmooth Kinf rho P).sub_mem h₁.1 h₂.1,
    𝓕.isCuspidalAlong_sub hsmooth Kinf rho P h₁.1 h₂.1 h₁.2.1 h₂.2.1, ?_⟩
  intro ψ hψ g
  obtain ⟨i₁, j₁, e₁⟩ := h₁.2.2 ψ hψ g
  obtain ⟨i₂, j₂, e₂⟩ := h₂.2.2 ψ hψ g
  refine ⟨?_, ?_, ?_⟩
  · rw [leviPairingIntegrand_sub']
    exact i₁.sub i₂
  · rw [leviPairingIntegrand_sub']
    exact j₁.sub j₂
  · unfold leviPairing at e₁ e₂ ⊢
    rw [leviPairingIntegrand_sub', leviPairingIntegrand_sub']
    simp only [Pi.sub_apply]
    rw [integral_sub i₁ i₂, integral_sub j₁ j₂, e₁, e₂]

end Linearity

section Ranks

/-- If `R = P ∪ {α}` with `α ∉ P`, every `Q ⊊ R` of at least the semisimple rank of `P` is a
maximal parabolic subgroup of `R`. -/
private theorem exists_root_insert_eq {P Q R : Idx} {α : relativeRoots 𝓕.i} (hαP : α.1 ∉ P.1)
    (hR : R.1 = insert α.1 P.1) (hQR : Q ≤ R) (hne : Q ≠ R) (hcard : P.1.ncard ≤ Q.1.ncard) :
    ∃ β : relativeRoots 𝓕.i, β.1 ∉ Q.1 ∧ insert β.1 Q.1 = R.1 := by
  have hss : Q.1 ⊂ R.1 := LE.le.ssubset_of_ne hQR (fun h => hne (Subtype.ext h))
  obtain ⟨b, hbR, hbQ⟩ := Set.exists_of_ssubset hss
  refine ⟨⟨b, simpleRelativeRoots_subset_relativeRoots 𝓕.i 𝓕.ν (R.2 hbR)⟩, hbQ, ?_⟩
  have hRfin : R.1.Finite := 𝓕.finite_simpleRoots.subset R.2
  have hPfin : P.1.Finite := 𝓕.finite_simpleRoots.subset P.2
  have hQfin : Q.1.Finite := 𝓕.finite_simpleRoots.subset Q.2
  apply Set.eq_of_subset_of_ncard_le (Set.insert_subset hbR hQR) _ hRfin
  rw [Set.ncard_insert_of_notMem hbQ hQfin, hR, Set.ncard_insert_of_notMem hαP hPfin]
  omega

end Ranks

section Main

attribute [local instance] positiveSplitComponentCommGroup

/-- Bernstein–Lapid, Corollary 6.4, from the lemma of §6.4 for the Levi of `P_α`
(`CuspidalExponentNonexistenceStatement`), the vanishing criterion (8.1) and the automorphy of
constant terms. -/
theorem exists_cuspidalExponent_ascent
    (hnon : CuspidalExponentNonexistenceStatement.{u})
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (hcta : ConstantTermAutomorphyStatement.{u})
    (K : Subgroup (AdelicGroupPoints F G)) (hK : IsMaximalCompactSubgroup F G K)
    (hKmin : IsIwasawaCompact (𝓕.p ⟨∅, Set.empty_subset _⟩) K)
    (hKlevi : ∀ J : Idx, IsMaximalCompactSubgroup F (𝓕.M J)
      (K.comap (AdelicGroupPoints.map F (𝓕.M J) G (𝓕.l J ≫ 𝓕.p J)).toMonoidHom))
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hrho : IsClosedSubgroup rho)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
      (rationalSubgroup F G) (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    (φc : Idx → AdelicGroupPoints F G → ℂ)
    (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ)
    (hdata : 𝓕.IsCuspidalExponentFamily hsmooth (K.comap (ofInfinite F G).toMonoidHom) rho
      φ φc s c)
    (P : Idx) (lam : ComplexCharacterParameter F (𝓕.P P)) (hlam : lam ∈ s P)
    (hclam : c P lam ≠ 0)
    (hmin : ∀ Q : Idx, Q.1.ncard < P.1.ncard → ∀ mu ∈ s Q, c Q mu = 0)
    (α : relativeRoots 𝓕.i) (hαs : α.1 ∈ simpleRelativeRoots 𝓕.i 𝓕.ν) (hαP : α.1 ∉ P.1) :
    ∃ (Q : Idx) (β : relativeRoots 𝓕.i), β.1 ∉ Q.1 ∧ insert β.1 Q.1 = insert α.1 P.1 ∧
      ∃ mu ∈ s Q, c Q mu ≠ 0 ∧
        0 ≤ pair 𝓕.T (𝓕.realExponent Q mu) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) ∧
        𝓕.realExponent P lam - 𝓕.realExponent Q mu ∈ 𝓕.rootSpanReal (insert α.1 P.1) := by
  classical
  set Kinf := K.comap (ofInfinite F G).toMonoidHom with hKinf
  have : Finite Idx := (Set.Finite.finite_subsets 𝓕.finite_simpleRoots).to_subtype
  let := Fintype.ofFinite Idx
  by_contra hcon
  -- the negation of the conclusion
  have hH : ∀ (Q : Idx) (β : relativeRoots 𝓕.i), β.1 ∉ Q.1 → insert β.1 Q.1 = insert α.1 P.1 →
      ∀ mu ∈ s Q, c Q mu ≠ 0 →
      𝓕.realExponent P lam - 𝓕.realExponent Q mu ∈ 𝓕.rootSpanReal (insert α.1 P.1) →
      pair 𝓕.T (𝓕.realExponent Q mu) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) < 0 := by
    intro Q β hβ hins mu hmu hc hspan
    by_contra hge
    exact hcon ⟨Q, β, hβ, hins, mu, hmu, hc, not_lt.mp hge, hspan⟩
  -- the parabolic `P_α`
  let R : Idx := ⟨insert α.1 P.1, Set.insert_subset hαs P.2⟩
  have hPR : P ≤ R := Set.subset_insert _ _
  have hPneR : P ≠ R := by
    intro h
    apply hαP
    have : α.1 ∈ R.1 := Set.mem_insert _ _
    rwa [← h] at this
  -- `f₀ = C_R φ - φc_R` on `U_R(𝔸) M_R(F) \ G(𝔸)`
  have hφtop : 𝓕.IsAutomorphicOn hsmooth Kinf rho 𝓕.top φ := by
    unfold IsAutomorphicOn
    rw [𝓕.parabolicQuotientSubgroup_top]
    exact hφ
  have hCR : 𝓕.IsAutomorphicOn hsmooth Kinf rho R (𝓕.constantTerm R φ) :=
    hcta F G 𝓕 Kinf rho hsmooth hrho 𝓕.top R (𝓕.le_top R) φ hφtop
  have hcR := (hdata R).1
  set f₀ := 𝓕.constantTerm R φ - φc R with hf₀def
  have hf₀ : 𝓕.IsAutomorphicOn hsmooth Kinf rho R f₀ :=
    (𝓕.automorphicSubmodule hsmooth Kinf rho R).sub_mem hCR hcR.1
  let fφ : ContinuousRationalFunctions F G := ⟨⟨φ, fun r x => hφ.1 _ ⟨r, rfl⟩ x⟩, hφ.2.1.1⟩
  -- its family of cuspidal projections and exponent decompositions
  let φc₀ : Idx → AdelicGroupPoints F G → ℂ := fun Q => if Q = R then 0 else φc Q
  let s₀ : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)) :=
    fun Q => if Q = R then ∅ else s Q
  have hfam₀ : ∀ Q : Idx, Q ≤ R →
      𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q f₀) (φc₀ Q) ∧
        𝓕.IsExponentDecomposition hsmooth Kinf rho Q (φc₀ Q) (s₀ Q) (c Q) := by
    intro Q hQR
    by_cases hQ : Q = R
    · subst hQ
      simp only [φc₀, s₀, ite_true]
      rw [𝓕.constantTerm_eq_self_of_automorphicOn R hf₀]
      refine ⟨?_, ⟨by simp, fun _ h => absurd h (Finset.notMem_empty _),
        fun _ h => absurd h (Finset.notMem_empty _), fun _ h => absurd h (Finset.notMem_empty _)⟩⟩
      have hself : 𝓕.IsCuspidalProjection hsmooth Kinf rho R (φc R) (φc R) :=
        ⟨hcR.1, hcR.2.1, fun t ht g =>
          ⟨(hcR.2.2 t ht g).2.1, (hcR.2.2 t ht g).2.1, rfl⟩⟩
      have h := 𝓕.isCuspidalProjection_sub' hsmooth Kinf rho hcR hself
      rwa [sub_self] at h
    · have hlt : Q < R := lt_of_le_of_ne hQR hQ
      simp only [φc₀, s₀, hQ, ↓reduceIte]
      have hint₁ := (𝓕.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQR le_rfl
        hCR).2
      have hint₂ := (𝓕.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQR le_rfl
        hcR.1).2
      have htrans : 𝓕.constantTerm Q (𝓕.constantTerm R φ) = 𝓕.constantTerm Q φ :=
        𝓕.constantTerm_constantTerm_of_le hQR fφ
      rw [hf₀def, 𝓕.constantTerm_sub_of_integrable' hint₁ hint₂, htrans, hcR.2.1 Q hlt, sub_zero]
      exact hdata Q
  -- the difference operator killing the components whose exponents have the wrong real
  -- central character on `𝔄_R`
  let Ix := Σ Q : Idx, ComplexCharacterParameter F (𝓕.P Q)
  let bad : Ix → Prop := fun x => ∃ (h : x.1 ≤ R) (a : 𝓕.positiveSplitComponent R),
    ‖parameterPower F (𝓕.P x.1) x.2 (𝓕.splitLift h a)‖ ≠
      ‖parameterPower F (𝓕.P P) lam (𝓕.splitLift hPR a)‖
  let Bad : Finset Ix := ((Finset.univ : Finset Idx).sigma s).filter bad
  let A : Ix → 𝓕.positiveSplitComponent R := fun x =>
    if hx : bad x then hx.choose_spec.choose else 1
  let Z : Ix → ℂ := fun x =>
    if hx : bad x then parameterPower F (𝓕.P x.1) x.2 (𝓕.splitLift hx.choose (A x)) else 0
  let kdeg : Ix → ℕ := fun x =>
    if hx : x.2 ∈ s x.1 then ((hdata x.1).2.exponent x.2 hx).choose else 0
  let M : Ix → ℕ := fun x => kdeg x + 1
  let D : MonoidAlgebra ℂ (𝓕.positiveSplitComponent R) :=
    ∏ x ∈ Bad, (MonoidAlgebra.of ℂ _ (A x) - algebraMap ℂ _ (Z x)) ^ M x
  have hdeg : ∀ (Q : Idx) (mu : ComplexCharacterParameter F (𝓕.P Q)) (hmu : mu ∈ s Q),
      𝓕.HasPolynomialOrbit Q mu (kdeg ⟨Q, mu⟩) (c Q mu) := by
    intro Q mu hmu
    have h := ((hdata Q).2.exponent mu hmu).choose_spec
    simp only [kdeg, hmu, ↓reduceDIte]
    exact h
  have hkill : ∀ x ∈ Bad, 𝓕.shiftAlgHom R D (c x.1 x.2) = 0 := by
    intro x hxB
    obtain ⟨hxs, hxb⟩ := Finset.mem_filter.mp hxB
    have hmem : x.2 ∈ s x.1 := (Finset.mem_sigma.mp hxs).2
    apply 𝓕.shiftAlgHom_prod_eq_zero Bad A Z M hxB
    have h := 𝓕.shiftAlgHom_factor_eq_zero hxb.choose (hdeg x.1 x.2 hmem) (A x)
    simp only [Z, M, hxb, ↓reduceDIte]
    exact h
  have hZ : ∀ x ∈ Bad, Z x ≠ parameterPower F (𝓕.P P) lam (𝓕.splitLift hPR (A x)) := by
    intro x hxB heq
    have hxb := (Finset.mem_filter.mp hxB).2
    have hspec := hxb.choose_spec.choose_spec
    simp only [Z, A, hxb, ↓reduceDIte] at heq
    exact hspec (congrArg norm heq)
  -- the lemma of §6.4 for the filtered function
  have hL1 : 𝓕.IsAutomorphicOn hsmooth Kinf rho R (𝓕.shiftAlgHom R D f₀) :=
    IsAutomorphicOn.shiftAlgHom 𝓕 hsmooth Kinf rho le_rfl hf₀ D
  have hL2 : 𝓕.IsRelativeCuspidalExponentFamily hsmooth Kinf rho R (𝓕.shiftAlgHom R D f₀)
      (fun Q => 𝓕.shiftAlgHom R D (φc₀ Q)) s₀ (fun Q mu => 𝓕.shiftAlgHom R D (c Q mu)) := by
    intro Q hQR
    obtain ⟨hp, hd⟩ := hfam₀ Q hQR
    rw [𝓕.constantTerm_shiftAlgHom hQR
      (𝓕.mem_radicalIntegrableSubmodule_of_automorphicOn hsmooth Kinf rho hQR le_rfl hf₀) D]
    exact ⟨IsCuspidalProjection.shiftAlgHom 𝓕 hsmooth Kinf rho hQR hp D,
      IsExponentDecomposition.shiftAlgHom 𝓕 hsmooth Kinf rho hQR hd D⟩
  have hL3 : ∀ Q : Idx, Q ≤ R → ∀ mu ∈ s₀ Q, 𝓕.shiftAlgHom R D (c Q mu) ≠ 0 →
      ∃ β : relativeRoots 𝓕.i, β.1 ∉ Q.1 ∧ insert β.1 Q.1 = R.1 ∧
        pair 𝓕.T (𝓕.realExponent Q mu) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) < 0 := by
    intro Q hQR mu hmu hne
    by_cases hQ : Q = R
    · exfalso
      simp [s₀, hQ] at hmu
    · have hmu' : mu ∈ s Q := by simpa only [s₀, hQ, ↓reduceIte] using hmu
      have hc : c Q mu ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
      have hgood : ∀ a : 𝓕.positiveSplitComponent R,
          ‖parameterPower F (𝓕.P Q) mu (𝓕.splitLift hQR a)‖ =
            ‖parameterPower F (𝓕.P P) lam (𝓕.splitLift hPR a)‖ := by
        by_contra hb
        push Not at hb
        have hxB : (⟨Q, mu⟩ : Ix) ∈ Bad :=
          Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hmu'⟩, hQR, hb⟩
        exact hne (hkill _ hxB)
      have hspan := 𝓕.realExponent_sub_mem_rootSpanReal hPR hQR lam mu hgood
      have hcard : P.1.ncard ≤ Q.1.ncard := by
        by_contra hlt
        exact hc (hmin Q (not_le.mp hlt) mu hmu')
      obtain ⟨β, hβ, hins⟩ := 𝓕.exists_root_insert_eq hαP rfl hQR hQ hcard
      exact ⟨β, hβ, hins, hH Q β hβ hins mu hmu' hc hspan⟩
  have hzero : 𝓕.shiftAlgHom R D f₀ = 0 :=
    hnon F G 𝓕 K hK hKmin hKlevi rho hsmooth hrho R _ hL1 _ s₀ _ hL2 hL3
  -- the filtered components along `P` vanish, hence so does `c P λ`
  obtain ⟨hpP, hdP⟩ := hL2 P hPR
  rw [hzero, constantTerm_zero'] at hpP
  have hφc0 := 𝓕.eq_zero_of_isCuspidalProjection_zero hsmooth rho hvan K hK hKmin hrho hpP
  have hs₀P : s₀ P = s P := by simp only [s₀, hPneR, ↓reduceIte]
  have hsum : ∑ mu ∈ s P, 𝓕.shiftAlgHom R D (c P mu) = 0 := by
    rw [← hs₀P, ← hdP.sum_eq]
    exact hφc0
  have hDlam := 𝓕.eq_zero_of_sum_eq_zero_of_hasUnnormalizedExponent P (s P)
    (fun mu => 𝓕.shiftAlgHom R D (c P mu))
    (fun mu hmu => hdP.exponent mu (hs₀P ▸ hmu)) hsum lam hlam
  exact hclam (𝓕.eq_zero_of_shiftAlgHom_prod_eq_zero hPR Bad A Z M (hdeg P lam hlam) hZ hDlam)

end Main

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

/-- Bernstein–Lapid, Corollary 6.4 (`CuspidalExponentAscentStatement`), from the lemma of §6.4
(`CuspidalExponentNonexistenceStatement`), the vanishing criterion (8.1)
(`ParabolicCuspidalVanishingStatement`) and the automorphy of constant terms
(`ConstantTermAutomorphyStatement`). -/
def CuspidalExponentAscentReductionStatement : Prop :=
  CuspidalExponentNonexistenceStatement.{u} → ParabolicCuspidalVanishingStatement.{u} →
    ConstantTermAutomorphyStatement.{u} → CuspidalExponentAscentStatement.{u}

/-- The reduction of Corollary 6.4 to the lemma of §6.4, for closed embeddings of every size. -/
theorem cuspidalExponentAscentReduction : CuspidalExponentAscentReductionStatement.{u} := by
  intro hnon hvan hcta F _ _ G _ _ _ fam K hK hKmin hKlevi N d rho hsmooth hrho Kinf φ hφ φc s c
    hdata P lam hlam hclam hmin α hαs hαP _
  exact fam.exists_cuspidalExponent_ascent hnon hvan hcta K hK hKmin hKlevi rho hsmooth hrho hφ
    φc s c hdata P lam hlam hclam hmin α hαs hαP

end Langlands.Global
