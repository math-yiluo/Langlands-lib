import Langlands.Global.AdelicCuspidalExponentBoundednessStatement
import Langlands.Global.AdelicCuspidalExponentAscentReduction
import Langlands.Global.AdelicParabolicConstantTermTransitivity
import Langlands.Analysis.BoundedExponentialPolynomial
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # The lemma of Bernstein–Lapid §6.4 from the boundedness of Mœglin–Waldspurger I.4.1 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Polynomial
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

section Roots

omit [NumberField F] in
/-- The restriction to the maximal split torus of a character of the Levi `M_J` is annihilated
by the coroots of `J`. -/
theorem leviCharacter_mem_corootAnnihilator (J : Idx)
    (χ : GroupScheme.rationalCharacters (𝓕.M J)) :
    rationalCharacterRestrictReal (𝓕.torus J) ((1 : ℝ) ⊗ₜ[ℤ] χ) ∈
      corootAnnihilator 𝓕.i 𝓕.coroots J.1 := by
  have hp := (𝓕.isCompatible J).parabolic.isClosedSubgroup
  have hLevi := (𝓕.isCompatible J).levi.isClosedSubgroup.comp hp
  let : Mono (𝓕.l J ≫ 𝓕.p J).hom.hom.left := hLevi.mono
  have hrep : (standardLevi 𝓕.i 𝓕.ν J.1).IsRepresentedBy (𝓕.l J ≫ 𝓕.p J) :=
    ⟨Over.mono_of_mono_left _, (𝓕.isCompatible J).levi_eq⟩
  have hAnn := standardLeviCharacterAnnihilator F G 𝓕.connectedReductive 𝓕.T 𝓕.i
    𝓕.maximalSplit 𝓕.ν 𝓕.generic J.1 J.2 (𝓕.M J) (𝓕.l J ≫ 𝓕.p J) hLevi hrep (𝓕.torus J)
    (𝓕.torus_comp J) 𝓕.coroots
  rw [← hAnn]
  exact ⟨_, rfl⟩

omit [NumberField F] in
/-- The real exponent of a parameter of `P_J` is annihilated by the coroots of `J`. -/
theorem realExponent_mem_corootAnnihilator_of_le (J : Idx)
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
  exact ⟨rationalCharacterRestrictReal (𝓕.l J) (parameterRealPart F (𝓕.P J) lam), hcomp _⟩

omit [NumberField F] in
/-- For a simple root `β` of `R ⊇ Q`, the projection `w` of `β^∨` to `𝔞_Q` along the coroots of
`Q` lies in the coroot span of `R`; it pairs with `𝔞_Q^*` as `β^∨` does and is annihilated by
`𝔞_R^*`. -/
theorem exists_coroot_projection {Q R : Idx} (hQR : Q ≤ R) (β : relativeRoots 𝓕.i)
    (hβ : β.1 ∈ R.1) :
    ∃ w : V 𝓕.T, w ∈ rootAnnihilator 𝓕.T Q.1 ∧
      (∀ x ∈ corootAnnihilator 𝓕.i 𝓕.coroots R.1, pair 𝓕.T x w = 0) ∧
      ∀ x ∈ corootAnnihilator 𝓕.i 𝓕.coroots Q.1,
        pair 𝓕.T x w = pair 𝓕.T x ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) := by
  have hc : IsCompl (rootAnnihilator 𝓕.T Q.1) (Submodule.span ℝ (𝓕.coroots.realCorootsOf Q.1)) :=
    ((standardLeviRealDecomposition F G 𝓕.connectedReductive 𝓕.T 𝓕.i 𝓕.maximalSplit
      𝓕.ν 𝓕.generic 𝓕.coroots).2.2.2 Q.1 R.1 hQR R.2).2.1
  have hmem : 𝓕.coroots.realCoroot β ∈
      rootAnnihilator 𝓕.T Q.1 ⊔ Submodule.span ℝ (𝓕.coroots.realCorootsOf Q.1) := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨w, hw, u, hu, hwu⟩ := Submodule.mem_sup.mp hmem
  have hker : ∀ (J : Set (characterLattice 𝓕.T)) (x : Vstar 𝓕.T),
      x ∈ corootAnnihilator 𝓕.i 𝓕.coroots J →
      Submodule.span ℝ (𝓕.coroots.realCorootsOf J) ≤ LinearMap.ker (pair 𝓕.T x) := by
    intro J x hx
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, hb, rfl⟩
    exact (mem_corootAnnihilator 𝓕.i 𝓕.coroots J x).mp hx b hb
  have hsub : 𝓕.coroots.realCorootsOf Q.1 ⊆ 𝓕.coroots.realCorootsOf R.1 := by
    rintro _ ⟨b, hb, rfl⟩
    exact ⟨b, hQR hb, rfl⟩
  have h1 : 𝓕.coroots.realCoroot β ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf R.1) :=
    Submodule.subset_span ⟨β, hβ, rfl⟩
  have h2 : u ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf R.1) := Submodule.span_mono hsub hu
  have hw' : w = 𝓕.coroots.realCoroot β - u := eq_sub_of_add_eq hwu
  have hwR : w ∈ Submodule.span ℝ (𝓕.coroots.realCorootsOf R.1) := by
    rw [hw']
    exact Submodule.sub_mem _ h1 h2
  refine ⟨w, hw, fun x hx => hker R.1 x hx hwR, fun x hx => ?_⟩
  have hu0 : pair 𝓕.T x u = 0 := hker Q.1 x hx hu
  have hβeq : (1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β = w + u := hwu.symm
  rw [hβeq, map_add, hu0, add_zero]

end Roots

section Torus

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
theorem cocharacterFunctional_smul {T : CommGroupScheme (Spec (CommRingCat.of F))} (t : ℝ)
    (w : V T) : cocharacterFunctional (t • w) = t • cocharacterFunctional (F := F) w := by
  apply AddMonoidHom.ext
  intro χ
  change pair T (1 ⊗ₜ[ℤ] χ) (t • w) = t * pair T (1 ⊗ₜ[ℤ] χ) w
  rw [map_smul, smul_eq_mul]

omit [NumberField F] [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The real part of `⟨μ, H⟩` at the image of the logarithm of a torus point. -/
theorem re_complexParameterPairing_cocharacterFunctional
    {T : CommGroupScheme (Spec (CommRingCat.of F))} {H : GroupScheme (Spec (CommRingCat.of F))}
    (j : T.toGrp ⟶ H) (mu : ComplexCharacterParameter F H) (v : V T) :
    (complexParameterPairing F H mu
      (realCharacterDualMap F T.toGrp H j (cocharacterFunctional v))).re =
      pair T (realParameterRestriction j (parameterRealPart F H mu)) v := by
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

/-- A point of `𝔄_Q` with the image in `G(𝔸)` of a torus point `t` is the image of `t`. -/
theorem eq_map_torus_of_map_eq {Q : Idx} {a : AdelicGroupPoints F (𝓕.P Q)}
    {t : AdelicGroupPoints F 𝓕.T.toGrp}
    (ht : map F (𝓕.P Q) G (𝓕.p Q) a = map F 𝓕.T.toGrp G 𝓕.i t) :
    a = map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) t := by
  let := (𝓕.isCompatible Q).parabolic.isClosedSubgroup.mono
  have : Mono (𝓕.p Q).hom.hom := Over.mono_of_mono_left _
  have h1 : map F (𝓕.P Q) G (𝓕.p Q) a =
      map F (𝓕.P Q) G (𝓕.p Q) (map F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) t) := by
    rw [ht, ← map_comp_apply_of_hom, Category.assoc, 𝓕.torus_comp]
  simp only [map_apply, GroupScheme.affinePointsTarget_apply] at h1
  exact (cancel_mono _).mp h1

/-- A torus point whose logarithm is annihilated by the restricted characters of `M_R` maps into
the norm-one subgroup `M_R(𝔸)^1`. -/
theorem map_torus_mem_normOneSubgroup (R : Idx) {t : AdelicGroupPoints F 𝓕.T.toGrp}
    {v : V 𝓕.T} (ht : characterLog F 𝓕.T.toGrp t = cocharacterFunctional v)
    (hv : ∀ x ∈ corootAnnihilator 𝓕.i 𝓕.coroots R.1, pair 𝓕.T x v = 0) :
    map F 𝓕.T.toGrp (𝓕.M R) (𝓕.torus R) t ∈ normOneSubgroup F (𝓕.M R) := by
  rw [mem_normOneSubgroup]
  intro χ
  have hlog := congrArg (fun ℓ : RealCharacterDual F 𝓕.T.toGrp =>
    ℓ (GroupScheme.characterRestrict (𝓕.torus R) (Additive.ofMul χ))) ht
  have hzero : cocharacterFunctional v (GroupScheme.characterRestrict (𝓕.torus R)
      (Additive.ofMul χ)) = 0 := by
    rw [cocharacterFunctional_apply]
    exact hv _ (𝓕.leviCharacter_mem_corootAnnihilator R (Additive.ofMul χ))
  rw [hzero, characterLog_apply] at hlog
  have hpos : (0 : ℝ) < ((characterNorm F 𝓕.T.toGrp
      (GroupScheme.characterRestrict (𝓕.torus R) (Additive.ofMul χ)).toMul t : NNReal) : ℝ) := by
    exact_mod_cast pos_iff_ne_zero.mpr (characterNorm F 𝓕.T.toGrp _ t).ne_zero
  have h1 := Real.eq_one_of_pos_of_log_eq_zero hpos hlog
  rw [← characterNorm_comp]
  have h2 : ((characterNorm F 𝓕.T.toGrp (𝓕.torus R ≫ χ) t : NNReal) : ℝ) = 1 := h1
  refine Units.ext (NNReal.eq ?_)
  simpa using h2

end Torus

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

section Helpers

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


/-- For a closed embedding into the general linear group of rank zero, a function with cuspidal
projection `0` along `Q` vanishes (the pairing with the cusp form `1` detects its value). -/
private theorem eq_zero_of_isCuspidalProjection_of_fin_zero
    (rho : MatrixRepresentation G (Fin 0)) (hrho : IsClosedSubgroup rho) {Q : Idx}
    {h : AdelicGroupPoints F G → ℂ} (hp : 𝓕.IsCuspidalProjection hsmooth Kinf rho Q h 0) :
    h = 0 := by
  have : Subsingleton (AdelicGroupPoints F G) := subsingleton_hom_of_fin_zero rho hrho _
  funext g
  obtain ⟨hi, -, he⟩ := hp.2.2 (fun _ => 1) (𝓕.isLeviCuspForm_one_of_fin_zero Kinf rho hrho Q) g
  have hint : 𝓕.leviPairingIntegrand Q h g (fun _ => 1) = fun _ => h g := by
    funext x
    simp only [leviPairingIntegrand, map_one, mul_one]
    rw [Subsingleton.elim (map F (𝓕.M Q) G (𝓕.l Q ≫ 𝓕.p Q) _ * g) g]
  have hz : 𝓕.leviPairingIntegrand Q 0 g (fun _ => 1) = 0 := by
    funext x
    simp [leviPairingIntegrand]
  unfold leviPairing at he
  rw [hint, hz] at he
  rw [hint] at hi
  simp only [Pi.zero_apply, integral_zero, integral_const] at he
  rcases integrable_const_iff.mp hi with h0 | h0
  · exact h0
  · rcases smul_eq_zero.mp he with h' | h'
    · exfalso
      have hu : normOneRationalQuotientHaarMeasure F (𝓕.M Q) Set.univ = 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).mp h'
      exact normOneRationalQuotientHaarMeasure_ne_zero F (𝓕.M Q)
        (Measure.measure_univ_eq_zero.mp hu)
    · exact h'

end Helpers

section Maximal

/-- Bernstein–Lapid, proof of the lemma of §6.4, for a maximal parabolic `Q` of `R`
(`R = Q ∪ {β}`): a finite sum `ψ = ∑ c μ` of functions with generalized exponents `μ` along `Q`,
all nonzero ones with `⟨Re μ, β^∨⟩ < 0`, whose right translates are bounded on `M_R(𝔸)^1`,
vanishes. On the line of torus points with logarithm `t w`, `w` the projection of `β^∨` to
`𝔞_Q`, the function is an exponential polynomial in `t` with exponents of negative real part. -/
theorem eq_zero_of_bounded_of_maximal {Q R : Idx} (hQR : Q ≤ R) (β : relativeRoots 𝓕.i)
    (hins : insert β.1 Q.1 = R.1) {s : Finset (ComplexCharacterParameter F (𝓕.P Q))}
    {c : ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ}
    {ψ : AdelicGroupPoints F G → ℂ} (hsum : ψ = ∑ mu ∈ s, c mu)
    (hexp : ∀ mu ∈ s, 𝓕.HasUnnormalizedExponent Q mu (c mu))
    (hneg : ∀ mu ∈ s, c mu ≠ 0 →
      pair 𝓕.T (𝓕.realExponent Q mu) ((1 : ℝ) ⊗ₜ[ℤ] 𝓕.coroots.coroot β) < 0)
    (hbd : ∀ g : AdelicGroupPoints F G, ∃ C : ℝ, ∀ m ∈ normOneSubgroup F (𝓕.M R),
      ‖ψ (map F (𝓕.M R) G (𝓕.l R ≫ 𝓕.p R) m * g)‖ ≤ C) :
    ψ = 0 := by
  classical
  have hβR : β.1 ∈ R.1 := hins ▸ Set.mem_insert _ _
  obtain ⟨w, hwQ, hwR, hwβ⟩ := 𝓕.exists_coroot_projection hQR β hβR
  funext g
  obtain ⟨C, hC⟩ := hbd g
  have hP : ∀ mu, mu ∈ s → ∃ P : RealCharacterDual F (𝓕.P Q) → ℂ,
      (∃ n, P ∈ polynomialFunctions (RealCharacterDual F (𝓕.P Q)) n) ∧
      ∀ x ∈ 𝓕.positiveSplitComponent Q,
        𝓕.unnormalizedAction Q x (c mu) g * parameterPower F (𝓕.P Q) (-mu) x =
          P (characterLog F (𝓕.P Q) x) := by
    intro mu hmu
    obtain ⟨n, hn⟩ := hexp mu hmu
    obtain ⟨P, hPm, hPe⟩ := hn g
    exact ⟨P, ⟨n, hPm⟩, hPe⟩
  choose! P hPpoly hPeq using hP
  let H₀ : RealCharacterDual F (𝓕.P Q) :=
    realCharacterDualMap F 𝓕.T.toGrp (𝓕.P Q) (𝓕.torus Q ≫ 𝓕.l Q) (cocharacterFunctional w)
  have hq : ∀ mu, mu ∈ s → ∃ q : ℂ[X], ∀ t : ℝ, P mu (t • H₀) = q.eval (t : ℂ) := by
    intro mu hmu
    obtain ⟨n, hn⟩ := hPpoly mu hmu
    exact Langlands.Analysis.exists_polynomial_eval_smul hn H₀
  choose! q hqeq using hq
  let z : ComplexCharacterParameter F (𝓕.P Q) → ℂ := fun mu =>
    complexParameterPairing F (𝓕.P Q) mu H₀
  let S := s.filter (fun mu => c mu ≠ 0)
  have hS : ∀ x : AdelicGroupPoints F G, ∑ mu ∈ s, c mu x = ∑ mu ∈ S, c mu x := by
    intro x
    refine (Finset.sum_filter_of_ne fun mu _ hne => ?_).symm
    intro h0
    exact hne (by rw [h0, Pi.zero_apply])
  have hinv : ∀ (mu : ComplexCharacterParameter F (𝓕.P Q)) (x : AdelicGroupPoints F (𝓕.P Q)),
      parameterPower F (𝓕.P Q) mu x * parameterPower F (𝓕.P Q) (-mu) x = 1 := by
    intro mu x
    rw [← parameterPower_add, add_neg_cancel]
    simp [parameterPower]
  -- the values along the line of torus points
  have hline : ∀ t : ℝ, ∃ m ∈ normOneSubgroup F (𝓕.M R),
      ψ (map F (𝓕.M R) G (𝓕.l R ≫ 𝓕.p R) m * g) = Langlands.Analysis.expPolynomial S z q t := by
    intro t
    have htw : t • w ∈ rootAnnihilator 𝓕.T Q.1 := Submodule.smul_mem _ t hwQ
    obtain ⟨a, τ, haτ, hlog⟩ := 𝓕.exists_positiveSplitComponent_torus_log Q htw
    have hτR : ∀ x ∈ corootAnnihilator 𝓕.i 𝓕.coroots R.1, pair 𝓕.T x (t • w) = 0 := by
      intro x hx
      rw [map_smul, hwR x hx, smul_zero]
    refine ⟨map F 𝓕.T.toGrp (𝓕.M R) (𝓕.torus R) τ,
      𝓕.map_torus_mem_normOneSubgroup R hlog hτR, ?_⟩
    have hmap : map F (𝓕.M R) G (𝓕.l R ≫ 𝓕.p R) (map F 𝓕.T.toGrp (𝓕.M R) (𝓕.torus R) τ) =
        map F (𝓕.P Q) G (𝓕.p Q) a := by
      rw [haτ, ← 𝓕.torus_comp R]
      simp only [map_apply, GroupScheme.affinePointsTarget_apply, Grp.comp_hom_hom,
        Category.assoc]
    have ha := 𝓕.eq_map_torus_of_map_eq haτ
    have hlogA : characterLog F (𝓕.P Q) a = t • H₀ := by
      rw [ha, characterLog_map, hlog, cocharacterFunctional_smul, map_smul]
    have hpow : ∀ mu, parameterPower F (𝓕.P Q) mu a = Complex.exp (t * z mu) := by
      intro mu
      simp only [parameterPower, hlogA, map_smul, Complex.real_smul, z]
    rw [hmap, hsum, Finset.sum_apply, hS]
    unfold Langlands.Analysis.expPolynomial
    refine Finset.sum_congr rfl fun mu hmu => ?_
    have hmus : mu ∈ s := (Finset.mem_filter.mp hmu).1
    have he := hPeq mu hmus a a.2
    rw [hlogA, hqeq mu hmus t] at he
    change c mu (map F (𝓕.P Q) G (𝓕.p Q) a * g) * _ = _ at he
    calc c mu (map F (𝓕.P Q) G (𝓕.p Q) a * g)
        = parameterPower F (𝓕.P Q) mu a *
            (c mu (map F (𝓕.P Q) G (𝓕.p Q) a * g) * parameterPower F (𝓕.P Q) (-mu) a) := by
          linear_combination -(c mu (map F (𝓕.P Q) G (𝓕.p Q) a * g)) * hinv mu a
      _ = _ := by rw [he, hpow]
  have hbound : ∃ C' : ℝ, ∀ t : ℝ, ‖Langlands.Analysis.expPolynomial S z q t‖ ≤ C' :=
    ⟨C, fun t => by
      obtain ⟨m, hm, heq⟩ := hline t
      rw [← heq]
      exact hC m hm⟩
  have hre : ∀ mu ∈ S, (z mu).re < 0 := by
    intro mu hmu
    obtain ⟨hmus, hc⟩ := Finset.mem_filter.mp hmu
    have h1 := re_complexParameterPairing_cocharacterFunctional (𝓕.torus Q ≫ 𝓕.l Q) mu w
    change (z mu).re = pair 𝓕.T (𝓕.realExponent Q mu) w at h1
    rw [h1, hwβ _ (𝓕.realExponent_mem_corootAnnihilator_of_le Q mu)]
    exact hneg mu hmus hc
  have hzero := Langlands.Analysis.expPolynomial_eq_zero_of_bounded S z hre q hbound 0
  -- the value at `g` is the exponential polynomial at `0`
  rw [hsum, Finset.sum_apply, hS, Pi.zero_apply, ← hzero]
  unfold Langlands.Analysis.expPolynomial
  refine Finset.sum_congr rfl fun mu hmu => ?_
  have hmus : mu ∈ s := (Finset.mem_filter.mp hmu).1
  have he := hPeq mu hmus 1 (𝓕.positiveSplitComponent Q).one_mem
  rw [characterLog_one, show (0 : RealCharacterDual F (𝓕.P Q)) = (0 : ℝ) • H₀ from
    (zero_smul ℝ H₀).symm, hqeq mu hmus 0] at he
  change c mu (map F (𝓕.P Q) G (𝓕.p Q) 1 * g) * parameterPower F (𝓕.P Q) (-mu) 1 = _ at he
  rw [map_one, one_mul] at he
  have h1 : parameterPower F (𝓕.P Q) (-mu) 1 = 1 := by simp [parameterPower]
  rw [h1, mul_one] at he
  rw [he]
  simp

end Maximal

section Ranks

/-- Below a maximal parabolic `Q` of `R`, no standard parabolic is maximal in `R`. -/
private theorem not_maximal_of_lt {Q'' Q' Q R : Idx} (h1 : Q'' ≤ Q') (h2 : Q' < Q)
    {β : relativeRoots 𝓕.i} (hβ : β.1 ∉ Q.1) (hins : insert β.1 Q.1 = R.1) :
    ¬ ∃ b : relativeRoots 𝓕.i, b.1 ∉ Q''.1 ∧ insert b.1 Q''.1 = R.1 := by
  rintro ⟨b, hb, hins'⟩
  have hQfin : Q.1.Finite := 𝓕.finite_simpleRoots.subset Q.2
  have hQ''fin : Q''.1.Finite := 𝓕.finite_simpleRoots.subset Q''.2
  have e1 := Set.ncard_insert_of_notMem hβ hQfin
  have e2 := Set.ncard_insert_of_notMem hb hQ''fin
  rw [hins] at e1
  rw [hins'] at e2
  have hne : Q'' ≠ Q := ne_of_lt (lt_of_le_of_lt h1 h2)
  have hsub : Q''.1 ⊆ Q.1 := h1.trans h2.le
  have hss : Q''.1 ⊂ Q.1 := Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hne (Subtype.ext h)⟩
  have hlt := Set.ncard_lt_ncard hss hQfin
  omega

end Ranks

section Main

/-- Bernstein–Lapid, the lemma of §6.4 (`CuspidalExponentNonexistenceStatement`), from the
boundedness of constant terms on `M_R(𝔸)^1` (`CuspidalExponentBoundednessStatement`, the input
from Mœglin–Waldspurger I.4.1), the vanishing criterion (8.1) and the automorphy of constant
terms. -/
theorem cuspidalExponentNonexistence_of_boundedness
    (hB : CuspidalExponentBoundednessStatement.{u})
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (hcta : ConstantTermAutomorphyStatement.{u}) :
    CuspidalExponentNonexistenceStatement.{u} := by
  intro F _ _ G _ _ _ fam K hK hKmin hKlevi N d rho hsmooth hrho Kinf R f hf φc s c hfam hexp
  classical
  -- components along non-maximal parabolics vanish
  have hnm : ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R →
      (¬ ∃ b : relativeRoots fam.i, b.1 ∉ Q.1 ∧ insert b.1 Q.1 = R.1) → φc Q = 0 := by
    intro Q hQ hnot
    rw [(hfam Q hQ).2.sum_eq]
    refine Finset.sum_eq_zero fun mu hmu => ?_
    by_contra hc
    obtain ⟨b, hb, hins, -⟩ := hexp Q hQ mu hmu hc
    exact hnot ⟨b, hb, hins⟩
  -- a vanishing projection puts the constant term in the cuspidal annihilator
  have hann : ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R → φc Q = 0 →
      fam.InCuspidalAnnihilator Kinf rho Q (fam.constantTerm Q f) := by
    intro Q hQ h0 ψ hψ g
    obtain ⟨hi, -, he⟩ := (hfam Q hQ).1.2.2 ψ hψ g
    refine ⟨hi, he.trans ?_⟩
    rw [h0]
    have hz : fam.leviPairingIntegrand Q 0 g ψ = 0 := by
      funext x
      simp [leviPairingIntegrand]
    simp [leviPairing, hz]
  have hR0 : φc R = 0 :=
    hnm R le_rfl (fun ⟨b, hb, hins⟩ => hb (hins ▸ Set.mem_insert _ _))
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    have hp := (hfam R le_rfl).1
    rw [hR0, fam.constantTerm_eq_self_of_automorphicOn R hf] at hp
    exact fam.eq_zero_of_isCuspidalProjection_of_fin_zero hsmooth Kinf rho hrho hp
  have hbdd := hB F G fam K hK hKmin hKlevi rho hsmooth hrho R f hf φc s c hfam hexp
  have hall : ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R → φc Q = 0 := by
    intro Q hQR
    by_cases hQmax : ∃ b : relativeRoots fam.i, b.1 ∉ Q.1 ∧ insert b.1 Q.1 = R.1
    · obtain ⟨β, hβQ, hins⟩ := hQmax
      -- the constant terms along `Q' ⊊ Q` vanish
      have hlow : ∀ Q' : StandardIndex F G fam.i fam.ν, Q' < Q → fam.constantTerm Q' f = 0 := by
        intro Q' hQ'
        have hQ'R : Q' ≤ R := hQ'.le.trans hQR
        have hCQ' := hcta F G fam Kinf rho hsmooth hrho R Q' hQ'R f hf
        apply hvan F G fam K hK (fam.isIwasawaCompact_of_minimal' hKmin) rho hN hrho Q'
          (fam.constantTerm Q' f) ⟨hCQ'.1, hCQ'.2.1.1, hCQ'.2.2.2.2⟩
        intro Q'' hQ''
        rw [fam.constantTerm_constantTerm_of_parabolicQuotient hQ'' hQ'R hf.2.1.1 hf.1]
        exact hann Q'' (hQ''.trans hQ'R)
          (hnm Q'' (hQ''.trans hQ'R) (fam.not_maximal_of_lt hQ'' hQ' hβQ hins))
      -- hence `C_Q f` is cuspidal along `Q` and equals its projection `φc Q`
      have hCQ := hcta F G fam Kinf rho hsmooth hrho R Q hQR f hf
      have hcusp : fam.IsCuspidalAlong Q (fam.constantTerm Q f) := by
        intro Q' hQ'
        rw [fam.constantTerm_constantTerm_of_parabolicQuotient hQ'.le hQR hf.2.1.1 hf.1]
        exact hlow Q' hQ'
      have hself : fam.IsCuspidalProjection hsmooth Kinf rho Q (fam.constantTerm Q f)
          (fam.constantTerm Q f) :=
        ⟨hCQ, hcusp, fun ψ hψ g =>
          ⟨((hfam Q hQR).1.2.2 ψ hψ g).1, ((hfam Q hQR).1.2.2 ψ hψ g).1, rfl⟩⟩
      have hdiff := fam.isCuspidalProjection_sub' hsmooth Kinf rho hself (hfam Q hQR).1
      rw [sub_self] at hdiff
      have heq := fam.eq_zero_of_isCuspidalProjection_zero hsmooth rho hvan K hK hKmin hrho hdiff
      have hCφ : fam.constantTerm Q f = φc Q := sub_eq_zero.mp heq
      -- the exponential-polynomial argument
      refine fam.eq_zero_of_bounded_of_maximal hQR β hins (hfam Q hQR).2.sum_eq
        (hfam Q hQR).2.exponent ?_ ?_
      · intro mu hmu hc
        obtain ⟨b, hb, hins', hlt⟩ := hexp Q hQR mu hmu hc
        have hbR : b.1 ∈ R.1 := hins' ▸ Set.mem_insert _ _
        rw [← hins] at hbR
        have hbβ : b = β := by
          rcases hbR with h | h
          · exact Subtype.ext h
          · exact absurd h hb
        rw [← hbβ]
        exact hlt
      · intro g
        obtain ⟨C, hC⟩ := hbdd Q hQR g
        refine ⟨C, fun m hm => ?_⟩
        rw [← hCφ]
        exact hC m hm
    · exact hnm Q hQR hQmax
  exact hvan F G fam K hK (fam.isIwasawaCompact_of_minimal' hKmin) rho hN hrho R f
    ⟨hf.1, hf.2.1.1, hf.2.2.2.2⟩ (fun Q hQ => hann Q hQ (hall Q hQ))

end Main

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

/-- Bernstein–Lapid, the lemma of §6.4 (`CuspidalExponentNonexistenceStatement`), from the
boundedness supplied by Mœglin–Waldspurger I.4.1 (`CuspidalExponentBoundednessStatement`), the
vanishing criterion (8.1) (`ParabolicCuspidalVanishingStatement`) and the automorphy of
constant terms (`ConstantTermAutomorphyStatement`). -/
def CuspidalExponentNonexistenceReductionStatement : Prop :=
  CuspidalExponentBoundednessStatement.{u} → ParabolicCuspidalVanishingStatement.{u} →
    ConstantTermAutomorphyStatement.{u} → CuspidalExponentNonexistenceStatement.{u}

theorem cuspidalExponentNonexistenceReduction :
    CuspidalExponentNonexistenceReductionStatement.{u} :=
  fun hB hvan hcta => StandardParabolicFamily.cuspidalExponentNonexistence_of_boundedness hB hvan hcta

/-- Bernstein–Lapid, Corollary 6.4 (`CuspidalExponentAscentStatement`), from the boundedness
supplied by Mœglin–Waldspurger I.4.1, the vanishing criterion (8.1) and the automorphy of
constant terms. -/
theorem cuspidalExponentAscent_of_boundedness (hB : CuspidalExponentBoundednessStatement.{u})
    (hvan : ParabolicCuspidalVanishingStatement.{u})
    (hcta : ConstantTermAutomorphyStatement.{u}) : CuspidalExponentAscentStatement.{u} :=
  cuspidalExponentAscentReduction (cuspidalExponentNonexistenceReduction hB hvan hcta) hvan hcta

end Langlands.Global
