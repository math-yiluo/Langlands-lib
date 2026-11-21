import Langlands.Automorphic.GeneralLinearBlockConstantTermOperator
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Langlands.Global.AdelicLeviFiniteVolume
import Langlands.Global.RelativelyCompactFundamentalDomainProof

/-! # Smooth archimedean coordinates of block constant terms -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Set Topology
open scoped ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Analysis

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type w} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {D : Type u} [TopologicalSpace D] [DiscreteTopology D]

/-- A continuous discrete parameter takes finitely many values on the compact
integration set. On each fiber the compact linear-parameter integral applies. -/
theorem contDiffOn_integral_discrete_parameter (ν : Measure Y) [IsFiniteMeasureOnCompacts ν]
    {K : Set Y} (hK : IsCompact K) {s : Set V} (hs : IsOpen s) {t : Set W} (ht : IsOpen t)
    (p : Y → D) (hp : Continuous p) (A : Y → V →L[ℝ] W) (hA : Continuous A)
    (ψ : D → W → ℂ) (hψ : ∀ q, ContDiffOn ℝ ∞ (ψ q) t)
    (φ : V → Y → ℂ) (hφ : ∀ x ∈ s, Continuous (φ x))
    (heq : ∀ y ∈ K, ∀ x ∈ s, φ x y = ψ (p y) (A y x))
    (hAt : ∀ y ∈ K, ∀ x ∈ s, A y x ∈ t) :
    ContDiffOn ℝ ∞ (fun x => ∫ y in K, φ x y ∂ν) s := by
  classical
  let hP := (hK.image hp).finite_of_discrete
  let P := hP.toFinset
  let C (q : D) := K ∩ p ⁻¹' {q}
  have hC (q : D) : IsCompact (C q) := hK.inter_right ((isClosed_discrete {q}).preimage hp)
  have hCK (q : D) : C q ⊆ K := inter_subset_left
  have hcover : (⋃ q ∈ P, C q) = K := by
    ext y
    rw [mem_iUnion₂]
    exact ⟨fun ⟨q, _, hy⟩ => hCK q hy,
      fun hy => ⟨p y, hP.mem_toFinset.mpr ⟨y, hy, rfl⟩, hy, rfl⟩⟩
  have hdisjoint : (P : Set D).Pairwise (fun q r => Disjoint (C q) (C r)) := by
    intro q _ r _ hqr
    refine Set.disjoint_left.mpr fun y hy hz => hqr ?_
    exact (show p y = q from hy.2).symm.trans (show p y = r from hz.2)
  have hdiff (q : D) : ContDiffOn ℝ ∞ (fun x => ∫ y in C q, ψ q (A y x) ∂ν) s := by
    simpa only [one_mul] using (compactLinearParameterIntegral Y V W ν (C q) (hC q) s hs t ht
      (fun _ => 1) continuous_const A hA (ψ q) (hψ q)
      (fun y hy x hx => hAt y (hCK q hy) x hx)).1
  refine (ContDiffOn.sum (s := P) fun q _ => hdiff q).congr ?_
  intro x hx
  have hint (q : D) : IntegrableOn (φ x) (C q) ν :=
    (hφ x hx).continuousOn.integrableOn_compact (hC q)
  calc
    ∫ y in K, φ x y ∂ν = ∑ q ∈ P, ∫ y in C q, φ x y ∂ν := by
      rw [← hcover, integral_biUnion_finset _ (fun q _ => (hC q).measurableSet)
        hdisjoint (fun q _ => hint q)]
    _ = ∑ q ∈ P, ∫ y in C q, ψ q (A y x) ∂ν := by
      refine Finset.sum_congr rfl fun q _ => setIntegral_congr_fun (hC q).measurableSet ?_
      intro y hy
      rw [heq y (hCK q hy) x hx, show p y = q from hy.2]

end Langlands.Analysis

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.ArchimedeanGL
  Langlands.GroupScheme.GeneralLinear AdelicSubgroupPoints GeneralLinearBlockSemidirect
open scoped CategoryTheory.MonObj Classical Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}

local notation "RF" => CommRingCat.of F
local notation "G" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "N(" e ")" => blockUnipotent (Fin n) RF e
local notation "R(" e ")" => adelicPoints F G N(e)

local instance constantTermSmoothAffine : IsAffine (G).X.left := isAffine_groupScheme (Fin n) RF
local instance constantTermSmoothSmooth : Smooth (G).X.hom := smoothStatement (Fin n) RF
local instance constantTermSmoothLocallyCompact (e : Fin n → ℤ) : LocallyCompactSpace R(e) :=
  (isClosed_adelicPoints_blockUnipotent F e).locallyCompactSpace
local instance constantTermSmoothCompactQuotient (e : Fin n → ℤ) :
    CompactSpace (RationalQuotient F G N(e)) :=
  GroupSchemeFunctions.blockUnipotentRationalQuotientCompactSpace F e
local instance generalLinearConstantTermSmoothRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance generalLinearConstantTermSmoothContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance generalLinearConstantTermSmoothFiniteAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

/-- The same normalized constant term is computed on a measurable fundamental
domain with compact closure, uniformly in the form and evaluation point. -/
theorem exists_blockConstantTerm_compactDomain (e : Fin n → ℤ) :
    ∃ D : Set R(e), MeasurableSet D ∧ IsCompact (closure D) ∧
      ∀ (f : FiniteSmoothRationalFunctions F n) (g : AdelicGL F n),
        finiteSmoothBlockConstantTerm F e f ((GeneralLinearGroupPoints.adelicEquiv F n).symm g) =
          ((Measure.haar : Measure R(e)) D).toReal⁻¹ • ∫ y in D,
            ContinuousRationalFunctions.evaluate F n f.val
              (GeneralLinearGroupPoints.adelicEquiv F n y.val * g) ∂Measure.haar := by
  let Γ := rationalSubgroup F G N(e)
  let a := GeneralLinearGroupPoints.adelicEquiv F n
  have hΓ := isDiscrete_rationalSubgroup F G N(e)
  obtain ⟨K, hK, hcover⟩ := LeftCosetSpace.exists_isCompact_cover Γ
  obtain ⟨D, hD, hDc, _, hFD, -⟩ := LeftCosetSpace.relativelyCompactFundamentalDomain Γ hΓ K hK
    (fun x => by
      obtain ⟨q, hq, hx⟩ := hcover x
      exact ⟨⟨q, hq⟩, hx⟩)
  refine ⟨D, hD, hDc, fun f g => ?_⟩
  let φ (y : R(e)) := ContinuousRationalFunctions.evaluate F n f.val (a y.val * g)
  have hφ (q : Γ) (y : R(e)) : φ (q.val * y) = φ y := by
    obtain ⟨r, hr⟩ := q.property
    change f.val.val.val (a (q.val.val * y.val) * g) = _
    rw [← hr, map_mul, rational_coe, GeneralLinearGroupPoints.adelicEquiv_rational, mul_assoc]
    exact f.val.val.property (GeneralLinearGroupPoints.rationalEquiv F n r.val) _
  have hcount : Countable Γ := LeftCosetSpace.countable_of_isDiscrete Γ hΓ
  rw [finiteSmoothBlockConstantTerm_apply, GroupSchemeFunctions.normalizedBlockConstantTerm_eq_domain]
  have harg : (fun y : R(e) => GroupSchemeFunctions.evaluate F G
      ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm f.val)
      (y.val * a.symm g)) = φ := by
    funext y
    change f.val.val.val (a (y.val * a.symm g)) = _
    rw [map_mul, a.apply_symm_apply]
    rfl
  rw [harg]
  unfold LeftCosetSpace.normalizedFundamentalDomainIntegral
  change ((Measure.haar : Measure R(e)) (LeftCosetSpace.fundamentalDomain Γ hΓ)).toReal⁻¹ •
    (∫ y in LeftCosetSpace.fundamentalDomain Γ hΓ, φ y ∂Measure.haar) =
      ((Measure.haar : Measure R(e)) D).toReal⁻¹ • ∫ y in D, φ y ∂Measure.haar
  rw [(LeftCosetSpace.isFundamentalDomain Γ hΓ Measure.haar).measure_eq (hFD _),
    (LeftCosetSpace.isFundamentalDomain Γ hΓ Measure.haar).setIntegral_eq (hFD _) hφ]

/-- The coordinate expression of the block constant term at one finite
adelic argument. The smoothness assertion is on the invertible locus. -/
def blockConstantTermMatrixSlice (e : Fin n → ℤ) (f : FiniteSmoothRationalFunctions F n)
    (b : FiniteAdelicGL F n) (x : ArchimedeanMatrix F n) : ℂ :=
  finiteSmoothBlockConstantTerm F e f ((GeneralLinearGroupPoints.adelicEquiv F n).symm
    (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm ((unitsChart F n).symm x)) b))

set_option maxHeartbeats 800000 in
/-- A finite-smooth function has a smooth archimedean constant term at
every finite adelic argument. -/
theorem contDiffOn_blockConstantTermMatrixSlice (e : Fin n → ℤ)
    (f : FiniteSmoothRationalFunctions F n) (b : FiniteAdelicGL F n) :
    ContDiffOn ℝ ∞ (blockConstantTermMatrixSlice F e f b)
      (range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n)) := by
  obtain ⟨D, hD, hDc, hFD⟩ := exists_blockConstantTerm_compactDomain F e
  obtain ⟨L, hL⟩ := f.property.2
  let T := FiniteAdelicGL F n ⧸ L.toSubgroup
  let : DiscreteTopology T := QuotientGroup.discreteTopology L.isOpen
  let yFull (y : R(e)) := GeneralLinearGroupPoints.adelicHomeomorph F n y.val
  let yArch (y : R(e)) := archimedeanGLCoordinates F n (AdelicGL.infinite F n (yFull y))
  let yFin (y : R(e)) := AdelicGL.finite F n (yFull y) * b
  let p : R(e) → T := fun y => QuotientGroup.mk (yFin y)
  let A (y : R(e)) : ArchimedeanMatrix F n →L[ℝ] ArchimedeanMatrix F n :=
    ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n) (yArch y).val
  let ψ (q : T) := coordinateExtension F n (finiteSmoothSlice F n q.out f)
  let φ (x : ArchimedeanMatrix F n) (y : R(e)) := ContinuousRationalFunctions.evaluate F n f.val
    (yFull y * AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm ((unitsChart F n).symm x)) b)
  let U := range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n)
  let ν := (Measure.haar : Measure R(e)).restrict D
  have hU : IsOpen U := Units.isOpenEmbedding_val.isOpen_range
  have hFull : Continuous yFull := (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous.comp
    continuous_subtype_val
  have hyArch : Continuous yArch := (archimedeanGLCoordinates F n).continuous.comp
    ((AdelicGL.infinite F n).continuous.comp hFull)
  have hp : Continuous p := QuotientGroup.continuous_mk.comp
    (((AdelicGL.finite F n).continuous.comp hFull).mul_const b)
  have hA : Continuous A := (ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n)).continuous.comp
    (Units.continuous_val.comp hyArch)
  have hchart (x : ArchimedeanGL F n) : (unitsChart F n).symm x.val = x := by
    simp only [unitsChart, IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]
  have heq (y : R(e)) (x : ArchimedeanGL F n) : φ x.val y = ψ (p y) (A y x.val) := by
    have hcoset : QuotientGroup.mk ((p y).out) = QuotientGroup.mk (yFin y) :=
      Quotient.out_eq (p y)
    have hy : (p y).out⁻¹ * yFin y ∈ L.toSubgroup := QuotientGroup.eq.mp hcoset
    let c : L := ⟨_, hy⟩
    let a := (archimedeanGLCoordinates F n).symm (yArch y * x)
    have hright := congrArg (fun s : ContinuousRationalFunctions F n =>
      ContinuousRationalFunctions.evaluate F n s (AdelicGL.pair F n a (p y).out)) (hL c)
    change f.val.val.val (AdelicGL.pair F n a (p y).out * AdelicGL.ofFinite F n c.val) =
      f.val.val.val (AdelicGL.pair F n a (p y).out) at hright
    rw [AdelicGL.ofFinite_eq_pair, AdelicGL.pair_mul, mul_one] at hright
    change f.val.val.val (AdelicGL.pair F n a ((p y).out * ((p y).out⁻¹ * yFin y))) = _ at hright
    rw [mul_inv_cancel_left] at hright
    change f.val.val.val (yFull y * AdelicGL.pair F n _ b) = _
    rw [hchart, show yFull y = AdelicGL.pair F n (AdelicGL.infinite F n (yFull y))
      (AdelicGL.finite F n (yFull y)) from (AdelicGL.pair_projections F n _).symm,
      AdelicGL.pair_mul]
    change f.val.val.val (AdelicGL.pair F n _ (yFin y)) = ψ (p y) (A y x.val)
    change _ = ψ (p y) (yArch y * x : ArchimedeanGL F n).val
    rw [show ψ (p y) (yArch y * x : ArchimedeanGL F n).val =
      f.val.val.val (AdelicGL.pair F n a (p y).out) from coordinateExtension_apply F n _ _]
    rw [← hright]
    simp only [a, yArch, map_mul, ContinuousMulEquiv.symm_apply_apply]
  have hDiff := Langlands.Analysis.contDiffOn_integral_discrete_parameter ν hDc hU hU p hp A hA
    ψ (fun q => coordinateExtension_contDiffOn F n _) φ
    (fun x _ => f.val.property.comp (hFull.mul_const _))
    (by rintro y _ _ ⟨x, rfl⟩; exact heq y x)
    (by rintro y _ _ ⟨x, rfl⟩; exact ⟨yArch y * x, rfl⟩)
  refine ((contDiffOn_const (c := (((Measure.haar : Measure R(e)) D).toReal⁻¹ : ℂ))).mul
    hDiff).congr ?_
  intro x _
  rw [blockConstantTermMatrixSlice, hFD]
  have hrestrict : ν.restrict (closure D) = (Measure.haar : Measure R(e)).restrict D := by
    rw [Measure.restrict_restrict isClosed_closure.measurableSet, inter_eq_right.mpr subset_closure]
  rw [show (∫ y in closure D, φ x y ∂ν) = ∫ y in D, φ x y ∂Measure.haar by rw [← hrestrict]]
  simp only [Complex.real_smul, Complex.ofReal_inv]
  rfl

end Langlands.Automorphic
