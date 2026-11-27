import Langlands.Shimura.PEL.HarrisPrimitiveWeilScalar
import Langlands.AbelianScheme.Tate.FullIsogenyDegree
import Langlands.AbelianScheme.Tate.PrimitiveHom

/-! # Finite kernels of the normalized Harris polarization -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme Langlands.Global
open Global.RationalProfiniteIntegerAdeleComparison (integralEquiv)
open GroupScheme.Tate (Index)

local notation "PAll" => (fun _ : ℕ => True)
local notation "Af" => FiniteAdeles ℚ
local notation "Rf" => integralFiniteAdeles ℚ

private theorem exists_nsmul_eq_iff_dvd {M : Type} [AddCommGroup M]
    (e : Rf ≃+ M) (m : ℕ) (b : Rf) :
    (∃ z, e b = m • z) ↔ (m : Rf) ∣ b := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨a, rfl⟩ := e.surjective z
    rw [← map_nsmul e] at hz
    exact ⟨a, by simpa only [nsmul_eq_mul] using e.injective hz⟩
  · rintro ⟨a, rfl⟩
    exact ⟨e a, by rw [← nsmul_eq_mul, map_nsmul]⟩

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "multiples" => harrisIntegralSourceMultiples D C
local notation "Value" => harrisPrimitiveSourceAdeleValue D C

/-- Source residues pairing to zero at level `m` after a fixed source
operator and multiplication by `a` in the second variable of the primitive form. -/
def HarrisPrimitiveSourceTorsionKernel (u : Λf → Λf) (a m : ℕ) :=
  {q : HarrisIntegralSourceMod D C m //
    ∃ v : Λf, (multiples m).mkQ v = q ∧ ∀ w : Λf, (m : Rf) ∣ (a : Rf) * Value w (u v)}

variable (P : Prerequisites.{0}) {S : Scheme.{0}} [QuasiSeparatedSpace S]
  [IsLocallyNoetherian S] [ConnectedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (s : Spec (.of Ω) ⟶ S)
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index PAll, IsUnit (k.val : Γ(S, ⊤)))

local notation "T" => Over.mk s
local notation "R" => Γ((Over.mk s).left, ⊤)
local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (S := S)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "DOf" X:max =>
  letI := auxiliaryStarRing D C
  dualAbelianSchemeFromEvaluation (BOf X) (X).hasDual (X).geometry P.preservation
    (X).inversePoincare (X).evaluation P.stability P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "Normalized" => HarrisIntegralFrameCondition D C P compatibility h s
local notation "IntAlong" X:max =>
  letI := auxiliaryStarRing D C
  integralWeilAlongHomBilinearMap P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility T
local notation "IntPair" X:max =>
  letI := auxiliaryStarRing D C
  integralWeilBilinearMap P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual
    (X).inversePoincare (X).evaluation compatibility T
local notation "fullEquiv" => harrisIntegralFrameFull D C P compatibility h s
local notation "torsionEquiv" => harrisIntegralFrameTorsionEquiv D C P compatibility h s hu
local notation "primitive" => HarrisPrimitivePolarization D C P
local notation "LevelMap" f:max m:max =>
  GroupScheme.Tate.levelMap T (groupHom f) (m).val
local notation "pointKernel" f:max =>
  (GroupScheme.pointsHom (groupHom f) T).ker
local notation "Intertwines" X:max eta:max hn:max f:max u:max =>
  ∀ v : Λf, GroupScheme.Tate.map T PAll (groupHom f) (fullEquiv X eta hn v) =
    fullEquiv X eta hn (u v)

include htor hu in
/-- A finite-level kernel condition is exactly divisibility of every
integral pairing against the fixed source lattice. -/
theorem primitivePolarization_levelMap_mkQ_eq_zero_iff
    (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (a : ℕ) (m : Index PAll) (v : Λf) :
    (LevelMap (a • mu) m) (torsionEquiv X m eta hn ((multiples m.val).mkQ v)) = 0 ↔
      ∀ w : Λf, (m.val : Rf) ∣ (a : Rf) * Value w v := by
  let := auxiliaryStarRing D C
  let u := harrisPrimitiveWeilUnit D C P compatibility h s htor hu X eta hn mu hmu
  let e : Rf ≃+ TateTwist.Divisibility.Full R :=
    (integralEquiv h).symm.toAddEquiv.trans
      (TateTwist.Divisibility.geometricFullIntegralBasis Ω).toAddEquiv
  let y := GroupScheme.Tate.map T PAll (groupHom (a • mu)) (fullEquiv X eta hn v)
  have hp (w : Λf) : (∃ z, (IntPair X) PAll (fullEquiv X eta hn w) y = m.val • z) ↔
      (m.val : Rf) ∣ (a : Rf) * Value w v := by
    have hval : (IntPair X) PAll (fullEquiv X eta hn w) y =
        e ((a : Rf) * u.val * Value w v) :=
      harrisPrimitiveWeilUnit_integralAlong_nsmul D C P compatibility h s htor hu
        X eta hn mu hmu a w v
    rw [hval, exists_nsmul_eq_iff_dvd e, mul_comm (a : Rf) u.val, mul_assoc]
    exact Units.dvd_mul_left
  rw [harrisIntegralFrameTorsionEquiv_mkQ, ← GroupScheme.Tate.evaluation_map]
  constructor
  · intro hz w
    obtain ⟨y', hy'⟩ := GroupScheme.Tate.full_exists_nsmul_of_evaluation_eq_zero
      (DOf X).toGrp T m y hz
    exact (hp w).mp ⟨(IntPair X) PAll (fullEquiv X eta hn w) y', by
      rw [← hy', map_nsmul]⟩
  · intro hv
    obtain ⟨y', hy'⟩ := integralWeil_exists_nsmul_of_forall P.preservation
      P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      X.hasDual X.inversePoincare X.evaluation compatibility P.square P.universality
      X.geometry hu s m y (fun x => by
        obtain ⟨w, rfl⟩ := (fullEquiv X eta hn).surjective x
        exact (hp w).mpr (hv w))
    change GroupScheme.Tate.evaluation (DOf X).toGrp T PAll m y = 0
    rw [← hy', map_nsmul]
    exact GroupScheme.Tate.level_nsmul_eq_zero (DOf X).toGrp T m.val _

include htor hu in
/-- The actual finite Tate kernel of a multiple of the primitive
polarization composed with an endomorphism is identified with the fixed
source kernel for the corresponding source operator. -/
def primitivePolarizationLevelKernelEquiv
    (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (f : BOf X ⟶ BOf X) (u : Λf → Λf) (hu' : Intertwines X eta hn f u)
    (a : ℕ) (m : Index PAll) :
    HarrisPrimitiveSourceTorsionKernel D C u a m.val ≃ (LevelMap (f ≫ (a • mu)) m).ker :=
  (torsionEquiv X m eta hn).toEquiv.subtypeEquiv (by
    have hlevel (v : Λf) :
        (LevelMap f m) (torsionEquiv X m eta hn ((multiples m.val).mkQ v)) =
          torsionEquiv X m eta hn ((multiples m.val).mkQ (u v)) := by
      rw [harrisIntegralFrameTorsionEquiv_mkQ, harrisIntegralFrameTorsionEquiv_mkQ,
        ← GroupScheme.Tate.evaluation_map, hu']
    have hzero (v : Λf) :
        (LevelMap (f ≫ (a • mu)) m) (torsionEquiv X m eta hn ((multiples m.val).mkQ v)) = 0 ↔
          ∀ w : Λf, (m.val : Rf) ∣ (a : Rf) * Value w (u v) := by
      rw [AbelianScheme.Tate.levelMap_comp, hlevel]
      exact primitivePolarization_levelMap_mkQ_eq_zero_iff D C P compatibility h s
        htor hu X eta hn mu hmu a m (u v)
    intro q
    change (∃ v : Λf, (multiples m.val).mkQ v = q ∧ _) ↔
      (LevelMap (f ≫ (a • mu)) m) (torsionEquiv X m eta hn q) = 0
    constructor
    · rintro ⟨v, rfl, hv⟩
      exact (hzero v).mpr hv
    · intro hq
      obtain ⟨v, rfl⟩ := (multiples m.val).mkQ_surjective q
      exact ⟨v, rfl, (hzero v).mp hq⟩)

omit [QuasiSeparatedSpace S] [IsLocallyNoetherian S] [ConnectedSpace S]
  [IsAlgClosed Ω] [CharZero Ω] in
private def levelKernelEquivPointKernel {B B' : AbelianScheme S} (f : B ⟶ B')
    (m : Index PAll) (hkill : ∀ x : pointKernel f, x.val ^ m.val = 1) :
    (LevelMap f m).ker ≃ pointKernel f where
  toFun x := ⟨(Additive.toMul x.val).val, by
    exact congrArg (fun z : GroupScheme.Tate.Level B'.toGrp T m.val =>
      (Additive.toMul z).val) x.property⟩
  invFun x := ⟨Additive.ofMul ⟨x.val,
    (GroupScheme.Tate.mem_levelGroup B.toGrp T m.val x.val).mpr (hkill x)⟩, by
      apply GroupScheme.Tate.toSection_injective B'.toGrp T m.val
      exact x.property⟩
  left_inv x := rfl
  right_inv x := rfl

include htor hu in
/-- An annihilating torsion level computes the native geometric rank using
the fixed finite source kernel. -/
theorem primitivePolarization_nativeRank_eq_card_sourceKernel
    (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (f : BOf X ⟶ BOf X) (u : Λf → Λf) (hu' : Intertwines X eta hn f u) (a : ℕ)
    (hf : AbelianScheme.IsIsogeny (f ≫ (a • mu))) (m : Index PAll)
    (hkill : ∀ x : pointKernel (f ≫ (a • mu)), x.val ^ m.val = 1)
    (y : ((AbelianScheme.baseChange s).obj (DOf X)).X.left) :
    (hom (f ≫ (a • mu))).finrank (pullback.fst (DOf X).X.hom s y) =
      Nat.card (HarrisPrimitiveSourceTorsionKernel D C u a m.val) := by
  let := auxiliaryStarRing D C
  let ek := levelKernelEquivPointKernel s (f ≫ (a • mu)) m hkill
  let ev := primitivePolarizationLevelKernelEquiv D C P compatibility h s htor hu
    X eta hn mu hmu f u hu' a m
  exact (Tate.finrank_eq_card_fullIsogenyCokernel_at (f ≫ (a • mu)) hf s y).trans
    ((Nat.card_congr (Tate.fullIsogenyCokernelEquiv (f ≫ (a • mu)) hf s).toEquiv).trans
      (Nat.card_congr (ev.trans ek)).symm)

section Comparison

variable {S' : Scheme.{0}} [QuasiSeparatedSpace S'] [IsLocallyNoetherian S']
  [ConnectedSpace S']
  {Ω' : Type} [Field Ω'] [IsAlgClosed Ω'] [CharZero Ω'] (s' : Spec (.of Ω') ⟶ S')
  (hu' : ∀ k : Index PAll, IsUnit (k.val : Γ(S', ⊤)))

local notation "PObj'" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (S := S')
local notation "Frame'" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s'
local notation "Normalized'" => HarrisIntegralFrameCondition D C P compatibility h s'
local notation "pointKernel'" f:max =>
  (GroupScheme.pointsHom (groupHom f) (Over.mk s')).ker
local notation "Intertwines'" Y:max eta:max hn:max f:max u:max =>
  ∀ v : Λf, GroupScheme.Tate.map (Over.mk s') PAll (groupHom f)
    (harrisIntegralFrameFull D C P compatibility h s' Y eta hn v) =
      harrisIntegralFrameFull D C P compatibility h s' Y eta hn (u v)

include htor hu hu' in
/-- Composing the same multiple of the primitive polarization with two
endomorphisms represented by the same source operator gives equal native
geometric ranks whenever both composites are isogenies. -/
theorem primitivePolarizationComp_nativeRank_eq
    (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (Y : PObj') (eta' : Frame' Y) (hn' : Normalized' Y eta')
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : primitive Y mu')
    (f : BOf X ⟶ BOf X) (f' : BOf Y ⟶ BOf Y) (u : Λf → Λf)
    (hmap : Intertwines X eta hn f u) (hmap' : Intertwines' Y eta' hn' f' u) (a : ℕ)
    (hf : AbelianScheme.IsIsogeny (f ≫ (a • mu)))
    (hf' : AbelianScheme.IsIsogeny (f' ≫ (a • mu')))
    (y : ((AbelianScheme.baseChange s).obj (DOf X)).X.left)
    (y' : ((AbelianScheme.baseChange s').obj (DOf Y)).X.left) :
    (hom (f ≫ (a • mu))).finrank (pullback.fst (DOf X).X.hom s y) =
      (hom (f' ≫ (a • mu'))).finrank (pullback.fst (DOf Y).X.hom s' y') := by
  let := auxiliaryStarRing D C
  let K := pointKernel (f ≫ (a • mu))
  let K' := pointKernel' (f' ≫ (a • mu'))
  have : Finite K := hf.finite_ker_pointsHom s
  have : Finite K' := hf'.finite_ker_pointsHom s'
  let m : Index PAll :=
    ⟨Nat.card K * Nat.card K', Nat.mul_pos Nat.card_pos Nat.card_pos, trivial⟩
  have hx (x : K) : x.val ^ m.val = 1 := by
    have hx' := congrArg Subtype.val (pow_card_eq_one' (G := K) (x := x))
    change x.val ^ Nat.card K = 1 at hx'
    change x.val ^ (Nat.card K * Nat.card K') = 1
    rw [pow_mul, hx', one_pow]
  have hx' (x : K') : x.val ^ m.val = 1 := by
    have hk := congrArg Subtype.val (pow_card_eq_one' (G := K') (x := x))
    change x.val ^ Nat.card K' = 1 at hk
    change x.val ^ (Nat.card K * Nat.card K') = 1
    rw [mul_comm, pow_mul, hk, one_pow]
  exact (primitivePolarization_nativeRank_eq_card_sourceKernel D C P compatibility h s
    htor hu X eta hn mu hmu f u hmap a hf m hx y).trans
    (primitivePolarization_nativeRank_eq_card_sourceKernel D C P compatibility h s'
      htor hu' Y eta' hn' mu' hmu' f' u hmap' a hf' m hx' y').symm

include htor hu hu' in
/-- The same multiple of the primitive polarization has the same native
rank at geometric fibres of any two normalized Harris objects. -/
theorem primitivePolarization_nativeRank_eq
    (X : PObj) (eta : Frame X) (hn : Normalized X eta)
    (Y : PObj') (eta' : Frame' Y) (hn' : Normalized' Y eta')
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : primitive Y mu') (a : ℕ)
    (hf : AbelianScheme.IsIsogeny (a • mu)) (hf' : AbelianScheme.IsIsogeny (a • mu'))
    (y : ((AbelianScheme.baseChange s).obj (DOf X)).X.left)
    (y' : ((AbelianScheme.baseChange s').obj (DOf Y)).X.left) :
    (hom (a • mu)).finrank (pullback.fst (DOf X).X.hom s y) =
      (hom (a • mu')).finrank (pullback.fst (DOf Y).X.hom s' y') := by
  let := auxiliaryStarRing D C
  have hx : Intertwines X eta hn (𝟙 (BOf X)) id := by
    intro v
    change GroupScheme.Tate.map T PAll (𝟙 (BOf X).toGrp) (fullEquiv X eta hn v) = _
    rw [GroupScheme.Tate.map_id]
    rfl
  have hy : Intertwines' Y eta' hn' (𝟙 (BOf Y)) id := by
    intro v
    change GroupScheme.Tate.map (Over.mk s') PAll (𝟙 (BOf Y).toGrp)
      (harrisIntegralFrameFull D C P compatibility h s' Y eta' hn' v) = _
    rw [GroupScheme.Tate.map_id]
    rfl
  simpa only [Category.id_comp] using
    primitivePolarizationComp_nativeRank_eq D C P compatibility h s htor hu s' hu'
      X eta hn Y eta' hn' mu hmu mu' hmu' (𝟙 _) (𝟙 _) id hx hy a
      (by simpa only [Category.id_comp] using hf) (by simpa only [Category.id_comp] using hf') y y'

end Comparison

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
