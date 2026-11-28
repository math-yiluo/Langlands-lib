import Langlands.Shimura.PEL.HarrisIntegralLatticeBounds
import Langlands.Shimura.PEL.HarrisIntegralLatticeIsogeny

/-! # Integral Tate lattices for arbitrary compact Harris levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry
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
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "G" => ScalarExtensionSimilitudes A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "HP" => ScalarExtensionSimilitudePoints A A
  (Global.FiniteAdeles ℚ) (D.harrisHodgePELForm C)
local notation "Level" => FiniteAdelicScalarExtensionLevel A A (D.harrisHodgePELForm C)

variable (P : Prerequisites.{0})
  {S : Scheme.{0}} [QuasiSeparatedSpace S]
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ S)

local notation "PObj" => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S)
local notation "Frame" X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability (X).hasDual
  (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization h
  (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "rightAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameRightAction P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  (X).hasDual (X).geometry (X).inversePoincare (X).evaluation compatibility (X).polarization
  h (X).actionObj.action A (D.harrisHodgePELForm C) s

local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Rat" X:max =>
  letI := auxiliaryStarRing D C
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "integralModule" X:max =>
  letI := auxiliaryStarRing D C
  letI := Tate.finiteAdeleModule (X).actionObj.abelianScheme (Over.mk s) (fun _ => True) h
  Module.compHom (Rat X) (Rf).subtype
local notation "lattice" => harrisIntegralFrameLattice D C P compatibility h s

/-- Intersect the integral source spans carried by all level translates of a frame. -/
def harrisCompactFrameLattice (X : PObj) (K : Subgroup G) (eta : Frame X) :
    letI := integralModule X
    Submodule Rf (Rat X) := by
  let := integralModule X
  let := rightAction X
  exact ⨅ g : K, lattice X (right eta g.val)

local notation "frameLattice" => harrisCompactFrameLattice D C P compatibility h s

omit [IsScalarTower ℚ F A] in
@[simp] theorem mem_harrisCompactFrameLattice (X : PObj) (K : Subgroup G)
    (eta : Frame X) (w : Rat X) :
    letI := rightAction X
    w ∈ frameLattice X K eta ↔ ∀ g : K, w ∈ lattice X (right eta g.val) := by
  let := integralModule X
  let := rightAction X
  exact Submodule.mem_iInf (fun g : K => lattice X (right eta g.val))

omit [IsScalarTower ℚ F A] in
theorem harrisCompactFrameLattice_right (X : PObj) (K : Subgroup G) (eta : Frame X)
    (g : G) (hg : g ∈ K) :
    letI := rightAction X
    frameLattice X K (right eta g) = frameLattice X K eta := by
  let := integralModule X
  let := rightAction X
  ext w
  simp only [mem_harrisCompactFrameLattice]
  constructor
  · intro hw u
    simpa only [right_mul, mul_inv_cancel_left] using
      hw ⟨g⁻¹ * u.val, K.mul_mem (K.inv_mem hg) u.property⟩
  · intro hw u
    simpa only [right_mul] using hw ⟨g * u.val, K.mul_mem hg u.property⟩

omit [IsScalarTower ℚ F A] in
/-- At a level preserving the fixed source span, the intersection is the
original lattice carried by the frame. -/
theorem harrisCompactFrameLattice_eq_of_le_stabilizer (X : PObj) (K : Subgroup G)
    (hK : K ≤ harrisIntegralAdeleStabilizer D C) (eta : Frame X) :
    frameLattice X K eta = lattice X eta := by
  let := integralModule X
  let := rightAction X
  ext w
  rw [mem_harrisCompactFrameLattice]
  constructor
  · intro hw
    simpa only [Subgroup.coe_one, right_one] using hw 1
  · intro hw g
    rwa [harrisIntegralFrameLattice_right D C P compatibility h s X eta g.val (hK g.property)]

/-- The intersection of the spans is determined by the right orbit. -/
def harrisCompactOrbitLattice (X : PObj) (K : Subgroup G) :
    letI := rightAction X
    letI := integralModule X
    RightOrbit (Frame X) K → Submodule Rf (Rat X) := by
  let := integralModule X
  let := rightAction X
  refine Quotient.lift (frameLattice X K) ?_
  rintro eta _ ⟨g, hg, rfl⟩
  exact (harrisCompactFrameLattice_right D C P compatibility h s X K eta g hg).symm

local notation "orbitLattice" => harrisCompactOrbitLattice D C P compatibility h s

omit [IsScalarTower ℚ F A] in
@[simp] theorem harrisCompactOrbitLattice_mk (X : PObj) (K : Subgroup G) (eta : Frame X) :
    letI := rightAction X
    orbitLattice X K (RightOrbit.mk K eta) = frameLattice X K eta := rfl

variable
  (hs : ∀ Y : Cover S, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})
  (hu : ∀ k : Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))

omit [IsScalarTower ℚ F A] in
include hs htor hu in
/-- Compactness reduces the intersection to finitely many translates and
therefore gives a single integer for both full-Tate-image bounds. -/
theorem harrisCompactFrameLattice_integerBounds (X : PObj) (K : Level) (eta : Frame X) :
    letI := auxiliaryStarRing D C
    ∃ m : ℕ, 0 < m ∧
      (∀ x : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
        m • GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) x ∈ frameLattice X K.toSubgroup eta) ∧
      (∀ w : Rat X, w ∈ frameLattice X K.toSubgroup eta →
        ∃ x : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
          GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
            (fun _ => True) x = m • w) := by
  classical
  let := auxiliaryStarRing D C
  let := integralModule X
  let := rightAction X
  let : Module.Finite ℚ A := Module.Finite.of_basis
    ((Module.finBasis ℤ (D.harrisHodgePELIntegralLattice C)).extendOfIsLattice ℚ)
  let U : Subgroup HP := K.subgroup
  let H : Subgroup U := (show Subgroup HP from harrisIntegralAdeleStabilizer D C).subgroupOf U
  let Q := U ⧸ H
  let : CompactSpace U := isCompact_iff_compactSpace.mp K.isCompact
  have hOpen : IsOpen (↑H : Set U) := (harrisIntegralAdeleStabilizer_isOpen D C).preimage
    (show Continuous (fun g : U => (g.val : HP)) from continuous_subtype_val)
  let : Finite Q := Subgroup.quotient_finite_of_isOpen H hOpen
  let : Fintype Q := Fintype.ofFinite Q
  let rep (c : Q) : U := Quotient.out c
  let lat (g : U) := lattice X (right eta (show G from g.val))
  have sameLattice (g : U) : lat (rep (QuotientGroup.mk g : Q)) = lat g := by
    let r := rep (QuotientGroup.mk g : Q)
    have hr : (QuotientGroup.mk r : Q) = QuotientGroup.mk g := Quotient.out_eq' _
    have hrg := QuotientGroup.eq.mp hr
    have hstab : (show G from r.val)⁻¹ * (show G from g.val) ∈
        harrisIntegralAdeleStabilizer D C := hrg
    have hsame := harrisIntegralFrameLattice_right D C P compatibility h s X
      (right eta (show G from r.val)) _ hstab
    simpa only [right_mul, mul_inv_cancel_left] using
      (show _ = lat (rep (QuotientGroup.mk g : Q)) from hsame).symm
  choose m hm hlower hupper using
    (fun c : Q => harrisIntegralFrameLattice_integerBounds D C P compatibility h s hs htor hu X
      (right eta (show G from (rep c).val)))
  let N := ∏ c : Q, m c
  have dvdN (c : Q) : m c ∣ N := Finset.dvd_prod_of_mem m (Finset.mem_univ c)
  refine ⟨N, Finset.prod_pos (fun c _ => hm c), ?_, ?_⟩
  · intro x
    apply (mem_harrisCompactFrameLattice D C P compatibility h s X U eta _).mpr
    intro g
    change N • _ ∈ lat g
    rw [← sameLattice g]
    let c : Q := QuotientGroup.mk g
    obtain ⟨k, hk⟩ := dvdN c
    rw [hk, Nat.mul_comm, ← smul_smul]
    exact (lat (rep c)).nsmul_mem (hlower c x) k
  · intro w hw
    let c : Q := QuotientGroup.mk (1 : U)
    have hw' := (mem_harrisCompactFrameLattice D C P compatibility h s X U eta _).mp hw (rep c)
    obtain ⟨x, hx⟩ := hupper c w hw'
    obtain ⟨k, hk⟩ := dvdN c
    refine ⟨k • x, ?_⟩
    rw [map_nsmul, hx, smul_smul, Nat.mul_comm k, ← hk]

variable
  [hμfin : ∀ k : Index (fun _ => True), IsFinite (mu S k.val).X.hom]
  [hμet : ∀ k : Index (fun _ => True), Etale (mu S k.val).X.hom]

local notation "tower" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelTower P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu X
local notation "leftAction" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameMonodromyAction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation (X).polarization h (X).actionObj.action A
    (D.harrisHodgePELForm C) s hs htor hu
local notation "actionsComm" X:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameActionsComm P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability compatibility
    rationalWeilGeometricTransport (X).hasDual (X).geometry (X).inversePoincare
    (X).evaluation (X).polarization h (X).actionObj.action A
    (D.harrisHodgePELForm C) s hs htor hu
local notation "monodromy" X:max =>
  Tate.rationalMonodromy s hs htor (X).actionObj.abelianScheme (fun _ => True) hu

omit [IsScalarTower ℚ F A] in
/-- The intersection lattice of a monodromy-fixed orbit is monodromy invariant. -/
theorem harrisCompactOrbitLattice_monodromy (X : PObj) (K : Level) :
    letI := auxiliaryStarRing D C
    ∀ (x : (tower X).obj K) (gamma : FundamentalGroup s hs) (w : Rat X),
      (monodromy X) gamma w ∈ orbitLattice X K.toSubgroup x.1 ↔
        w ∈ orbitLattice X K.toSubgroup x.1 := by
  let := auxiliaryStarRing D C
  let := integralModule X
  let := rightAction X
  let := leftAction X
  let := actionsComm X
  intro x gamma w
  let U := K.toSubgroup
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  have hfix : RightOrbit.mk U eta ∈
      MulAction.fixedPoints (FundamentalGroup s hs) (RightOrbit (Frame X) U) := by
    change (⟦eta⟧ : RightOrbit (Frame X) U) ∈ _
    rw [heta]
    exact x.2
  obtain ⟨g, hg, hγ⟩ := (RightOrbit.mk_mem_fixedPoints U eta).mp hfix gamma
  have hlat : orbitLattice X U x.1 = frameLattice X U eta :=
    congrArg (orbitLattice X U) heta.symm
  have hlat' : orbitLattice X U x.1 = frameLattice X U (gamma • eta) := by
    rw [hlat, hγ, harrisCompactFrameLattice_right D C P compatibility h s X U eta g hg]
  change (monodromy X) gamma w ∈ orbitLattice X U x.1 ↔ w ∈ orbitLattice X U x.1
  calc
    _ ↔ (monodromy X) gamma w ∈ frameLattice X U (gamma • eta) := by rw [hlat']
    _ ↔ w ∈ frameLattice X U eta := by
      simp only [mem_harrisCompactFrameLattice]
      apply forall_congr'
      intro u
      rw [← right_comm, mem_harrisIntegralFrameLattice, mem_harrisIntegralFrameLattice]
      constructor
      · rintro ⟨v, hv, hEq⟩
        exact ⟨v, hv, ((monodromy X) gamma).injective hEq⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v, hv, rfl⟩
    _ ↔ _ := by rw [hlat]

omit [IsScalarTower ℚ F A] in
/-- A fixed level orbit's intersection lattice satisfies the integer bounds. -/
theorem harrisCompactOrbitLattice_integerBounds (X : PObj) (K : Level) :
    letI := auxiliaryStarRing D C
    ∀ x : (tower X).obj K, ∃ m : ℕ, 0 < m ∧
      (∀ t : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
        m • GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
          (fun _ => True) t ∈ orbitLattice X K.toSubgroup x.1) ∧
      (∀ w : Rat X, w ∈ orbitLattice X K.toSubgroup x.1 →
        ∃ t : GroupScheme.Tate.Full X.actionObj.abelianScheme.toGrp (Over.mk s),
          GroupScheme.Tate.toRational X.actionObj.abelianScheme.toGrp (Over.mk s)
            (fun _ => True) t = m • w) := by
  let := auxiliaryStarRing D C
  let := rightAction X
  intro x
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  have hlat : orbitLattice X K.toSubgroup x.1 = frameLattice X K.toSubgroup eta :=
    congrArg (orbitLattice X K.toSubgroup) heta.symm
  rw [hlat]
  exact harrisCompactFrameLattice_integerBounds D C P compatibility h s hs htor hu X K eta

variable (additivity : PositivePairAdditivity D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
  P.universality (S := S))

local notation "Mult" =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.Multiple P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality additivity
local notation "transport" =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.levelIso P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality
    compatibility h A (D.harrisHodgePELForm C) s hs htor hu additivity
local notation "frameIso" X:max Y:max q:max e:max he:max =>
  letI := auxiliaryStarRing D C
  Tate.weilAdelicFrameIsogeny P.preservation P.composition
    P.unitCoherence P.associativity P.comparison P.symmetry P.stability
    (X).hasDual (Y).hasDual (X).geometry (Y).geometry (X).inversePoincare (X).evaluation
    (Y).inversePoincare (Y).evaluation (additivity X Y) (X).polarization (Y).polarization
    compatibility rationalWeilFunctoriality h (X).actionObj.action (Y).actionObj.action
    A (D.harrisHodgePELForm C) s q (RationalAlgebraAction.underlyingIso e)
    (RationalAlgebraAction.intertwines (e).hom) he

omit [IsScalarTower ℚ F A] in
/-- Exact rational-isogeny transport of a level orbit carries its intersection
lattice by the same rational Tate map. -/
theorem harrisCompactOrbitLattice_isogeny (X Y : PObj) (K : Level) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : X.actionObj ≅ Y.actionObj) (he : Mult X Y q e)
      (x : (tower X).obj K) (w : Rat X),
      Tate.rationalHomMap (Over.mk s) (fun _ => True)
        (RationalAlgebraAction.underlyingIso e).hom w ∈
          orbitLattice Y K.toSubgroup (transport X Y K q e he x).1 ↔
        w ∈ orbitLattice X K.toSubgroup x.1 := by
  let := auxiliaryStarRing D C
  intro e he x w
  let := rightAction X
  let := rightAction Y
  let f := frameIso X Y q e he
  let U := K.toSubgroup
  obtain ⟨eta, heta⟩ := Quotient.exists_rep x.1
  have hf : ∀ xi (g : G), f (right xi g) = right (f xi) g :=
    Tate.weilAdelicFrameIsogeny_right P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability
      X.hasDual Y.hasDual X.geometry Y.geometry X.inversePoincare X.evaluation
      Y.inversePoincare Y.evaluation (additivity X Y) X.polarization Y.polarization
      compatibility rationalWeilFunctoriality h X.actionObj.action Y.actionObj.action
      A (D.harrisHodgePELForm C) s q (RationalAlgebraAction.underlyingIso e)
      (RationalAlgebraAction.intertwines e.hom) he
  have targetOrbit : RightOrbit.mk U (f eta) = (transport X Y K q e he x).1 :=
    congrArg (RightOrbit.map U f hf) heta
  change _ ∈ orbitLattice Y U (transport X Y K q e he x).1 ↔
    w ∈ orbitLattice X U x.1
  rw [← targetOrbit, ← heta]
  change _ ∈ frameLattice Y U (f eta) ↔ w ∈ frameLattice X U eta
  simp only [mem_harrisCompactFrameLattice]
  apply forall_congr'
  intro g
  rw [← hf eta g.val]
  exact harrisIntegralFrameLattice_isogeny D C P compatibility h s additivity
    X Y q e he (right eta g.val) w

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
