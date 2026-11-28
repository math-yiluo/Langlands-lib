import Langlands.Shimura.PEL.HarrisPrimitiveTorsionKernel
import Langlands.Shimura.PEL.HarrisPrimitiveOrdinaryDegree
import Langlands.Shimura.PEL.HarrisIntegralOrderTate
import Langlands.Shimura.PEL.HarrisIntegralRosatiMumford
import Langlands.Shimura.PEL.PolarizedWeilOrderModel
import Langlands.Shimura.PEL.HarrisTaylorCMBaseAdmissibility
import Langlands.AlgebraicGeometry.Picard.LineBundleEulerPolynomialComparisonProof
import Langlands.AlgebraicGeometry.Picard.MumfordRosatiEulerDegreeProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPow
import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPowerFibreCohomology
import Langlands.AbelianScheme.AmpleSectionIsogenyDegree
import Langlands.AlgebraicGeometry.Picard.AffineMumfordTransport
import Langlands.Shimura.Unitary.DivisionCondition

/-! # Ranks of the twisted Mumford maps for the fixed Harris order -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0}) (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "PAll" => (fun _ : ℕ => True)
local notation "O" => D.harrisHodgePELIntegralOrder C
local notation "PObj" Tgt:max =>
  PositivePolarizedAction D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality (S := Tgt)
local notation "Frame" X:max s:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation:max "Normalized" s:max => HarrisIntegralFrameCondition D C P compatibility h s
local notation "Restriction" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.IntegralActionRestriction P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality O X
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "WOf" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction.dualWitness P X
local notation:max "DOf" X:max => (WOf X).dual P
local notation "RosatiEq" X:max i:max lam:max =>
  letI := auxiliaryStarRing D C
  IntegralRosatiEquations D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (BOf X) (X).hasDual
    (X).inversePoincare (X).evaluation (X).geometry (i).action lam
local notation "act" i:max a:max =>
  letI := auxiliaryStarRing D C
  ((i).action a).asHom
local notation "twistMap" X:max i:max a:max lam:max j:max =>
  j • lam + (act i a) ≫ lam ≫ (WOf X).map P (WOf X) (act i a)
local notation "primitive" => HarrisPrimitivePolarization D C P

variable {S S' : Scheme.{0}} [QuasiSeparatedSpace S] [IsLocallyNoetherian S]
  [ConnectedSpace S] [QuasiSeparatedSpace S'] [IsLocallyNoetherian S'] [ConnectedSpace S']
  {Ω Ω' : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
  [Field Ω'] [IsAlgClosed Ω'] [CharZero Ω']
  (s : Spec (.of Ω) ⟶ S) (s' : Spec (.of Ω') ⟶ S')
  (hu : ∀ k : Index PAll, IsUnit (k.val : Γ(S, ⊤)))
  (hu' : ∀ k : Index PAll, IsUnit (k.val : Γ(S', ⊤)))

include htor hu hu' in
/-- For the same order element and multiple of the primitive polarization,
the twisted Mumford expressions have equal native ranks at the geometric
fibres of any two normalized objects on which the expressions are isogenies. -/
theorem harrisPrimitiveMumfordTwist_nativeRank_eq
    (X : PObj S) (eta : Frame X s) (hn : Normalized s X eta) (i : Restriction X)
    (Y : PObj S') (eta' : Frame Y s') (hn' : Normalized s' Y eta') (i' : Restriction Y)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : primitive Y mu') (k : ℕ)
    (hr : RosatiEq X i (k • mu)) (hr' : RosatiEq Y i' (k • mu'))
    (a : O) (j : ℕ)
    (hf : AbelianScheme.IsIsogeny (twistMap X i a (k • mu) j))
    (hf' : AbelianScheme.IsIsogeny (twistMap Y i' a (k • mu') j))
    (y : ((AbelianScheme.baseChange s).obj (DOf X)).X.left)
    (y' : ((AbelianScheme.baseChange s').obj (DOf Y)).X.left) :
    (hom (twistMap X i a (k • mu) j)).finrank (pullback.fst (DOf X).X.hom s y) =
      (hom (twistMap Y i' a (k • mu') j)).finrank (pullback.fst (DOf Y).X.hom s' y') := by
  let := auxiliaryStarRing D C
  let u := harrisMumfordTwistOrderElement D C a j
  have hx : twistMap X i a (k • mu) j = (act i u) ≫ (k • mu) :=
    IntegralRosatiEquations.mumfordTwist_eq D C P (WOf X) i.action (k • mu) hr a j
  have hy : twistMap Y i' a (k • mu') j = (act i' u) ≫ (k • mu') :=
    IntegralRosatiEquations.mumfordTwist_eq D C P (WOf Y) i'.action (k • mu') hr' a j
  rw [hx] at hf
  rw [hy] at hf'
  rw [hx, hy]
  exact primitivePolarizationComp_nativeRank_eq D C P compatibility h s htor hu s' hu'
    X eta hn Y eta' hn' mu hmu mu' hmu' (act i u) (act i' u)
    (harrisIntegralSourceOrderOperator D C u)
    (harrisIntegralFrameFull_order D C P compatibility h s X eta hn i u)
    (harrisIntegralFrameFull_order D C P compatibility h s' Y eta' hn' i' u) k hf hf' y y'

section Field

open Filter

variable {K K' : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [Field K'] [IsAlgClosed K'] [CharZero K']

local notation "SOf" k:max => Spec (.of k)
local notation "point" k:max => (𝟙 (SOf k))
local notation "RP" =>
  (⟨P.preservation, P.composition, P.unitCoherence, P.associativity, P.comparison,
    P.symmetry, P.stability, P.square, P.universality⟩ : Rosati.Prerequisites.{0})
local notation "RW" X:max =>
  letI := auxiliaryStarRing D C
  (⟨(X).hasDual, (X).geometry, (X).inversePoincare, (X).evaluation⟩ : Rosati.DualData (BOf X))
local notation "Presentation" Tgt:max X:max lam:max =>
  AmpleMumfordIsogeny.AmpleMumfordPresentation RP Tgt (BOf X) (RW X) lam
local notation "pb" i:max a:max L:max =>
  (LineBundle.pullback (hom (act i a))).obj L
local notation "eulerSequence" X:max i:max a:max L:max =>
  coherentEulerSequence (BOf X).X.hom (pb i a L).obj
    (hasFiniteAffineSections_lineBundle _) L
local notation "eulerPolynomial" X:max i:max a:max L:max g:max =>
  coherentEulerPolynomial (BOf X).X.hom (pb i a L).obj
    (hasFiniteAffineSections_lineBundle _) L g

set_option maxHeartbeats 2000000 in
include htor in
/-- For two normalized objects over algebraically closed fields of characteristic zero,
the twisted Euler polynomials of the same order endomorphism agree when the two ample
bundles have Mumford maps equal to the same multiple of the primitive polarization. -/
theorem harrisPrimitiveOrderEulerPolynomial_eq
    (X : PObj (SOf K)) (eta : Frame X (point K)) (hn : Normalized (point K) X eta)
    (i : Restriction X)
    (Y : PObj (SOf K')) (eta' : Frame Y (point K')) (hn' : Normalized (point K') Y eta')
    (i' : Restriction Y) (g : ℕ) (hg : (BOf X).HasRelativeDimension g)
    (hg' : (BOf Y).HasRelativeDimension g)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : primitive Y mu') (k : ℕ)
    (hr : RosatiEq X i (k • mu)) (hr' : RosatiEq Y i' (k • mu'))
    (L : Presentation K X (k • mu)) (L' : Presentation K' Y (k • mu')) (a : O) :
    eulerPolynomial X i a L.L g = eulerPolynomial Y i' a L'.L g := by
  let := auxiliaryStarRing D C
  obtain ⟨j₀, hj₀⟩ := Rosati.mumfordEulerDegree RP K (BOf X) (RW X) (k • mu)
    L.L L.B L.evaluationB L.M L.evaluation L.isAmple L.hom_eq (act i a)
  obtain ⟨j₀', hj₀'⟩ := Rosati.mumfordEulerDegree RP K' (BOf Y) (RW Y) (k • mu')
    L'.L L'.B L'.evaluationB L'.M L'.evaluation L'.isAmple L'.hom_eq (act i' a)
  have hsquare : ∀ᶠ j : ℕ in atTop,
      (eulerSequence X i a L.L) j ^ 2 = (eulerSequence Y i' a L'.L) j ^ 2 := by
    filter_upwards [eventually_ge_atTop j₀, eventually_ge_atTop j₀'] with j hj hj'
    obtain ⟨hf, hrank⟩ := hj₀ j hj
    obtain ⟨hf', hrank'⟩ := hj₀' j hj'
    let y := unitSection ((AbelianScheme.baseChange (point K)).obj (DOf X))
      (IsLocalRing.closedPoint K)
    let y' := unitSection ((AbelianScheme.baseChange (point K')).obj (DOf Y))
      (IsLocalRing.closedPoint K')
    have hdeg := harrisPrimitiveMumfordTwist_nativeRank_eq D C P compatibility h htor
      (point K) (point K') (HarrisTaylorCMWeilLevel.cmBaseTorsionUnit (point K))
      (HarrisTaylorCMWeilLevel.cmBaseTorsionUnit (point K')) X eta hn i Y eta' hn' i'
      mu hmu mu' hmu' k hr hr' a j hf hf' y y'
    exact (hrank (pullback.fst (DOf X).X.hom (point K) y)).symm.trans
      ((congrArg (Nat.cast : ℕ → ℚ) hdeg).trans
        (hrank' (pullback.fst (DOf Y).X.hom (point K') y')))
  exact coherentEulerPolynomial_eq_of_eventually_sq_eq (BOf X).X.hom (BOf Y).X.hom
    g hg hg' inferInstance inferInstance L.L (pb i a L.L) L'.L (pb i' a L'.L)
    L.isAmple L'.isAmple hsquare

/-- The actual line bundle `f^*L ⊗ L` on the graph of the order endomorphism
`f`, identified with the abelian variety by its first projection. -/
def harrisOrderGraphBundle (X : PObj (SOf K)) (i : Restriction X)
    (a : O) (L : LineBundle (BOf X).X.left) : LineBundle (BOf X).X.left :=
  LineBundle.tensor P.preservation (pb i a L) L

/-- The Euler polynomial of the actual graph bundle for the specified
relative dimension. -/
def harrisOrderGraphEulerPolynomial (X : PObj (SOf K)) (i : Restriction X)
    (a : O) (L : LineBundle (BOf X).X.left) (g : ℕ) : Polynomial ℚ :=
  lineBundleEulerPolynomial (BOf X).X.hom (harrisOrderGraphBundle D C P X i a L) g

local notation "graphPolynomial" => harrisOrderGraphEulerPolynomial D C P

omit [IsAlgClosed K] in
private theorem harrisOrderEndomorphism_isFinite
    (hD : D.IsDivision) (X : PObj (SOf K)) (i : Restriction X)
    (a : O) (ha : (a : A) ≠ 0) : IsFinite (hom (act i a)) := by
  let := auxiliaryStarRing D C
  let B := BOf X
  let f := act i a
  obtain ⟨u, hu⟩ := hD (a : A) ha
  let u' := Units.map (X.actionObj.action).toMonoidHom u
  let w := (↑(u'⁻¹) : Rationalization.End B).asHom
  have hfw : Rationalization.comp B B B (Rationalization.ofHom f) w =
      Rationalization.identity B := by
    have h := congrArg CategoryTheory.End.asHom u'.inv_val
    change Rationalization.comp B B B (X.actionObj.action (u : A)).asHom w =
      Rationalization.identity B at h
    rw [hu, ← i.agrees a] at h
    exact h
  obtain ⟨m, hm, z, hz⟩ := Rationalization.exists_integral_multiple w
  let N := m.natAbs
  have hN : 0 < N := Int.natAbs_pos.mpr hm
  let q := m.sign • z
  have hq : Rationalization.ofHom q = N • w := by
    dsimp only [q, N]
    rw [map_zsmul, hz, smul_smul, Int.sign_mul_self_eq_natAbs, natCast_zsmul]
  let units := HarrisTaylorCMWeilLevel.cmBaseTorsionUnit (point K)
  have hcomp : f ≫ q = N • 𝟙 B := by
    apply Tate.ofHom_injective units B B
    rw [Rationalization.ofHom_comp, hq, map_nsmul, hfw]
    exact (map_nsmul (Rationalization.ofHom (X := B) (Y := B)) N (𝟙 B)).symm
  let : IsFinite (hom f ≫ hom q) := by
    rw [← AbelianScheme.hom_comp, hcomp]
    exact (multiplication_isIsogeny_of_isUnit B N (units ⟨N, hN, trivial⟩)).1
  have : IsSeparated (hom q ≫ B.X.hom) := by
    rw [Over.w]
    infer_instance
  let : IsSeparated (hom q) := IsSeparated.of_comp _ B.X.hom
  exact IsFinite.of_comp (hom f) (hom q)

omit [IsAlgClosed K] in
/-- In the division case a nonzero order endomorphism is finite, so both
factors of its graph bundle are ample when the original bundle is ample. -/
theorem harrisOrderGraphBundle_isAmple_of_division
    (hD : D.IsDivision) (X : PObj (SOf K)) (i : Restriction X)
    (a : O) (ha : (a : A) ≠ 0) (L : LineBundle (BOf X).X.left) (hL : L.IsAmple) :
    (harrisOrderGraphBundle D C P X i a L).IsAmple := by
  let : IsFinite (hom (act i a)) := harrisOrderEndomorphism_isFinite D C P hD X i a ha
  exact ampleTensor _ (pb i a L) L _ ⟨Iso.refl _⟩
    (affinePullbackAmple (hom (act i a)) L hL) hL

omit [CharZero K] in
/-- The positive powers of an ample graph bundle have the section dimensions
specified by its graph Euler polynomial. -/
theorem harrisOrderGraphEulerPolynomial_eval_finrank
    (X : PObj (SOf K)) (i : Restriction X) (a : O) (g : ℕ)
    (hg : (BOf X).HasRelativeDimension g) (L : LineBundle (BOf X).X.left)
    (hL : (harrisOrderGraphBundle D C P X i a L).IsAmple) (k : ℕ) (hk : 0 < k) :
    (graphPolynomial X i a L g).eval (k : ℚ) =
      (Module.finrank K ((relativeGlobalSections (BOf X).X.hom).obj
        (tensorPow (harrisOrderGraphBundle D C P X i a L).obj k)) : ℚ) := by
  let B := BOf X
  let : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  let : CompactSpace B.X.left := (quasiCompact_iff_compactSpace B.X.hom).mp inferInstance
  let : IsNoetherian B.X.left := ⟨⟩
  let : B.X.left.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := B.X.hom)).mp inferInstance
  have hdim := Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim K B.X.left
    B.X.hom g hg inferInstance
  let N := harrisOrderGraphBundle D C P X i a L
  let Nk : LineBundle B.X.left := ⟨tensorPow N.obj k, tensorPow_isLocallyFreeRankOne _ N k⟩
  let hf := lineBundleTensorPow_hasFiniteCohomology B.X.hom N k
  have hEuler := lineBundleEulerPolynomial_eval B.X.hom N g hdim k hf
  have hAmple : Nk.IsAmple := positiveTensorPowerAmple _ N Nk k hk hL ⟨Iso.refl _⟩
  have hFinrank := eulerCharacteristic_eq_finrank_ample B Nk hAmple hf
  have h := congrArg (Int.cast : ℤ → ℚ) hFinrank
  exact hEuler.trans (by simpa only [Int.cast_natCast] using h)

omit [IsAlgClosed K] [CharZero K] in
private theorem harrisOrderGraphEulerPolynomial_eval_power
    (X : PObj (SOf K)) (i : Restriction X) (a : O) (g : ℕ)
    (hg : (BOf X).HasRelativeDimension g)
    (L Lk : LineBundle (BOf X).X.left) (k : ℕ)
    (ek : Lk.obj ≅ tensorPow L.obj k) :
    (graphPolynomial X i a L g).eval (k : ℚ) = (eulerPolynomial X i a Lk g).eval 1 := by
  let B := BOf X
  let : IsLocallyNoetherian B.X.left := LocallyOfFiniteType.isLocallyNoetherian B.X.hom
  let : CompactSpace B.X.left := (quasiCompact_iff_compactSpace B.X.hom).mp inferInstance
  let : IsNoetherian B.X.left := ⟨⟩
  let : B.X.left.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := B.X.hom)).mp inferInstance
  have hdim := Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim K B.X.left
    B.X.hom g hg inferInstance
  let N := harrisOrderGraphBundle D C P X i a L
  have h := lineBundleEulerPolynomial_eval B.X.hom N g hdim k
    (lineBundleTensorPow_hasFiniteCohomology B.X.hom N k)
  change (graphPolynomial X i a L g).eval (k : ℚ) = _ at h
  rw [h]
  have hj := coherentEulerPolynomial_eval B.X.hom (pb i a Lk).obj
    (hasFiniteAffineSections_lineBundle (pb i a Lk)) Lk g
    (HasSupportDimensionLT.of_topologicalKrullDim_le hdim _) 1
  change (eulerPolynomial X i a Lk g).eval 1 = (eulerSequence X i a Lk) 1 at hj
  rw [hj]
  apply congrArg (Int.cast : ℤ → ℚ)
  apply eulerCharacteristic_eq_of_iso
  let f := hom (act i a)
  let q : (pb i a Lk).obj ≅ tensorPow (pb i a L).obj k :=
    (Scheme.Modules.pullback f).mapIso ek ≪≫ pullbackTensorPowIso f L.obj k
  let r := tensorPowOneIso Lk.obj ≪≫ ek
  exact tensorPowTensorIso (pb i a L).obj L.obj k ≪≫ tensorMapIso q.symm r.symm

set_option maxHeartbeats 2000000 in
include htor in
/-- A pair of normalized families has the same graph Euler polynomial for a
fixed order element when every positive power of the two chosen ample bundles
is presented by the corresponding multiple of the primitive polarizations. -/
theorem harrisPrimitiveOrderGraphEulerPolynomial_eq
    (X : PObj (SOf K)) (eta : Frame X (point K)) (hn : Normalized (point K) X eta)
    (i : Restriction X)
    (Y : PObj (SOf K')) (eta' : Frame Y (point K')) (hn' : Normalized (point K') Y eta')
    (i' : Restriction Y) (g : ℕ) (hg : (BOf X).HasRelativeDimension g)
    (hg' : (BOf Y).HasRelativeDimension g)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : primitive Y mu') (j : ℕ)
    (hr : RosatiEq X i (j • mu)) (hr' : RosatiEq Y i' (j • mu'))
    (L : LineBundle (BOf X).X.left) (L' : LineBundle (BOf Y).X.left)
    (hL : ∀ k : ℕ, 0 < k → ∃ b : Presentation K X ((k * j) • mu),
      Nonempty (b.L.obj ≅ tensorPow L.obj k))
    (hL' : ∀ k : ℕ, 0 < k → ∃ b : Presentation K' Y ((k * j) • mu'),
      Nonempty (b.L.obj ≅ tensorPow L'.obj k)) (a : O) :
    graphPolynomial X i a L g = graphPolynomial Y i' a L' g := by
  let := auxiliaryStarRing D C
  apply Langlands.Algebra.RationalPolynomial.eq_of_eventually_nat_eval_eq
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨b, ⟨eb⟩⟩ := hL k hk
  obtain ⟨b', ⟨eb'⟩⟩ := hL' k hk
  have ep := harrisOrderGraphEulerPolynomial_eval_power D C P X i a g hg L b.L k eb
  have ep' := harrisOrderGraphEulerPolynomial_eval_power D C P Y i' a g hg' L' b'.L k eb'
  have hx : RosatiEq X i ((k * j) • mu) := by
    rw [← smul_smul]
    exact IntegralRosatiEquations.nsmul D C P (WOf X) i.action (j • mu) hr k
  have hy : RosatiEq Y i' ((k * j) • mu') := by
    rw [← smul_smul]
    exact IntegralRosatiEquations.nsmul D C P (WOf Y) i'.action (j • mu') hr' k
  rw [ep, ep', harrisPrimitiveOrderEulerPolynomial_eq D C P compatibility h htor
    X eta hn i Y eta' hn' i' g hg hg' mu hmu mu' hmu' (k * j) hx hy b b' a]

/-- The ordinary field datum on the same abelian variety, using four
times the primitive polarization and the indicated ordered marking. -/
def harrisQuadrupledFieldDatum (X : PObj (SOf K)) (mu : BOf X ⟶ DOf X)
    (hmu : primitive X mu) {g d m : ℕ} (hg : (BOf X).HasRelativeDimension g)
    (hdegree : HasDegreeSquare ((4 : ℕ) • mu) d) (v : FullLevel (BOf X) g m) :
    Datum P (SOf K) g d m where
  abelian := BOf X
  dimension := hg
  dualWitness := WOf X
  polarization := (4 : ℕ) • mu
  polarized := primitivePolarization_four_isPolarization D C P X mu hmu
  degree := hdegree
  level := v

local notation "fieldDatum" => harrisQuadrupledFieldDatum D C P

omit [IsAlgClosed K] [CharZero K] in
private theorem harrisQuadrupledFieldDatum_cubicPowerPresentation
    (X : PObj (SOf K)) (mu : BOf X ⟶ DOf X) (hmu : primitive X mu) {g d m : ℕ}
    (hg : (BOf X).HasRelativeDimension g) (hdegree : HasDegreeSquare ((4 : ℕ) • mu) d)
    (v : FullLevel (BOf X) g m) (k : ℕ) (hk : 0 < k) :
    let a := fieldDatum X mu hmu hg hdegree v
    ∃ b : Presentation K X ((k * 24) • mu),
      Nonempty (b.L.obj ≅ tensorPow a.cubicBundle.obj k) := by
  let a := fieldDatum X mu hmu hg hdegree v
  obtain ⟨B, evaluationB, M, evaluation, hmap⟩ := a.cubicPowerBundleMumford k
  refine ⟨⟨a.cubicPowerBundle k, B, evaluationB, M, evaluation,
    a.cubicPowerBundle_isAmple k hk, ?_⟩, ⟨a.cubicPowerBundleIso k⟩⟩
  have hmul : (k * 24) • mu = (6 * k) • a.polarization := by
    change (k * 24) • mu = (6 * k) • ((4 : ℕ) • mu)
    rw [smul_smul]
    congr 1
    omega
  rw [hmul]
  exact hmap.symm

/-- The graph polynomial of the canonical cubic bundle of the ordinary
quadrupled primitive polarization, with the actual order endomorphism. -/
def harrisPrimitiveCubicGraphEulerPolynomial
    (X : PObj (SOf K)) (i : Restriction X) (a : O)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu) {g d m : ℕ}
    (hg : (BOf X).HasRelativeDimension g) (hdegree : HasDegreeSquare ((4 : ℕ) • mu) d)
    (v : FullLevel (BOf X) g m) : Polynomial ℚ :=
  graphPolynomial X i a (fieldDatum X mu hmu hg hdegree v).cubicBundle g

local notation "cubicGraph" => harrisPrimitiveCubicGraphEulerPolynomial D C P

set_option maxHeartbeats 2200000 in
include htor in
/-- Each fixed order element gives the same actual cubic graph Euler
polynomial on normalized fibres with the original Lie dimension. -/
theorem harrisPrimitiveCubicGraphEulerPolynomial_eq
    (X : PObj (SOf K)) (eta : Frame X (point K)) (hn : Normalized (point K) X eta)
    (i : Restriction X)
    (Y : PObj (SOf K')) (eta' : Frame Y (point K')) (hn' : Normalized (point K') Y eta')
    (i' : Restriction Y) {g d d' m m' : ℕ} (hg : (BOf X).HasRelativeDimension g)
    (hg' : (BOf Y).HasRelativeDimension g)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : primitive Y mu')
    (hdeg : HasDegreeSquare ((4 : ℕ) • mu) d)
    (hdeg' : HasDegreeSquare ((4 : ℕ) • mu') d')
    (hr : RosatiEq X i ((4 : ℕ) • mu)) (hr' : RosatiEq Y i' ((4 : ℕ) • mu'))
    (v : FullLevel (BOf X) g m) (v' : FullLevel (BOf Y) g m') (a : O) :
    cubicGraph X i a mu hmu hg hdeg v = cubicGraph Y i' a mu' hmu' hg' hdeg' v' := by
  let := auxiliaryStarRing D C
  have hx : RosatiEq X i ((24 : ℕ) • mu) := by
    rw [show (24 : ℕ) = 6 * 4 by decide, ← smul_smul]
    exact IntegralRosatiEquations.nsmul D C P (WOf X) i.action (4 • mu) hr 6
  have hy : RosatiEq Y i' ((24 : ℕ) • mu') := by
    rw [show (24 : ℕ) = 6 * 4 by decide, ← smul_smul]
    exact IntegralRosatiEquations.nsmul D C P (WOf Y) i'.action (4 • mu') hr' 6
  exact harrisPrimitiveOrderGraphEulerPolynomial_eq D C P compatibility h htor
    X eta hn i Y eta' hn' i' g hg hg' mu hmu mu' hmu' 24 hx hy
    (fieldDatum X mu hmu hg hdeg v).cubicBundle (fieldDatum Y mu' hmu' hg' hdeg' v').cubicBundle
    (harrisQuadrupledFieldDatum_cubicPowerPresentation D C P X mu hmu hg hdeg v)
    (harrisQuadrupledFieldDatum_cubicPowerPresentation D C P Y mu' hmu' hg' hdeg' v') a

/-- In the division case the cubic graph polynomial gives the ordinary section
rank at every positive exponent for a nonzero order element. -/
theorem harrisPrimitiveCubicGraphEulerPolynomial_eval_finrank
    (hD : D.IsDivision)
    (X : PObj (SOf K)) (i : Restriction X) (a : O) (ha : (a : A) ≠ 0)
    (mu : BOf X ⟶ DOf X) (hmu : primitive X mu) {g d m : ℕ}
    (hg : (BOf X).HasRelativeDimension g) (hdegree : HasDegreeSquare ((4 : ℕ) • mu) d)
    (v : FullLevel (BOf X) g m) (k : ℕ) (hk : 0 < k) :
    let L := (fieldDatum X mu hmu hg hdegree v).cubicBundle
    (cubicGraph X i a mu hmu hg hdegree v).eval (k : ℚ) =
      (Module.finrank K ((relativeGlobalSections (BOf X).X.hom).obj
        (tensorPow (harrisOrderGraphBundle D C P X i a L).obj k)) : ℚ) := by
  let b := fieldDatum X mu hmu hg hdegree v
  have hA := harrisOrderGraphBundle_isAmple_of_division D C P hD X i a ha
    b.cubicBundle b.cubicBundle_isAmple
  exact harrisOrderGraphEulerPolynomial_eval_finrank D C P X i a g hg b.cubicBundle hA k hk

end Field

/-- A fixed polynomial for every order element on the normalized
characteristic-zero fibres of the chosen dimension. -/
def HarrisPrimitiveCubicGraphPolynomialUniform (g : ℕ) (pol : O → Polynomial ℚ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K]
    (X : PObj (Spec (.of K))) (eta : Frame X (𝟙 (Spec (.of K)))),
    Normalized (𝟙 (Spec (.of K))) X eta →
    ∀ (i : Restriction X) (a : O) (mu : BOf X ⟶ DOf X) (hmu : primitive X mu) (d m : ℕ)
      (hg : (BOf X).HasRelativeDimension g) (hdegree : HasDegreeSquare ((4 : ℕ) • mu) d)
      (_ : RosatiEq X i ((4 : ℕ) • mu)) (v : FullLevel (BOf X) g m),
      harrisPrimitiveCubicGraphEulerPolynomial D C P X i a mu hmu hg hdegree v = pol a

include htor in
/-- Choose one collection of graph polynomials for the fixed order and
dimension. The comparison across normalized fibres makes every such test
give the same labels. -/
theorem exists_harrisPrimitiveCubicGraphPolynomialUniform (g : ℕ) :
    ∃ pol : O → Polynomial ℚ, HarrisPrimitiveCubicGraphPolynomialUniform D C P compatibility h g pol := by
  classical
  by_cases hz : HarrisPrimitiveCubicGraphPolynomialUniform D C P compatibility h g 0
  · exact ⟨0, hz⟩
  · simp only [HarrisPrimitiveCubicGraphPolynomialUniform, not_forall] at hz
    obtain ⟨K, hK, hAlg, hChar, X, eta, hn, i, -, mu, hmu, d, m, hg, hdegree, hr, v, _⟩ := hz
    let := hK
    let := hAlg
    let := hChar
    refine ⟨fun a => harrisPrimitiveCubicGraphEulerPolynomial D C P X i a mu hmu hg hdegree v, ?_⟩
    intro K' _ _ _ Y eta' hn' i' a mu' hmu' d' m' hg' hdegree' hr' v'
    exact harrisPrimitiveCubicGraphEulerPolynomial_eq D C P compatibility h htor
      Y eta' hn' i' X eta hn i hg' hg mu' hmu' mu hmu hdegree' hdegree hr' hr v' v a

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
