import Langlands.Shimura.PEL.HarrisPrimitiveTorsionKernel
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationDoublingDivisionProof
import Langlands.AbelianScheme.PolarizedFiniteLevel.PolarizationDoubleDegree
import Langlands.Shimura.PEL.HarrisNormalizedPolarizationTransport
import Langlands.AbelianScheme.AlgebraicallyClosedFieldAmpleExistenceProof
import Langlands.AbelianScheme.FieldCubePullbackProof
import Langlands.AbelianScheme.MultiplicationDegree
import Langlands.AlgebraicGeometry.FiniteFlatConstantRankCompositionProof

/-! # Uniform ordinary polarization degree for normalized Harris objects -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules Langlands.SchemeModule
open Langlands.GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
  (P : Prerequisites.{0})
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)

local notation "PAll" => (fun _ : ℕ => True)
local notation "PObj" S₀:max => PositivePolarizedAction D C P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  (S := S₀)
local notation:max "BOf" X:max =>
  letI := auxiliaryStarRing D C
  (X).actionObj.abelianScheme
local notation:max "WOf" X:max =>
  letI := auxiliaryStarRing D C
  PolarizedWeilLevel.PolarizedAction.dualWitness P X
local notation:max "DOf" X:max =>
  letI := auxiliaryStarRing D C
  (WOf X).dual P
local notation "FrameAt" s:max X:max =>
  letI := auxiliaryStarRing D C
  Tate.WeilAdelicFrame P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability (X).hasDual (X).geometry
    (X).inversePoincare (X).evaluation compatibility (X).polarization h
    (X).actionObj.action A (D.harrisHodgePELForm C) s
local notation "NormalizedAt" s:max => HarrisIntegralFrameCondition D C P compatibility h s
local notation "Primitive" => HarrisPrimitivePolarization D C P

section Polarization

variable {S : Scheme.{0}}

private theorem primitivePolarization_double_isPolarization (X : PObj S)
    (mu : BOf X ⟶ DOf X) (hmu : Primitive X mu) :
    (WOf X).IsPolarization P (2 • mu) := by
  let := auxiliaryStarRing D C
  obtain ⟨-, k, hk, h⟩ := hmu
  apply polarizationDoublingDivision P S (BOf X) (WOf X) mu k hk
  rw [h]
  exact X.isPolarization

/-- Four times the primitive homomorphism is an actual polarization on
the original abelian scheme. -/
theorem primitivePolarization_four_isPolarization (X : PObj S)
    (mu : BOf X ⟶ DOf X) (hmu : Primitive X mu) :
    (WOf X).IsPolarization P ((4 : ℕ) • mu) := by
  let := auxiliaryStarRing D C
  have h2 := primitivePolarization_double_isPolarization D C P X mu hmu
  have h4 := polarizationDoublingDivision P S (BOf X) (WOf X) (2 • mu) 1
    Nat.one_pos (by simpa only [one_smul] using h2)
  simpa only [smul_smul, show (2 : ℕ) * 2 = 4 by decide] using h4

variable [IsLocallyNoetherian S] [ConnectedSpace S]
  {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (s : Spec (.of Ω) ⟶ S)

/-- The positive degree index of the ordinary polarization obtained by
quadrupling the primitive representative of the ray. -/
def harrisPrimitiveOrdinaryDegreeIndex (X : PObj S)
    (mu : BOf X ⟶ DOf X) (hmu : Primitive X mu) : ℕ :=
  (WOf X).doubledDegreeIndex P (2 • mu)
    (primitivePolarization_double_isPolarization D C P X mu hmu) s

theorem harrisPrimitiveOrdinaryDegreeIndex_spec (X : PObj S)
    (mu : BOf X ⟶ DOf X) (hmu : Primitive X mu) :
    0 < harrisPrimitiveOrdinaryDegreeIndex D C P s X mu hmu ∧
      HasDegreeSquare ((4 : ℕ) • mu) (harrisPrimitiveOrdinaryDegreeIndex D C P s X mu hmu) := by
  have hs := (WOf X).doubledDegreeIndex_spec P (2 • mu)
    (primitivePolarization_double_isPolarization D C P X mu hmu) s
  exact ⟨hs.1, by
    simpa only [harrisPrimitiveOrdinaryDegreeIndex, smul_smul,
      show (2 : ℕ) * 2 = 4 by decide] using hs.2⟩

end Polarization

private theorem finrank_field_nsmul_of_constantDegree
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    {B D' : AbelianScheme (Spec (.of Ω))} {g r k : ℕ}
    (hg : B.HasRelativeDimension g) (hk : 0 < k)
    (f : B ⟶ D') (hf : AbelianScheme.IsIsogeny f) (hr : HasConstantDegree (hom f) r) :
    HasConstantDegree (hom (k • f)) (k ^ (2 * g) * r) := by
  let mul := k • (𝟙 B)
  have hmul := multiplication_isIsogeny_of_ne_zero B k
    (Nat.cast_ne_zero.mpr hk.ne' : (k : Ω) ≠ 0)
  have hmul' : AbelianScheme.IsIsogeny mul := by
    change GroupScheme.IsIsogeny (groupHom (k • 𝟙 B))
    rw [Tate.groupHom_nsmul_id]
    exact hmul
  let : IsFinite (hom mul) := hmul'.1
  let : Flat (hom mul) := hmul'.2.1
  let : IsFinite (hom f) := hf.1
  let : Flat (hom f) := hf.2.1
  let : IsLocallyNoetherian D'.X.left := LocallyOfFiniteType.isLocallyNoetherian D'.X.hom
  obtain ⟨L, hL⟩ := GroupScheme.algebraicallyClosedFieldAmpleExistence Ω B.toGrp B.smooth
    B.proper B.geometricallyConnected
  have hdegree : HasConstantDegree (hom mul) (k ^ (2 * g)) := by
    intro y
    change (groupHom (k • 𝟙 B)).hom.hom.left.finrank y = _
    rw [Tate.groupHom_nsmul_id]
    exact finrank_multiplication_eq_of_ne_zero B GroupScheme.fieldCubePullback g hg L hL k
      (Nat.cast_ne_zero.mpr hk.ne') y
  have hcomp : hom mul ≫ hom f = hom (k • f) := by
    rw [← AbelianScheme.hom_comp]
    change hom ((k • 𝟙 B) ≫ f) = hom (k • f)
    rw [Preadditive.nsmul_comp, Category.id_comp]
  rw [← hcomp]
  exact Langlands.AlgebraicGeometry.finiteFlatConstantRankComposition
    B.X.left B.X.left D'.X.left (hom mul) (hom f) _ _ hdegree hr

private theorem equal_polarization_multiple_of_squareDegree
    {S : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (s : Spec (.of Ω) ⟶ S)
    {B D' : AbelianScheme S} {mu : B ⟶ D'} {g d k j : ℕ}
    (hg : 0 < g) (hd : 0 < d) (hk : 0 < k) (hj : 0 < j)
    (hdim : B.HasRelativeDimension g)
    (hfk : AbelianScheme.IsIsogeny (k • mu)) (hfj : AbelianScheme.IsIsogeny (j • mu))
    (hdk : HasDegreeSquare (k • mu) d) (hdj : HasDegreeSquare (j • mu) d) :
    k = j := by
  let b := (AbelianScheme.baseChange s).obj B
  let target := (AbelianScheme.baseChange s).obj D'
  let f := (AbelianScheme.baseChange s).map (k • mu)
  let f' := (AbelianScheme.baseChange s).map (j • mu)
  have hFg : b.HasRelativeDimension g := hasRelativeDimension_baseChange B g hdim s
  have hfDegree {p : B ⟶ D'} (hp : AbelianScheme.IsIsogeny p) (hdeg : HasDegreeSquare p d) :
      HasDegreeSquare ((AbelianScheme.baseChange s).map p) d := by
    let : IsFinite (hom p) := hp.1
    let : Flat (hom p) := hp.2.1
    intro y
    exact (Scheme.Hom.finrank_of_isPullback _ _ _ _ (hom_baseChange_isPullback s p) y).trans
      (hdeg (pullback.fst D'.X.hom s y))
  have hfd := finrank_field_nsmul_of_constantDegree hFg hj f (hfk.baseChange s)
    (hfDegree hfk hdk)
  have hfd' := finrank_field_nsmul_of_constantDegree hFg hk f' (hfj.baseChange s)
    (hfDegree hfj hdj)
  have hfjk : j • f = k • f' := by
    dsimp only [f, f']
    rw [← Functor.map_nsmul, ← Functor.map_nsmul, smul_smul, smul_smul, Nat.mul_comm j k]
  let y := unitSection target (IsLocalRing.closedPoint Ω)
  have h := (hfd y).symm.trans ((congrArg (fun p => (hom p).finrank y) hfjk).trans (hfd' y))
  exact (Nat.pow_left_injective (Nat.mul_pos (by decide : 0 < 2) hg).ne'
    (Nat.eq_of_mul_eq_mul_right (pow_pos hd 2) h)).symm

/-- If the original polarization and the quadrupled primitive map have the
same positive square degree in positive relative dimension, the maps agree. -/
theorem harrisQuadrupledPrimitive_eq_of_squareDegree
    {S : Scheme.{0}} {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (s : Spec (.of Ω) ⟶ S) (X : PObj S) (mu : BOf X ⟶ DOf X) (hmu : Primitive X mu)
    {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (hdim : (BOf X).HasRelativeDimension g)
    (hdeg : letI := auxiliaryStarRing D C; HasDegreeSquare X.polarization d)
    (hdeg' : HasDegreeSquare ((4 : ℕ) • mu) d) :
    letI := auxiliaryStarRing D C
    (4 : ℕ) • mu = X.polarization := by
  let := auxiliaryStarRing D C
  have hf4 := (primitivePolarization_four_isPolarization D C P X mu hmu).1
  obtain ⟨-, k, hk, hpol⟩ := hmu
  have hfk : AbelianScheme.IsIsogeny (k • mu) := hpol.symm ▸ X.isPolarization.1
  have heq := equal_polarization_multiple_of_squareDegree s hg hd hk
    (by decide : 0 < (4 : ℕ)) hdim hfk hf4 (hpol.symm ▸ hdeg) hdeg'
  rwa [heq] at hpol

section Comparison

variable (htor : TorsionFiniteEtaleStatement.{0})
  {S S' : Scheme.{0}} [IsLocallyNoetherian S] [IsLocallyNoetherian S']
  [ConnectedSpace S] [ConnectedSpace S']
  {Ω Ω' : Type} [Field Ω] [Field Ω'] [IsAlgClosed Ω] [IsAlgClosed Ω']
  [CharZero Ω] [CharZero Ω']
  (s : Spec (.of Ω) ⟶ S) (s' : Spec (.of Ω') ⟶ S')
  (hu : ∀ k : Index PAll, IsUnit (k.val : Γ(S, ⊤)))
  (hu' : ∀ k : Index PAll, IsUnit (k.val : Γ(S', ⊤)))

include htor hu hu' in
/-- The ordinary degree index is independent of the normalized object,
its primitive representative and its geometric point. -/
theorem harrisPrimitiveOrdinaryDegreeIndex_eq
    (X : PObj S) (eta : FrameAt s X) (hn : (NormalizedAt s) X eta)
    (Y : PObj S') (eta' : FrameAt s' Y) (hn' : (NormalizedAt s') Y eta')
    (mu : BOf X ⟶ DOf X) (hmu : Primitive X mu)
    (mu' : BOf Y ⟶ DOf Y) (hmu' : Primitive Y mu') :
    harrisPrimitiveOrdinaryDegreeIndex D C P s X mu hmu =
      harrisPrimitiveOrdinaryDegreeIndex D C P s' Y mu' hmu' := by
  let := auxiliaryStarRing D C
  let y := unitSection ((baseChange s).obj (DOf X)) (IsLocalRing.closedPoint Ω)
  let y' := unitSection ((baseChange s').obj (DOf Y)) (IsLocalRing.closedPoint Ω')
  have hRank := primitivePolarization_nativeRank_eq D C P compatibility h s htor hu
    s' hu' X eta hn Y eta' hn' mu hmu mu' hmu' 4
    (primitivePolarization_four_isPolarization D C P X mu hmu).1
    (primitivePolarization_four_isPolarization D C P Y mu' hmu').1 y y'
  have hx := (harrisPrimitiveOrdinaryDegreeIndex_spec D C P s X mu hmu).2
    (pullback.fst (DOf X).X.hom s y)
  have hy := (harrisPrimitiveOrdinaryDegreeIndex_spec D C P s' Y mu' hmu').2
    (pullback.fst (DOf Y).X.hom s' y')
  exact Nat.pow_left_injective (n := 2) (by decide) (hx.symm.trans (hRank.trans hy))

end Comparison

/-- A degree index for the quadrupled primitive representatives on all
connected normalized Harris bases. -/
def HarrisPrimitiveOrdinaryDegreeUniform (d : ℕ) : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] [ConnectedSpace S]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (s : Spec (.of Ω) ⟶ S),
    (∀ k : Index PAll, IsUnit (k.val : Γ(S, ⊤))) →
      ∀ (X : PObj S) (eta : FrameAt s X), (NormalizedAt s) X eta →
        ∀ (mu : BOf X ⟶ DOf X), Primitive X mu → HasDegreeSquare ((4 : ℕ) • mu) d

/-- A single positive degree index works for all indicated normalized
Harris objects, independently of principal level. -/
theorem exists_harrisPrimitiveOrdinaryDegreeUniform (htor : TorsionFiniteEtaleStatement.{0}) :
    ∃ d : ℕ, 0 < d ∧ HarrisPrimitiveOrdinaryDegreeUniform D C P compatibility h d := by
  classical
  by_cases hOne : HarrisPrimitiveOrdinaryDegreeUniform D C P compatibility h 1
  · exact ⟨1, Nat.one_pos, hOne⟩
  · simp only [HarrisPrimitiveOrdinaryDegreeUniform, not_forall] at hOne
    obtain ⟨S, hS, hC, Ω, hΩ, hAlg, hChar, s, hu, X, eta, hn, mu, hmu, _⟩ := hOne
    let := hS
    let := hC
    let := hΩ
    let := hAlg
    let := hChar
    let d := harrisPrimitiveOrdinaryDegreeIndex D C P s X mu hmu
    refine ⟨d, (harrisPrimitiveOrdinaryDegreeIndex_spec D C P s X mu hmu).1, ?_⟩
    intro S' _ _ Ω' _ _ _ s' hu' Y eta' hn' mu' hmu'
    have he : d = harrisPrimitiveOrdinaryDegreeIndex D C P s' Y mu' hmu' :=
      harrisPrimitiveOrdinaryDegreeIndex_eq D C P compatibility h htor s s' hu hu'
        X eta hn Y eta' hn' mu hmu mu' hmu'
    exact he.symm ▸ (harrisPrimitiveOrdinaryDegreeIndex_spec D C P s' Y mu' hmu').2

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
