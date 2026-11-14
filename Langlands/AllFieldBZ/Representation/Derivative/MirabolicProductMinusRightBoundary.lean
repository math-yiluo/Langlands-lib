import Langlands.AllFieldBZ.Group.GL.MirabolicModulusProof
import Langlands.AllFieldBZ.Representation.Derivative.MinusVanishing
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
import Langlands.AllFieldBZ.Representation.Induction.InverseTranspose
import Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary

/-!
# All-field port of `Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open MeasureTheory
open MeasureTheory.Measure
open scoped TensorProduct
open scoped NNReal
namespace Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
open Langlands.Derivative.MirabolicProductMinus hiding LeftPhiBoundary LeftPhiCompatibility LeftPsiCompatibility RightPhiBoundary RightPhiShortExact RightPsiCompatibility leftPhiExpected leftPhiProduct mirabolicRankCastIso mulEquivHaarChar_conj_levi_inv psiMinus_zero_trivial radical_compactOpenBasis radical_compactOpenCover rightBoundaryQuotient rightBoundaryQuotientEquiv rightBoundaryQuotientEquiv_action rightBoundaryQuotientEquiv_natural rightBoundaryTopEquiv rightPhiBoundary rightPhiProduct rightPhiQuotient rightPhiSubobject twist_rightInducing_levi_zero
open Langlands.GeneralLinear
open Langlands.AllFieldBZ.GeneralLinear
open Langlands.GeneralLinear.Mirabolic hiding leviRadical_haarCharacter radicalCoordinates_isAddHaar radicalHaar_map_leviConj
open Langlands.AllFieldBZ.GeneralLinear.Mirabolic
open Langlands.GeneralLinear.Mirabolic.MixedProduct
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllFieldBZ.HarmonicAnalysis
universe uF uV

/-! ## Transport along equal subgroups and trivial localizations -/

section Transport
variable {G : Type*} [Group G]

end Transport
/-! ## Split kernels with trivial intersection -/

section TrivialIntersection
open Langlands.Induction
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G]
variable {L : Type*} [Group L] [TopologicalSpace L]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable (r : G →* L) (s : L →* G) (hrs : ∀ l, r (s l) = l)
variable (hr : Continuous r) (hs : Continuous s)
variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (hsH : ∀ l, s l ∈ H)
variable (σ : Representation ℂ H V) (hσ : IsSmooth σ) (θ : SmoothCharacter ℂ r.ker)
variable (hI : ∀ i : H.comap r.ker.subtype, i = 1)

variable [MeasurableSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype))]
  [BorelSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype))]
variable (ν : Measure (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)))
  [IsFiniteMeasureOnCompacts ν]
variable [LocallyCompactSpace r.ker] [MeasurableSpace r.ker] [BorelSpace r.ker]
variable [MeasurableSpace (H.comap r.ker.subtype)] [BorelSpace (H.comap r.ker.subtype)]
variable (hBasis : ∀ O : Set r.ker, IsOpen O → (1 : r.ker) ∈ O →
  ∃ K : OpenSubgroup r.ker, IsCompact (K : Set r.ker) ∧ (K : Set r.ker) ⊆ O)
variable (μN : Measure r.ker) (μI : Measure (H.comap r.ker.subtype))
variable [IsHaarMeasure μN] [μN.Regular] [IsMulRightInvariant μN]
variable [IsHaarMeasure μI] [μI.Regular] [IsMulRightInvariant μI]
variable (hCompatible : QuotientIntegration.IsCompatible (H.comap r.ker.subtype) μN μI ν)

end TrivialIntersection
/-! ## The explicit rank cast of the mirabolic group -/

section RankCast
variable {R : Type*} [CommRing R]

end RankCast
/-! ## The case (III) subgroup for `r = 0` -/

section RightZero
variable {R : Type*} [CommRing R] {m : ℕ}

end RightZero
variable {F : LocalFieldPackage.{uF}}

/-! ## Radical boxes and the Levi Haar modulus -/

section Padic
/-- Radical boxes form a basis of compact open subgroups at the identity. -/
theorem radical_compactOpenBasis (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ O : Set (radical (m + 1) F.Carrier), IsOpen O → (1 : radical (m + 1) F.Carrier) ∈ O →
      ∃ K : OpenSubgroup (radical (m + 1) F.Carrier),
        IsCompact (K : Set (radical (m + 1) F.Carrier)) ∧
          (K : Set (radical (m + 1) F.Carrier)) ⊆ O := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro O hO h1
  have h0 : radicalElement ⁻¹' O ∈ nhds (0 : Fin (m + 1) → F.Carrier) := by
    apply (hO.preimage continuous_radicalElement).mem_nhds
    rw [Set.mem_preimage, radicalElement_zero]
    exact h1
  obtain ⟨N, hN⟩ := Mirabolic.exists_latticeBox_subset T h0
  refine ⟨Mirabolic.radicalBox T m N, Mirabolic.isCompact_radicalBox T m N, fun u hu => ?_⟩
  have h := hN ((Mirabolic.mem_radicalBox T).mp hu)
  rwa [Set.mem_preimage, radicalElement_coordinates] at h

/-- Every radical element lies in a compact open radical box. -/
theorem radical_compactOpenCover (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ u : radical (m + 1) F.Carrier, ∃ K : OpenSubgroup (radical (m + 1) F.Carrier),
      IsCompact (K : Set (radical (m + 1) F.Carrier)) ∧ u ∈ K := by
  let := T.topology
  intro u
  obtain ⟨M, hM⟩ := Mirabolic.exists_mem_latticeBox T (radicalCoordinates u)
  exact ⟨Mirabolic.radicalBox T m M, Mirabolic.isCompact_radicalBox T m M, hM⟩

/-- Conjugation `u ↦ diag(l,1)⁻¹ u diag(l,1)` scales Haar measure on the radical
by `|det l|⁻¹`. -/
theorem mulEquivHaarChar_conj_levi_inv (T : F.TopologicalData) (n : ℕ)
    (l : GeneralLinear n F.Carrier)
    (hl : (levi l)⁻¹ ∈ Subgroup.normalizer (radical n F.Carrier : Set (mirabolic n F.Carrier))) :
    letI := T.topology
    letI := T.fieldT2
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI := T.generalLinearLocallyCompactSpace (n + 1)
    letI := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
    letI : LocallyCompactSpace (radical n F.Carrier) := radical_isClosed.locallyCompactSpace
    letI : MeasurableSpace (radical n F.Carrier) := borel _
    haveI : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
    mulEquivHaarChar (HaarModulus.normalizerConj (radical n F.Carrier) ⟨(levi l)⁻¹, hl⟩) =
      (T.determinantNorm n l : ℝ≥0)⁻¹ := by
  let := T.topology
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (n + 1)
  let := T.generalLinearLocallyCompactSpace (n + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := n) (F := F.Carrier)
  let : LocallyCompactSpace (radical n F.Carrier) := radical_isClosed.locallyCompactSpace
  let : MeasurableSpace (radical n F.Carrier) := borel _
  have : BorelSpace (radical n F.Carrier) := ⟨rfl⟩
  have e : (⟨(levi l)⁻¹, hl⟩ :
      Subgroup.normalizer (radical n F.Carrier : Set (mirabolic n F.Carrier))) =
      Subgroup.inclusion leviSubgroup_le_normalizer (leviEquiv l⁻¹) :=
    Subtype.ext (map_inv levi l).symm
  have h := congrArg (fun χ : GeneralLinear n F.Carrier →* ℝ≥0ˣ => ((χ l⁻¹ : ℝ≥0ˣ) : ℝ≥0))
    (Langlands.AllFieldBZ.GeneralLinear.Mirabolic.leviRadical_haarCharacter F T n)
  rw [e]
  refine h.trans ?_
  rw [map_inv, Units.val_inv_eq_inv_val]

/-- For `r = 0`, the normalized case (III) inducing action of `diag(l, 1)` is
`|det l|^(-1/2) (1 ⊗ ρ(l))`. -/
theorem twist_rightInducing_levi_zero (T : F.TopologicalData) (k : ℕ) {W V : Type*}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (mirabolic 0 F.Carrier) W)
    (ρ : Representation ℂ (GeneralLinear k F.Carrier) V) (l : GeneralLinear (k + 0) F.Carrier)
    (w : W ⊗[ℂ] V) :
    letI := T.topology
    twist (T.rightCharacter k 0).toMonoidHom (rightInducingRepresentation τ ρ)
        ⟨levi l, levi_mem_rightSubgroup_zero l⟩ w =
      ((((T.determinantNorm k l : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
        TensorProduct.map LinearMap.id (ρ l) w := by
  let := T.topology
  have h : twist (T.rightCharacter k 0).toMonoidHom (rightInducingRepresentation τ ρ)
      ⟨levi l, levi_mem_rightSubgroup_zero l⟩ w =
      (T.rightLeviCharacter k 0 (rightProjection (k := k) (r := 0) (R := F.Carrier)
          (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup k 0 F.Carrier)) : ℂ) •
        TensorProduct.map (τ (rightProjection (k := k) (r := 0) (R := F.Carrier)
            (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup k 0 F.Carrier)).1)
          (ρ (rightProjection (k := k) (r := 0) (R := F.Carrier)
            (⟨levi l, levi_mem_rightSubgroup_zero l⟩ : rightSubgroup k 0 F.Carrier)).2) w := rfl
  rw [h, rightProjection_levi_zero, T.rightLeviCharacter_zero_right_apply]
  dsimp only
  rw [map_one]
  rfl

end Padic
/-! ## The target side: `(Ψ⁻τ) × (ρ|P)` at `r = 0` -/

section Target
/-- The target functor with its rank cast replaced by the explicit pullback. -/
abbrev rightBoundaryQuotient (T : F.TopologicalData) (k : ℕ) :
    letI := T.topology
    (SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (k + 0) F.Carrier) :=
  letI := T.topology
  (Mirabolic.psiMinus T 0).prod (generalLinearRestriction T k) ⋙
    T.leftMixedProductFunctor 0 k ⋙
      Langlands.Derivative.Mirabolic.continuousPullbackFunctor (mirabolicCastHom (Nat.add_comm 0 k))
        (continuous_mirabolicCastHom (Nat.add_comm 0 k))

theorem psiMinus_zero_trivial (T : F.TopologicalData)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier))
    (u : radical 0 F.Carrier) (v : A) :
    letI := T.topology
    A.representation (u : mirabolic 0 F.Carrier) v =
      (((1 : radical 0 F.Carrier →* ℂˣ) u : ℂˣ) : ℂ) • v := by
  let := T.topology
  rw [Subsingleton.elim u 1, OneMemClass.coe_one, map_one, map_one, Units.val_one, one_smul,
    Module.End.one_apply]

/-- Evaluation at `1` on `(Ψ⁻τ) × (ρ|P)` at `r = 0`, where the inducing
subgroup is the whole group. -/
def rightBoundaryTopEquiv (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (0 + k + 1)
  Induction.compactInducedTopEquiv (leftSubgroup 0 k F.Carrier) mem_leftSubgroup_zero
    (twist (T.leftCharacter 0 k).toMonoidHom
      (leftInducingRepresentation ((Mirabolic.psiMinus T 0).obj X.1).representation
        ((generalLinearRestriction T k).obj X.2).representation))
    ((isSmooth_twist_iff _ _ (T.leftCharacter 0 k).isOpen_ker).mpr
      (isSmooth_leftInducingRepresentation ((Mirabolic.psiMinus T 0).obj X.1).isSmooth
        ((generalLinearRestriction T k).obj X.2).isSmooth))

/-- The carrier of `(Ψ⁻τ) × (ρ|P)` at `r = 0`: evaluation at `1`, followed by the
trivial `V_1`-quotient of `τ`. -/
def rightBoundaryQuotientEquiv (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)) :
    letI := T.topology
    (rightBoundaryQuotient.{uF, uV} T k).obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2 :=
  letI := T.topology
  (rightBoundaryTopEquiv T k X).toLinearEquiv.trans
    (TensorProduct.congr
      (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
        (psiMinus_zero_trivial T X.1))
      (LinearEquiv.refl ℂ X.2))

/-- The identification turns the action of `g ∈ P_(k+1)` into `1 ⊗ ρ(g)`. -/
theorem rightBoundaryQuotientEquiv_action (T : F.TopologicalData) (k : ℕ)
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier))
    (g : mirabolic (k + 0) F.Carrier)
    (x : letI := T.topology; (rightBoundaryQuotient.{uF, uV} T k).obj X) :
    letI := T.topology
    rightBoundaryQuotientEquiv T k X
        (((rightBoundaryQuotient.{uF, uV} T k).obj X).representation g x) =
      TensorProduct.map LinearMap.id (X.2.representation g.val)
        (rightBoundaryQuotientEquiv T k X x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (0 + k + 1)
  let X' : SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (mirabolic k F.Carrier) :=
    ((Mirabolic.psiMinus T 0).obj X.1, (generalLinearRestriction T k).obj X.2)
  let g' : leftSubgroup 0 k F.Carrier :=
    Induction.topHom (leftSubgroup 0 k F.Carrier) mem_leftSubgroup_zero
      (mirabolicCastHom (Nat.add_comm 0 k) g)
  let eX := TensorProduct.congr
    (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
      (psiMinus_zero_trivial T X.1)) (LinearEquiv.refl ℂ X.2)
  have hB : T.leftMixedEval X' (((rightBoundaryQuotient.{uF, uV} T k).obj X).representation g x) 1 =
      T.leftMixedEval X' x (mirabolicCastHom (Nat.add_comm 0 k) g) :=
    (T.leftMixedProductFunctor_action X' (mirabolicCastHom (Nat.add_comm 0 k) g) x 1).trans
      (congrArg _ (one_mul _))
  have hc0 : T.leftLeviCharacter 0 k (leftProjection g') = 1 := by
    rw [T.leftLeviCharacter_zero_left k]
    rfl
  have hC : T.leftMixedEval X' x (mirabolicCastHom (Nat.add_comm 0 k) g) =
      leftInducingRepresentation X'.1.representation X'.2.representation g'
        (T.leftMixedEval X' x 1) := by
    have := T.leftMixedEval_covariant X' x g' 1
    rw [mul_one, hc0, Units.val_one, one_smul] at this
    exact this
  have e₁ : (leftProjection g').1 = 1 := Units.ext (Matrix.ext fun i => Fin.elim0 i)
  have e₂ : (leftProjection g').2 = g := leftUnitProjection_mirabolicCastHom k g
  have key : eX.toLinearMap ∘ₗ
        leftInducingRepresentation X'.1.representation X'.2.representation g' =
      TensorProduct.map LinearMap.id (X.2.representation g.val) ∘ₗ eX.toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    change TensorProduct.congr _ _ (X'.1.representation (leftProjection g').1 a ⊗ₜ[ℂ]
        X'.2.representation (leftProjection g').2 b) = _
    rewrite [e₁, e₂, map_one X'.1.representation]
    rfl
  have h1 : ∀ y : (rightBoundaryQuotient.{uF, uV} T k).obj X,
      rightBoundaryQuotientEquiv T k X y = eX (T.leftMixedEval X' y 1) := fun y => rfl
  have h2 : eX (T.leftMixedEval X'
        (((rightBoundaryQuotient.{uF, uV} T k).obj X).representation g x) 1) =
      eX (leftInducingRepresentation X'.1.representation X'.2.representation g'
        (T.leftMixedEval X' x 1)) := congrArg eX (hB.trans hC)
  have h3 : eX (leftInducingRepresentation X'.1.representation X'.2.representation g'
        (T.leftMixedEval X' x 1)) =
      TensorProduct.map LinearMap.id (X.2.representation g.val)
        (eX (T.leftMixedEval X' x 1)) :=
    LinearMap.congr_fun key (T.leftMixedEval X' x 1)
  exact ((h1 _).trans h2).trans (h3.trans (congrArg _ (h1 x).symm))

/-- The identification is natural in both inputs. -/
theorem rightBoundaryQuotientEquiv_natural (T : F.TopologicalData) (k : ℕ)
    {X Y : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)}
    (φ : letI := T.topology; X ⟶ Y)
    (x : letI := T.topology; (rightBoundaryQuotient.{uF, uV} T k).obj X) :
    letI := T.topology
    rightBoundaryQuotientEquiv T k Y
        (SmoothRep.hom ((rightBoundaryQuotient.{uF, uV} T k).map φ) x) =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
        (rightBoundaryQuotientEquiv T k X x) := by
  let := T.topology
  have h : (rightBoundaryTopEquiv T k Y).toLinearEquiv
      (SmoothRep.hom ((rightBoundaryQuotient.{uF, uV} T k).map φ) x) =
      TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T 0).map φ.1)).toLinearMap
        (SmoothRep.hom φ.2).toLinearMap ((rightBoundaryTopEquiv T k X).toLinearEquiv x) := rfl
  have key : (TensorProduct.congr
        (localizationTrivialEquiv Y.1.representation (radical 0 F.Carrier) 1
          (psiMinus_zero_trivial T Y.1)) (LinearEquiv.refl ℂ Y.2)).toLinearMap ∘ₗ
        TensorProduct.map (SmoothRep.hom ((Mirabolic.psiMinus T 0).map φ.1)).toLinearMap
          (SmoothRep.hom φ.2).toLinearMap =
      TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap ∘ₗ
        (TensorProduct.congr
          (localizationTrivialEquiv X.1.representation (radical 0 F.Carrier) 1
            (psiMinus_zero_trivial T X.1)) (LinearEquiv.refl ℂ X.2)).toLinearMap := by
    apply TensorProduct.ext'
    intro a b
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective _ _ _ a
    rfl
  exact (congrArg (TensorProduct.congr
    (localizationTrivialEquiv Y.1.representation (radical 0 F.Carrier) 1
      (psiMinus_zero_trivial T Y.1)) (LinearEquiv.refl ℂ Y.2)) h).trans
    (LinearMap.congr_fun key _)

end Target
/-- The actual rank transport is pullback along the explicit cast homomorphism. -/
def mirabolicRankCastIso (T : F.TopologicalData) {a b : ℕ} (h : a = b) :
    letI := T.topology
    mirabolicRankCast.{uF, uV} T h ≅
      Langlands.Derivative.Mirabolic.continuousPullbackFunctor (mirabolicCastHom h)
        (continuous_mirabolicCastHom h) := by
  letI := T.topology
  subst h
  exact Iso.refl _

/-! ## The boundary clause -/

section Boundary
open Langlands.Induction
set_option maxHeartbeats 400000 in
/-- BZ77 4.13(c) at source rank one: `Φ⁻(τ × ρ) ≅ (Ψ⁻τ) × (ρ|P)` naturally,
for `τ` on `P_1` and `ρ` on `GL_(k+1)`. -/
theorem rightPhiBoundary (T : F.TopologicalData) : RightPhiBoundary.{uF, uV} F T := by
  let := T.topology
  intro ψ k
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.generalLinearTopologicalGroup (k + 1 + 0 + 1)
  let := T.generalLinearLocallyCompactSpace (k + 1 + 0 + 1)
  let := GeneralLinear.Mirabolic.locallyCompactSpace (n := k + 1 + 0) (F := F.Carrier)
  -- The split group data: `G = P_(k+2)`, `r = projection`, `s = levi`, `H` of case (III).
  let r := projection (n := k + 1 + 0) (F := F.Carrier)
  let s := levi (n := k + 1 + 0) (F := F.Carrier)
  let H := rightSubgroup (k + 1) 0 F.Carrier
  have hrs : ∀ l, r (s l) = l := projection_levi
  have hr : Continuous r := GeneralLinear.Mirabolic.continuous_projection
  have hs : Continuous s := continuous_levi
  have hH : IsClosed (H : Set (mirabolic (k + 1 + 0) F.Carrier)) := rightSubgroup_isClosed
  have hsH : ∀ l, s l ∈ H := levi_mem_rightSubgroup_zero
  have hNr : r.ker = radical (k + 1 + 0) F.Carrier := ker_projection
  let θ : SmoothCharacter ℂ r.ker :=
    { toMonoidHom := (T.mirabolicTheta ψ (k + 0)).comp (Subgroup.inclusion hNr.le)
      isOpen_ker := (T.mirabolicTheta_isOpen_ker ψ (k + 0)).preimage
        (continuous_inclusion hNr.le) }
  have hI : ∀ i : H.comap r.ker.subtype, i = 1 := fun i =>
    Subtype.ext (Subtype.ext (eq_one_of_mem_rightSubgroup_zero (m := k + 1) i.2 i.1.2))
  -- Measures on the kernel, the trivial intersection and the quotient.
  have hNc : IsClosed (r.ker : Set (mirabolic (k + 1 + 0) F.Carrier)) := by
    rw [hNr]
    exact radical_isClosed
  let : LocallyCompactSpace r.ker := hNc.locallyCompactSpace
  have hIc : IsClosed ((H.comap r.ker.subtype : Subgroup r.ker) : Set r.ker) :=
    hH.preimage continuous_subtype_val
  let : LocallyCompactSpace (H.comap r.ker.subtype) := hIc.locallyCompactSpace
  let : MeasurableSpace r.ker := borel _
  have : BorelSpace r.ker := ⟨rfl⟩
  let : MeasurableSpace (H.comap r.ker.subtype) := borel _
  have : BorelSpace (H.comap r.ker.subtype) := ⟨rfl⟩
  let : MeasurableSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)) := borel _
  have : BorelSpace (QuotientIntegration.LeftQuotient (H.comap r.ker.subtype)) := ⟨rfl⟩
  have hBasis := compactOpenBasis_congr hNr.symm (radical_compactOpenBasis T (k + 0))
  have hCover := compactOpenCover_congr hNr.symm (radical_compactOpenCover T (k + 0))
  have hu := Haar.compactOpenCoverUnimodularity hCover
  let μN : Measure r.ker := haar
  let μI : Measure (H.comap r.ker.subtype) := haar
  have : IsMulRightInvariant μN := hu.1 μN
  have : IsMulRightInvariant μI := hu.2 _ hIc μI
  obtain ⟨ν, hν⟩ := QuotientIntegration.compatibleMeasureExists _ hIc μN μI
  have : ν.Regular := hν.regular
  -- The Levi Haar modulus and the invariance of `θ`.
  have hHaar : ∀ l : GeneralLinear (k + 1 + 0) F.Carrier,
      mulEquivHaarChar (splitKernelConjugation r s l) =
        (T.determinantNorm (k + 1 + 0) l : ℝ≥0)⁻¹ := by
    intro l
    let : LocallyCompactSpace (radical (k + 1 + 0) F.Carrier) :=
      radical_isClosed.locallyCompactSpace
    let : MeasurableSpace (radical (k + 1 + 0) F.Carrier) := borel _
    have : BorelSpace (radical (k + 1 + 0) F.Carrier) := ⟨rfl⟩
    have hl : (levi l)⁻¹ ∈ Subgroup.normalizer
        (radical (k + 1 + 0) F.Carrier : Set (mirabolic (k + 1 + 0) F.Carrier)) := by
      rw [← hNr]
      simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]
    exact (mulEquivHaarChar_normalizerConj_congr hNr ((levi l)⁻¹)
      (by simp only [Subgroup.normalizer_eq_top, Subgroup.mem_top]) hl).trans
      (mulEquivHaarChar_conj_levi_inv T (k + 1 + 0) l hl)
  have hθl : ∀ (h : mirabolic (k + 0) F.Carrier) (n : r.ker),
      θ.toMonoidHom (splitKernelConjugation r s h.val n) = θ.toMonoidHom n := by
    intro h n
    have hn : (n : mirabolic (k + 1 + 0) F.Carrier) ∈ radical (k + 0 + 1) F.Carrier :=
      hNr ▸ n.2
    have := Derivative.Mirabolic.theta_isInvariant ψ (k + 0) (successorEquiv h⁻¹) ⟨n.1, hn⟩
    refine (congrArg (Derivative.Mirabolic.theta ψ (k + 0)) (Subtype.ext ?_)).trans this
    change (levi h.val)⁻¹ * (n : mirabolic (k + 1 + 0) F.Carrier) * levi h.val =
      successor h⁻¹ * (n : mirabolic (k + 1 + 0) F.Carrier) * (successor h⁻¹)⁻¹
    rw [map_inv, inv_inv]
    rfl
  -- The source identification.
  let σ := fun X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier) =>
    twist (T.rightCharacter (k + 1) 0).toMonoidHom
      (rightInducingRepresentation X.1.representation X.2.representation)
  have hσ : ∀ X, IsSmooth (σ X) := fun X =>
    (isSmooth_twist_iff _ _ (T.rightCharacter (k + 1) 0).isOpen_ker).mpr
      (isSmooth_rightInducingRepresentation X.1.isSmooth X.2.isSmooth)
  let E : ∀ X : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier),
      (rightPhiProduct.{uF, uV} T ψ k 0).obj X ≃ₗ[ℂ] X.1 ⊗[ℂ] X.2 := fun X =>
    (Submodule.quotEquivOfEq _ _ (relations_congr (compactInduced H (σ X)) hNr.symm
      (T.mirabolicTheta ψ (k + 0)) θ.toMonoidHom fun _ => rfl)).trans
      (trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν)
  have hE : ∀ X (h : mirabolic (k + 0) F.Carrier)
      (v : (rightPhiProduct.{uF, uV} T ψ k 0).obj X),
      E X (((rightPhiProduct.{uF, uV} T ψ k 0).obj X).representation h v) =
        TensorProduct.map LinearMap.id (X.2.representation h.val) (E X v) := by
    intro X h v
    let A := (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
    obtain ⟨f, rfl⟩ := Mirabolic.phiMinusQuotient_surjective T ψ (k + 0) A v
    let l : GeneralLinear (k + 1 + 0) F.Carrier := h.val
    let w := trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν
      (Jacquet.Localization.mk (compactInduced H (σ X)) r.ker θ.toMonoidHom f)
    have h1 : E X (((rightPhiProduct.{uF, uV} T ψ k 0).obj X).representation h
          (Mirabolic.phiMinusQuotient T ψ (k + 0) A f)) =
        ((realPowerCharacter ((T.determinantNorm (k + 0 + 1)).comp
          (mirabolic (k + 0) F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ)) •
          trivialSplitKernelEquiv r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis μN μI hν
            (Jacquet.Localization.mk (compactInduced H (σ X)) r.ker θ.toMonoidHom
              (compactInduced H (σ X) (s l) f)) :=
      map_smul (E X) _ _
    have h2 := trivialSplitKernelEquiv_section r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν
      hBasis μN μI hν l (hθl h) f
    have h3 : σ X ⟨s l, hsH l⟩ w =
        ((((T.determinantNorm (k + 1) l : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) •
          TensorProduct.map LinearMap.id (X.2.representation h.val) w :=
      twist_rightInducing_levi_zero T (k + 1) X.1.representation X.2.representation l w
    have hc : ((realPowerCharacter ((T.determinantNorm (k + 0 + 1)).comp
          (mirabolic (k + 0) F.Carrier).subtype) (-(1 / 2 : ℝ)) h : ℂ)) *
        ((((mulEquivHaarChar (splitKernelConjugation r s l))⁻¹ : ℝ≥0) : ℝ) : ℂ) *
          ((((T.determinantNorm (k + 1) l : ℝ≥0) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
      rw [hHaar l, coe_realPowerCharacter]
      exact half_mul_inv_inv_mul_half (T.determinantNorm (k + 1) l)
    have hw : E X (Mirabolic.phiMinusQuotient T ψ (k + 0) A f) = w := rfl
    refine h1.trans ?_
    rw [h2, h3, hw]
    exact smul_smul_smul_of_mul_eq_one _ _ _ _ hc
  have hEnat : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (mirabolic 0 F.Carrier) ×
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (k + 1) F.Carrier)} (φ : X ⟶ Y)
      (v : (rightPhiProduct.{uF, uV} T ψ k 0).obj X),
      E Y (SmoothRep.hom ((rightPhiProduct.{uF, uV} T ψ k 0).map φ) v) =
        TensorProduct.map (SmoothRep.hom φ.1).toLinearMap (SmoothRep.hom φ.2).toLinearMap
          (E X v) := by
    intro X Y φ v
    let A := (T.rightMixedProductFunctor.{uF, uV} (k + 1) 0).obj X
    obtain ⟨f, rfl⟩ := Mirabolic.phiMinusQuotient_surjective T ψ (k + 0) A v
    exact trivialSplitKernelEquiv_natural r s hrs hr hs H hH hsH (σ X) (hσ X) θ hI ν hBasis
      μN μI hν (hσ Y) (twistIntertwining (T.rightCharacter (k + 1) 0).toMonoidHom
        (MixedProductTensor.pullbackMap rightProjection
          (MixedProductTensor.externalMap (SmoothRep.hom φ.1) (SmoothRep.hom φ.2)))) f
  -- Assemble the natural isomorphism.
  let iso0 : rightPhiProduct.{uF, uV} T ψ k 0 ≅ rightBoundaryQuotient.{uF, uV} T k :=
    NatIso.ofComponents
      (fun X => SmoothRep.mkIso (equivOfCommonModel
        (fun g => TensorProduct.map LinearMap.id (X.2.representation g.val)) (E X)
        (rightBoundaryQuotientEquiv T k X) (hE X) (rightBoundaryQuotientEquiv_action T k X)))
      (fun φ => MixedProductTensor.smoothRep_hom_ext fun v =>
        symm_comp_natural _ _ _ _ _ _ _ (hEnat φ) (rightBoundaryQuotientEquiv_natural T k φ) v)
  exact ⟨iso0 ≪≫ Functor.isoWhiskerLeft
    ((Mirabolic.psiMinus T 0).prod (generalLinearRestriction T k) ⋙
      T.leftMixedProductFunctor.{uF, uV} 0 k)
      (mirabolicRankCastIso.{uF, max uF uV} T (Nat.add_comm 0 k)).symm⟩

end Boundary
end Langlands.AllFieldBZ.Derivative.MirabolicProductMinus
