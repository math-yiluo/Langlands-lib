import Langlands.Automorphic.GeneralLinearQuotientOrbitCoefficients
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Automorphic.OperatorSubquotientArchimedean
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanSeparateJointFiniteProof
import Langlands.Global.ArchimedeanCompactLieOrbitDensityProof

/-! # Invariance of the Hilbert closure of actual operator-realization classes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj Topology

set_option autoImplicit false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.RationalInvariantFunctions F n) := Submodule.addCommGroup _

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (Langlands.Automorphic.ContinuousRationalFunctions F n) := Submodule.addCommGroup _

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

local instance (F : Type u) [Field F] [NumberField F] (n : ℕ)
    (R : OperatorRealization F n) : AddCommGroup R.Space := Submodule.addCommGroup R.toSubmodule

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

local notation "n" => r + 1
local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "μQ" => positiveRationalQuotientHaarMeasure F GLs T i
local notation "ρ" => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
local notation "E" => Lp ℂ 2 μQ
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F n
local notation "b∞" => fun g => ContinuousMulEquiv.symm m (AdelicGL.ofInfinite F n g)
local notation "b_f" => fun g => ContinuousMulEquiv.symm m (AdelicGL.ofFinite F n g)
local notation "hRI" => haarQuotientMeasureRightInvariant F GLs T i hi I e hc

set_option maxHeartbeats 800000 in
/-- The quotient class map intertwines the actual finite adelic action. -/
theorem generalLinear_formClass_finiteRepresentation
    (R : OperatorRealization F n) (j : R.Space →ₗ[ℂ] E)
    (hj : ∀ f, IsGeneralLinearFormClass F r T i (j f) (R.toContinuous f))
    (d : FiniteAdelicGL F n) (f : R.Space) :
    j (R.finiteRepresentation d f) = ρ (b_f d) (j f) := by
  have ht := (hj f).rightTranslate hRI (b_f d)
  have hEq : R.toContinuous (R.finiteRepresentation d f) =
      Langlands.Automorphic.continuousRightAction F n (m (b_f d)) (R.toContinuous f) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change ContinuousRationalFunctions.evaluate F n (R.toContinuous (R.finiteRepresentation d f)) x =
      ContinuousRationalFunctions.evaluate F n (R.toContinuous f) (x * m (b_f d))
    rw [R.evaluate_finiteRepresentation, (m).apply_symm_apply]
  rw [← hEq] at ht
  exact IsGeneralLinearFormClass.unique (hj (R.finiteRepresentation d f)) ht

set_option maxHeartbeats 800000 in
/-- The quotient class map intertwines the actual standard archimedean compact action. -/
theorem generalLinear_formClass_compactRepresentation
    (R : OperatorRealization F n) (j : R.Space →ₗ[ℂ] E)
    (hj : ∀ f, IsGeneralLinearFormClass F r T i (j f) (R.toContinuous f))
    (k : standardInfiniteCompact F n) (f : R.Space) :
    j (R.compactRepresentation k f) = ρ (b∞ k.val) (j f) := by
  have ht := (hj f).rightTranslate hRI (b∞ k.val)
  have hEq : R.toContinuous (R.compactRepresentation k f) =
      Langlands.Automorphic.continuousRightAction F n (m (b∞ k.val)) (R.toContinuous f) := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change ContinuousRationalFunctions.evaluate F n (R.toContinuous (R.compactRepresentation k f)) x =
      ContinuousRationalFunctions.evaluate F n (R.toContinuous f) (x * m (b∞ k.val))
    rw [R.evaluate_compactRepresentation, (m).apply_symm_apply]
  rw [← hEq] at ht
  exact IsGeneralLinearFormClass.unique (hj (R.compactRepresentation k f)) ht

omit [(Measure.haar : Measure (normOneSubgroup F GLs)).IsMulRightInvariant] in
set_option maxHeartbeats 1600000 in
private theorem coeff_isJointFinite
    (R : OperatorRealization F n) (C : R.Space →ₗ[ℂ] ArchimedeanGL.SmoothFunctions F n)
    (hD : ∀ D f, ArchimedeanGL.envelopingAction F n D (C f) = C (R.envelopingAction D f))
    (hK : ∀ (k : standardInfiniteCompact F n) (f : R.Space),
      C (R.compactRepresentation k f) = ArchimedeanGL.smoothRightAction F n k.val (C f))
    (f : R.Space) : ArchimedeanGL.IsJointFinite F n (C f) := by
  let ZMap : R.centerRepresentation.IntertwiningMap (ArchimedeanGL.centerRepresentation F n) :=
    { toLinearMap := C
      isIntertwining' := fun z => LinearMap.ext fun v =>
        (hD (ArchimedeanGL.centerInclusion F n z) v).symm }
  have hZ : ArchimedeanGL.IsCenterFinite F n (C f) :=
    (R.centerRepresentation_isFiniteVector f).map ZMap
  let KMap : R.compactRepresentation.IntertwiningMap
      ((ArchimedeanGL.smoothRightAction F n).comp (standardInfiniteCompact F n).subtype) :=
    { toLinearMap := C
      isIntertwining' := fun k => LinearMap.ext fun v => hK k v }
  have hgroup := (R.compactRepresentation_isFiniteVector f).map KMap
  exact ArchimedeanGL.separateJointFinite F n (C f) hZ
    (ArchimedeanGL.compactGroupFiniteDifferential F n (C f) hgroup)

/-- The Hilbert closure of the quotient classes of a represented operator realization is
invariant under the whole adelic group, without assuming irreducibility or cuspidality. -/
def GeneralLinearQuotientFormClassClosureStatement : Prop :=
  ∀ [CompactSpace (AdeleQuotient F)] (R : OperatorRealization F n)
    (j : R.Space →ₗ[ℂ] E), (∀ f, IsGeneralLinearFormClass F r T i (j f) (R.toContinuous f)) →
    ∀ x (v : E), v ∈ (LinearMap.range j).topologicalClosure →
      ρ x v ∈ (LinearMap.range j).topologicalClosure

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
/-- Annihilators of the class image vanish on every archimedean translate by analytic
continuation, since their jointly finite coefficients have zero jets at compact elements. -/
theorem generalLinearQuotientFormClassClosure :
    GeneralLinearQuotientFormClassClosureStatement F r T i hi I e hc := by
  intro _ R j hj
  let W := (LinearMap.range j).topologicalClosure
  have hK := generalLinear_formClass_compactRepresentation F r T i hi I e hc R j hj
  have hFin := generalLinear_formClass_finiteRepresentation F r T i hi I e hc R j hj
  have hArch (g : InfiniteAdelicGL F n) (f : R.Space) : ρ (b∞ g) (j f) ∈ W := by
    apply Langlands.Analysis.mem_topologicalClosure_of_forall_complex_annihilator
    intro ℓ hℓ
    obtain ⟨C, hC, hD⟩ := generalLinearQuotientOrbitCoefficients F r T i hi I e hc R j hj ℓ
    have hCk (k : standardInfiniteCompact F n) (v : R.Space) :
        C (R.compactRepresentation k v) = ArchimedeanGL.smoothRightAction F n k.val (C v) := by
      apply Subtype.ext
      funext a
      change (C (R.compactRepresentation k v)).val a = (C v).val (a * k.val)
      rw [hC, hC, hK]
      have hmul : (b∞ (a * k.val)) = (b∞ a) * (b∞ k.val) := by
        change (m).symm (AdelicGL.ofInfinite F n (a * k.val)) = _
        rw [map_mul, map_mul]
      rw [hmul, map_mul]
      rfl
    have hJ := coeff_isJointFinite F r R C hD hCk f
    have han := ArchimedeanGL.jointFiniteAnalyticity F n (C f) hJ
    obtain ⟨k, hgk⟩ := ArchimedeanGL.compactComponentCoverage F n g
    have hvanish (D : ArchimedeanGL.EnvelopingAlgebra F n) :
        (ArchimedeanGL.envelopingAction F n D (C f)).val k.val = 0 := by
      rw [hD, hC, ← hK]
      exact hℓ _ ⟨R.compactRepresentation k (R.envelopingAction D f), rfl⟩
    have hjet := ArchimedeanGL.envelopingZeroJet F n (C f) k.val hvanish
    exact (hC f g).symm.trans (ArchimedeanGL.analyticMatrixJetUniqueness F n (C f) k.val han hjet g hgk)
  have extend (a : AdelicGroupPoints F GLs) (ha : ∀ f, ρ a (j f) ∈ W) (v : E) (hv : v ∈ W) :
      ρ a v ∈ W := by
    have hsub : (LinearMap.range j : Set E) ⊆ (ρ a) ⁻¹' (W : Set E) := by
      rintro _ ⟨f, rfl⟩
      exact ha f
    exact closure_minimal hsub ((LinearMap.range j).isClosed_topologicalClosure.preimage
      (ρ a).continuous) hv
  intro x v hv
  let a := AdelicGL.infinite F n (m x)
  let d := AdelicGL.finite F n (m x)
  have hx : x = (b∞ a) * (b_f d) := by
    apply (m).injective
    rw [map_mul]
    change m x = m ((m).symm (AdelicGL.ofInfinite F n a)) *
      m ((m).symm (AdelicGL.ofFinite F n d))
    rw [(m).apply_symm_apply, (m).apply_symm_apply]
    exact AdelicGL.eq_ofInfinite_mul_ofFinite F n (m x)
  have hvf : ρ (b_f d) v ∈ W := extend _ (fun f => by
    rw [← hFin]
    exact (LinearMap.range j).le_topologicalClosure ⟨R.finiteRepresentation d f, rfl⟩) v hv
  rw [hx, map_mul]
  exact extend _ (hArch a) _ hvf

end Langlands.Automorphic.GroupSchemeFunctions
