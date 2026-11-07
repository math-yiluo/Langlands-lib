import Langlands.Representation.CuspidalSupport.RationalUniversalProgeneratorComparisonStatement
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-! The actual full-restriction compact-induction comparison of VI.4.1. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.CuspidalSupport

namespace UniversalComparison

universe uR uG uL uV

variable {R : Type uR} [CommRing R]
  {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {L : Type uL} [CommGroup L] [TopologicalSpace L] [DiscreteTopology L]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (p : H →* L) (hp : Function.Surjective p)
  (hopen : IsOpen (p.ker : Set H))
  (ρ : Representation R H V) (hρ : IsSmooth ρ)

abbrev C := Induction.CompactFunctions p.ker (ρ.comp p.ker.subtype)

def sectionValue (a : L) (v : V) (x : H) : V :=
  by
    classical
    exact if p x = a⁻¹ then ρ x v else 0

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace L]
  [DiscreteTopology L] in
theorem sectionValue_covariant (a : L) (v : V) (k : p.ker) (x : H) :
    sectionValue p ρ a v ((k : H) * x) =
      ρ (k : H) (sectionValue p ρ a v x) := by
  classical
  have hk : p (k : H) = 1 := k.property
  simp only [sectionValue, map_mul, hk, one_mul, Module.End.mul_apply]
  split_ifs <;> simp

include hp in
omit [IsTopologicalGroup H] [TopologicalSpace L] [DiscreteTopology L] in
theorem sectionValue_compactSupport (a : L) (v : V) :
    IsCompact (Induction.quotientSupport p.ker (sectionValue p ρ a v)) := by
  classical
  obtain ⟨y, hy⟩ := hp a⁻¹
  apply Set.Finite.isCompact
  apply (Set.finite_singleton (Induction.quotientMap p.ker y)).subset
  rintro _ ⟨x, hx, rfl⟩
  have hx' : p x = a⁻¹ := by
    by_contra hn
    exact hx (by simp [sectionValue, hn])
  apply Set.mem_singleton_iff.mpr
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  change p (y * x⁻¹) = 1
  simp [hy, hx']

def compactSection (a : L) (v : V) : C p ρ := by
  classical
  let K := Classical.choose (hρ v)
  have hK := Classical.choose_spec (hρ v)
  let N : OpenSubgroup H := ⟨p.ker, hopen⟩
  refine Induction.compactFunctionOf p.ker (ρ.comp p.ker.subtype)
    (sectionValue p ρ a v) (sectionValue_covariant p ρ a v)
    (N ⊓ K) ?_ (sectionValue_compactSupport p hp ρ a v)
  intro k x
  have hk : p (k : H) = 1 := k.property.1
  have hkv : ρ (k : H) v = v := hK ⟨(k : H), k.property.2⟩
  simp only [sectionValue, map_mul, hk, mul_one, Module.End.mul_apply, hkv]

omit [TopologicalSpace L] [DiscreteTopology L] in
@[simp]
theorem section_apply (a : L) (v : V) (x : H) :
    Induction.eval p.ker (ρ.comp p.ker.subtype)
      (compactSection p hp hopen ρ hρ a v).val x = sectionValue p ρ a v x := by
  rfl

def sectionLinear (a : L) : V →ₗ[R] C p ρ where
  toFun := compactSection p hp hopen ρ hρ a
  map_add' v w := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change sectionValue p ρ a (v + w) x =
      sectionValue p ρ a v x + sectionValue p ρ a w x
    simp only [sectionValue]
    split_ifs <;> simp
  map_smul' c v := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change sectionValue p ρ a (c • v) x = c • sectionValue p ρ a v x
    simp only [sectionValue]
    split_ifs <;> simp

def fromFinsupp : (L →₀ V) →ₗ[R] C p ρ :=
  Finsupp.lsum R (sectionLinear p hp hopen ρ hρ)

omit [TopologicalSpace L] [DiscreteTopology L] in
theorem fromFinsupp_apply (s : L →₀ V) (x : H) :
    Induction.eval p.ker (ρ.comp p.ker.subtype)
      (fromFinsupp p hp hopen ρ hρ s).val x = ρ x (s (p x)⁻¹) := by
  classical
  induction s using Finsupp.induction_linear with
  | zero => simp [fromFinsupp, Induction.eval]
  | add s t hs ht =>
      change Induction.eval _ _ ((fromFinsupp p hp hopen ρ hρ) (s + t)).val x = _
      rw [map_add]
      change Induction.eval _ _ (fromFinsupp p hp hopen ρ hρ s).val x +
        Induction.eval _ _ (fromFinsupp p hp hopen ρ hρ t).val x = _
      rw [hs, ht]
      simp
  | single a v =>
      rw [fromFinsupp, Finsupp.lsum_single]
      change sectionValue p ρ a v x = _
      by_cases hx : p x = a⁻¹
      · simp [sectionValue, hx]
      · have hx' : a ≠ (p x)⁻¹ := by
          intro he
          apply hx
          rw [he, inv_inv]
        simp [sectionValue, hx, Finsupp.single_eq_of_ne' hx']

def quotientIndex : Induction.LeftQuotient p.ker → L :=
  Quotient.lift (fun x => (p x)⁻¹) (by
    intro x y hxy
    have h : p (y * x⁻¹) = 1 := QuotientGroup.rightRel_apply.mp hxy
    have he : p y = p x := by
      simpa [map_mul, map_inv, mul_inv_eq_one] using h
    rw [he])

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace L]
  [DiscreteTopology L] in
@[simp]
theorem quotientIndex_mk (x : H) :
    quotientIndex p (Induction.quotientMap p.ker x) = (p x)⁻¹ := rfl

omit [IsTopologicalGroup H] in
theorem continuous_quotientIndex (hc : Continuous p) :
    Continuous (quotientIndex p) :=
  hc.inv.quotient_lift _

def representative (a : L) : H := Classical.choose (hp a⁻¹)

omit [TopologicalSpace H] [IsTopologicalGroup H] [TopologicalSpace L]
  [DiscreteTopology L] in
@[simp]
theorem representative_projection (a : L) :
    p (representative p hp a) = a⁻¹ :=
  Classical.choose_spec (hp a⁻¹)

omit [TopologicalSpace L] [DiscreteTopology L] in
theorem normalizedEval_eq (f : C p ρ) (x y : H) (hxy : p x = p y) :
    ρ x⁻¹ (Induction.eval _ _ f.val x) =
      ρ y⁻¹ (Induction.eval _ _ f.val y) := by
  have hk : y * x⁻¹ ∈ p.ker := by
    change p (y * x⁻¹) = 1
    simp [map_mul, hxy]
  have hf : Induction.eval _ _ f.val y =
      ρ (y * x⁻¹) (Induction.eval _ _ f.val x) := by
    simpa [mul_assoc, Induction.eval] using f.val.val.property ⟨y * x⁻¹, hk⟩ x
  rw [hf, ← Module.End.mul_apply, ← map_mul]
  simp

def coefficient (f : C p ρ) (a : L) : V :=
  ρ (representative p hp a)⁻¹
    (Induction.eval _ _ f.val (representative p hp a))

theorem coefficient_support_finite (hc : Continuous p) (f : C p ρ) :
    (Function.support (coefficient p hp ρ f)).Finite := by
  apply ((f.property.image (continuous_quotientIndex p hc)).finite_of_discrete).subset
  intro a ha
  refine ⟨Induction.quotientMap p.ker (representative p hp a), ?_, ?_⟩
  · refine ⟨representative p hp a, ?_, rfl⟩
    intro hz
    exact ha (by simp [coefficient, hz])
  · change (p (representative p hp a))⁻¹ = a
    simp

def toFinsupp (hc : Continuous p) (f : C p ρ) : L →₀ V :=
  Finsupp.ofSupportFinite (coefficient p hp ρ f)
    (coefficient_support_finite p hp ρ hc f)

@[simp]
theorem toFinsupp_apply (hc : Continuous p) (f : C p ρ) (a : L) :
    toFinsupp p hp ρ hc f a = coefficient p hp ρ f a := rfl

include hp hopen hρ in
omit [TopologicalSpace L] [DiscreteTopology L] in
theorem fromFinsupp_injective :
    Function.Injective (fromFinsupp p hp hopen ρ hρ) := by
  intro s t hst
  ext a
  have he := congrArg
    (fun f : C p ρ => Induction.eval _ _ f.val (representative p hp a)) hst
  simp only [fromFinsupp_apply, representative_projection, inv_inv] at he
  have he' := congrArg (ρ (representative p hp a)⁻¹) he
  simpa [← Module.End.mul_apply, ← map_mul] using he'

theorem fromFinsupp_toFinsupp (hc : Continuous p) (f : C p ρ) :
    fromFinsupp p hp hopen ρ hρ (toFinsupp p hp ρ hc f) = f := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change Induction.eval _ _
    (fromFinsupp p hp hopen ρ hρ (toFinsupp p hp ρ hc f)).val x = _
  rw [fromFinsupp_apply, toFinsupp_apply, coefficient]
  have he := normalizedEval_eq p ρ f x (representative p hp (p x)⁻¹) (by simp)
  rw [← he, ← Module.End.mul_apply, ← map_mul]
  simp [Induction.eval]

def finsuppEquiv (hc : Continuous p) : (L →₀ V) ≃ₗ[R] C p ρ :=
  LinearEquiv.ofBijective (fromFinsupp p hp hopen ρ hρ)
    ⟨fromFinsupp_injective p hp hopen ρ hρ,
      fun f => ⟨toFinsupp p hp ρ hc f, fromFinsupp_toFinsupp p hp hopen ρ hρ hc f⟩⟩

def indexEquiv : Additive L ≃ L :=
  ⟨Additive.toMul, Additive.ofMul, fun _ => rfl, fun _ => rfl⟩

def groupAlgebraEquiv (hc : Continuous p) :
    (AddMonoidAlgebra R (Additive L) ⊗[R] V) ≃ₗ[R] C p ρ := by
  classical
  exact (TensorProduct.congr (AddMonoidAlgebra.coeffLinearEquiv R) (LinearEquiv.refl R V)).trans
    ((TensorProduct.finsuppScalarLeft R V (Additive L)).trans
      ((Finsupp.domLCongr indexEquiv).trans (finsuppEquiv p hp hopen ρ hρ hc)))

theorem groupAlgebraEquiv_single (hc : Continuous p) (a : L) (v : V) :
    groupAlgebraEquiv p hp hopen ρ hρ hc
      (AddMonoidAlgebra.single (Additive.ofMul a) 1 ⊗ₜ[R] v) =
        compactSection p hp hopen ρ hρ a v := by
  classical
  have ht : TensorProduct.finsuppScalarLeft R V (Additive L)
      (Finsupp.single (Additive.ofMul a) 1 ⊗ₜ[R] v) =
        Finsupp.single (Additive.ofMul a) v := by
    apply (TensorProduct.finsuppScalarLeft R V (Additive L)).symm.injective
    simp
  simp only [groupAlgebraEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul]
  change fromFinsupp p hp hopen ρ hρ
    ((Finsupp.domLCongr indexEquiv)
      (TensorProduct.finsuppScalarLeft R V (Additive L)
        (Finsupp.single (Additive.ofMul a) 1 ⊗ₜ[R] v))) = _
  rw [ht, Finsupp.domLCongr_single]
  rw [fromFinsupp, Finsupp.lsum_single]
  rfl

omit [TopologicalSpace L] [DiscreteTopology L] in
theorem compactSection_action (g : H) (a : L) (v : V) :
    Induction.compactInduced p.ker (ρ.comp p.ker.subtype) g
      (compactSection p hp hopen ρ hρ a v) =
        compactSection p hp hopen ρ hρ (p g * a) (ρ g v) := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change sectionValue p ρ a v (x * g) = sectionValue p ρ (p g * a) (ρ g v) x
  have he : p (x * g) = a⁻¹ ↔ p x = (p g * a)⁻¹ := by
    rw [map_mul, mul_inv_rev, ← eq_mul_inv_iff_mul_eq]
  simp only [sectionValue, he]
  split_ifs <;> simp [map_mul]

end UniversalComparison

open Plancherel

universe uF uV

section Rational

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalUniversalProgeneratorComparisonProofPointTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance rationalUniversalProgeneratorComparisonProofTopologicalGroup : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

theorem isOpen_rationalImageProjectionKernel :
    IsOpen ((rationalValuationImageProjection G).ker :
      Set (GroupScheme.rationalPoints G)) := by
  simpa only [rationalValuationImageProjection_ker] using isOpen_rationalCommonNormKernel G

def rationalUniversalTensorToImageCompactLinearEquiv
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    RationalUniversalTensor G π ≃ₗ[ℂ]
      UniversalComparison.C (rationalValuationImageProjection G) π.representation :=
  (TensorProduct.congr
    (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G).symm.toLinearEquiv
    (LinearEquiv.refl ℂ π)).trans
      (UniversalComparison.groupAlgebraEquiv (rationalValuationImageProjection G)
        (rationalValuationImageProjection_surjective G)
        (isOpen_rationalImageProjectionKernel G) π.representation π.isSmooth
        (continuous_rationalValuationImageProjection G))

theorem rationalUniversalTensorToImageCompactLinearEquiv_single
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (a : Additive (rationalDiscreteValuationImage G)) (v : π) :
    rationalUniversalTensorToImageCompactLinearEquiv G π
      (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
        (AddMonoidAlgebra.single a 1) ⊗ₜ[ℂ] v) =
      UniversalComparison.compactSection (rationalValuationImageProjection G)
        (rationalValuationImageProjection_surjective G)
        (isOpen_rationalImageProjectionKernel G) π.representation π.isSmooth a.toMul v := by
  simp only [rationalUniversalTensorToImageCompactLinearEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, LinearEquiv.refl_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.symm_apply_apply]
  exact UniversalComparison.groupAlgebraEquiv_single _ _ _ _ _ _ a.toMul v

theorem rationalCoordinateAlgebraEquiv_projection
    (g : GroupScheme.rationalPoints G) :
    rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
      (AddMonoidAlgebra.single (Additive.ofMul (rationalValuationImageProjection G g)) 1) =
      unramifiedEvaluationRegular (fun χ => (rationalNormCharacters G χ).toMul) g := by
  apply Subtype.ext
  funext χ
  change rationalUnramifiedCoordinateEvaluation G
    (continuous_rationalValuationImageProjection G) _ χ = _
  simp [unramifiedEvaluationRegular, unramifiedEvaluation]

theorem rationalCoordinateAlgebraEquiv_mul_single
    (g : GroupScheme.rationalPoints G)
    (a : Additive (rationalDiscreteValuationImage G)) :
    unramifiedEvaluationRegular (fun χ => (rationalNormCharacters G χ).toMul) g *
        rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
          (AddMonoidAlgebra.single a 1) =
      rationalCanonicalUnramifiedCoordinateAlgebraEquiv G
        (AddMonoidAlgebra.single
          (Additive.ofMul (rationalValuationImageProjection G g) + a) 1) := by
  rw [← rationalCoordinateAlgebraEquiv_projection G g]
  exact (map_mul (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G)
    (AddMonoidAlgebra.single
      (Additive.ofMul (rationalValuationImageProjection G g)) 1)
    (AddMonoidAlgebra.single a 1)).symm.trans
      (congrArg (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G)
        (by simp only [AddMonoidAlgebra.single_mul_single, one_mul]))

set_option maxHeartbeats 800000 in
theorem rationalUniversalTensorToImageCompactLinearEquiv_intertwines
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))
    (g : GroupScheme.rationalPoints G) (t : RationalUniversalTensor G π) :
    rationalUniversalTensorToImageCompactLinearEquiv G π
      (rationalUniversalTensorRepresentation G π g t) =
    Induction.compactInduced (rationalValuationImageProjection G).ker
      (π.representation.comp (rationalValuationImageProjection G).ker.subtype) g
      (rationalUniversalTensorToImageCompactLinearEquiv G π t) := by
  classical
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul b v =>
      obtain ⟨b, rfl⟩ := (rationalCanonicalUnramifiedCoordinateAlgebraEquiv G).surjective b
      induction b using AddMonoidAlgebra.induction_on generalizing v with
      | of a =>
          simp only [AddMonoidAlgebra.of_apply, toAdd_ofAdd]
          rw [rationalUniversalTensorRepresentation_tmul,
            rationalCoordinateAlgebraEquiv_mul_single G g a]
          simp only [rationalUniversalTensorToImageCompactLinearEquiv_single]
          exact (UniversalComparison.compactSection_action _ _ _ _ _ g a.toMul v).symm
      | add b c hb hc =>
          simp only [map_add, TensorProduct.add_tmul, hb, hc]
      | smul c b hb =>
          simpa only [map_smul, TensorProduct.smul_tmul] using hb (c • v)

def rationalUniversalTensorImageCompactEquiv
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    (rationalUniversalTensorRepresentation G π).Equiv
      (Induction.compactInduced (rationalValuationImageProjection G).ker
        (π.representation.comp (rationalValuationImageProjection G).ker.subtype)) :=
  Representation.Equiv.mk (rationalUniversalTensorToImageCompactLinearEquiv G π) (by
    intro g
    apply LinearMap.ext
    intro t
    exact rationalUniversalTensorToImageCompactLinearEquiv_intertwines G π g t)

def rationalUniversalProgeneratorComparisonIso
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    rationalNormKernelCompactInduction G π ≅ rationalUniversalTensorSmoothRep G π := by
  apply SmoothRep.mkIso
  change (Induction.compactInduced (rationalCommonNormKernel G)
      (π.representation.comp (rationalCommonNormKernel G).subtype)).Equiv
    (rationalUniversalTensorRepresentation G π)
  rw [← rationalValuationImageProjection_ker G]
  exact (rationalUniversalTensorImageCompactEquiv G π).symm

theorem hasRationalUniversalProgeneratorComparison
    (π : SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :
    HasRationalUniversalProgeneratorComparison G π :=
  ⟨rationalUniversalProgeneratorComparisonIso G π⟩

end Rational

theorem rationalUniversalProgeneratorComparison :
    RationalUniversalProgeneratorComparisonStatement.{uF, uV} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  dsimp only
  intro _ _ _ ν hν hStandard hRoots hU π _ _
  exact hasRationalUniversalProgeneratorComparison G π

end Langlands.CuspidalSupport
