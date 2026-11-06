import Langlands.Representation.Plancherel.RationalNormalizedInducedSpecializationStatement
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Induction.UnramifiedCompactStabilizer
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section

open scoped TensorProduct NNReal

namespace Langlands.Plancherel.SpecializationProof

universe uB uG uV

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {H : Type uG} [Group H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

local instance tensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (B ⊗[ℂ] E) := TensorProduct.addCommGroup

section Coefficients

variable (ρ : Representation B H (B ⊗[ℂ] V)) (τ : Representation ℂ H V)
  (J : Subgroup H)
  (hl : ∀ q : J, ρ q = (τ q).baseChange B)

include hl in
private theorem tensor_fixed_mem (w : B ⊗[ℂ] fixedVectors τ J) :
    (fixedVectors τ J).subtype.baseChange B w ∈ fixedVectors ρ J := by
  intro q
  induction w using TensorProduct.inductionOn with
  | tmul b v =>
      change ρ q (b ⊗ₜ[ℂ] v.val) = b ⊗ₜ[ℂ] v.val
      rw [hl q]
      change b ⊗ₜ[ℂ] τ q v.val = _
      exact congrArg (fun z => b ⊗ₜ[ℂ] z) (v.property q)
  | add w z hw hz =>
      simp only [map_add, hw, hz]

private def fixedTensorMap :
    B ⊗[ℂ] fixedVectors τ J →ₗ[B] fixedVectors ρ J :=
  ((fixedVectors τ J).subtype.baseChange B).codRestrict _ (tensor_fixed_mem ρ τ J hl)

private theorem coord_baseChange {ι : Type*} [DecidableEq ι] (e : Module.Basis ι ℂ B)
    (A : V →ₗ[ℂ] V) (w : B ⊗[ℂ] V) (i : ι) :
    TensorProduct.equivFinsuppOfBasisLeft e (A.baseChange B w) i =
      A (TensorProduct.equivFinsuppOfBasisLeft e w i) := by
  classical
  induction w using TensorProduct.inductionOn with
  | tmul b v => simp
  | add w z hw hz => simp only [map_add, Finsupp.add_apply, hw, hz]

private theorem fixedTensorMap_bijective :
    Function.Bijective (fixedTensorMap ρ τ J hl) := by
  classical
  constructor
  · obtain ⟨C, hC⟩ := Submodule.exists_isCompl (fixedVectors τ J)
    let p := Submodule.projectionOnto (fixedVectors τ J) C hC
    have hp : p ∘ₗ (fixedVectors τ J).subtype = LinearMap.id := by
      ext v
      simp [p]
    intro w z hwz
    have hh := congrArg (fun w : fixedVectors ρ J => p.baseChange B w.val) hwz
    change (p.baseChange B) ((fixedVectors τ J).subtype.baseChange B w) =
      (p.baseChange B) ((fixedVectors τ J).subtype.baseChange B z) at hh
    simpa only [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hp,
      LinearMap.baseChange_id, LinearMap.id_apply] using hh
  · intro w
    let e := Module.Free.chooseBasis ℂ B
    let c := TensorProduct.equivFinsuppOfBasisLeft e w.val
    have hc : ∀ i, c i ∈ fixedVectors τ J := by
      intro i q
      have heq : (τ q).baseChange B w.val = w.val := by
        rw [← hl q]
        exact w.property q
      change τ q (TensorProduct.equivFinsuppOfBasisLeft e w.val i) =
        TensorProduct.equivFinsuppOfBasisLeft e w.val i
      rw [← coord_baseChange e (τ q) w.val i, heq]
    refine ⟨∑ i ∈ c.support, e i ⊗ₜ[ℂ] (⟨c i, hc i⟩ : fixedVectors τ J), ?_⟩
    apply Subtype.ext
    change (fixedVectors τ J).subtype.baseChange B
      (∑ i ∈ c.support, e i ⊗ₜ[ℂ] (⟨c i, hc i⟩ : fixedVectors τ J)) = w.val
    simp only [map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply]
    simpa only [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum] using
      (TensorProduct.equivFinsuppOfBasisLeft e).symm_apply_apply w.val

section Fiber

variable [Algebra B ℂ] [IsScalarTower ℂ B ℂ]
  (T : B ⊗[ℂ] V →ₛₗ[algebraMap B ℂ] V)
  (hT : ∀ b v, T (b ⊗ₜ[ℂ] v) = algebraMap B ℂ b • v)
  (hcov : ∀ q w, T (ρ q w) = τ q (T w))

private def fixedCoefficientEvaluation :
    fixedVectors ρ J →ₛₗ[algebraMap B ℂ] fixedVectors τ J where
  toFun w := ⟨T w.val, fun q => by
    change τ q (T w.val) = T w.val
    rw [← hcov]
    exact congrArg T (w.property q)⟩
  map_add' w z := Subtype.ext (T.map_add w.val z.val)
  map_smul' b w := Subtype.ext (T.map_smulₛₗ b w.val)

include hl hT in
private theorem fixedCoefficientFiber_bijective :
    Function.Bijective
      (scalarExtensionOfSemilinear (fixedCoefficientEvaluation ρ τ J T hcov)) := by
  let e := LinearEquiv.ofBijective (fixedTensorMap ρ τ J hl)
    (fixedTensorMap_bijective ρ τ J hl)
  let c := (TensorProduct.AlgebraTensorModule.cancelBaseChange
    ℂ B ℂ ℂ (fixedVectors τ J)).trans (TensorProduct.lid ℂ (fixedVectors τ J))
  have he : Function.Bijective ((fixedTensorMap ρ τ J hl).baseChange ℂ) :=
    (e.baseChange B ℂ).bijective
  have hc : (scalarExtensionOfSemilinear (fixedCoefficientEvaluation ρ τ J T hcov)).comp
      ((fixedTensorMap ρ τ J hl).baseChange ℂ) = c.toLinearMap := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul z w =>
        induction w using TensorProduct.inductionOn with
        | tmul b v =>
            apply Subtype.ext
            change z • T (b ⊗ₜ[ℂ] v.val) = (b • z) • v.val
            rw [hT, Algebra.smul_def, mul_smul]
            exact smul_comm _ _ _
        | add w v hw hv =>
            simpa only [TensorProduct.tmul_add, map_add] using
              congrArg₂ (fun a b => a + b) hw hv
    | add w v hw hv =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hw hv
  exact (Function.Bijective.of_comp_iff _ he).mp (by
    change Function.Bijective
      ((scalarExtensionOfSemilinear (fixedCoefficientEvaluation ρ τ J T hcov)).comp
        ((fixedTensorMap ρ τ J hl).baseChange ℂ))
    rw [hc]
    exact c.bijective)

end Fiber

end Coefficients

section Induced

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]
  [Algebra B ℂ] [IsScalarTower ℂ B ℂ]
  (P : Subgroup G)
  (ρ : Representation B P (B ⊗[ℂ] V)) (τ : Representation ℂ P V)
  (T : B ⊗[ℂ] V →ₛₗ[algebraMap B ℂ] V)
  (hT : ∀ b v, T (b ⊗ₜ[ℂ] v) = algebraMap B ℂ b • v)
  (hcov : ∀ q w, T (ρ q w) = τ q (T w))
  (E : SmoothFunctions P ρ →ₛₗ[algebraMap B ℂ] SmoothFunctions P τ)
  (hE : ∀ f x, eval P τ (E f) x = T (eval P ρ f x))
  (hEquiv : ∀ g f, E (smoothInduced P ρ g f) = smoothInduced P τ g (E f))

private def fixedInducedEvaluation (K : OpenSubgroup G) :
    fixedVectors (smoothInduced P ρ) K.toSubgroup →ₛₗ[algebraMap B ℂ]
      fixedVectors (smoothInduced P τ) K.toSubgroup where
  toFun f := ⟨E f.val, fun k => by
    change smoothInduced P τ k (E f.val) = E f.val
    rw [← hEquiv]
    exact congrArg E (f.property k)⟩
  map_add' f g := Subtype.ext (E.map_add f.val g.val)
  map_smul' b f := Subtype.ext (E.map_smulₛₗ b f.val)

include hT hE hcov in
private theorem fixedInducedFiber_bijective [CompactSpace (LeftQuotient P)]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hl : ∀ x (q : (conjOpenSubgroup P K x).toSubgroup),
      ρ q = (τ q).baseChange B) :
    Function.Bijective
      (scalarExtensionOfSemilinear (fixedInducedEvaluation P ρ τ E hEquiv K)) := by
  classical
  obtain ⟨t, hcover, hdistinct⟩ := exists_finset_doubleCoset_representatives P K
  let eB := fixedEvaluationEquiv P ρ K hK t hcover hdistinct
  let eC := fixedEvaluationEquiv P τ K hK t hcover hdistinct
  let c := fun i : t => scalarExtensionOfSemilinear
    (fixedCoefficientEvaluation ρ τ (conjOpenSubgroup P K i).toSubgroup T hcov)
  have hc : ∀ i, Function.Bijective (c i) := fun i =>
    fixedCoefficientFiber_bijective ρ τ _ (hl i) T hT hcov
  let ep := LinearEquiv.piCongrRight (fun i => LinearEquiv.ofBijective (c i) (hc i))
  let e := ((eB.baseChange B ℂ).trans
    (TensorProduct.piRight B ℂ ℂ
      (fun i : t => fixedVectors ρ (conjOpenSubgroup P K i).toSubgroup))).trans ep
  let L := scalarExtensionOfSemilinear (fixedInducedEvaluation P ρ τ E hEquiv K)
  have he : eC.toLinearMap.comp L = e.toLinearMap := by
    apply LinearMap.ext
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul z f =>
        funext i
        apply Subtype.ext
        change z • eval P τ (E f.val) i = z • T (eval P ρ f.val i)
        rw [hE]
    | add w v hw hv =>
        simpa only [map_add] using congrArg₂ (fun a b => a + b) hw hv
  exact (Function.Bijective.of_comp_iff' eC.bijective L).mp (by
    change Function.Bijective (eC.toLinearMap.comp L)
    rw [he]
    exact e.bijective)

omit [IsScalarTower ℂ B ℂ] in
private theorem fixedRange_mono (K L : OpenSubgroup G) (hKL : K ≤ L) :
    LinearMap.range ((fixedVectors (smoothInduced P ρ) L.toSubgroup).subtype.baseChange ℂ) ≤
      LinearMap.range ((fixedVectors (smoothInduced P ρ) K.toSubgroup).subtype.baseChange ℂ) := by
  have hle : fixedVectors (smoothInduced P ρ) L.toSubgroup ≤
      fixedVectors (smoothInduced P ρ) K.toSubgroup :=
    fun _ hf k => hf ⟨k.val, hKL k.property⟩
  have he : (fixedVectors (smoothInduced P ρ) L.toSubgroup).subtype.baseChange ℂ =
      ((fixedVectors (smoothInduced P ρ) K.toSubgroup).subtype.baseChange ℂ).comp
        ((Submodule.inclusion hle).baseChange ℂ) := by
    rw [← LinearMap.baseChange_comp]
    rfl
  rw [he]
  exact LinearMap.range_comp_le_range _ _

omit [IsScalarTower ℂ B ℂ] in
private theorem exists_tensor_compact_level [LocallyCompactSpace G]
    (w : ℂ ⊗[B] SmoothFunctions P ρ) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧
      w ∈ LinearMap.range ((fixedVectors (smoothInduced P ρ) K.toSubgroup).subtype.baseChange ℂ) := by
  induction w using TensorProduct.inductionOn with
  | tmul z f =>
      obtain ⟨L, hL⟩ := smoothInduced_smooth P ρ f
      obtain ⟨K, hK, hKL⟩ := Langlands.compactOpenSubgroupBasis G
        (L : Set G) (L.isOpen.mem_nhds L.one_mem)
      refine ⟨K, hK, z ⊗ₜ[B] (⟨f, ?_⟩ : fixedVectors (smoothInduced P ρ) K.toSubgroup), rfl⟩
      exact fun k => hL ⟨k.val, hKL k.property⟩
  | add w v hw hv =>
      obtain ⟨K, hK, hw⟩ := hw
      obtain ⟨L, _, hv⟩ := hv
      refine ⟨K ⊓ L, hK.of_isClosed_subset (K ⊓ L).isClosed
        (fun _ h => h.1), add_mem ?_ ?_⟩
      · exact fixedRange_mono P ρ (K ⊓ L) K inf_le_left hw
      · exact fixedRange_mono P ρ (K ⊓ L) L inf_le_right hv

omit [IsScalarTower ℂ B ℂ] in
private theorem fixedInducedFiber_comm (K : OpenSubgroup G) :
    (fixedVectors (smoothInduced P τ) K.toSubgroup).subtype.comp
        (scalarExtensionOfSemilinear (fixedInducedEvaluation P ρ τ E hEquiv K)) =
      (scalarExtensionOfSemilinear E).comp
        ((fixedVectors (smoothInduced P ρ) K.toSubgroup).subtype.baseChange ℂ) := by
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul z f => rfl
  | add w v hw hv =>
      simpa only [map_add] using congrArg₂ (fun a b => a + b) hw hv

include hT hcov hE hEquiv in
private theorem inducedFiber_bijective [CompactSpace (LeftQuotient P)]
    [LocallyCompactSpace G]
    (hl : ∀ (K : OpenSubgroup G), IsCompact (K : Set G) →
      ∀ x (q : (conjOpenSubgroup P K x).toSubgroup), ρ q = (τ q).baseChange B) :
    Function.Bijective (scalarExtensionOfSemilinear E) := by
  have hb := fun K hK =>
    fixedInducedFiber_bijective P ρ τ T hT hcov E hE hEquiv K hK (hl K hK)
  constructor
  · apply (injective_iff_map_eq_zero (scalarExtensionOfSemilinear E)).mpr
    intro w hw
    obtain ⟨K, hK, v, rfl⟩ := exists_tensor_compact_level P ρ w
    have hv : scalarExtensionOfSemilinear (fixedInducedEvaluation P ρ τ E hEquiv K) v = 0 := by
      apply Subtype.ext
      exact (LinearMap.congr_fun (fixedInducedFiber_comm P ρ τ E hEquiv K) v).trans hw
    rw [(hb K hK).injective (hv.trans (map_zero _).symm), map_zero]
  · intro f
    obtain ⟨L, hL⟩ := smoothInduced_smooth P τ f
    obtain ⟨K, hK, hKL⟩ := Langlands.compactOpenSubgroupBasis G
      (L : Set G) (L.isOpen.mem_nhds L.one_mem)
    let fk : fixedVectors (smoothInduced P τ) K.toSubgroup :=
      ⟨f, fun k => hL ⟨k.val, hKL k.property⟩⟩
    obtain ⟨v, hv⟩ := (hb K hK).surjective fk
    refine ⟨(fixedVectors (smoothInduced P ρ) K.toSubgroup).subtype.baseChange ℂ v, ?_⟩
    exact (LinearMap.congr_fun (fixedInducedFiber_comm P ρ τ E hEquiv K) v).symm.trans
      (congrArg Subtype.val hv)

end Induced

section Parabolic

open Induction UnramifiedNormalized

universe uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G} {I : Type uI}
  (ν : I → (M →* ℝ≥0ˣ))
  (h : Aubert.General.IsSemidirectDecomposition P M U)
  (hU : IsClosed (U : Set G))
  (σ : Representation ℂ M V) (χ : unramifiedCharacters ν)

private theorem compact_inducing_baseChange (hP : IsClosed (P : Set G))
    (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : G)
    (q : (conjOpenSubgroup P K x).toSubgroup) :
    universalInducingRepresentation ν h hU σ q =
      (complexInducingRepresentation ν h hU σ χ q).baseChange
        (unramifiedRegularFunctions ν) := by
  have ht : ∀ ξ : unramifiedCharacters ν, ξ.val (h.projection q.val) = 1 :=
    fun ξ => unramifiedPullback_eq_one_of_mem_conjOpenSubgroup
      P hP ν hν h.projection hr ξ K hK x q.property
  have hreg : unramifiedEvaluationRegular ν (h.projection q.val) = 1 := by
    apply Subtype.ext
    funext ξ
    change (ξ.val (h.projection q.val) : ℂ) = 1
    rw [ht ξ]
    rfl
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.inductionOn with
  | tmul b v =>
      change (algebraMap ℂ (unramifiedRegularFunctions ν)
          (HaarModulus.closedHalfCharacter U hU P h.le_normalizer q.val : ℂ)) •
          ((unramifiedEvaluationRegular ν (h.projection q.val) * b) ⊗ₜ[ℂ]
            σ (h.projection q.val) v) =
        b ⊗ₜ[ℂ] ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q.val : ℂ) •
          ((χ.val (h.projection q.val) : ℂ) • σ (h.projection q.val) v))
      rw [hreg, one_mul, ht χ]
      simp only [Units.val_one, one_smul, IsScalarTower.algebraMap_smul,
        TensorProduct.tmul_smul]
  | add w v hw hv =>
      simp only [map_add, hw, hv]

private theorem parabolic_inducedFiber_bijective
    (hP : IsClosed (P : Set G)) (hν : ∀ i, Continuous (ν i))
    (hr : Continuous h.projection) [CompactSpace (LeftQuotient P)] :
    letI : Algebra (unramifiedRegularFunctions ν) ℂ := (evaluation ν χ).toAlgebra
    Function.Bijective
      (scalarExtensionOfSemilinear (UnramifiedNormalized.inducedEvaluation ν h hU σ χ)) := by
  let : Algebra (unramifiedRegularFunctions ν) ℂ := (evaluation ν χ).toAlgebra
  let : IsScalarTower ℂ (unramifiedRegularFunctions ν) ℂ :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact inducedFiber_bijective P (universalInducingRepresentation ν h hU σ)
    (complexInducingRepresentation ν h hU σ χ) (tensorEvaluation ν V χ)
    (fun _ _ => rfl) (inducingEvaluation_action ν h hU σ χ)
    (UnramifiedNormalized.inducedEvaluation ν h hU σ χ) (fun _ _ => rfl)
    (UnramifiedNormalized.inducedEvaluation_action ν h hU σ χ)
    (fun K hK x q => compact_inducing_baseChange ν h hU σ χ hP hν hr K hK x q)

end Parabolic

end Langlands.Plancherel.SpecializationProof

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalNormalized

universe u uCarrier

/-- Canonical specialization of full actual rational normalized induction. -/
theorem rationalNormalizedInducedSpecialization :
    RationalNormalizedInducedSpecializationStatement.{u, uCarrier} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  intro _ _ M P U _ A p l a r n h hU hr hQ π χ
  let : CompactSpace (Induction.LeftQuotient (ParabolicPoints p)) := hQ
  have hP : IsClosed (ParabolicPoints p : Set (rationalPoints G)) := by
    let : T2Space F := Langlands.BruhatTits.localField_t2Space F
    have hp : IsClosedSubgroup p := r.isCompatible.parabolic.isClosedSubgroup
    have : IsClosedImmersion p.hom.hom.left := hp
    have hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
      ⟨Over.mono_of_mono_left _, rfl⟩
    exact isClosed_rationalPoint_subgroup F (SubgroupFunctor.range p) p hrep hp
  exact SpecializationProof.parabolic_inducedFiber_bijective
    (parabolicLeviRationalNormCharacters r) h hU π.representation χ hP
    (continuous_parabolicLeviRationalNormCharacters r) hr

end Langlands.Plancherel.RationalNormalized
