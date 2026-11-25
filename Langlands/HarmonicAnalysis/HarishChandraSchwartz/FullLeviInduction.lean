import Langlands.Representation.CompactCoefficient.GroupTransport
import Langlands.Representation.Aubert.General.RationalEndpoint
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalInducedCoefficients
import Langlands.Representation.Plancherel.CoefficientTensors

/-! # Evaluation and coefficient transport for induction from the whole group -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe uG uV u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General Langlands.Plancherel
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.HarishChandraSchwartz

section Generic

variable {Γ : Type uG} [Group Γ] [TopologicalSpace Γ]
  [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ]

/-- The actual identification of the ambient group with a full Levi subgroup. -/
def fullLeviGroupEquiv (M : Subgroup Γ) (hM : M = ⊤) : Γ ≃ₜ* M := by
  subst M
  exact
    { toMulEquiv :=
        { toFun := fun g => ⟨g, Subgroup.mem_top g⟩
          invFun := fun m => m.val
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_mul' := fun _ _ => rfl }
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }

omit [LocallyCompactSpace Γ] [NonarchimedeanGroup Γ] in
@[simp]
theorem coe_fullLeviGroupEquiv (M : Subgroup Γ) (hM : M = ⊤) (g : Γ) :
    (fullLeviGroupEquiv M hM g : Γ) = g := by
  subst M
  rfl

/-- A representation of a full Levi as a representation of the ambient group,
on exactly the original carrier universe. -/
def fullLeviAmbientSmoothRep (M : Subgroup Γ) (hM : M = ⊤)
    (A : SmoothRep.{0, uG, uV} ℂ M) : SmoothRep.{0, uG, uV} ℂ Γ :=
  SmoothRep.pullback (fullLeviGroupEquiv M hM) A

/-- The normalizing half-character is literally trivial when the radical is
trivial. This retains the actual Haar-modulus definition. -/
theorem fullLeviHalfCharacter_eq_one (U : Subgroup Γ)
    (hU : IsClosed (U : Set Γ)) (hbot : U = ⊥)
    (P : Subgroup Γ) (hPU : P ≤ Subgroup.normalizer (U : Set Γ)) (p : P) :
    HaarModulus.closedHalfCharacter U hU P hPU p = 1 := by
  have hchar (g : Subgroup.normalizer (U : Set Γ)) :
      HaarModulus.closedNormalizerCharacter U hU g = 1 := by
    let := hU.locallyCompactSpace
    let : MeasurableSpace U := borel U
    have : BorelSpace U := ⟨rfl⟩
    have : Subsingleton U := by rw [hbot]; infer_instance
    have he : HaarModulus.normalizerConj U g = ContinuousMulEquiv.refl U :=
      DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
    apply Units.ext
    change MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj U g) = 1
    rw [he]
    simp
  apply Units.ext
  change ((NNReal.sqrt
    (HaarModulus.closedNormalizerCharacter U hU ⟨p, hPU p.property⟩ : NNReal) : ℝ) : ℂ) = 1
  rw [hchar]
  simp

variable {P M U : Subgroup Γ}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set Γ))
  (hP : P = ⊤) (hM : M = ⊤) (hbot : U = ⊥)
  (A : SmoothRep.{0, uG, uV} ℂ M)

include hbot in
/-- At the full-group endpoint, normalized inflation is the ambient action. -/
theorem fullLeviInducingRepresentation_apply (p : P) :
    inducingRepresentation h hU A p =
      (fullLeviAmbientSmoothRep M hM A).representation (p : Γ) := by
  have hp : h.projection p = fullLeviGroupEquiv M hM (p : Γ) := by
    apply Subtype.ext
    exact inv_mul_eq_one.mp (by
      simpa only [hbot, Subgroup.mem_bot, coe_fullLeviGroupEquiv] using
        h.projection_inv_mul_mem p)
  ext v
  change (HaarModulus.closedHalfCharacter U hU P h.le_normalizer p : ℂˣ) •
    A.representation (h.projection p) v =
      A.representation (fullLeviGroupEquiv M hM (p : Γ)) v
  rw [fullLeviHalfCharacter_eq_one U hU hbot, one_smul, hp]

/-- Normalized induction from `P=M=Γ`, `U=1`, identified by evaluation at one.
The source has the usual `max uG uV` carrier and the target keeps `uV`. -/
def fullLeviInductionEquiv :
    ((normalizedInductionFunctor h hU).obj A).representation.Equiv
      (fullLeviAmbientSmoothRep M hM A).representation :=
  Induction.smoothInducedTopEquiv P hP (inducingRepresentation h hU A)
    (fullLeviAmbientSmoothRep M hM A).representation
    (fullLeviInducingRepresentation_apply h hU hM hbot A)
    (fullLeviAmbientSmoothRep M hM A).isSmooth

@[simp]
theorem fullLeviInductionEquiv_apply
    (f : (normalizedInductionFunctor h hU).obj A) :
    fullLeviInductionEquiv h hU hP hM hbot A f =
      Induction.eval P (inducingRepresentation h hU A) f 1 := rfl

@[simp]
theorem fullLeviInductionEquiv_symm_eval (v : A) (g : Γ) :
    Induction.eval P (inducingRepresentation h hU A)
      ((fullLeviInductionEquiv h hU hP hM hbot A).symm v) g =
        A.representation (fullLeviGroupEquiv M hM g) v := rfl

/-- Literal tensor transport from the normalized induced representation. -/
def fullLeviInductionTensorEquiv :
    CoefficientTensor ((normalizedInductionFunctor h hU).obj A) ≃ₗ[ℂ]
      CoefficientTensor (fullLeviAmbientSmoothRep M hM A) :=
  coefficientTensorCongr (fullLeviInductionEquiv h hU hP hM hbot A)

/-- Evaluation transport preserves each actual coefficient, without a scalar
or a change of measure. -/
theorem coefficientTensorMap_fullLeviInductionTensorEquiv
    (t : CoefficientTensor ((normalizedInductionFunctor h hU).obj A)) :
    coefficientTensorMap (fullLeviAmbientSmoothRep M hM A)
      (fullLeviInductionTensorEquiv h hU hP hM hbot A t) =
        coefficientTensorMap ((normalizedInductionFunctor h hU).obj A) t :=
  coefficientTensorMap_congr (fullLeviInductionEquiv h hU hP hM hbot A) t

end Generic

section Rational

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  [Fintype (RationalPointFamily.SimpleRoot i ν)]

private local instance : NonarchimedeanGroup (rationalPoints G) :=
  Plancherel.rationalPoints_nonarchimedeanGroup G

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (A : SmoothRep.{0, u, uV} ℂ
    (standardLeviPoints i ν (RationalPointFamily.rootSet i ν Finset.univ)))

/-- The preceding equivalence at the actual full simple-root standard
parabolic, using the proved structural endpoints and actual normalized action. -/
def rationalFullLeviInductionEquiv :
    ((normalizedInductionFunctor
      (isSemidirectDecomposition_standard hG hi hν
        (RationalPointFamily.rootSet_subset i ν Finset.univ))
      (isClosed_standardUnipotentPoints i ν
        (RationalPointFamily.rootSet i ν Finset.univ))).obj A).representation.Equiv
      (fullLeviAmbientSmoothRep _
        (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν) A).representation :=
  fullLeviInductionEquiv _ _
    (RationalPointFamily.parabolic_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.levi_univ_eq_top i ν standardCocharacter hG hi hν)
    (RationalPointFamily.unipotent_univ_eq_bot i ν) A

end Rational

end Langlands.HarishChandraSchwartz
