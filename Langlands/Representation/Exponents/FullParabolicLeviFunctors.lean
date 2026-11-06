import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.IsoParabolicInduction
import Langlands.Representation.Aubert.General.Endpoint

/-! # The actual Levi functors of a full represented parabolic -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Points

variable {k : Type u} [Field k]
  {G H P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- Every matching geometric radical of a full parabolic has trivial point image. -/
theorem pointImage_radical_eq_bot_of_isIso_parabolic
    (p : P ⟶ G) [IsIso p] (hG : IsConnectedReductive G)
    (r : U ⟶ P) (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    pointImage (r ≫ p) = ⊥ := by
  have hP := hG.of_iso (asIso p)
  have he := hr.1.range_eq_bot hP.hasTrivialUnipotentRadical
  apply le_antisymm ?_ bot_le
  rintro _ ⟨x, rfl⟩
  have hx : rationalPoints.map r x = 1 := by
    have hm : rationalPoints.map r x ∈
        (SubgroupFunctor.range r).carrier (Over.mk (𝟙 _)) := ⟨x, rfl⟩
    rw [he] at hm
    exact hm
  rw [pointMap_comp_apply, hx, map_one]
  exact Subgroup.one_mem _

end Points

section Characters

variable {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
  [LocallyCompactSpace Γ] [IsTopologicalGroup Γ]

private theorem fullParabolic_normalizerCharacter_eq_one
    (N : Subgroup Γ) (hN : IsClosed (N : Set Γ)) (hbot : N = ⊥)
    (g : Subgroup.normalizer (N : Set Γ)) :
    HaarModulus.closedNormalizerCharacter N hN g = 1 := by
  let := hN.locallyCompactSpace
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  have : Subsingleton N := by rw [hbot]; infer_instance
  have he : HaarModulus.normalizerConj N g = ContinuousMulEquiv.refl N :=
    DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj N g) = 1
  rw [he]
  simp

private theorem fullParabolic_halfCharacter_eq_one
    (N : Subgroup Γ) (hN : IsClosed (N : Set Γ)) (hbot : N = ⊥)
    (L : Subgroup Γ) (hLN : L ≤ Subgroup.normalizer (N : Set Γ)) (g : L) :
    HaarModulus.closedHalfCharacter N hN L hLN g = 1 := by
  apply Units.ext
  change ((NNReal.sqrt
    (HaarModulus.closedNormalizerCharacter N hN ⟨g, hLN g.property⟩ : NNReal) : ℝ) : ℂ) = 1
  rw [fullParabolic_normalizerCharacter_eq_one N hN hbot]
  simp

private theorem fullParabolic_inverseHalfCharacter_eq_one
    (N : Subgroup Γ) (hN : IsClosed (N : Set Γ)) (hbot : N = ⊥)
    (L : Subgroup Γ) (hLN : L ≤ Subgroup.normalizer (N : Set Γ)) (g : L) :
    HaarModulus.closedInverseHalfCharacter N hN L hLN g = 1 := by
  apply Units.ext
  rw [show (HaarModulus.closedInverseHalfCharacter N hN L hLN g : ℂ) =
      (((NNReal.sqrt
        (HaarModulus.closedNormalizerCharacter N hN ⟨g, hLN g.property⟩ :
          NNReal) : ℝ) : ℂ))⁻¹ from Jacquet.inverseHalfCharacter_apply _ _]
  rw [fullParabolic_normalizerCharacter_eq_one N hN hbot]
  simp

end Characters

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance fullParabolicAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable (p : P ⟶ G) [IsIso p] (l : M ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hG : IsConnectedReductive G)

/-- The original Levi map of a full parabolic as a topological-group isomorphism. -/
def fullParabolicLeviPointsEquiv :
    letI := leviPointTopology l hl
    rationalPoints M ≃ₜ* rationalPoints G := by
  let := leviPointTopology l hl
  have := hl.isIso_of_isIso_parabolic (p := p) hG
  let htop := pointImage_eq_top_of_isIso (l ≫ p)
  let e : pointImage (l ≫ p) ≃ₜ* rationalPoints G :=
    { toMulEquiv := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  exact (leviPointsEquiv p l hp hl).trans e

omit [T2Space k] in
@[simp] theorem fullParabolicLeviPointsEquiv_apply (m : rationalPoints M) :
    fullParabolicLeviPointsEquiv p l hp hl hG m =
      rationalPoints.map (l ≫ p) m := rfl

variable [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]
  (r : U ⟶ P) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))

/-- Full-parabolic normalized Jacquet restriction is transport of the original
action along the actual Levi map. The linear map sends a class to its vector. -/
def fullParabolicLeviJacquetEquiv
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) :
    letI := leviPointTopology l hl
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.Equiv
      (π.representation.comp (rationalPoints.map (l ≫ p))) := by
  let := leviPointTopology l hl
  let N := pointImage (r ≫ p)
  have hbot : N = ⊥ := pointImage_radical_eq_bot_of_isIso_parabolic p hG r hr
  let e := endpointCoinvariantsEquiv N hbot π
  refine Representation.Equiv.mk e ?_
  intro m
  ext q
  obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective π.representation N 1 q
  change e
      (((HaarModulus.closedInverseHalfCharacter N
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (pointImage (l ≫ p)) (pointImage_le_normalizer p l r hr)
          (leviPointsEquiv p l hp hl m) : ℂˣ) : ℂ) •
        Jacquet.Localization.mk π.representation N 1
          (π.representation (rationalPoints.map (l ≫ p) m) x)) =
    π.representation (rationalPoints.map (l ≫ p) m)
      (e (Jacquet.Localization.mk π.representation N 1 x))
  rw [fullParabolic_inverseHalfCharacter_eq_one _ _ hbot]
  simp only [Units.val_one, one_smul, e, endpointCoinvariantsEquiv_mk]

@[simp] theorem fullParabolicLeviJacquetEquiv_mk
    (π : SmoothRep.{0, u, v} ℂ (rationalPoints G)) (x : π) :
    fullParabolicLeviJacquetEquiv p l hp hl hG r hr hmul π
      (Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x) = x :=
  endpointCoinvariantsEquiv_mk _
    (pointImage_radical_eq_bot_of_isIso_parabolic p hG r hr) π x

set_option maxHeartbeats 800000 in
/-- Full-parabolic normalized induction is transport along the inverse of the
actual Levi-point isomorphism. The forward map is evaluation at the identity. -/
def fullParabolicLeviInductionEquiv
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.Equiv
      (σ.representation.comp (fullParabolicLeviPointsEquiv p l hp hl hG).symm.toMonoidHom) := by
  let := leviPointTopology l hl
  have := hl.isIso_of_isIso_parabolic (p := p) hG
  let e := fullParabolicLeviPointsEquiv p l hp hl hG
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hN := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  let A := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ
  let ρ := σ.representation.comp e.symm.toMonoidHom
  have hL : pointImage (l ≫ p) = ⊤ := pointImage_eq_top_of_isIso (l ≫ p)
  have hbot := pointImage_radical_eq_bot_of_isIso_parabolic p hG r hr
  exact Induction.smoothInducedTopEquiv (pointImage p)
    (pointImage_eq_top_of_isIso p) (inducingRepresentation h hN A) ρ
    (by
      intro y
      ext x
      have hproj : (h.projection y : rationalPoints G) = (y : rationalPoints G) := by
        have hy : (y : rationalPoints G) ∈ pointImage (l ≫ p) := by rw [hL]; trivial
        exact congrArg Subtype.val (h.projection_levi ⟨y, hy⟩)
      change ((HaarModulus.closedHalfCharacter _ hN _ h.le_normalizer y : ℂˣ) : ℂ) •
          σ.representation ((leviPointsEquiv p l hp hl).symm (h.projection y)) x =
        σ.representation (e.symm (y : rationalPoints G)) x
      rw [fullParabolic_halfCharacter_eq_one _ _ hbot]
      simp only [Units.val_one, one_smul]
      apply congrArg (fun m => σ.representation m x)
      apply e.injective
      rw [e.apply_symm_apply]
      change fullParabolicLeviPointsEquiv p l hp hl hG
        ((leviPointsEquiv p l hp hl).symm (h.projection y)) = (y : rationalPoints G)
      rw [fullParabolicLeviPointsEquiv_apply, ← leviPointsEquiv_apply_coe p l hp hl,
        ContinuousMulEquiv.apply_symm_apply]
      exact hproj)
    (isSmooth_comp e.symm.toMonoidHom e.symm.continuous σ.isSmooth)

set_option maxHeartbeats 800000 in
/-- The actual full-parabolic induction equivalence is evaluation at the identity. -/
@[simp] theorem fullParabolicLeviInductionEquiv_apply
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : (leviInductionFunctor p l r hp hr hl hmul).obj σ) :
    letI := leviPointTopology l hl
    fullParabolicLeviInductionEquiv p l hp hl hG r hr hmul σ f = f.1.1 1 := rfl

set_option maxHeartbeats 800000 in
/-- The inverse equivalence sends a vector to its transported orbit function. -/
@[simp] theorem fullParabolicLeviInductionEquiv_symm_apply
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (x : σ) (g : rationalPoints G) :
    letI := leviPointTopology l hl
    ((fullParabolicLeviInductionEquiv p l hp hl hG r hr hmul σ).symm x).1.1 g =
      σ.representation ((fullParabolicLeviPointsEquiv p l hp hl hG).symm g) x := rfl

end Langlands.Aubert.General.RepresentedParabolic
