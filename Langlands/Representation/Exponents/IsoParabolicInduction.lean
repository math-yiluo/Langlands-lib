import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Aubert.General.RationalFixedLeviComparisonProof
import Langlands.Representation.Induction.SingleBlock
import Langlands.GroupScheme.Rational.FullParabolicLevi

/-! # Normalized induction along an isomorphic represented parabolic

If the represented parabolic `p : P ⟶ G` and its rational Levi `l : M ⟶ P` are
isomorphisms, the literal Levi image is all of `G(F)`, the radical image is trivial and
the modulus character is trivial. Evaluation at `1` then identifies the normalized
induction `i_P^G σ` of `leviInductionFunctor` with `σ`, intertwining the action of a point
`(l ≫ p)(a)` of `G(F)` with the action of `a ∈ M(F)`. When `G` is connected reductive,
`[IsIso p]` alone forces `[IsIso l]`.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))}

/-- The point map of an isomorphism of group schemes is surjective. -/
theorem pointImage_eq_top_of_isIso (j : M ⟶ G) [IsIso j] : pointImage j = ⊤ := by
  refine top_unique fun x _ => ⟨rationalPoints.map (inv j) x, ?_⟩
  rw [← pointMap_comp_apply, IsIso.inv_hom_id]
  simp [rationalPoints.map_apply]

section Characters

variable {H : Type*} [Group H] [TopologicalSpace H]
  [LocallyCompactSpace H] [IsTopologicalGroup H]

private theorem closedNormalizerCharacter_eq_one_of_eq_bot
    (N : Subgroup H) (hN : IsClosed (N : Set H)) (hbot : N = ⊥)
    (g : Subgroup.normalizer (N : Set H)) :
    HaarModulus.closedNormalizerCharacter N hN g = 1 := by
  let _ := hN.locallyCompactSpace
  let _ : MeasurableSpace N := borel N
  let _ : BorelSpace N := ⟨rfl⟩
  have : Subsingleton N := by rw [hbot]; infer_instance
  have he : HaarModulus.normalizerConj N g = ContinuousMulEquiv.refl N :=
    DFunLike.ext _ _ (fun _ => Subsingleton.elim _ _)
  apply Units.ext
  change MeasureTheory.mulEquivHaarChar (HaarModulus.normalizerConj N g) = 1
  rw [he]
  simp

private theorem closedHalfCharacter_eq_one_of_eq_bot
    (N : Subgroup H) (hN : IsClosed (N : Set H)) (hbot : N = ⊥)
    (K : Subgroup H) (hKN : K ≤ Subgroup.normalizer (N : Set H)) (x : K) :
    HaarModulus.closedHalfCharacter N hN K hKN x = 1 := by
  apply Units.ext
  change ((NNReal.sqrt
    (HaarModulus.closedNormalizerCharacter N hN ⟨x, hKN x.property⟩ : NNReal) : ℝ) : ℂ) = 1
  rw [closedNormalizerCharacter_eq_one_of_eq_bot N hN hbot]
  simp

end Characters

section Induction

variable [TopologicalSpace k] [IsAffineHom G.X.hom]

local instance isoParabolicAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

/-- For an isomorphic parabolic `p` and Levi `l`, the point map of `l ≫ p` is a
topological-group isomorphism `M(F) ≃ G(F)`: the literal Levi image is all of `G(F)`. -/
def isoLeviPointsEquiv (p : P ⟶ G) (l : M ⟶ P) [IsIso p] [IsIso l]
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) :
    letI := leviPointTopology l hl
    rationalPoints M ≃ₜ* rationalPoints G :=
  letI := leviPointTopology l hl
  have hM : pointImage (l ≫ p) = ⊤ := pointImage_eq_top_of_isIso (l ≫ p)
  { toFun := fun a => (leviPointsEquiv p l hp hl a : rationalPoints G)
    invFun := fun g => (leviPointsEquiv p l hp hl).symm ⟨g, hM ▸ Subgroup.mem_top g⟩
    left_inv := fun a => (leviPointsEquiv p l hp hl).symm_apply_apply a
    right_inv := fun _ => congrArg Subtype.val ((leviPointsEquiv p l hp hl).apply_symm_apply _)
    map_mul' := fun a b => congrArg Subtype.val (map_mul (leviPointsEquiv p l hp hl) a b)
    continuous_toFun := continuous_subtype_val.comp (leviPointsEquiv p l hp hl).continuous
    continuous_invFun :=
      (leviPointsEquiv p l hp hl).symm.continuous.comp (continuous_id.subtype_mk _) }

/-- The isomorphism `M(F) ≃ G(F)` is the point map of `l ≫ p`. -/
@[simp] theorem isoLeviPointsEquiv_apply (p : P ⟶ G) (l : M ⟶ P) [IsIso p] [IsIso l]
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (a : rationalPoints M) :
    letI := leviPointTopology l hl
    isoLeviPointsEquiv p l hp hl a = rationalPoints.map (l ≫ p) a :=
  rfl

variable [T2Space k] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)]

-- Unifying the induced representation with the published smooth induction is slow.
set_option maxHeartbeats 400000 in
/-- For an isomorphic parabolic `p` and Levi `l`, evaluation at `1` is an equivalence of
representations of `G(F)` from the normalized induction `i_P^G σ` to `σ` transported to
`G(F)` along `(l ≫ p)⁻¹`. -/
def isoParabolicInductionRepEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) [IsIso p] [IsIso l]
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.Equiv
      (SmoothRep.pullback (isoLeviPointsEquiv p l hp hl).symm σ).representation := by
  letI := leviPointTopology l hl
  have hM : pointImage (l ≫ p) = ⊤ := pointImage_eq_top_of_isIso (l ≫ p)
  let h := isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul
  let hU := isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup
  have hbot : pointImage (r ≫ p) = ⊥ := h.unipotent_eq_bot_of_levi_eq_top hM
  let A := SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ
  let B := SmoothRep.pullback (isoLeviPointsEquiv p l hp hl).symm σ
  refine Induction.smoothInducedTopEquiv (pointImage p)
    (h.parabolic_eq_top_of_levi_eq_top hM) (inducingRepresentation h hU A)
    B.representation ?_ B.isSmooth
  intro x
  ext w
  have hm : (x : rationalPoints G) ∈ pointImage (l ≫ p) := hM ▸ Subgroup.mem_top _
  have hx : h.projection x = ⟨x, hm⟩ := h.projection_levi ⟨x, hm⟩
  change ((HaarModulus.closedHalfCharacter (pointImage (r ≫ p)) hU (pointImage p)
    h.le_normalizer x : ℂˣ) : ℂ) • A.representation (h.projection x) w =
      A.representation ⟨x, hm⟩ w
  rw [closedHalfCharacter_eq_one_of_eq_bot _ hU hbot, Units.val_one, one_smul, hx]

/-- For an isomorphic parabolic `p` and Levi `l`, evaluation at `1` is a linear
equivalence from the normalized induction `i_P^G σ` to `σ`. -/
def isoParabolicInductionEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) [IsIso p] [IsIso l]
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    (leviInductionFunctor p l r hp hr hl hmul).obj σ ≃ₗ[ℂ] σ :=
  letI := leviPointTopology l hl
  (isoParabolicInductionRepEquiv p l r hp hr hl hmul σ).toLinearEquiv

/-- The equivalence is evaluation of the induced function at `1`. -/
theorem isoParabolicInductionEquiv_apply (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    [IsIso p] [IsIso l]
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : letI := leviPointTopology l hl; (leviInductionFunctor p l r hp hr hl hmul).obj σ) :
    letI := leviPointTopology l hl
    isoParabolicInductionEquiv p l r hp hr hl hmul σ f =
      Induction.eval (pointImage p)
        (inducingRepresentation
          (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
          (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
          (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)) f 1 :=
  rfl

/-- The equivalence intertwines the action of `(l ≫ p)(a)` on `i_P^G σ` with the action
of `a` on `σ`. -/
theorem isoParabolicInductionEquiv_map (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    [IsIso p] [IsIso l]
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (a : rationalPoints M)
    (f : letI := leviPointTopology l hl; (leviInductionFunctor p l r hp hr hl hmul).obj σ) :
    letI := leviPointTopology l hl
    isoParabolicInductionEquiv p l r hp hr hl hmul σ
        (((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
          (rationalPoints.map (l ≫ p) a) f) =
      σ.representation a (isoParabolicInductionEquiv p l r hp hr hl hmul σ f) := by
  let := leviPointTopology l hl
  exact (Representation.IntertwiningMap.isIntertwining _ _
    (isoParabolicInductionRepEquiv p l r hp hr hl hmul σ).toIntertwiningMap
    (isoLeviPointsEquiv p l hp hl a) f).trans
      (congrArg (fun m => σ.representation m _)
        ((isoLeviPointsEquiv p l hp hl).symm_apply_apply a))

/-- Renard's degenerate case of normalized induction: along a represented parabolic
`p` that is an isomorphism onto a connected reductive group, `i_P^G σ` is linearly
equivalent to `σ`, intertwining the action of `(l ≫ p)(a)` with that of `a`. -/
theorem exists_isoParabolicInductionEquiv (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P) [IsIso p]
    (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
    (hG : IsConnectedReductive G)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    ∃ T : (leviInductionFunctor p l r hp hr hl hmul).obj σ ≃ₗ[ℂ] σ,
      ∀ (a : rationalPoints M) (f : (leviInductionFunctor p l r hp hr hl hmul).obj σ),
        T (((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation
          (rationalPoints.map (l ≫ p) a) f) = σ.representation a (T f) := by
  let := leviPointTopology l hl
  have := hl.isIso_of_isIso_parabolic (p := p) hG
  exact ⟨isoParabolicInductionEquiv p l r hp hr hl hmul σ,
    isoParabolicInductionEquiv_map p l r hp hr hl hmul σ⟩

end Induction

end Langlands.Aubert.General.RepresentedParabolic
