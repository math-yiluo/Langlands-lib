import Langlands.Representation.Intertwining.PQOuterLeviSupport
import Langlands.Representation.Intertwining.HaarTransportComparison
import Langlands.Representation.Intertwining.LeviInductionStagesFormula
import Langlands.Representation.Intertwining.PQIntegralUniqueness

/-! # The operator identity of Renard VII.3.5 (iii)

For `P₁ ⊂ Q₁ = LU₁`, `P₂ ⊂ Q₂ = LU₂` and `P' = P₁ ∩ L = P₂ ∩ L`, the integral-normalized
operators `J_{P₂|P₁}(σ)` and `J_{Q₂|Q₁}(i_{P'}^L(σ))` correspond under induction in stages,
when their integration domains `V` and `W` coincide and carry compatible Haar measures.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Measure

variable {H : Type*} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {V W : Subgroup H} [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]

/-- If two subgroups are equal, every Haar measure on the second gives a Haar measure on the
first with the same integrals of all functions on the ambient group. -/
theorem exists_haar_integral_eq_of_subgroup_eq (hVW : V = W) (haarW : Measure W)
    [haarW.IsHaarMeasure] :
    ∃ haarV : Measure V, haarV.IsHaarMeasure ∧
      ∀ φ : H → ℂ, ∫ x : W, φ x ∂haarW = ∫ x : V, φ x ∂haarV := by
  let e : W ≃ₜ* V := subgroupCongrContinuous hVW.symm
  obtain ⟨h₁, h₂⟩ := map_isHaarMeasure_integral_eq V e haarW
  exact ⟨haarW.map e, h₁, fun φ => h₂ φ⟩

/-- For equal closed subgroups of a locally compact second countable group, Haar measures
with the same integrals of continuous compactly supported functions have the same integrals
of all functions. -/
theorem integral_eq_of_subgroup_eq [LocallyCompactSpace H] [SecondCountableTopology H]
    (hVW : V = W) (hV : IsClosed (V : Set H)) (haarW : Measure W) [haarW.IsHaarMeasure]
    (haarV : Measure V) [haarV.IsHaarMeasure]
    (h : ∀ φ : H → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x : W, φ x ∂haarW = ∫ x : V, φ x ∂haarV)
    (ψ : H → ℂ) : ∫ x : W, ψ x ∂haarW = ∫ x : V, ψ x ∂haarV := by
  let e : W ≃ₜ* V := subgroupCongrContinuous hVW.symm
  have hmap : haarV = haarW.map e := haar_eq_map_of_integral_eq V hV e haarW haarV h
  rw [hmap, integral_map_continuousMulEquiv e haarW (fun x : V => ψ x)]
  rfl

end Measure

section SmoothIso

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] [TopologicalSpace Γ]

/-- `e⁻¹ (e x) = x` for an isomorphism of smooth representations. -/
theorem smoothRep_iso_inv_hom_apply {A B : SmoothRep.{_, _, v} R Γ} (e : A ≅ B) (x : A) :
    SmoothRep.hom e.inv (SmoothRep.hom e.hom x) = x :=
  congrArg (fun φ => SmoothRep.hom φ x) e.hom_inv_id

/-- `e (e⁻¹ x) = x` for an isomorphism of smooth representations. -/
theorem smoothRep_iso_hom_inv_apply {A B : SmoothRep.{_, _, v} R Γ} (e : A ≅ B) (x : B) :
    SmoothRep.hom e.hom (SmoothRep.hom e.inv x) = x :=
  congrArg (fun φ => SmoothRep.hom φ x) e.inv_hom_id

end SmoothIso

end Langlands.Aubert.General.RepresentedParabolic

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

section Operator

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G M P₁ N₁ P₂ N₂ L Q₁ U₁ Q₂ U₂ P' N' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

local instance outerOperatorPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hG : IsConnectedReductive G)
  {p₁ : P₁ ⟶ G} {l₁ : M ⟶ P₁} {r₁ : N₁ ⟶ P₁} (hp₁ : IsParabolicSubgroup p₁)
  (hl₁ : IsRationalLeviSubgroup l₁) (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
  (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
  {p₂ : P₂ ⟶ G} {l₂ : M ⟶ P₂} {r₂ : N₂ ⟶ P₂} (hp₂ : IsParabolicSubgroup p₂)
  (hl₂ : IsRationalLeviSubgroup l₂) (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
  (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
  {q₁ : Q₁ ⟶ G} {lQ₁ : L ⟶ Q₁} {rQ₁ : U₁ ⟶ Q₁} (hq₁ : IsParabolicSubgroup q₁)
  (hlQ₁ : IsRationalLeviSubgroup lQ₁) (hrQ₁ : LeviSubgroup.IsGeometricUnipotentRadical rQ₁)
  (hmulQ₁ : IsIso (subgroupMultiplication lQ₁ rQ₁))
  {q₂ : Q₂ ⟶ G} {lQ₂ : L ⟶ Q₂} {rQ₂ : U₂ ⟶ Q₂} (hq₂ : IsParabolicSubgroup q₂)
  (hlQ₂ : IsRationalLeviSubgroup lQ₂) (hrQ₂ : LeviSubgroup.IsGeometricUnipotentRadical rQ₂)
  (hmulQ₂ : IsIso (subgroupMultiplication lQ₂ rQ₂))
  {p' : P' ⟶ L} {l' : M ⟶ P'} {r' : N' ⟶ P'} (hp' : IsParabolicSubgroup p')
  (hl' : IsRationalLeviSubgroup l') (hr' : LeviSubgroup.IsGeometricUnipotentRadical r')
  (hmul' : IsIso (subgroupMultiplication l' r'))
  (hlev₂ : l₂ ≫ p₂ = l₁ ≫ p₁) (hlevQ₂ : lQ₂ ≫ q₂ = lQ₁ ≫ q₁)
  (hPQ₁ : pointImage p₁ ≤ pointImage q₁) (hPQ₂ : pointImage p₂ ≤ pointImage q₂)
  (hM : l' ≫ p' ≫ lQ₁ ≫ q₁ = l₁ ≫ p₁)
  (hP'₁ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₁ ⊓ pointImage (lQ₁ ≫ q₁))
  (hP'₂ : pointImage (p' ≫ lQ₁ ≫ q₁) = pointImage p₂ ⊓ pointImage (lQ₁ ≫ q₁))

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
include hlev₂ hlevQ₂ hM in
/-- The common Levi `M` seen through `P' ⊂ L ⊂ Q₂` is the one seen through `P₂`. -/
theorem outer_levi₂_eq : l' ≫ p' ≫ lQ₂ ≫ q₂ = l₂ ≫ p₂ := by
  rw [hlevQ₂, hM, hlev₂]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  [IsAffineHom G.X.hom] [LocallyCompactSpace (rationalPoints G)]
  [NonarchimedeanGroup (rationalPoints G)] in
include hlevQ₂ hP'₂ in
/-- `P'(F) = L(F) ∩ P₂(F)`, with `L` seen through `Q₂`. -/
theorem outer_parabolic₂_eq :
    pointImage (p' ≫ lQ₂ ≫ q₂) = pointImage (lQ₂ ≫ q₂) ⊓ pointImage p₂ := by
  rw [hlevQ₂]
  exact hP'₂.trans (inf_comm _ _)

include hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁ hq₂ hlQ₂ hrQ₂ hmulQ₂
  hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ in
/-- Renard VII.3.5 (iii), operator identity through the stage isomorphisms
`Φᵢ : i_{Pᵢ}^G(σ) ≅ i_{Qᵢ}^G(i_{P'}^L(σ))`: if `V = W` with compatible Haar measures and
`X = i_{P'}^L(σ)` is `Q₁Q₂`-regular, then `J_Q (Φ₁ f) = Φ₂ (J f)`. -/
theorem outer_intertwiner_stages
    {AL : CommGroupScheme (Spec (CommRingCat.of k))} (aL : AL.toGrp ⟶ L)
    (haL : IsSplitComponent aL)
    (V W : Subgroup (rationalPoints G)) (hVW : V = W)
    (hV : IsClosed (V : Set (rationalPoints G)))
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace W] [BorelSpace W]
    (haarW : Measure W) (haarV : Measure V) [haarW.IsHaarMeasure] [haarV.IsHaarMeasure]
    (hcompat : ∀ φ : rationalPoints G → ℂ, Continuous φ → HasCompactSupport φ →
      ∫ x : W, φ x ∂haarW = ∫ x : V, φ x ∂haarV) :
    haveI := hlQ₁.isConnectedReductive.isAffineHom
    letI : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
    haveI : LocallyCompactSpace (rationalPoints L) :=
      leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
    haveI : NonarchimedeanGroup (rationalPoints L) :=
      leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
    letI : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
    ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)),
      IsPQRegular q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂ aL
        ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ) →
      ∀ (J : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
            σ).representation.IntertwiningMap
          ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).representation)
        (JQ : ((leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj
            ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ)).representation.IntertwiningMap
          ((leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj
            ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ)).representation),
        IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
          V haarV σ J →
        IsIntegralIntertwiner q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂
          W haarW ((leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ) JQ →
        ∀ f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ,
          JQ (SmoothRep.hom ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
              q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
              (hP'₁.trans (inf_comm _ _)) hG).hom.app σ) f) =
            SmoothRep.hom ((leviInductionStagesIso p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
              q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ p' l' r' hp' hl' hr' hmul' hPQ₂
              (outer_levi₂_eq hlev₂ hlevQ₂ hM) (outer_parabolic₂_eq hlevQ₂ hP'₂) hG).hom.app σ)
              (J f) := by
  have := hlQ₁.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints L) := leviPointTopology lQ₁ hlQ₁
  have : LocallyCompactSpace (rationalPoints L) := leviPoints_locallyCompactSpace q₁ lQ₁ hq₁ hlQ₁
  have : NonarchimedeanGroup (rationalPoints L) := leviPoints_nonarchimedeanGroup q₁ lQ₁ hq₁ hlQ₁
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l₁ hl₁
  intro σ hreg J JQ hJ hJQ f
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  let X := (leviInductionFunctor p' l' r' hp' hr' hl' hmul').obj σ
  let Φ₁ := (leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
    (hP'₁.trans (inf_comm _ _)) hG).app σ
  let Φ₂ := (leviInductionStagesIso p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
    q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ p' l' r' hp' hl' hr' hmul' hPQ₂
    (outer_levi₂_eq hlev₂ hlevQ₂ hM) (outer_parabolic₂_eq hlevQ₂ hP'₂) hG).app σ
  let evalG₁ : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ → rationalPoints G → σ :=
    fun f g =>
    Induction.eval (pointImage p₁)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
        (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f g
  let evalG₂ : (leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ → rationalPoints G → σ :=
    fun f g =>
    Induction.eval (pointImage p₂)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂)
        (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm σ)) f g
  let evalL : X → rationalPoints L → σ := fun φ x =>
    Induction.eval (pointImage p')
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage p' l' r' hp'.isClosedSubgroup hr' hmul')
        (isClosed_pointImage_comp p' r' hp'.isClosedSubgroup hr'.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv p' l' hp' hl').symm σ)) φ x
  let evalQ₁ : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X →
      rationalPoints G → X := fun F g =>
    Induction.eval (pointImage q₁)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage q₁ lQ₁ rQ₁ hq₁.isClosedSubgroup hrQ₁ hmulQ₁)
        (isClosed_pointImage_comp q₁ rQ₁ hq₁.isClosedSubgroup hrQ₁.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv q₁ lQ₁ hq₁ hlQ₁).symm X)) F g
  let evalQ₂ : (leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj X →
      rationalPoints G → X := fun F g =>
    Induction.eval (pointImage q₂)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage q₂ lQ₂ rQ₂ hq₂.isClosedSubgroup hrQ₂ hmulQ₂)
        (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv q₂ lQ₂ hq₂ hlQ₂).symm X)) F g
  -- the stage formulas at the identity of `L(F)`
  have hΦ₁ : ∀ f g, evalL (evalQ₁ (SmoothRep.hom Φ₁.hom f) g) 1 = evalG₁ f g := by
    intro f g
    refine (leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      q₁ lQ₁ rQ₁ hq₁ hlQ₁ hrQ₁ hmulQ₁ p' l' r' hp' hl' hr' hmul' hPQ₁ hM
      (hP'₁.trans (inf_comm _ _)) hG σ f g 1).trans ?_
    simp only [map_one, Units.val_one, inv_one, one_smul, one_mul]
    rfl
  have hΦ₂ : ∀ f (g : rationalPoints G) (y : rationalPoints L),
      evalL (evalQ₂ (SmoothRep.hom Φ₂.hom f) g) y =
        ((HaarModulus.closedHalfCharacter (pointImage (rQ₂ ≫ q₂))
            (isClosed_pointImage_comp q₂ rQ₂ hq₂.isClosedSubgroup hrQ₂.1.isClosedSubgroup)
            (pointImage q₂)
            (isSemidirectDecomposition_pointImage q₂ lQ₂ rQ₂ hq₂.isClosedSubgroup hrQ₂
              hmulQ₂).le_normalizer
            (Subgroup.inclusion (pointImage_comp_le q₂ lQ₂)
              (leviPointsEquiv q₂ lQ₂ hq₂ hlQ₂ y)) : ℂˣ) : ℂ)⁻¹ •
          evalG₂ f (rationalPoints.map (lQ₂ ≫ q₂) y * g) :=
    leviInductionStagesIso_eval' p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
      q₂ lQ₂ rQ₂ hq₂ hlQ₂ hrQ₂ hmulQ₂ p' l' r' hp' hl' hr' hmul' hPQ₂
      (outer_levi₂_eq hlev₂ hlevQ₂ hM) (outer_parabolic₂_eq hlevQ₂ hP'₂) hG σ
  have hΦ₂₁ : ∀ f g, evalL (evalQ₂ (SmoothRep.hom Φ₂.hom f) g) 1 = evalG₂ f g := by
    intro f g
    refine (hΦ₂ f g 1).trans ?_
    simp only [map_one, Units.val_one, inv_one, one_smul, one_mul]
  -- the stage formula along `L(F)` with an unnamed scalar
  have hΦ₂' : ∀ y : rationalPoints L, ∃ c : ℂ, ∀ f g,
      evalL (evalQ₂ (SmoothRep.hom Φ₂.hom f) g) y =
        c • evalG₂ f (rationalPoints.map (lQ₂ ≫ q₂) y * g) :=
    fun y => ⟨_, fun f g => hΦ₂ f g y⟩
  let ρQ₁ := ((leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj
    X).representation
  let ρQ₂ := ((leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj
    X).representation
  let ρG₂ := ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).representation
  let emb₂ : rationalPoints L →* rationalPoints G := rationalPoints.map (lQ₂ ≫ q₂)
  have hemb₂ : ∀ y, emb₂ y ∈ pointImage q₂ := fun y => pointImage_comp_le q₂ lQ₂ ⟨y, rfl⟩
  -- (H1) the value at `y` of `H(1)` is a multiple of the value at `1` of a translate of `H`
  have hH1 : ∀ y : rationalPoints L, ∃ c : ℂ,
      ∀ H : (leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj X,
        evalL (evalQ₂ H 1) y = c • evalL (evalQ₂ (ρQ₂ (emb₂ y) H) 1) 1 := by
    intro y
    obtain ⟨c, hc⟩ := hΦ₂' y
    refine ⟨c, fun H => ?_⟩
    obtain ⟨h, rfl⟩ : ∃ h, SmoothRep.hom Φ₂.hom h = H :=
      ⟨SmoothRep.hom Φ₂.inv H, smoothRep_iso_hom_inv_apply Φ₂ H⟩
    calc evalL (evalQ₂ (SmoothRep.hom Φ₂.hom h) 1) y
        = c • evalG₂ h (emb₂ y * 1) := hc h 1
      _ = c • evalG₂ (ρG₂ (emb₂ y) h) 1 := by
          rw [mul_one]
          exact congrArg (c • ·) (congrArg (evalG₂ h) (one_mul (emb₂ y)).symm)
      _ = c • evalL (evalQ₂ (SmoothRep.hom Φ₂.hom (ρG₂ (emb₂ y) h)) 1) 1 := by
          rw [hΦ₂₁]
      _ = c • evalL (evalQ₂ (ρQ₂ (emb₂ y) (SmoothRep.hom Φ₂.hom h)) 1) 1 := by
          rw [(SmoothRep.hom Φ₂.hom).isIntertwining]
          rfl
  -- (H3) the boundary-vanishing space is stable under `Q₂(F)`
  have hS : ∀ y : rationalPoints L,
      ∀ F' : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X,
        F' ∈ (boundaryVanishingSubfunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂
          (identityParabolicDoubleCoset q₁ q₂)).obj X →
        ρQ₁ (emb₂ y) F' ∈ (boundaryVanishingSubfunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂
          (identityParabolicDoubleCoset q₁ q₂)).obj X :=
    fun y F' hF' => ((boundaryVanishingSubfunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂
      (identityParabolicDoubleCoset q₁ q₂)).obj X).apply_mem_toSubmodule ⟨emb₂ y, hemb₂ y⟩ hF'
  -- the composite operator `T = Φ₂ ∘ J ∘ Φ₁⁻¹`
  let T : ((leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj
        X).representation.IntertwiningMap
      ((leviInductionFunctor.{u, max u v} q₂ lQ₂ rQ₂ hq₂ hrQ₂ hlQ₂ hmulQ₂).obj X).representation :=
    (SmoothRep.hom Φ₂.hom).comp (J.comp (SmoothRep.hom Φ₁.inv))
  have hTΦ : ∀ f, T (SmoothRep.hom Φ₁.hom f) = SmoothRep.hom Φ₂.hom (J f) := by
    intro f
    change SmoothRep.hom Φ₂.hom (J (SmoothRep.hom Φ₁.inv (SmoothRep.hom Φ₁.hom f))) = _
    rw [smoothRep_iso_inv_hom_apply]
  -- (K) `J_Q` and `T` have the same values at `1`, evaluated at `1 ∈ L(F)`
  have hK : ∀ F'' : (leviInductionFunctor.{u, max u v} q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X,
      F'' ∈ (boundaryVanishingSubfunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂
        (identityParabolicDoubleCoset q₁ q₂)).obj X →
      evalL (evalQ₂ (JQ F'') 1) 1 = evalL (evalQ₂ (T F'') 1) 1 := by
    intro F'' hF''
    obtain ⟨f'', rfl⟩ : ∃ f'', SmoothRep.hom Φ₁.hom f'' = F'' :=
      ⟨SmoothRep.hom Φ₁.inv F'', smoothRep_iso_hom_inv_apply Φ₁ F''⟩
    rw [hTΦ, hΦ₂₁]
    have hf'' : f'' ∈ (boundaryVanishingSubfunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂
        (identityParabolicDoubleCoset p₁ p₂)).obj σ := by
      have hQ := (Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage q₁)
        (pointImage q₂) _
        (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset q₁ q₂))
        ((leviInducingFunctor q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁).obj X) _).mp hF''
      refine (Geometric.mem_rawSmoothVanishingSubfunctor_iff (R := ℂ) (pointImage p₁)
        (pointImage p₂) _
        (Geometric.boundary_doubleCoset_mul_mem _ _ (identityParabolicDoubleCoset p₁ p₂))
        ((leviInducingFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ) f'').mpr ?_
      intro g hg
      have h0 : evalQ₁ (SmoothRep.hom Φ₁.hom f'') g = 0 :=
        hQ g (outer_boundary_subset hG hp₁ hl₁ hr₁ hmul₁ hp₂ hl₂ hr₂ hmul₂ hq₁ hlQ₁ hrQ₁ hmulQ₁
          hq₂ hlQ₂ hrQ₂ hmulQ₂ hp' hl' hr' hmul' hlev₂ hlevQ₂ hPQ₁ hPQ₂ hM hP'₁ hP'₂ hg)
      change evalG₁ f'' g = 0
      calc evalG₁ f'' g = evalL (evalQ₁ (SmoothRep.hom Φ₁.hom f'') g) 1 := (hΦ₁ f'' g).symm
        _ = evalL 0 1 := by rw [h0]
        _ = 0 := rfl
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro ℓ
    rw [map_sub, sub_eq_zero]
    let ℓ' : Module.Dual ℂ X :=
      { toFun := fun φ => ℓ (evalL φ 1)
        map_add' := fun φ ψ => map_add ℓ (evalL φ 1) (evalL ψ 1)
        map_smul' := fun c φ => map_smul ℓ c (evalL φ 1) }
    have h₁ := (hJQ _ hF'' ℓ').2
    have h₂ := (hJ f'' hf'' ℓ).2
    calc ℓ (evalL (evalQ₂ (JQ (SmoothRep.hom Φ₁.hom f'')) 1) 1)
        = ∫ x : W, ℓ' (evalQ₁ (SmoothRep.hom Φ₁.hom f'') x) ∂haarW := h₁
      _ = ∫ x : W, ℓ (evalG₁ f'' x) ∂haarW := by
          congr 1
          funext x
          exact congrArg ℓ (hΦ₁ f'' x)
      _ = ∫ x : V, ℓ (evalG₁ f'' x) ∂haarV :=
          integral_eq_of_subgroup_eq hVW hV haarW haarV hcompat (fun g => ℓ (evalG₁ f'' g))
      _ = ℓ (evalG₂ (J f'') 1) := h₂.symm
  -- uniqueness on the `Q₁Q₂` side
  have hT : JQ = T := by
    refine intertwiner_eq_of_eval_one_eq q₁ lQ₁ rQ₁ hq₁ hrQ₁ hlQ₁ hmulQ₁ q₂ lQ₂ rQ₂ hq₂ hrQ₂
      hlQ₂ hmulQ₂ hG aL haL X hreg JQ T ?_
    intro F' hF'
    apply Subtype.ext
    apply Subtype.ext
    funext y
    change evalL (evalQ₂ (JQ F') 1) y = evalL (evalQ₂ (T F') 1) y
    obtain ⟨c, hc⟩ := hH1 y
    rw [hc (JQ F'), hc (T F'), ← JQ.isIntertwining, ← T.isIntertwining,
      hK _ (hS y F' hF')]
  change JQ (SmoothRep.hom Φ₁.hom f) = SmoothRep.hom Φ₂.hom (J f)
  rw [hT, hTΦ]

end Operator

end Langlands.Aubert.General.RepresentedParabolic
