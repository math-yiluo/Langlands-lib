import Langlands.Representation.Intertwining.InnerLeviOperatorIdentity
import Langlands.Representation.Aubert.General.StandardLeviJacquetFiniteLength
import Langlands.Representation.Aubert.General.NestedParabolicTransitivity
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero

/-! # Regularity in stages for Renard VII.3.5 (ii)

For represented parabolics `P₁ = MN₁`, `P₂ = MN₂` of `G` inside `Q = LU`, with traces
`P₁' = MN₁'`, `P₂' = MN₂'` in `L`, the map `T : i_{P₁}^G(σ) → i_{P₁'}^L(σ)`,
`T f (x) = δ_U(x)^{-1/2} f(x)`, induces a surjection
`r_{P₂} i_{P₁}(σ) / F^{<1̄}_{P₁P₂} → r_{P₂'} i_{P₁'}(σ) / F^{<1̄}_{P₁'P₂'}` compatible with the
actions of `M(F)`. Hence `I^{P₁P₂}_σ ⊆ I^{P₁'P₂'}_σ`, and `P₁P₂`-regularity of `σ` implies
`P₁'P₂'`-regularity.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands

/-- For a surjective linear map intertwining the actions of `B` through `φ`, the kernel in
`ℂ[B]` of the source action lies in that of the target action. -/
theorem groupAlgebraKernel_le_of_surjective {H B : Type*} [Monoid H] [Monoid B]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H W) (φ : B →* H)
    (T : V →ₗ[ℂ] W) (hT : Function.Surjective T)
    (hcomm : ∀ (b : B) (v : V), T (ρ (φ b) v) = ρ' (φ b) (T v)) :
    groupAlgebraKernel ρ φ ≤ groupAlgebraKernel ρ' φ := by
  intro x hx
  rw [mem_groupAlgebraKernel_iff] at hx ⊢
  have key : ∀ (y : MonoidAlgebra ℂ B) (v : V),
      T (Representation.asAlgebraHom (ρ.comp φ) y v) =
        Representation.asAlgebraHom (ρ'.comp φ) y (T v) := by
    intro y
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      intro v
      simp only [Representation.asAlgebraHom_of, MonoidHom.coe_comp, Function.comp_apply]
      exact hcomm b v
    | add y z hy hz =>
      intro v
      simp only [map_add, LinearMap.add_apply, hy, hz]
    | smul c y hy =>
      intro v
      simp only [map_smul, LinearMap.smul_apply, hy]
  ext w
  obtain ⟨v, rfl⟩ := hT w
  rw [← key, hx]
  simp

/-- The quotient form of `groupAlgebraKernel_le_of_surjective`: a surjective intertwining
linear map carrying `S` into `S'` gives the inclusion of the kernels on `V/S` and `W/S'`. -/
theorem groupAlgebraKernel_quotient_le {H B : Type*} [Monoid H] [Monoid B]
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ H V) (ρ' : Representation ℂ H W) (φ : B →* H)
    (S : Submodule ℂ V) (hS : ∀ g, S ≤ S.comap (ρ g))
    (S' : Submodule ℂ W) (hS' : ∀ g, S' ≤ S'.comap (ρ' g))
    (T : V →ₗ[ℂ] W) (hT : Function.Surjective T) (hTS : S ≤ S'.comap T)
    (hcomm : ∀ (b : B) (v : V), T (ρ (φ b) v) = ρ' (φ b) (T v)) :
    groupAlgebraKernel (ρ.quotient S hS) φ ≤ groupAlgebraKernel (ρ'.quotient S' hS') φ := by
  apply groupAlgebraKernel_le_of_surjective _ _ φ (S.mapQ S' T hTS)
  · intro w
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective S' w
    obtain ⟨v, rfl⟩ := hT w
    exact ⟨Submodule.mkQ S v, rfl⟩
  · intro b v
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S v
    change Submodule.Quotient.mk (T (ρ (φ b) v)) = Submodule.Quotient.mk (ρ' (φ b) (T v))
    rw [hcomm]

end Langlands

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G M P₁ N₁ P₂ N₂ Q L U P₁' N₁' P₂' N₂' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom] [IsAffineHom M.X.hom]

local instance innerRegularityAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

local instance innerRegularityInnerTopology : TopologicalSpace (rationalPoints L) :=
  RationalPointFamily.pointTopology

local instance innerRegularityLeviTopology : TopologicalSpace (rationalPoints M) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  [LocallyCompactSpace (rationalPoints L)] [NonarchimedeanGroup (rationalPoints L)]
  (hG : IsConnectedReductive G)
  (p₁ : P₁ ⟶ G) (l₁ : M ⟶ P₁) (r₁ : N₁ ⟶ P₁)
  (hp₁ : IsParabolicSubgroup p₁) (hl₁ : IsRationalLeviSubgroup l₁)
  (hr₁ : LeviSubgroup.IsGeometricUnipotentRadical r₁)
  (hmul₁ : IsIso (subgroupMultiplication l₁ r₁))
  (p₂ : P₂ ⟶ G) (l₂ : M ⟶ P₂) (r₂ : N₂ ⟶ P₂)
  (hp₂ : IsParabolicSubgroup p₂) (hl₂ : IsRationalLeviSubgroup l₂)
  (hr₂ : LeviSubgroup.IsGeometricUnipotentRadical r₂)
  (hmul₂ : IsIso (subgroupMultiplication l₂ r₂))
  (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
  (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hmulQ : IsIso (subgroupMultiplication lQ rQ))
  (hPQ₁ : pointImage p₁ ≤ pointImage q) (hPQ₂ : pointImage p₂ ≤ pointImage q)
  (p₁' : P₁' ⟶ L) (l₁' : M ⟶ P₁') (r₁' : N₁' ⟶ P₁')
  (hp₁' : IsParabolicSubgroup p₁') (hl₁' : IsRationalLeviSubgroup l₁')
  (hr₁' : LeviSubgroup.IsGeometricUnipotentRadical r₁')
  (hmul₁' : IsIso (subgroupMultiplication l₁' r₁'))
  (p₂' : P₂' ⟶ L) (l₂' : M ⟶ P₂') (r₂' : N₂' ⟶ P₂')
  (hp₂' : IsParabolicSubgroup p₂') (hl₂' : IsRationalLeviSubgroup l₂')
  (hr₂' : LeviSubgroup.IsGeometricUnipotentRadical r₂')
  (hmul₂' : IsIso (subgroupMultiplication l₂' r₂'))
  (hM₁ : l₁' ≫ p₁' ≫ lQ ≫ q = l₁ ≫ p₁) (hM₂ : l₂' ≫ p₂' ≫ lQ ≫ q = l₂ ≫ p₂)
  (hPL₁ : pointImage (p₁' ≫ lQ ≫ q) = pointImage p₁ ⊓ pointImage (lQ ≫ q))
  (hPL₂ : pointImage (p₂' ≫ lQ ≫ q) = pointImage p₂ ⊓ pointImage (lQ ≫ q))

/-- The half modulus `c(x) = δ_U(x)^{1/2}` of `Q = LU` on `L(F)`, as a character. -/
def innerLeviHalfModulus : rationalPoints L →* ℂˣ :=
  (HaarModulus.closedHalfCharacter (pointImage (rQ ≫ q))
      (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
      (pointImage q)
      (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ
        hmulQ).le_normalizer).comp
    ((Subgroup.inclusion (pointImage_comp_le q lQ)).comp
      (leviPointsEquiv q lQ hq hlQ).toMulEquiv.toMonoidHom)

/-- Renard's restriction `T : i_{P₁}^G(σ) → i_{P₁'}^L(σ)`, `T f = f̃(1)`, that is,
`T f (x) = δ_U(x)^{-1/2} f(x)` for `x ∈ L(F)`. -/
def innerStageRestriction (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ →ₗ[ℂ]
      (leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ where
  toFun f := Induction.eval (pointImage q)
    (inducingRepresentation
      (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
      (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
      (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
        ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ)))
    (SmoothRep.hom ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG).hom.app σ) f) 1
  map_add' f g := by
    rw [map_add]
    rfl
  map_smul' c f := by
    rw [map_smul]
    rfl

include hG hPQ₁ hM₁ hPL₁ in
/-- The formula `T f (x) = δ_U(x)^{-1/2} f(x)`. -/
theorem innerStageRestriction_eval (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ) (x : rationalPoints L) :
    Induction.eval (pointImage p₁')
        (inducingRepresentation
          (isSemidirectDecomposition_pointImage p₁' l₁' r₁' hp₁'.isClosedSubgroup hr₁' hmul₁')
          (isClosed_pointImage_comp p₁' r₁' hp₁'.isClosedSubgroup hr₁'.1.isClosedSubgroup)
          (SmoothRep.pullback (leviPointsEquiv p₁' l₁' hp₁' hl₁').symm σ))
        (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
          p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f) x =
      ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ x : ℂˣ) : ℂ)⁻¹ •
        Induction.eval (pointImage p₁)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
            (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f
          (rationalPoints.map (lQ ≫ q) x) := by
  have h := leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG σ f 1 x
  rw [mul_one] at h
  exact h


include hG hPQ₁ hM₁ hPL₁ in
/-- `T` intertwines the action of `L(F)` up to the half modulus:
`T (emb(y) · f) = c(y) · (y · T f)`. -/
theorem innerStageRestriction_levi (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ) (y : rationalPoints L) :
    innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ
        (((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
          (rationalPoints.map (lQ ≫ q) y) f) =
      ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ y : ℂˣ) : ℂ) •
        ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ).representation y
          (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
            p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  have h1 := innerStageRestriction_eval hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ
    (((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
      (rationalPoints.map (lQ ≫ q) y) f) x
  have h2 := innerStageRestriction_eval hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f (x * y)
  rw [map_mul (rationalPoints.map (lQ ≫ q)) x y] at h2
  refine h1.trans ?_
  refine Eq.trans ?_ (congrArg (fun v => ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ y :
    ℂˣ) : ℂ) • v) h2.symm)
  have hs : ∀ a b : ℂˣ, (a : ℂ)⁻¹ = (b : ℂ) * ((a * b : ℂˣ) : ℂ)⁻¹ := by
    intro a b
    rw [Units.val_mul, mul_inv, mul_left_comm, mul_inv_cancel₀ b.ne_zero, mul_one]
  have hgen : ∀ {W : Type v} [AddCommGroup W] [Module ℂ W] (w : W),
      ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ x : ℂˣ) : ℂ)⁻¹ • w =
        ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ y : ℂˣ) : ℂ) •
          ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ (x * y) : ℂˣ) : ℂ)⁻¹ • w := by
    intro W _ _ w
    rw [smul_smul, map_mul, ← hs]
  exact hgen _


include hG hPQ₁ hM₁ hPL₁ in
/-- `T` is invariant under `U(F)`: `T (w · f) = T f` for `w ∈ U(F)`. -/
theorem innerStageRestriction_unipotent (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ) (w : rationalPoints G)
    (hw : w ∈ pointImage (rQ ≫ q)) :
    innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ
        (((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation w f) =
      innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f := by
  have hQdec := isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
  have hUc := isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup
  have hcov := normalizedInductionFunctor_covariant hQdec hUc
    (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
      ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ))
    (SmoothRep.hom ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG).hom.app σ) f)
    ⟨w, hQdec.unipotent_le hw⟩ 1
  rw [hQdec.projection_unipotent ⟨w, hw⟩, map_one,
    closedHalfCharacter_eq_one_of_isLimitOfCompactSubgroups hQdec hUc hQdec.unipotent_le
      (isLimitOfCompactSubgroups_pointImage_radical q rQ hq.isClosedSubgroup hrQ.1) ⟨w, hw⟩,
    Units.val_one, one_smul, mul_one] at hcov
  refine Eq.trans ?_ hcov
  apply Subtype.ext
  apply Subtype.ext
  funext x
  refine (innerStageRestriction_eval hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ
    (((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation w f) x).trans ?_
  exact (leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG σ f w x).symm

include hG hPQ₁ hM₁ hPL₁ in
/-- `T` is surjective: every `φ ∈ i_{P₁'}^L(σ)` is `F(1)` for some `F ∈ i_Q^G(i_{P₁'}^L(σ))`. -/
theorem innerStageRestriction_surjective (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Function.Surjective (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ) := by
  intro φ
  obtain ⟨F, hF⟩ := normalizedInduction_eval_surjective
    (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
    (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
    (continuous_projection_pointImage q lQ rQ hq hlQ hrQ hmulQ)
    (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
      ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ)) φ
  refine ⟨SmoothRep.hom ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG).inv.app σ) F, ?_⟩
  have h := congrArg (fun ψ => SmoothRep.hom ψ F) ((leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG).inv_hom_id_app σ)
  refine Eq.trans ?_ hF
  exact congrArg (fun G' => Induction.eval (pointImage q)
    (inducingRepresentation
      (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
      (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
      (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
        ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ))) G' 1) h

include hG r₂ hp₂ hl₂ hr₂ hmul₂ rQ hq hlQ hrQ hmulQ r₂' hp₂' hl₂' hr₂' hmul₂'
  hPQ₁ hPQ₂ hM₁ hM₂ hPL₁ hPL₂ in
/-- `T` carries `F̃^{<1̄}_{P₁P₂}(σ)` into `F̃^{<1̄}_{P₁'P₂'}(σ)`. -/
theorem innerStageRestriction_mem_boundary (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
    (hf : f ∈ (boundaryVanishingSubfunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂
      (identityParabolicDoubleCoset p₁ p₂)).obj σ) :
    innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f ∈
      (boundaryVanishingSubfunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁' p₂'
        (identityParabolicDoubleCoset p₁' p₂')).obj σ := by
  refine mem_innerBoundaryVanishing_of_map hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂
    hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁'
    p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ f _ hf ?_
  intro x hx
  refine (innerStageRestriction_eval hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f x).trans ?_
  have hz : ∀ {W : Type v} [AddCommGroup W] [Module ℂ W] (c : ℂ) (w : W), w = 0 → c • w = 0 := by
    intro W _ _ c w hw
    rw [hw, smul_zero]
  exact hz _ _ hx


/-- Half-character algebra: if `a = b c` for positive moduli, then
`(a^{1/2})⁻¹ b^{1/2} = (c^{1/2})⁻¹` in `ℂ`. -/
theorem inverseHalfCharacter_mul_halfCharacter {H₁ H₂ H₃ : Type*} [Group H₁] [Group H₂]
    [Group H₃] (δ₁ : H₁ →* NNRealˣ) (δ₂ : H₂ →* NNRealˣ) (δ₃ : H₃ →* NNRealˣ)
    (h₁ : H₁) (h₂ : H₂) (h₃ : H₃) (h : δ₁ h₁ = δ₂ h₂ * δ₃ h₃) :
    (Jacquet.inverseHalfCharacter δ₁ h₁ : ℂ) *
        (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter δ₂) h₂ : ℂ) =
      (Jacquet.inverseHalfCharacter δ₃ h₃ : ℂ) := by
  simp only [Jacquet.inverseHalfCharacter, MonoidHom.inv_apply, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, h, map_mul]
  rw [← Units.val_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- The Haar modulus of conjugation on a closed subgroup depends only on the conjugating
element of the ambient group. -/
theorem closedRestrictCharacter_congr_elem {H : Type*} [Group H] [TopologicalSpace H]
    [LocallyCompactSpace H] [IsTopologicalGroup H] (U : Subgroup H)
    (hU : IsClosed (U : Set H)) {M M' : Subgroup H}
    (hM : M ≤ Subgroup.normalizer (U : Set H)) (hM' : M' ≤ Subgroup.normalizer (U : Set H))
    {m : M} {m' : M'} (hm : (m : H) = m') :
    HaarModulus.closedRestrictCharacter U hU M hM m =
      HaarModulus.closedRestrictCharacter U hU M' hM' m' := by
  simp only [HaarModulus.closedRestrictCharacter, MonoidHom.comp_apply]
  congr 1
  exact Subtype.ext hm

omit [IsAffineHom M.X.hom] in
include hG hmul₂ hmul₂' hPQ₂ hM₂ hPL₂ in
/-- The modulus identity of induction in stages on `M(F)`:
`δ_{P₂}(m)^{-1/2} δ_U(m)^{1/2} = δ_{P₂'}(m)^{-1/2}`, from `N₂(F) = N₂'(F) U(F)`. -/
theorem innerLevi_inverseHalfModulus_mul (m : rationalPoints M) :
    ((HaarModulus.closedInverseHalfCharacter (pointImage (r₂ ≫ p₂))
        (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
        (pointImage (l₂ ≫ p₂)) (pointImage_le_normalizer p₂ l₂ r₂ hr₂)
        (leviPointsEquiv p₂ l₂ hp₂ hl₂ m) : ℂˣ) : ℂ) *
      ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ
        (rationalPoints.map (l₂' ≫ p₂') m) : ℂˣ) : ℂ) =
    ((HaarModulus.closedInverseHalfCharacter (pointImage (r₂' ≫ p₂'))
        (isClosed_pointImage_comp p₂' r₂' hp₂'.isClosedSubgroup hr₂'.1.isClosedSubgroup)
        (pointImage (l₂' ≫ p₂')) (pointImage_le_normalizer p₂' l₂' r₂' hr₂')
        (leviPointsEquiv p₂' l₂' hp₂' hl₂' m) : ℂˣ) : ℂ) := by
  have : SecondCountableTopology (rationalPoints G) :=
    RationalPointFamily.reductiveRationalPoint_secondCountable k G hG
  have hjc : IsClosedSubgroup (lQ ≫ q) := hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  have : IsClosedImmersion (lQ ≫ q).hom.hom.left := hjc
  have : Mono (lQ ≫ q).hom.hom := Over.mono_of_mono_left _
  have hinj : Function.Injective (rationalPoints.map (lQ ≫ q)) := fun a b hab =>
    (cancel_mono (lQ ≫ q).hom.hom).mp hab
  obtain ⟨hNL₂, hprod₂, -⟩ := nestedParabolicPointDecomposition k G hG P₂ M N₂ Q L U P₂' N₂'
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂'
    hPQ₂ hM₂ (by rw [inf_comm]; exact hPL₂)
  have hN₂ : pointImage (r₂' ≫ p₂' ≫ lQ ≫ q) = pointImage (lQ ≫ q) ⊓ pointImage (r₂ ≫ p₂) :=
    hNL₂
  have hcomp : ∀ x : rationalPoints M, rationalPoints.map (l₂ ≫ p₂) x =
      rationalPoints.map (lQ ≫ q) (rationalPoints.map (l₂' ≫ p₂') x) := by
    intro x
    rw [← hM₂]
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hP := isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂
  have hQ := isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
  have hL : IsClosed (pointImage (lQ ≫ q) : Set (rationalPoints G)) :=
    isClosed_leviPoints q lQ hq hlQ
  have hN := isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup
  have hU := isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup
  have hSL : pointImage (l₂ ≫ p₂) ≤ pointImage (lQ ≫ q) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨rationalPoints.map (l₂' ≫ p₂') x, (hcomp x).symm⟩
  have hSN := pointImage_le_normalizer p₂ l₂ r₂ hr₂
  have hδ := NestedParabolic.modulus_product hP hQ hL hN hU hPQ₂ hprod₂
    (continuous_projection_pointImage q lQ rQ hq hlQ hrQ hmulQ) hSL hSN
    (leviPointsEquiv p₂ l₂ hp₂ hl₂ m)
  let := hL.locallyCompactSpace
  have hUU' : ∀ x : rationalPoints L, x ∈ pointImage (r₂' ≫ p₂') ↔
      leviPointsEquiv q lQ hq hlQ x ∈
        (pointImage (r₂ ≫ p₂)).subgroupOf (pointImage (lQ ≫ q)) := by
    intro x
    rw [Subgroup.mem_subgroupOf, leviPointsEquiv_apply_coe]
    constructor
    · intro hx
      have h := map_mem_pointImage_comp (lQ ≫ q) hx
      rw [Category.assoc, hN₂] at h
      exact h.2
    · intro hx
      apply mem_pointImage_of_map_mem_comp (j := lQ ≫ q)
      rw [Category.assoc, hN₂]
      exact ⟨⟨x, rfl⟩, hx⟩
  have hMM' : ∀ x : rationalPoints L, x ∈ pointImage (l₂' ≫ p₂') ↔
      leviPointsEquiv q lQ hq hlQ x ∈
        (pointImage (l₂ ≫ p₂)).subgroupOf (pointImage (lQ ≫ q)) := by
    intro x
    rw [Subgroup.mem_subgroupOf, leviPointsEquiv_apply_coe]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hcomp z⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, hinj ((hcomp z).symm.trans hz)⟩
  have hT := GroupTransport.closedRestrictCharacter_transport (leviPointsEquiv q lQ hq hlQ)
    hUU' hMM' (hN.preimage continuous_subtype_val)
    (isClosed_pointImage_comp p₂' r₂' hp₂'.isClosedSubgroup hr₂'.1.isClosedSubgroup)
    (normalizes_subgroupOf hSN) (pointImage_le_normalizer p₂' l₂' r₂' hr₂')
    (leviPointsEquiv p₂' l₂' hp₂' hl₂' m)
  have hsub : GroupTransport.subgroupEquiv (leviPointsEquiv q lQ hq hlQ) hMM'
      (leviPointsEquiv p₂' l₂' hp₂' hl₂' m) =
      (subgroupOfContinuousEquiv hSL).symm (leviPointsEquiv p₂ l₂ hp₂ hl₂ m) :=
    Subtype.ext (Subtype.ext (hcomp m).symm)
  have hcU := closedRestrictCharacter_congr_elem (pointImage (rQ ≫ q)) hU hQ.le_normalizer
    hQ.levi_le_normalizer
    (m := Subgroup.inclusion (pointImage_comp_le q lQ)
      (leviPointsEquiv q lQ hq hlQ (rationalPoints.map (l₂' ≫ p₂') m)))
    (m' := ⟨leviPointsEquiv p₂ l₂ hp₂ hl₂ m, hSL (leviPointsEquiv p₂ l₂ hp₂ hl₂ m).2⟩)
    (hcomp m).symm
  have hc : ((innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ
        (rationalPoints.map (l₂' ≫ p₂') m) : ℂˣ) : ℂ) =
      (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter
        (HaarModulus.closedRestrictCharacter (pointImage (rQ ≫ q)) hU (pointImage q)
          hQ.le_normalizer))
        (Subgroup.inclusion (pointImage_comp_le q lQ)
          (leviPointsEquiv q lQ hq hlQ (rationalPoints.map (l₂' ≫ p₂') m))) : ℂ) := rfl
  rw [hc]
  have h : HaarModulus.closedRestrictCharacter (pointImage (r₂ ≫ p₂)) hN (pointImage (l₂ ≫ p₂))
        hSN (leviPointsEquiv p₂ l₂ hp₂ hl₂ m) =
      HaarModulus.closedRestrictCharacter (pointImage (rQ ≫ q)) hU (pointImage q)
          hQ.le_normalizer
          (Subgroup.inclusion (pointImage_comp_le q lQ)
            (leviPointsEquiv q lQ hq hlQ (rationalPoints.map (l₂' ≫ p₂') m))) *
        HaarModulus.closedRestrictCharacter (pointImage (r₂' ≫ p₂'))
          (isClosed_pointImage_comp p₂' r₂' hp₂'.isClosedSubgroup hr₂'.1.isClosedSubgroup)
          (pointImage (l₂' ≫ p₂')) (pointImage_le_normalizer p₂' l₂' r₂' hr₂')
          (leviPointsEquiv p₂' l₂' hp₂' hl₂' m) := by
    rw [hcU, hT, hsub]
    exact hδ
  exact inverseHalfCharacter_mul_halfCharacter _ _ _ _ _ _ h

include hG hPQ₁ hM₁ hPL₁ hp₂ hl₂ hr₂ hmul₂ hp₂' hl₂' hr₂' hmul₂' hPQ₂ hM₂ hPL₂ in
/-- `T` descends to the coinvariants: for `n ∈ N₂(F)`, `[T (n · f)] = [T f]` in the
`N₂'(F)`-coinvariants of `i_{P₁'}^L(σ)`. Write `n = y w` with `y ∈ L(F) ∩ N₂(F) = N₂'(F)` and
`w ∈ U(F)`; then `T (n · f) = c(y) · y · T f` with `c(y) = 1`. -/
theorem innerStageRestriction_descends (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (n : pointImage (r₂ ≫ p₂)) (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ) :
    Jacquet.Localization.mk ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj
        σ).representation (pointImage (r₂' ≫ p₂')) 1
      (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ
        (((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation n f)) =
      (((1 : pointImage (r₂ ≫ p₂) →* ℂˣ) n : ℂˣ) : ℂ) •
        Jacquet.Localization.mk ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj
          σ).representation (pointImage (r₂' ≫ p₂')) 1
        (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
          p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f) := by
  rw [MonoidHom.one_apply, Units.val_one, one_smul]
  have hjc : IsClosedSubgroup (lQ ≫ q) := hlQ.isClosedSubgroup.comp hq.isClosedSubgroup
  have : IsClosedImmersion (lQ ≫ q).hom.hom.left := hjc
  have : Mono (lQ ≫ q).hom.hom := Over.mono_of_mono_left _
  obtain ⟨hNL₂, hprod₂, -⟩ := nestedParabolicPointDecomposition k G hG P₂ M N₂ Q L U P₂' N₂'
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂'
    hPQ₂ hM₂ (by rw [inf_comm]; exact hPL₂)
  have hN₂ : pointImage (r₂' ≫ p₂' ≫ lQ ≫ q) = pointImage (lQ ≫ q) ⊓ pointImage (r₂ ≫ p₂) :=
    hNL₂
  have hprod : (pointImage (r₂ ≫ p₂) : Set (rationalPoints G)) =
      ((pointImage (lQ ≫ q) ⊓ pointImage (r₂ ≫ p₂) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) * (pointImage (rQ ≫ q) : Set (rationalPoints G)) := hprod₂
  have hn : (n : rationalPoints G) ∈
      ((pointImage (lQ ≫ q) ⊓ pointImage (r₂ ≫ p₂) : Subgroup (rationalPoints G)) :
        Set (rationalPoints G)) * (pointImage (rQ ≫ q) : Set (rationalPoints G)) := by
    rw [← hprod]
    exact n.2
  obtain ⟨y, hy, w, hw, hyw⟩ := Set.mem_mul.mp hn
  obtain ⟨y', rfl⟩ := hy.1
  have hy' : y' ∈ pointImage (r₂' ≫ p₂') := by
    apply mem_pointImage_of_map_mem_comp (j := lQ ≫ q)
    rw [Category.assoc, hN₂]
    exact hy
  have hrep : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation n f =
      ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
        (rationalPoints.map (lQ ≫ q) y')
        (((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation w f) := by
    rw [← hyw, map_mul]
    rfl
  rw [hrep, innerStageRestriction_levi hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ _ y',
    innerStageRestriction_unipotent hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f w hw]
  have hc1 : innerLeviHalfModulus q lQ rQ hq hlQ hrQ hmulQ y' = 1 :=
    halfModulus_eq_one_of_mem_innerRadical q lQ rQ hq hlQ hrQ hmulQ p₂' r₂'
      hp₂'.isClosedSubgroup hr₂' hy'
  rw [hc1, Units.val_one, one_smul]
  have h := Jacquet.Localization.mk_apply_subgroup
    ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ).representation
    (pointImage (r₂' ≫ p₂')) 1 ⟨y', hy'⟩
    (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ f)
  rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
  exact h

/-- Renard's map `r_{P₂}(i_{P₁}σ) → r_{P₂'}(i_{P₁'}σ)` induced by `T` on coinvariants:
`[f] ↦ [T f]`. -/
def innerStageJacquetMap (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    Jacquet.Localization.Coinvariants
        ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
        (pointImage (r₂ ≫ p₂)) 1 →ₗ[ℂ]
      Jacquet.Localization.Coinvariants
        ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ).representation
        (pointImage (r₂' ≫ p₂')) 1 :=
  Jacquet.Localization.lift _ _ 1
    (Jacquet.Localization.mk _ _ 1 ∘ₗ
      innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ)
    (innerStageRestriction_descends hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
      q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁'
      p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ)

/-- Linear algebra behind the compatibility of `T̄` with the actions of `M(F)`. -/
theorem smul_mk_transfer {V₁ V₂ W₁ W₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂]
    (mk₁ : V₁ →ₗ[ℂ] W₁) (mk₂ : V₂ →ₗ[ℂ] W₂) (Tb : W₁ →ₗ[ℂ] W₂) (T : V₁ →ₗ[ℂ] V₂)
    (hTb : ∀ v, Tb (mk₁ v) = mk₂ (T v)) (a b c : ℂ) (x x' : V₁) (y : V₂)
    (hx : x = x') (hT : T x' = b • y) (habc : a * b = c) :
    Tb (a • mk₁ x) = c • mk₂ y := by
  rw [map_smul, hTb, hx, hT, map_smul, smul_smul, habc]


variable {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)

include hG hp₂ hl₂ hr₂ hmul₂ hq hlQ hrQ hmulQ hp₂' hl₂' hr₂' hmul₂' hPQ₁ hPQ₂ hM₁ hM₂ hPL₁ hPL₂ in
/-- Renard's inclusion `I^{P₁P₂}_σ ⊆ I^{P₁'P₂'}_σ`: the map `[f] ↦ [T f]` is a surjection
`r_{P₂} i_{P₁}(σ) → r_{P₂'} i_{P₁'}(σ)` commuting with `M(F)` and carrying `F^{<1̄}_{P₁P₂}` into
`F^{<1̄}_{P₁'P₂'}`. -/
theorem innerLevi_pqRegularityKernel_le (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    pqRegularityKernel p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ ≤
      pqRegularityKernel p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁' p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂'
        a σ := by
  have hcomp : ∀ x : rationalPoints M, rationalPoints.map (l₂ ≫ p₂) x =
      rationalPoints.map (lQ ≫ q) (rationalPoints.map (l₂' ≫ p₂') x) := by
    intro x
    rw [← hM₂]
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have hsurj : Function.Surjective (innerStageJacquetMap hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
      hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ) := by
    intro w
    obtain ⟨v', rfl⟩ := Jacquet.Localization.mk_surjective
      ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ).representation
      (pointImage (r₂' ≫ p₂')) 1 w
    obtain ⟨v, rfl⟩ := innerStageRestriction_surjective hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      q lQ rQ hq hlQ hrQ hmulQ hPQ₁ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ v'
    exact ⟨Jacquet.Localization.mk _ _ 1 v, rfl⟩
  have hcomm : ∀ (m : rationalPoints M)
      (x : Jacquet.Localization.Coinvariants
        ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
        (pointImage (r₂ ≫ p₂)) 1),
      innerStageJacquetMap hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
        p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
        hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ
        (((leviJacquetInductionFunctor.{u, v} p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁
          p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).ρ m x) =
      ((leviJacquetInductionFunctor.{u, v} p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁'
          p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂').obj σ).ρ m
        (innerStageJacquetMap hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
          p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
          hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ x) := by
    intro m x
    obtain ⟨v, rfl⟩ := Jacquet.Localization.mk_surjective
      ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
      (pointImage (r₂ ≫ p₂)) 1 x
    exact smul_mk_transfer
      (Jacquet.Localization.mk
        ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
        (pointImage (r₂ ≫ p₂)) 1)
      (Jacquet.Localization.mk
        ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ).representation
        (pointImage (r₂' ≫ p₂')) 1)
      (innerStageJacquetMap hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
        p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
        hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ)
      (innerStageRestriction hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ)
      (fun _ => rfl) _ _ _ _ _ _
      (congrArg (fun g => ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ).representation
        g v) (hcomp m))
      (innerStageRestriction_levi hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ hPQ₁
        p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hM₁ hPL₁ σ v (rationalPoints.map (l₂' ≫ p₂') m))
      (innerLevi_inverseHalfModulus_mul hG p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ
        hPQ₂ p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₂ hPL₂ m)
  have hTS : ((boundarySupportImage p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
        (identityParabolicDoubleCoset p₁ p₂)).obj σ).toSubmodule ≤
      (((boundarySupportImage p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁' p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂'
        (identityParabolicDoubleCoset p₁' p₂')).obj σ).toSubmodule).comap
        (innerStageJacquetMap hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
          p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
          hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ) := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨_, innerStageRestriction_mem_boundary hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
      hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ σ v hv, rfl⟩
  exact groupAlgebraKernel_quotient_le _ _ (rationalPoints.map a) _ _ _ _ _ hsurj hTS
    (fun b x => hcomm _ x)

include hG hp₂ hl₂ hr₂ hmul₂ hq hlQ hrQ hmulQ hp₂' hl₂' hr₂' hmul₂' hPQ₁ hPQ₂ hM₁ hM₂ hPL₁ hPL₂ in
/-- Renard VII.3.5 (ii), regularity: `P₁P₂`-regularity of `σ` implies `P₁'P₂'`-regularity. -/
theorem innerLevi_isPQRegular (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (h : IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ) :
    IsPQRegular p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁' p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂' a σ := by
  unfold IsPQRegular at h ⊢
  rw [eq_top_iff] at h ⊢
  exact h.trans (sup_le_sup le_rfl (innerLevi_pqRegularityKernel_le hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
    p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁'
    hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ a σ))

end Langlands.Aubert.General.RepresentedParabolic
