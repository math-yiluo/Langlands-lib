import Langlands.Representation.Intertwining.InnerLeviBoundaryTransfer
import Langlands.Representation.Intertwining.LeviInductionStagesFormula
import Langlands.Representation.Intertwining.PQIntegralUniqueness
import Langlands.Representation.Intertwining.HaarTransportComparison

/-! # The operator identity of Renard VII.3.5 (ii)

For represented parabolics `P₁ = MN₁`, `P₂ = MN₂` of `G` inside `Q = LU`, with traces
`P₁' = MN₁'`, `P₂' = MN₂'` in `L`, an integral-normalized operator `J' = J^L_{P₂'|P₁'}(σ)` on
`V' ⊂ N₂'(F)` induces `K = Ψ₂⁻¹ ∘ i_Q^G(J') ∘ Ψ₁ : i_{P₁}^G(σ) → i_{P₂}^G(σ)`, where `Ψᵢ` is
induction in stages. When `V'` is carried onto `V` by the point map `L(F) → G(F)` and the Haar
measure on `V` is the image of the one on `V'`, the operator `K` satisfies the integral formula
on `V`; for `P₁P₂`-regular `σ` it is therefore the integral-normalized `J^G_{P₂|P₁}(σ)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G M P₁ N₁ P₂ N₂ Q L U P₁' N₁' P₂' N₂' : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom L.X.hom] [IsAffineHom M.X.hom]

local instance operatorAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

local instance operatorInnerPointTopology : TopologicalSpace (rationalPoints L) :=
  RationalPointFamily.pointTopology

local instance operatorLeviPointTopology : TopologicalSpace (rationalPoints M) :=
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

include hG r₂ hp₂ hl₂ hr₂ hmul₂ rQ hq hlQ hrQ hmulQ r₂' hp₂' hl₂' hr₂' hmul₂'
  hPQ₁ hPQ₂ hM₁ hM₂ hPL₁ hPL₂ in
/-- Renard VII.3.5 (ii): a function `φ` of `i_{P₁'}^L(σ)` vanishing wherever
`x ↦ f(emb x)` vanishes, for `f ∈ F̃^{<1̄}_{P₁P₂}(σ)`, lies in `F̃^{<1̄}_{P₁'P₂'}(σ)`. -/
theorem mem_innerBoundaryVanishing_of_map
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
    (φ : (leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ)
    (hf : f ∈ (boundaryVanishingSubfunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂
      (identityParabolicDoubleCoset p₁ p₂)).obj σ)
    (hφ : ∀ x : rationalPoints L,
      Induction.eval (pointImage p₁)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
            (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f
          (rationalPoints.map (lQ ≫ q) x) = 0 →
        Induction.eval (pointImage p₁')
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p₁' l₁' r₁' hp₁'.isClosedSubgroup hr₁'
              hmul₁')
            (isClosed_pointImage_comp p₁' r₁' hp₁'.isClosedSubgroup hr₁'.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p₁' l₁' hp₁' hl₁').symm σ)) φ x = 0) :
    φ ∈ (boundaryVanishingSubfunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁' p₂'
      (identityParabolicDoubleCoset p₁' p₂')).obj σ := by
  apply (Geometric.mem_rawSmoothVanishingSubfunctor_iff _ _ _
    (Geometric.boundary_doubleCoset_mul_mem _ _ _) _ φ).mpr
  intro x hx
  apply hφ
  exact (Geometric.mem_rawSmoothVanishingSubfunctor_iff _ _ _
    (Geometric.boundary_doubleCoset_mul_mem _ _ _) _ f).mp hf _
    (map_mem_identityBoundary hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂
      q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁'
      p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂ x hx)

include hG hPQ₁ hPQ₂ hM₁ hM₂ hPL₁ hPL₂ in
/-- Renard VII.3.5 (ii), operator identity. Let `V ⊂ G(F)` and `V' ⊂ N₂'(F)` be subgroups
carried onto each other by the point map `emb` (through `e`), with `haar = e_* haar'`. If
`J = J^G_{P₂|P₁}(σ)` on `V` and `J' = J^L_{P₂'|P₁'}(σ)` on `V'` are integral-normalized and
`σ` is `P₁P₂`-regular, then `J'(f̃(g))(x) = c(x)⁻¹ J(f)(emb(x) g)` whenever
`f̃(g)(x) = c(x)⁻¹ f(emb(x) g)` for all `g`, `x`. -/
theorem innerLevi_integralIntertwiner_formula
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M) (ha : IsSplitComponent a)
    (V : Subgroup (rationalPoints G)) (V' : Subgroup (rationalPoints L))
    [MeasurableSpace V] [BorelSpace V] [MeasurableSpace V'] [BorelSpace V']
    (hV' : V' ≤ pointImage (r₂' ≫ p₂'))
    (e : V' ≃ₜ* V) (he : ∀ x : V', (e x : rationalPoints G) = rationalPoints.map (lQ ≫ q) x)
    (haar' : Measure V') (haar : Measure V) (hhaar : haar = haar'.map e)
    (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hreg : IsPQRegular p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ a σ)
    (J : ((leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj
          σ).representation.IntertwiningMap
        ((leviInductionFunctor p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂).obj σ).representation)
    (J' : ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj
          σ).representation.IntertwiningMap
        ((leviInductionFunctor p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂').obj σ).representation)
    (hJ : IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
      V haar σ J)
    (hJ' : IsIntegralIntertwiner p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁'
      p₂' l₂' r₂' hp₂' hr₂' hl₂' hmul₂' V' haar' σ J')
    (f : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
    (F : (leviInductionFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ).obj
      ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ))
    (hF : ∀ (g : rationalPoints G) (x : rationalPoints L),
      Induction.eval (pointImage p₁')
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p₁' l₁' r₁' hp₁'.isClosedSubgroup hr₁'
              hmul₁')
            (isClosed_pointImage_comp p₁' r₁' hp₁'.isClosedSubgroup hr₁'.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p₁' l₁' hp₁' hl₁').symm σ))
          (Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
              (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
                ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ))) F g) x =
        (((HaarModulus.closedHalfCharacter (pointImage (rQ ≫ q))
            (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
            (pointImage q)
            (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ
              hmulQ).le_normalizer
            (Subgroup.inclusion (pointImage_comp_le q lQ) (leviPointsEquiv q lQ hq hlQ x)) :
              ℂˣ) : ℂ))⁻¹ •
          Induction.eval (pointImage p₁)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage p₁ l₁ r₁ hp₁.isClosedSubgroup hr₁ hmul₁)
              (isClosed_pointImage_comp p₁ r₁ hp₁.isClosedSubgroup hr₁.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv p₁ l₁ hp₁ hl₁).symm σ)) f
            (rationalPoints.map (lQ ≫ q) x * g))
    (g : rationalPoints G) (x : rationalPoints L) :
    Induction.eval (pointImage p₂')
        (inducingRepresentation
          (isSemidirectDecomposition_pointImage p₂' l₂' r₂' hp₂'.isClosedSubgroup hr₂' hmul₂')
          (isClosed_pointImage_comp p₂' r₂' hp₂'.isClosedSubgroup hr₂'.1.isClosedSubgroup)
          (SmoothRep.pullback (leviPointsEquiv p₂' l₂' hp₂' hl₂').symm σ))
        (J' (Induction.eval (pointImage q)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
            (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
              ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ))) F g)) x =
      (((HaarModulus.closedHalfCharacter (pointImage (rQ ≫ q))
          (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
          (pointImage q)
          (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ
            hmulQ).le_normalizer
          (Subgroup.inclusion (pointImage_comp_le q lQ) (leviPointsEquiv q lQ hq hlQ x)) :
            ℂˣ) : ℂ))⁻¹ •
        Induction.eval (pointImage p₂)
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂)
            (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm σ)) (J f)
          (rationalPoints.map (lQ ≫ q) x * g) := by
  let Ψ₁ := leviInductionStagesIso p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ hmulQ
    p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG
  let Ψ₂ := leviInductionStagesIso p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ
    p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hPQ₂ hM₂ (hPL₂.trans (inf_comm _ _)) hG
  let IQ := leviInductionFunctor.{u, max u v} q lQ rQ hq hrQ hlQ hmulQ
  let K := Ψ₁.hom.app σ ≫ IQ.map (SmoothRep.ofHom J') ≫ Ψ₂.inv.app σ
  have hK : K ≫ Ψ₂.hom.app σ = Ψ₁.hom.app σ ≫ IQ.map (SmoothRep.ofHom J') := by
    simp only [K, Category.assoc, Iso.inv_hom_id_app]
    exact congrArg (Ψ₁.hom.app σ ≫ ·) (Category.comp_id _)
  -- the stage formula for `K`
  have hstar : ∀ (f₀ : (leviInductionFunctor p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁).obj σ)
      (g : rationalPoints G) (x : rationalPoints L),
      Induction.eval (pointImage p₂')
          (inducingRepresentation
            (isSemidirectDecomposition_pointImage p₂' l₂' r₂' hp₂'.isClosedSubgroup hr₂'
              hmul₂')
            (isClosed_pointImage_comp p₂' r₂' hp₂'.isClosedSubgroup hr₂'.1.isClosedSubgroup)
            (SmoothRep.pullback (leviPointsEquiv p₂' l₂' hp₂' hl₂').symm σ))
          (J' (Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
              (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
                ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ)))
            (SmoothRep.hom (Ψ₁.hom.app σ) f₀) g)) x =
        (((HaarModulus.closedHalfCharacter (pointImage (rQ ≫ q))
            (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
            (pointImage q)
            (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ
              hmulQ).le_normalizer
            (Subgroup.inclusion (pointImage_comp_le q lQ) (leviPointsEquiv q lQ hq hlQ x)) :
              ℂˣ) : ℂ))⁻¹ •
          Induction.eval (pointImage p₂)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage p₂ l₂ r₂ hp₂.isClosedSubgroup hr₂ hmul₂)
              (isClosed_pointImage_comp p₂ r₂ hp₂.isClosedSubgroup hr₂.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv p₂ l₂ hp₂ hl₂).symm σ))
            (SmoothRep.hom K f₀) (rationalPoints.map (lQ ≫ q) x * g) := by
    intro f₀ g x
    have h2 := leviInductionStagesIso_eval' p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ
      p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hPQ₂ hM₂ (hPL₂.trans (inf_comm _ _)) hG σ
      (SmoothRep.hom K f₀) g x
    have h3 : SmoothRep.hom (Ψ₂.hom.app σ) (SmoothRep.hom K f₀) =
        SmoothRep.hom (IQ.map (SmoothRep.ofHom J')) (SmoothRep.hom (Ψ₁.hom.app σ) f₀) :=
      congrArg (fun φ => SmoothRep.hom φ f₀) hK
    rw [h3] at h2
    exact h2
  -- the half modulus is trivial on `N₂'(F) ⊇ V'`
  have hc := fun (y : rationalPoints L) (hy : y ∈ pointImage (r₂' ≫ p₂')) =>
    halfModulus_eq_one_of_mem_innerRadical q lQ rQ hq hlQ hrQ hmulQ p₂' r₂'
      hp₂'.isClosedSubgroup hr₂' hy
  -- `K` satisfies the integral formula on `V`
  have hKint : IsIntegralIntertwiner p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂
      V haar σ (SmoothRep.hom K) := by
    intro f₀ hf₀ ℓ
    let φ := Induction.eval (pointImage q)
      (inducingRepresentation
        (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
        (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
        (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm
          ((leviInductionFunctor p₁' l₁' r₁' hp₁' hr₁' hl₁' hmul₁').obj σ)))
      (SmoothRep.hom (Ψ₁.hom.app σ) f₀) 1
    have hφmem := mem_innerBoundaryVanishing_of_map hG p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
      p₂ l₂ r₂ hp₂ hl₂ hr₂ hmul₂ q lQ rQ hq hlQ hrQ hmulQ hPQ₁ hPQ₂
      p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' p₂' l₂' r₂' hp₂' hl₂' hr₂' hmul₂' hM₁ hM₂ hPL₁ hPL₂
      σ f₀ φ hf₀ (fun y hy => by
        have h := leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ
          hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG σ
          f₀ 1 y
        rw [mul_one, hy, smul_zero] at h
        exact h)
    obtain ⟨hint', hval'⟩ := hJ' φ hφmem ℓ
    have h1 := hstar f₀ 1 1
    rw [hc 1 (one_mem _), map_one, one_mul, Units.val_one, inv_one, one_smul] at h1
    subst hhaar
    refine ⟨?_, ?_⟩
    · refine (integrable_map_equiv e.toHomeomorph.toMeasurableEquiv _).mpr ?_
      convert hint' using 1
      funext y
      have h := leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ
        hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG σ
        f₀ 1 y
      rw [mul_one, hc _ (hV' y.2), Units.val_one, inv_one, one_smul, ← he y] at h
      exact congrArg ℓ h.symm
    · rw [integral_map_continuousMulEquiv]
      refine (congrArg ℓ h1).symm.trans (hval'.trans ?_)
      congr 1
      funext y
      have h := leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁ q lQ rQ hq hlQ hrQ
        hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁ (hPL₁.trans (inf_comm _ _)) hG σ
        f₀ 1 y
      rw [mul_one, hc _ (hV' y.2), Units.val_one, inv_one, one_smul, ← he y] at h
      exact congrArg ℓ h
  have hJK : J = SmoothRep.hom K :=
    integralIntertwiner_unique p₁ l₁ r₁ hp₁ hr₁ hl₁ hmul₁ p₂ l₂ r₂ hp₂ hr₂ hl₂ hmul₂ hG a ha σ
      hreg V haar J (SmoothRep.hom K) hJ hKint
  have hFeq : F = SmoothRep.hom (Ψ₁.hom.app σ) f :=
    leviInductionStages_ext q lQ rQ hq hlQ hrQ hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' σ F _
      (fun g x => (hF g x).trans (leviInductionStagesIso_eval' p₁ l₁ r₁ hp₁ hl₁ hr₁ hmul₁
        q lQ rQ hq hlQ hrQ hmulQ p₁' l₁' r₁' hp₁' hl₁' hr₁' hmul₁' hPQ₁ hM₁
        (hPL₁.trans (inf_comm _ _)) hG σ f g x).symm)
  subst hFeq
  rw [hJK]
  exact hstar f g x

end Langlands.Aubert.General.RepresentedParabolic
