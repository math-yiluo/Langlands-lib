import Langlands.Representation.Intertwining.PQIntegralIntertwiningStatements
import Langlands.Representation.Intertwining.PQIntertwiningOperatorProof

/-! # Uniqueness of integral-normalized intertwining operators

For a `PQ`-regular representation `σ`, an intertwining operator `i_P^G(σ) → i_Q^G(σ)` is
determined by the values `J(f)(1)` for `f ∈ F̃^{<1̄}_{PQ}(σ)`. In particular two operators
satisfying the integral formula `IsIntegralIntertwiner` for the same measure agree.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance uniquenessAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q U : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
  (hp : IsParabolicSubgroup p) (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hl : IsRationalLeviSubgroup l) (hmul : IsIso (subgroupMultiplication l r))
  (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
  (hq : IsParabolicSubgroup q) (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
  (hlQ : IsRationalLeviSubgroup lQ) (hmulQ : IsIso (subgroupMultiplication lQ rQ))

/-- For `PQ`-regular `σ`, two intertwining operators `i_P^G(σ) → i_Q^G(σ)` with the same
values at `1` on `F̃^{<1̄}_{PQ}(σ)` are equal. -/
theorem intertwiner_eq_of_eval_one_eq (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
    (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)
    (J₁ J₂ : letI := leviPointTopology l hl
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
        ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation)
    (h : letI := leviPointTopology l hl
      ∀ f : (leviInductionFunctor p l r hp hr hl hmul).obj σ,
        f ∈ (boundaryVanishingSubfunctor p l r hp hr hl hmul q
          (identityParabolicDoubleCoset p q)).obj σ →
        Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
              (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ)) (J₁ f) 1 =
          Induction.eval (pointImage q)
            (inducingRepresentation
              (isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ)
              (isClosed_pointImage_comp q rQ hq.isClosedSubgroup hrQ.1.isClosedSubgroup)
              (SmoothRep.pullback (leviPointsEquiv q lQ hq hlQ).symm σ)) (J₂ f) 1) :
    J₁ = J₂ := by
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  let I := (leviInductionFunctor p l r hp hr hl hmul).obj σ
  let R := (leviJacquetInductionFunctor.{u, v} p l r hp hr hl hmul
    q lQ rQ hq hrQ hlQ hmulQ).obj σ
  let T := boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)
  obtain ⟨F, hF⟩ := leviFrobeniusReciprocity k G hG Q M U q lQ rQ hq hlQ hrQ hmulQ I σ
  change _ ≃ₗ[ℂ] R.ρ.IntertwiningMap σ.representation at F
  let qT : (T.obj σ).toRepresentation.IntertwiningMap σ.representation :=
    { toLinearMap := (F J₁).toLinearMap.comp (T.obj σ).toSubmodule.subtype
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        exact Representation.IntertwiningMap.isIntertwining _ _ (F J₁) g (x : R) }
  obtain ⟨K, -, hunique⟩ := existsUnique_intertwining_extension
    (ρ := R.ρ) (rationalPoints.map a)
    ha.isCentralSplitTorus.isCentral.map_mem_center (T.obj σ) qT hreg
  have h₁ : F J₁ = K := hunique _ (fun _ => rfl)
  have h₂ : F J₂ = K := by
    apply hunique
    intro x
    obtain ⟨f, hf, hfx⟩ := x.property
    change F J₂ (x : R) = F J₁ (x : R)
    rw [← hfx]
    exact (hF J₂ f).trans ((h f hf).symm.trans (hF J₁ f).symm)
  exact F.injective (h₁.trans h₂.symm)

/-- Two operators satisfying the integral formula for the same measure on the same subgroup
agree, for `PQ`-regular `σ`. -/
theorem integralIntertwiner_unique (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (a : A.toGrp ⟶ M)
    (ha : IsSplitComponent a)
    (σ : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M))
    (hreg : IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ)
    (V : Subgroup (rationalPoints G)) [MeasurableSpace V] (haar : Measure V)
    (J₁ J₂ : letI := leviPointTopology l hl
      ((leviInductionFunctor p l r hp hr hl hmul).obj σ).representation.IntertwiningMap
        ((leviInductionFunctor q lQ rQ hq hrQ hlQ hmulQ).obj σ).representation)
    (h₁ : IsIntegralIntertwiner p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ V haar σ J₁)
    (h₂ : IsIntegralIntertwiner p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ V haar σ J₂) :
    J₁ = J₂ := by
  apply intertwiner_eq_of_eval_one_eq p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ hG a ha σ
    hreg J₁ J₂
  intro f hf
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  rw [map_sub]
  exact sub_eq_zero.mpr ((h₁ f hf ℓ).2.trans (h₂ f hf ℓ).2.symm)

end Langlands.Aubert.General.RepresentedParabolic
