import Langlands.Representation.LanglandsClassification.PQRegularIntertwiningDimension
import Langlands.Representation.Intertwining.PQIdentitySupportProof

/-! # A nonzero intertwiner from `PQ`-regularity -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- For represented parabolics `P = MN` and `Q = MU` with the same Levi subgroup and a
nonzero smooth representation `σ` of `M(F)` that is `PQ`-regular for a split component,
some morphism `i_P^G(σ) ⟶ i_Q^G(σ)` is nonzero (Renard VII.3.4). -/
theorem exists_ne_zero_of_isPQRegular
    (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N Q U : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r))
      (q : Q ⟶ G) (lQ : M ⟶ Q) (rQ : U ⟶ Q)
      (hq : IsParabolicSubgroup q) (hlQ : IsRationalLeviSubgroup lQ)
      (hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
      (hmulQ : IsIso (subgroupMultiplication lQ rQ)),
      l ≫ p = lQ ≫ q →
      ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (a : A.toGrp ⟶ M),
        IsSplitComponent a →
        letI := leviPointTopology l hl
        ∀ (σ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), Nontrivial σ →
          IsPQRegular p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ a σ →
          ∃ f : (leviInductionFunctor.{u, v} p l r hp hr hl hmul).obj σ ⟶
              (leviInductionFunctor.{u, v} q lQ rQ hq hrQ hlQ hmulQ).obj σ,
            f ≠ 0 := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M N Q U p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame A a ha
  let := leviPointTopology l hl
  intro σ hσ hreg
  obtain ⟨e, -⟩ := (pqSupportGraded.{u, v} k G hG P M N Q U
    p l r hp hl hr hmul q lQ rQ hq hlQ hrQ hmulQ hsame).2
  let S := closureSupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)
  let T := boundarySupportImage.{u, v} p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ
    (identityParabolicDoubleCoset p q)
  let ψ : (T.obj σ).toRepresentation.IntertwiningMap σ.representation :=
    (e σ).toIntertwiningMap.comp (S.quotientProjection T σ).hom
  have hψsurj : Function.Surjective ψ :=
    (e σ).surjective.comp (S.quotientProjection_surjective T σ)
  have hψ : ψ ≠ 0 := by
    intro h0
    obtain ⟨v, hv⟩ := exists_ne (0 : σ)
    obtain ⟨x, hx⟩ := hψsurj v
    apply hv
    rw [← hx, h0]
    rfl
  let E := pqRegularIntertwiningRestrictionEquiv hG p l r hp hl hr hmul q lQ rQ hq hlQ
    hrQ hmulQ a ha σ hreg
  refine ⟨SmoothRep.ofHom (E.symm ψ), ?_⟩
  intro h0
  apply hψ
  have h1 : E.symm ψ = 0 := by
    have h2 := congrArg SmoothRep.hom h0
    rw [SmoothRep.hom_ofHom] at h2
    rw [h2]
    rfl
  simpa using congrArg E h1

end Langlands.Aubert.General.RepresentedParabolic
