import Langlands.Representation.Aubert.General.CuspidalRemainderTransport
import Langlands.Representation.Exponents.LeviSecondAdjointnessStatement

/-! # Second adjointness on Levi points from the literal Levi image

Renard 2026, VI.9.6 Theorem (VI.9.6.1) (printed p.201, PDF p.207), transport step for
represented parabolics. Let `P = MN` and `P̄ = M N̄` be represented parabolics with
`mbar ≫ pbar = m ≫ p`. An adjunction `i_N ⊣ r_{N̄}` between normalized induction from, and
normalized Jacquet restriction to, smooth representations of the literal Levi image
`pointImage (m ≫ p)` gives the adjunction of `LeviSecondAdjointnessStatement` between the
functors on smooth representations of `M(F)` itself.
-/

noncomputable section

universe u v uG uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

section Transport

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {H : Type uG} [Group H] [TopologicalSpace H]

/-- Transport of a second adjunction along Levi identifications. Let `P = M₁ ⋉ U` and let
`Ū` be a closed subgroup normalized by `M₁ = M₂`. Suppose that normalized induction
`i_U` from `M₁` is left adjoint to the normalized Jacquet functor `r_{Ū}` to `M₁`. Let
`e₁ : H ≃ₜ* M₁` and `e₂ : H ≃ₜ* M₂` have the same values in `G`. Then
`A ↦ i_U((e₁⁻¹)^* A)` is left adjoint to `π ↦ e₂^*(r_{Ū} π)`. -/
theorem nonempty_pullback_induction_jacquet_adjunction
    {P M₁ M₂ U : Subgroup G} (Ubar : Subgroup G) (hM : M₁ = M₂)
    (h : IsSemidirectDecomposition P M₁ U) (hU : IsClosed (U : Set G))
    (hUbar : IsClosed (Ubar : Set G)) (hMUbar₂ : M₂ ≤ Subgroup.normalizer (Ubar : Set G))
    (e₁ : H ≃ₜ* M₁) (e₂ : H ≃ₜ* M₂) (he : ∀ x, (e₁ x : G) = e₂ x)
    (hadj : ∀ hMUbar₁ : M₁ ≤ Subgroup.normalizer (Ubar : Set G),
      Nonempty (normalizedInductionFunctor.{uG, max uG uV} h hU ⊣
        normalizedJacquetFunctor.{uG, max uG uV} Ubar M₁ hUbar hMUbar₁)) :
    Nonempty (SmoothRep.pullbackFunctor.{uG, uG, max uG uV} e₁.symm ⋙
        normalizedInductionFunctor.{uG, max uG uV} h hU ⊣
      normalizedJacquetFunctor.{uG, max uG uV} Ubar M₂ hUbar hMUbar₂ ⋙
        SmoothRep.pullbackFunctor.{uG, uG, max uG uV} e₂) := by
  subst hM
  obtain rfl : e₁ = e₂ := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  obtain ⟨adj⟩ := hadj hMUbar₂
  exact ⟨(SmoothRep.pullbackEquivalence.{uG, uG, max uG uV} e₁).symm.toAdjunction.comp adj⟩

end Transport

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k] [T2Space k]
  {G P Pbar M N Nbar : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance secondAdjointnessTransportPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

/-- Second adjointness for represented parabolics from the literal Levi image: if
`mbar ≫ pbar = m ≫ p` and normalized induction `i_N` from smooth representations of
`pointImage (m ≫ p)` is left adjoint to the normalized Jacquet functor of the closed subgroup
`N̄(F) = pointImage (nbar ≫ pbar)` to smooth representations of `pointImage (m ≫ p)`, then
`i_P` is left adjoint to `r_{P̄}` as functors between smooth representations of `G(F)` and
of `M(F)`. -/
theorem nonempty_leviSecondAdjunction_of_pointImage
    (p : P ⟶ G) (m : M ⟶ P) (n : N ⟶ P)
    (hp : IsParabolicSubgroup p) (hm : IsRationalLeviSubgroup m)
    (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
    (hmul : IsIso (subgroupMultiplication m n))
    (pbar : Pbar ⟶ G) (mbar : M ⟶ Pbar) (nbar : Nbar ⟶ Pbar)
    (hpbar : IsParabolicSubgroup pbar) (hmbar : IsRationalLeviSubgroup mbar)
    (hnbar : LeviSubgroup.IsGeometricUnipotentRadical nbar)
    (hmulbar : IsIso (subgroupMultiplication mbar nbar))
    (hP : mbar ≫ pbar = m ≫ p)
    (hadj : ∀ (hUbar : IsClosed (pointImage (nbar ≫ pbar) : Set (rationalPoints G)))
      (hMUbar : pointImage (m ≫ p) ≤
        Subgroup.normalizer (pointImage (nbar ≫ pbar) : Set (rationalPoints G))),
      Nonempty (inductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
        normalizedJacquetFunctor.{u, max u v} (pointImage (nbar ≫ pbar)) (pointImage (m ≫ p))
          hUbar hMUbar)) :
    letI := leviPointTopology m hm
    Nonempty (leviInductionFunctor.{u, max u v} p m n hp hn hm hmul ⊣
      leviJacquetFunctor.{u, max u v} pbar mbar nbar hpbar hnbar hmbar hmulbar) := by
  let := leviPointTopology m hm
  have hUbar := isClosed_pointImage_comp pbar nbar hpbar.isClosedSubgroup
    hnbar.1.isClosedSubgroup
  exact nonempty_pullback_induction_jacquet_adjunction (pointImage (nbar ≫ pbar))
    (congrArg pointImage hP.symm)
    (isSemidirectDecomposition_pointImage p m n hp.isClosedSubgroup hn hmul)
    (isClosed_pointImage_comp p n hp.isClosedSubgroup hn.1.isClosedSubgroup) hUbar
    (pointImage_le_normalizer pbar mbar nbar hnbar)
    (leviPointsEquiv p m hp hm) (leviPointsEquiv pbar mbar hpbar hmbar)
    (fun x => by simp only [leviPointsEquiv_apply_coe, hP])
    (hadj hUbar)

end Langlands.Aubert.General.RepresentedParabolic
