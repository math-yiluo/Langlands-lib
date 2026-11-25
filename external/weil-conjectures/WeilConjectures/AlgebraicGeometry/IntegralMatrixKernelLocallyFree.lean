/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
import all WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels

/-! # Integral matrix kernels with locally free rational cokernel -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev LocalFree {X : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) : Prop :=
  ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
    Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod R).obj M)

private theorem localFree_of_free {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (h : Mod.IsFree R M) : IsLocallyFree R M := by
  exact ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ free_pullback _ h⟩

private theorem localFree_of_cover {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [IsCommMonObj R]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R}
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ i, IsLocallyFree ((ProEtale.upperStar Ab.{u + 1} (C.f i)).obj R)
      (((ProEtale.upperStar Ab.{u + 1} (C.f i)).mapMod R).obj M)) : IsLocallyFree R M := by
  choose V hV using h
  refine ⟨C.bind V, fun ij ↦ ?_⟩
  rcases ij with ⟨i, j⟩
  exact (free_pullback_comp_iff ((V i).f j) (C.f i) M).mpr (hV i j)

private theorem localFree_of_comap {X : Scheme.{u}}
    {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (h : IsLocallyFree R ((Mod.comap φ).obj M)) : IsLocallyFree S M := by
  exact locally_free_of_iso (locally_free_comap (inv φ) h)
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.app M).symm

/-- A map of finite free integral modules whose rational cokernel is locally free
has locally free integral kernel.
Source: Bhatt--Scholze, Section 6.8; the continuous matrix pivot construction.
(auxiliary; not a blueprint node)
Proof. Induct on the source rank using integralMatrix_pivot_cover. On a zero-matrix
piece the kernel is the source. On a nonzero piece, the monic pivot identifies the
kernel with the kernel of the smaller Schur complement. After rationalization the
pivot is invertible, so its cokernel agrees with that of the Schur complement.
Thus the smaller matrix satisfies the same rational-cokernel hypothesis. Apply
induction, transport across the kernel isomorphism, undo coefficient normalization,
and compose the resulting pro-etale covers. Rank zero and empty pieces are included. -/
theorem integralMatrixKernel_locallyFree (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u})
    (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B)
    (hA : Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) A)
    (hB : Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B)
    (hLF : IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X)
      ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj (cokernel a))) :
    IsLocallyFree (condensedRingObj (integralCoeff ℓ E) X) (kernel a) := by
  have H (n : ℕ) : ∀ (X : Scheme.{u})
      (A B : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (integralCoeff ℓ E) X)) (a : A ⟶ B),
      Nonempty (A ≅ Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n) →
      Mod.IsFree (condensedRingObj (integralCoeff ℓ E) X) B →
      IsLocallyFree (condensedRingObj (Profinite.continuousMapRingObj E) X)
        ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj (cokernel a)) →
      IsLocallyFree (condensedRingObj (integralCoeff ℓ E) X) (kernel a) := by
    induction n using Nat.strong_induction_on with
    | h n IH =>
      intro X A B a hA hB hLF
      obtain ⟨V, hV⟩ := integralMatrix_pivot_cover ℓ E n X A B a hA hB hLF
      apply localFree_of_cover V
      intro k
      let R := condensedRingObj (integralCoeff ℓ E) X
      let R' := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let F := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod R
      let α := condensedPullbackHom (integralCoeff ℓ E) (V.f k)
      let J := Mod.comap (D := Sheaf (Scheme.ProEt.topology (V.X k)) Ab.{u + 1}) (inv α)
      let T := F ⋙ J
      have hT : IsLocallyFree R' (kernel (T.map a)) := by
        rcases hV k with hz | ⟨m, hmn, A₁, B₁, iA, hB₁, p, hp, hunit, r, c, d, eA, eB, he⟩
        · rw [show T.map a = 0 from hz]
          exact locally_free_of_iso (localFree_of_free
            (free_comap (inv α) (free_pullback (V.f k) ⟨n, hA⟩)))
            kernelZeroIsoSource.symm
        · let _ := hp
          let b := biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc c d)
          let e : kernel (T.map a) ≅ kernel b :=
            kernel.mapIso (T.map a) b eA eB (by
              dsimp only [b]
              rw [← he]
              simp only [Iso.hom_inv_id_assoc]
              rfl)
          let L := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) (V.X k))
          have : IsIso (L.map p) := hunit
          let eC : cokernel (T.map a) ≅ cokernel b :=
            cokernel.mapIso (T.map a) b eA eB (by
              dsimp only [b]
              rw [← he]
              simp only [Iso.hom_inv_id_assoc]
              rfl)
          let eS := L.mapIso eC ≪≫ mappedPivotCokernelIso L p r c d
          have hS : RationalCokernelFree ℓ E (d - r ≫ c) :=
            locally_free_of_iso (rationalCokernelFree_pullback ℓ E (V.f k) a hLF) eS
          have hK := IH m hmn (V.X k) A₁ B₁ (d - r ≫ c) ⟨iA⟩ hB₁ hS
          exact locally_free_of_iso hK ((pivotKernelIso p r c d).symm ≪≫ e.symm)
      have hJ := locally_free_of_iso hT (PreservesKernel.iso J (F.map a)).symm
      have hF := localFree_of_comap (inv α) hJ
      exact locally_free_of_iso hF (PreservesKernel.iso F a).symm
  obtain ⟨n, hn⟩ := hA
  exact H n X A B a hn hB hLF

/-- The kernel is locally free when the rationalized matrix is surjective.
Source: the preceding pivot induction, with zero rational cokernel.
(auxiliary; not a blueprint node) -/
theorem integralMatrixKernel_locallyFree_of_rational_epi
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (n m : ℕ)
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) m)
    [Epi ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).map f)] :
    IsLocallyFree (condensedRingObj (integralCoeff ℓ E) X) (kernel f) := by
  let L := Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  have hQ : IsZero (L.obj (cokernel f)) :=
    (isZero_cokernel_of_epi (L.map f)).of_iso (PreservesCokernel.iso L f)
  have hzero : IsZero (Mod.finiteFree S 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply biproduct.hom_ext
    intro j
    exact Fin.elim0 j
  have hfree : Mod.IsFree S (L.obj (cokernel f)) := ⟨0, ⟨hQ.iso hzero⟩⟩
  exact integralMatrixKernel_locallyFree ℓ E X _ _ f
    ⟨n, ⟨Iso.refl _⟩⟩ ⟨m, ⟨Iso.refl _⟩⟩ (localFree_of_free hfree)

end AlgebraicGeometry.ProEtale.CondensedRing
