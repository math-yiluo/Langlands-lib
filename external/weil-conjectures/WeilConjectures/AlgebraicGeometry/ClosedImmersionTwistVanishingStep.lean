/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.ClosedImmersionTwistAcyclicPresentation
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Cohomology.Exact
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # A step in projective Serre vanishing -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The descending Serre induction step, simultaneously for all coherent coefficients.
Source: Stacks Project, Tag 01YS (4), proof of part (4).
(blueprint: lem-pc-j4-closed-immersion-twist-vanishing-step)

Proof: Apply the hypothesis to the identity immersion of projective space. This gives
next-degree vanishing for every coherent ambient module, in particular the kernel of
a finite sum of twists surjecting onto i_*F. The kernel is coherent over the Noetherian
base. Tensor this exact sequence by the invertible O(t). For large t the finite sum
has zero positive-degree cohomology by the projective twist computation, and the
hypothesis kills the next-degree cohomology of the kernel. The long exact sequence
kills degree q of the twisted pushforward. The projection formula and the closed
immersion cohomology comparison transfer this vanishing to X. Take the maximum of
the two integer thresholds and zero to obtain a natural-number threshold. -/
theorem exists_isZero_closedImmersion_twist_of_next_degree
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (q : ℕ) (hq : 0 < q)
    (hnext : ∀ {Y : Scheme.{u}}
      (j : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion j]
      (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation],
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace (q + 1)).obj
          (tensorObj F (ProjectiveSpace.twistRestrict j t))))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by
  classical
  let P := ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))
  obtain ⟨S, hS, ⟨eS⟩, hK₁, hK₂, b, hb⟩ :=
    exists_closedImmersion_twist_acyclic_presentation A i F q hq
  let : S.X₁.IsQuasicoherent := hK₁
  let : S.X₁.IsFinitePresentation := hK₂
  obtain ⟨a, ha⟩ := hnext (𝟙 P) S.X₁
  refine ⟨max a b, fun t ht ↦ ?_⟩
  let T := ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) t
  obtain ⟨e₁⟩ := ProjectiveSpace.nonempty_tensorObj_twist_iso
    (ULift.{u} (Fin (N + 1))) (Spec (.of A)) (t : ℤ) (-(t : ℤ))
  let E := BraidedCategory.tensorRightEquivalence T
    (ProjectiveSpace.twist (ULift.{u} (Fin (N + 1))) (Spec (.of A)) (-(t : ℤ)))
    (e₁ ≪≫ eqToIso (congrArg _ (add_neg_cancel (t : ℤ))) ≪≫
      (ProjectiveSpace.unitIsoTwistZero _ _).symm)
  have : (tensorRight T).IsEquivalence := E.isEquivalence_functor
  have hSt := hS.map_of_exact (tensorRight T)
  have hK := ha t (le_trans (le_max_left _ _) ht)
  let eid : tensorObj S.X₁ (ProjectiveSpace.twistRestrict (𝟙 P) t) ≅
      tensorObj S.X₁ T := Iso.refl S.X₁ ⊗ᵢ (pullbackId P).app T
  have hKt : IsZero ((RingedSpace.moduleCohomology P.toRingedSpace (q + 1)).obj
      (tensorObj S.X₁ T)) := hK.of_iso
        ((RingedSpace.moduleCohomology P.toRingedSpace (q + 1)).mapIso
          eid).symm
  obtain ⟨eq, _⟩ := exists_moduleCohomology_source_comparison P q
  obtain ⟨eq₁, _⟩ := exists_moduleCohomology_source_comparison P (q + 1)
  have hB : Subsingleton ((tensorObj S.X₂ T).H q) := by
    have := (ModuleCat.isZero_iff_subsingleton).mp
      (hb t (le_trans (le_max_right _ _) ht))
    exact (eq _).symm.toEquiv.subsingleton
  have hKnext : Subsingleton ((tensorObj S.X₁ T).H (q + 1)) := by
    have := (ModuleCat.isZero_iff_subsingleton).mp hKt
    exact (eq₁ _).symm.toEquiv.subsingleton
  have : Subsingleton ((tensorObj S.X₃ T).H q) :=
    @subsingleton_H_of_shortExact _ _ hSt q hB hKnext
  have : Subsingleton ((tensorObj ((pushforward i).obj F) T).H q) :=
    subsingleton_H_of_iso (eS ⊗ᵢ Iso.refl T) q
  obtain ⟨pf⟩ := nonempty_pushforward_tensorObj_pullback_iso i F T
  have : Subsingleton (((pushforward i).obj
      (tensorObj F (ProjectiveSpace.twistRestrict i t))).H q) :=
    subsingleton_H_of_iso pf.symm q
  have : (tensorObj F (ProjectiveSpace.twistRestrict i t)).IsQuasicoherent :=
    isQuasicoherent_tensorObj F (ProjectiveSpace.twistRestrict i t)
  obtain ⟨ec⟩ := nonempty_functorH_iso_pushforwardAb_of_isAffineHom i q
  let M := tensorObj F (ProjectiveSpace.twistRestrict i t)
  let Q : (cechAcyclicOnAffines X).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj M,
      cechAcyclicOnAffines_of_isQuasicoherent M⟩
  have hpush : Subsingleton (((pushforward i).obj M).H q) := inferInstance
  have : Subsingleton (M.H q) := by
    exact @Equiv.subsingleton _ _ (ec.app Q).addCommGroupIsoToAddEquiv.toEquiv hpush
  obtain ⟨ex, _⟩ := exists_moduleCohomology_source_comparison X q
  exact (ModuleCat.isZero_iff_subsingleton).mpr (ex M).toEquiv.subsingleton

end AlgebraicGeometry.Scheme.Modules
