/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsPowerQuotient
import WeilConjectures.AlgebraicGeometry.Curve.ReductionNilradicalNilpotence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-! # A finite quasi-coherent filtration of infinitesimal units

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-finite-filtration)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem isZero_reduction_units_kernel_of_eq_bot (X : Scheme.{u})
    (I : X.IdealSheafData) (h : I = ⊥) :
    IsZero (kernel (gmSheafToLowerStarGmSheaf I.subschemeι)) := by
  have : IsIso I.subschemeι := by
    subst I
    infer_instance
  have : IsUniversalHomeomorphism I.subschemeι := inferInstance
  have : (Etale.upperStar AddCommGrpCat.{u + 1} I.subschemeι).IsEquivalence :=
    Etale.isEquivalence_upperStar _ I.subschemeι
  have : IsIso (upperStarGmSheafToGmSheaf I.subschemeι) :=
    isIso_upperStarGmSheafToGmSheaf _
  have heq : gmSheafToLowerStarGmSheaf I.subschemeι =
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} I.subschemeι).unit.app
        X.gmSheaf ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} I.subschemeι).map
        (upperStarGmSheafToGmSheaf I.subschemeι) := by
    unfold upperStarGmSheafToGmSheaf
    simpa only [Adjunction.homEquiv_unit] using
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} I.subschemeι).homEquiv
        X.gmSheaf I.subscheme.gmSheaf).apply_symm_apply
          (gmSheafToLowerStarGmSheaf I.subschemeι)).symm
  have : IsIso (gmSheafToLowerStarGmSheaf I.subschemeι) := by rw [heq]; infer_instance
  exact isZero_kernel_of_mono _

/-- The reduction units kernel has a finite filtration with pulled-back additive
quasi-coherent quotients. This statement concerns sheaves, not their cohomology.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-reduction-units-finite-filtration)

Proof: Let N be the nilradical of X. Noetherianity and a finite affine cover give
N^m = 0 for some m >= 1. On an affine etale object V over X, flat pullback identifies
the reduction ideal with N O_V: its quotient is etale over the reduced scheme and
therefore reduced. The kernel of G_m,X -> i_* G_m,X_red is consequently 1+N.
Use the descending filtration 1+N^(j+1), ending at j=m-1. For j >= 0 the map
1+a to a identifies its quotient by 1+N^(j+2) with N^(j+1)/N^(j+2): the cross term
belongs to N^(2j+2), hence to N^(j+2). These are quasi-coherent modules. The map
is locally surjective since nilpotent elements give units, and flat pullback
preserves the ideal quotients. Lift the additive coefficients sectionwise to
AddCommGrpCat in universe u+1. Pull this finite filtration to X_red. Reduction
induces an exact equivalence of etale topoi. Its counit on G_m,X_red is an
isomorphism, so preservation of kernels identifies its first term with the
kernel of upperStarGmSheafToGmSheaf i. Exactness preserves each short exact
sequence and its last zero term. A reduced or empty X permits the zero-length
filtration, so no nonemptiness or positive dimension assumption is needed. -/
theorem exists_reduction_units_finite_filtration (X : Scheme.{u}) [IsNoetherian X] :
    ∃ (n : ℕ) (E : ℕ → Sheaf X.nilradical.subscheme.smallEtaleTopology
        AddCommGrpCat.{u + 1}),
      Nonempty (E 0 ≅ kernel (upperStarGmSheafToGmSheaf X.nilradical.subschemeι)) ∧
      IsZero (E n) ∧
      ∀ j, j < n → ∃ (F : X.Modules) (_ : F.IsQuasicoherent)
        (S : ShortComplex (Sheaf X.nilradical.subscheme.smallEtaleTopology
          AddCommGrpCat.{u + 1})),
        S.ShortExact ∧ Nonempty (S.X₁ ≅ E (j + 1)) ∧ Nonempty (S.X₂ ≅ E j) ∧
        Nonempty (S.X₃ ≅ (Etale.upperStar AddCommGrpCat.{u + 1} X.nilradical.subschemeι).obj
          ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
            (Modules.etaleTensorSectionsSheaf F))) := by
  let i := X.nilradical.subschemeι
  let U := Etale.upperStar AddCommGrpCat.{u + 1} i
  have : Surjective i :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X).2.2.1
  have : IsUniversalHomeomorphism i := {}
  have : U.IsEquivalence := Etale.isEquivalence_upperStar _ i
  have : (Etale.lowerStar AddCommGrpCat.{u + 1} i).IsEquivalence :=
    Etale.isEquivalence_lowerStar _ i
  let adj := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i
  have : IsIso (adj.counit.app X.nilradical.subscheme.gmSheaf) := inferInstance
  obtain ⟨n, hn⟩ := exists_nilradical_pow_succ_eq_bot X
  let E := X.reductionUnitsPowerKernel
  have e₀ : E 0 ≅ kernel (gmSheafToLowerStarGmSheaf i) :=
    eqToIso (congrArg (fun I : X.IdealSheafData ↦
      kernel (gmSheafToLowerStarGmSheaf I.subschemeι)) (pow_one X.nilradical))
  have hzero : IsZero (E n) :=
    isZero_reduction_units_kernel_of_eq_bot X (X.nilradical ^ (n + 1)) hn
  refine ⟨n, fun j ↦ U.obj (E j), ?_, U.map_isZero hzero, ?_⟩
  · refine ⟨U.mapIso e₀ ≪≫ PreservesKernel.iso U (gmSheafToLowerStarGmSheaf i) ≪≫ ?_⟩
    exact (kernelCompMono (U.map (gmSheafToLowerStarGmSheaf i))
      (adj.counit.app X.nilradical.subscheme.gmSheaf)).symm ≪≫
      kernelIsoOfEq (by
        dsimp [upperStarGmSheafToGmSheaf]
        rw [Adjunction.homEquiv_counit])
  · intro j _hj
    obtain ⟨F, hF, S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
      exists_reduction_units_power_quotient X j
    exact ⟨F, hF, S.map U, hS.map_of_exact U,
      ⟨U.mapIso e₁⟩, ⟨U.mapIso e₂⟩, ⟨U.mapIso e₃⟩⟩

end AlgebraicGeometry.Scheme
