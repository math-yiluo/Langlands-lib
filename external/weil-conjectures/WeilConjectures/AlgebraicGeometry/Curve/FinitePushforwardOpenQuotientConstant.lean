/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.FinitePushforwardFiniteStalkModule

/-!
# Constructibility of finite pushforward of open quotient constants

Source: normalization exact-sequence blueprint, unit
`proposition-proper-base-change-projective-line`. (blueprint: lemma-normalization-constant-sheaf--1)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry
open Etale
variable (Λ : Type (u + 1)) [CommRing Λ]

private theorem constantModule_constructible (Y : Scheme.{u})
    (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] :
    Scheme.IsConstructibleSheaf ((constantSheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).obj M) := by
  let : LocallySmall.{u + 1} Y.Etale := locallySmall_max.{u + 1, u, u + 1}
  let F := (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  have hconst : F.IsConstant Y.smallEtaleTopology := by
    exact Sheaf.isConstant_of_iso _ (Iso.refl _)
  let : Scheme.IsLocallyConstantSheaf F := by
    have : Scheme.etalePrecoverage.{u}.HasIsos :=
      inferInstanceAs (Scheme.precoverage @Etale).HasIsos
    refine ⟨⟨⟨.singleton (𝟙 Y) (Precoverage.mem_coverings_of_isIso _), fun _ ↦ ?_⟩⟩⟩
    rw [Scheme.isConstant_over_iff_upperStar]
    have := hconst
    exact Sheaf.IsConstant.upperStar (ModuleCat.{u + 1} Λ) (𝟙 Y) F
  let : Scheme.IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F := ⟨fun Ω _ _ s ↦ by
    let Φ := (Scheme.pointSmallEtale s).ulift.{u + 1}
    let e : (Scheme.pointSmallEtale s).sheafFiber.obj F ≅ M :=
      (((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} Λ)).app F).symm ≪≫ Φ.sheafFiberConstantSheafIso M
    exact ((ModuleCat.isFinitelyGenerated_iff M).mpr inferInstance).of_iso e.symm⟩
  let : Scheme.IsFiniteLocallyConstantSheaf F := {}
  refine ⟨Scheme.Stratification.trivial Y, fun i ↦ ?_⟩
  exact Scheme.IsFiniteLocallyConstantSheaf.upperStar (𝟙 Y) F

private theorem finite_open_constantModule_stalk {X U : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j]
    (M : ModuleCat.{u + 1} Λ) [Finite M] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    Finite ((((Scheme.pointSmallEtale s).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).obj
      ((j)_!open[ModuleCat.{u + 1} Λ].obj
        ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  classical
  let : LocallySmall.{u + 1} U.Etale := locallySmall_max.{u + 1, u, u + 1}
  by_cases hs : s.base (IsLocalRing.closedPoint Ω) ∈ Set.range j.base
  · have hrange : Set.range s.base ⊆ Set.range j.base := by
      rintro _ ⟨y, rfl⟩
      simpa only [Subsingleton.elim y (IsLocalRing.closedPoint Ω)] using hs
    let t := IsOpenImmersion.lift j s hrange
    have hts : t ≫ j = s := IsOpenImmersion.lift_fac j s hrange
    let e : ((Scheme.pointSmallEtale (t ≫ j)).ulift.{u + 1}).sheafFiber.obj
        ((j)_!open[ModuleCat.{u + 1} Λ].obj
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) ≅ M :=
      (Etale.openImmersionLowerShriekCompUliftSheafFiberIso (ModuleCat.{u + 1} Λ)
        j t).app ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ≪≫
      ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiberConstantSheafIso M
    rw [← hts]
    exact Finite.of_equiv M e.toLinearEquiv.toEquiv.symm
  · have hz := Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj
      (ModuleCat.{u + 1} Λ) j s hs
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
    have := ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

/-- Finite pushforward of an extension-by-zero finite quotient constant is constructible.

Source: normalization exact-sequence blueprint,
`sec-proper-base-change/sk-thm-p1/lemma-weil-pbc-normalization-exact-sequence.md`,
constructibility of the middle term.
(blueprint: lemma-normalization-constant-sheaf--1)

Proof: Y is Noetherian, since it is finite over X. Write R = Λ/(ℓ). Its constant sheaf
is finite locally constant, because R is cyclic as a Λ-module. Extend its stratification
by the closed complement of the quasi-compact open j to obtain constructibility of j_!R.
Its underlying abelian sheaf has finite constructible stalks. Finite direct image preserves
this constructibility by finite base change, the finite geometric-fibre formula and
Noetherian induction. Extension by zero and finite direct image preserve annihilation by ℓ,
so the module action factors through the finite ring R. Refine the finite-set trivializations
on every stratum to trivialize the finitely many R-operations. These give constant finite
R-module values, finitely generated over Λ, and hence the required module stratification.
Neither finiteness nor Noetherianity of Λ is needed. Empty opens and the zero quotient
produce zero sheaves, which satisfy the same conclusion. -/
theorem finite_pushforward_open_constantModSheaf_constructible
    {X Y U : Scheme.{u}} [IsNoetherian X] (ν : Y ⟶ X) [IsFinite ν]
    (j : U ⟶ Y) [IsOpenImmersion j] (ℓ : ℕ)
    [Finite (Λ ⧸ Ideal.span {(ℓ : Λ)})] :
    Scheme.IsConstructibleSheaf ((ν)_*[ModuleCat.{u + 1} Λ].obj
      ((j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ))) := by
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType ν
  let F := (j)_!open[ModuleCat.{u + 1} Λ].obj (Etale.constantModSheaf Λ U ℓ)
  let M := ModuleCat.of Λ (Λ ⧸ (Ideal.span {(ℓ : Λ)} : Ideal Λ))
  let : Scheme.IsConstructibleSheaf (Etale.constantModSheaf Λ U ℓ) :=
    constantModule_constructible Λ U M
  have hF : Scheme.IsConstructibleSheaf F :=
    Scheme.IsConstructibleSheaf.openImmersionLowerShriek j
      j.closedComplement j.range_closedComplement _
  exact Scheme.isConstructibleSheaf_lowerStar_of_finite_stalks Λ ν F hF
    (fun Ω _ _ s ↦ finite_open_constantModule_stalk Λ j M s)
end AlgebraicGeometry
