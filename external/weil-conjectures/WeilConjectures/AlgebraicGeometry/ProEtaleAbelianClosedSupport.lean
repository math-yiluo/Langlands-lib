/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.DetectionAb

/-!
# Closed support for abelian pro-etale sheaves

Source: Stacks Project, Tags 09AA and 09AH
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

private theorem abJointZero {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (ProEt.topology X) Ab.{u + 1})
    (hi : IsZero ((upperStar Ab.{u + 1} i).obj F))
    (hj : IsZero ((upperStar Ab.{u + 1} j).obj F)) : IsZero F := by
  let Y : Bool → Scheme.{u} := fun b ↦ bif b then Z else U
  let g : ∀ b, Y b ⟶ X := fun b ↦ match b with | true => i | false => j
  have : ∀ b, QuasiCompact (g b) := by rintro (_ | _) <;> dsimp [g] <;> infer_instance
  refine (IsZero.iff_id_eq_zero F).2
    (eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp g (fun x ↦ ?_) (𝟙 F) ?_)
  · by_cases hx : x ∈ Set.range i.base
    · exact ⟨true, hx⟩
    · exact ⟨false, hij ▸ hx⟩
  · rintro (_ | _)
    · exact hj.eq_of_src _ _
    · exact hi.eq_of_src _ _

private theorem abDetectIso {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    {F G : Sheaf (ProEt.topology X) Ab.{u + 1}} (φ : F ⟶ G)
    [IsIso ((upperStar Ab.{u + 1} i).map φ)]
    [IsIso ((upperStar Ab.{u + 1} j).map φ)] : IsIso φ := by
  have hker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((g)^*[Ab.{u + 1}].map φ)],
      IsZero ((g)^*[Ab.{u + 1}].obj (kernel φ)) := fun g _ ↦
    (isZero_kernel_of_mono ((g)^*[Ab.{u + 1}].map φ)).of_iso
      (PreservesKernel.iso _ φ)
  have hcoker : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [IsIso ((g)^*[Ab.{u + 1}].map φ)],
      IsZero ((g)^*[Ab.{u + 1}].obj (cokernel φ)) := fun g _ ↦
    (isZero_cokernel_of_epi ((g)^*[Ab.{u + 1}].map φ)).of_iso
      (PreservesCokernel.iso _ φ)
  have : Mono φ := Preadditive.mono_of_isZero_kernel _
    (abJointZero i j hij _ (hker i) (hker j))
  have : Epi φ := Preadditive.epi_of_isZero_cokernel _
    (abJointZero i j hij _ (hcoker i) (hcoker j))
  exact isIso_of_mono_of_epi φ

/-- The closed unit is invertible on abelian sheaves whose restriction to the quasi-compact open
complement vanishes. This is the `Ab` counterpart of base
`ProEtale.isIso_upperStarLowerStarAdjunction_unit_app_of_isCompl` (stated for modules).

Source: Stacks, Tags 09AA and 09AH
(auxiliary; not a blueprint node).

Proof: the counit of `i^* ⊣ i_*` is invertible (`isIso_upperStarLowerStarAdjunction_counit`), so
the closed restriction of the unit is invertible by the adjunction triangle identity. Its open
restriction is a map between zero objects: its source is zero by hypothesis, and the open
restriction of a closed direct image is zero (`isZero_upperStar_lowerStar_of_disjoint`). The
closed immersion and its quasi-compact open complement jointly detect isomorphisms of abelian
sheaves (`eq_zero_of_forall_upperStar_map_eq_zero_addCommGrp`, applied to kernel and cokernel). -/
theorem abelian_closed_support {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ)
    (F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    (hF : IsZero ((upperStar Ab.{u + 1} j).obj F)) :
    IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F) := by
  have := isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i
  set adj := upperStarLowerStarAdjunction Ab.{u + 1} i
  have : IsIso ((i)^*[Ab.{u + 1}].map (adj.unit.app F)) := by
    have h := adj.left_triangle_components F
    have : IsIso ((i)^*[Ab.{u + 1}].map (adj.unit.app F) ≫
        adj.counit.app ((i)^*[Ab.{u + 1}].obj F)) := by
      rw [h]
      exact IsIso.id _
    exact IsIso.of_isIso_comp_right _ (adj.counit.app _)
  have hdisj : Disjoint (Set.range i.base) (Set.range j.base) := by
    rw [hij]
    exact disjoint_compl_right
  have : IsIso ((j)^*[Ab.{u + 1}].map (adj.unit.app F)) :=
    ⟨⟨0, hF.eq_of_src _ _,
      (isZero_upperStar_lowerStar_of_disjoint Ab.{u + 1} i j hdisj _).eq_of_src _ _⟩⟩
  exact abDetectIso i j hij _

/-- The closed restriction counit `i^* i_* ⟶ 𝟭` of abelian sheaves is an isomorphism, and the unit
`F ⟶ i_* i^* F` is an isomorphism for every abelian sheaf `F` vanishing on the open complement
(`abelian_closed_support`). -/
theorem abelian_closed_support_counit_and_unit {X U Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X)
    [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j = (Set.range i)ᶜ) :
    IsIso (upperStarLowerStarAdjunction Ab.{u + 1} i).counit ∧
    ∀ F : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1},
      IsZero ((upperStar Ab.{u + 1} j).obj F) →
      IsIso ((upperStarLowerStarAdjunction Ab.{u + 1} i).unit.app F) :=
  ⟨isIso_upperStarLowerStarAdjunction_counit Ab.{u + 1} i,
    fun F hF ↦ abelian_closed_support i j hij F hF⟩

end AlgebraicGeometry.ProEtale
