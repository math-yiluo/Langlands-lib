/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import all WeilConjectures.AlgebraicGeometry.ThickeningSystemPushforwardAdic

/-! # The normalized quotient comparison for an ideal-power closed immersion

Source: Stacks Project, Lemma 087T and equation 0880.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem power_iso {X : Scheme.{v}} (J : X.IdealSheafData) (n : ℕ) :
    ∃ e : (Scheme.idealSheafPower J.toModulesι n).1 ≅ (J ^ n).toModules,
      e.hom ≫ (J ^ n).toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
  cases n with
  | succ n => exact power_inclusion_iso J (n + 1) (Nat.zero_lt_succ n)
  | zero =>
    have : Mono (Scheme.idealSheafPower J.toModulesι 0).2 := power_inclusion_mono J 0
    have hr (U : X.affineOpens) :
        Set.range ((Scheme.idealSheafPower J.toModulesι 0).2.app U.1) =
          Set.range ((J ^ 0).toModulesι.app U.1) := by
      rw [(J ^ 0).range_toModulesι_app]
      simp [Scheme.idealSheafPower]
    have he : Subobject.mk (Scheme.idealSheafPower J.toModulesι 0).2 =
        Subobject.mk (J ^ 0).toModulesι := le_antisymm
      (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).subset))
      (Scheme.subobject_le_of_affine_range _ _ (fun U ↦ (hr U).symm.subset))
    exact ⟨Subobject.isoOfMkEqMk _ _ he, by simp⟩

set_option backward.isDefEq.respectTransparency false in
/-- The quotient by an ideal power is the pushforward of restriction, with its
projection identified with the unit of the supplied adjunction.
Source: Stacks Project, Lemma 087T (lemma-i-star-equivalence), equation 0880.
(blueprint: lem-weil-pbc-closed-immersion-power-quotient).

Proof: On each affine open, the image of the recursively defined ideal-sheaf power
has range J(U)^n, by induction using the affine tensor multiplication calculation.
Thus its product with F has the same image subobject as multiplication by (J^n).
The equality is checked on affine opens and glued by sheaf separatedness. Replace
J^n by the kernel of j. The closed-immersion unit quotient theorem identifies the
cokernel of this image inclusion with j_*j^*F, taking the projection to the canonical
adjunction unit. Equal image subobjects induce the unique quotient isomorphism
preserving projections. Finally compose with the pushforward of leftAdjointUniq
from the canonical adjunction to a; its unit equation gives the claimed equality.
The zero power is the unit ideal, so the closed subscheme and both quotient objects
are zero; zero ideals and zero modules give the same calculation. -/
theorem closedImmersion_power_quotient {X Z : Scheme.{v}} (J : X.IdealSheafData)
    (n : ℕ) (j : Z ⟶ X) [IsClosedImmersion j] (hj : j.ker = J ^ n)
    (a : Scheme.Modules.tensorPullback j ⊣ Scheme.Modules.pushforward j)
    (F : X.Modules) :
    ∃ e : formalModuleQuotient J n F ≅
        (Scheme.Modules.pushforward j).obj ((Scheme.Modules.tensorPullback j).obj F),
      formalModuleQuotientπ J n F ≫ e.hom = a.unit.app F := by
  classical
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  obtain ⟨d, hd⟩ :
      ∃ d : (Scheme.idealSheafPower J.toModulesι n).1 ≅ j.ker.toModules,
        d.hom ≫ j.ker.toModulesι = (Scheme.idealSheafPower J.toModulesι n).2 := by
    rw [hj]
    exact power_iso J n
  let μ : MonoidalCategory.tensorObj (Scheme.idealSheafPower J.toModulesι n).1 F ⟶ F :=
    MonoidalCategory.whiskerRight (Scheme.idealSheafPower J.toModulesι n).2 F ≫
      (MonoidalCategory.leftUnitor F).hom
  let ν : MonoidalCategory.tensorObj j.ker.toModules F ⟶ F :=
    MonoidalCategory.whiskerRight j.ker.toModulesι F ≫ (MonoidalCategory.leftUnitor F).hom
  have hμ : μ ≫ (Iso.refl F).hom = (MonoidalCategory.whiskerRightIso d F).hom ≫ ν := by
    simp only [Iso.refl_hom, Category.comp_id, MonoidalCategory.whiskerRightIso_hom, ν, μ]
    rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hd]
  let q := cokernelImageι μ ≪≫
    cokernel.mapIso μ ν (MonoidalCategory.whiskerRightIso d F) (Iso.refl F) hμ ≪≫
    (cokernelImageι ν).symm
  have hq : formalModuleQuotientπ J n F ≫ q.hom = cokernel.π (image.ι ν) := by
    change cokernel.π (image.ι μ) ≫ q.hom = _
    simp [q]
  let adj : Scheme.Modules.tensorPullback j ⊣ Scheme.Modules.pushforward j :=
    Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction j)
  obtain ⟨η, hη, _⟩ := Scheme.Modules.closedImmersion_unit_quotient j
  have hηF := hη F
  have : IsIso (η F) := hηF.2.2.2
  let t := (Scheme.Modules.pushforward j).mapIso ((adj.leftAdjointUniq a).app F)
  refine ⟨q ≪≫ asIso (η F) ≪≫ t, ?_⟩
  change formalModuleQuotientπ J n F ≫ q.hom ≫ η F ≫ t.hom = _
  rw [← Category.assoc, hq, ← Category.assoc, hηF.2.2.1]
  exact adj.unit_leftAdjointUniq_hom_app a F

end AlgebraicGeometry
