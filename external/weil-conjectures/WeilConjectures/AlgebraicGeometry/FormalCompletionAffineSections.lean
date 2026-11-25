/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic

import all WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.Algebra.Module.AdicCompletionStableRanges

/-! # Affine sections of a module completion

Source: Stacks Project, Tags 01I8 and 01IC, and the quotient-limit definition of completion.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem quotient_sections_iso {Y : Scheme.{u}}
    (J : Y.IdealSheafData) (H : Y.Modules) [H.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let M := Γ(H, U)
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    ∃ q : ModuleCat.of R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) ≅
        E.obj (formalModuleQuotient J (n + 1) H),
      ModuleCat.ofHom (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M))) ≫ q.hom =
        E.map (formalModuleQuotientπ J (n + 1) H) := by
  let V : Y.affineOpens := ⟨U, hU⟩
  let R := Γ(Y, U)
  let I := J.ideal V
  let M := Γ(H, U)
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  let a := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H
  have hpower := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J H).2.2.1
    (n + 1) (Nat.succ_pos n)
  have := hpower
  have := Scheme.Modules.product_qc (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H
  have hpow := ((Scheme.Modules.ideal_times_quasiCoherent_affine_sections J H).2.2.2.1
    V).2.2.2 (n + 1) (Nat.succ_pos n)
  have heq : (LinearMap.range
      ((Scheme.idealSheafPower J.toModulesι (n + 1)).2.val.app (op U)).hom :
        Ideal R) = I ^ (n + 1) := SetLike.coe_injective hpow
  have hr := Scheme.Modules.multiplication_range
    (Scheme.idealSheafPower J.toModulesι (n + 1)).2 H V
  dsimp only at hr
  rw [heq] at hr
  have ha := (Scheme.Modules.quasiCoherent_cokernel_image a).2.2.2.2.2.2.2.2 V
  let ρ : M →ₗ[R] E.obj (formalModuleQuotient J (n + 1) H) :=
    (E.map (formalModuleQuotientπ J (n + 1) H)).hom
  have hsurj : Function.Surjective ρ := ha.2.1
  have hker : LinearMap.ker ρ = I ^ (n + 1) • (⊤ : Submodule R M) := by
    change LinearMap.ker ((cokernel.π a).val.app (op U)).hom = _
    rw [ha.2.2.1]
    exact SetLike.coe_injective hr
  let e := (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (ρ.quotKerEquivOfSurjective hsurj)
  refine ⟨e.toModuleIso, ?_⟩
  ext x
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine quotient identifications give a canonical completion isomorphism.
Source: Stacks Project, Tags 01I8 and 01IC; Cohomology of Schemes, Lemma 088B.
(blueprint: lem-weil-pbc-formal-completion-affine-sections)

Proof: Set A = Gamma(Y,U), I = J(U), and M = Gamma(U,H). On an affine open,
quasi-coherent sheaves are modules, and affine sections are exact. The range of the
inclusion of J^(n+1)H is I^(n+1)M: the ideal power formula and tensor section formula
identify multiplication, and exactness identifies its image. Thus the actual quotient
projection is surjective with kernel I^(n+1)M. Its first isomorphism theorem gives q_n,
with the displayed projection equation. Cancel the surjective quotient projections to
check that q_n commutes with all transitions. Evaluation preserves limits, so these
compatible isomorphisms identify the evaluated sheaf limit with the limit of M/I^(n+1)M.
This limit is the adic completion: the omitted exponent-zero quotient is zero, and
inserting its unique zero coordinate gives the inverse identification. Its projections
are exactly AdicCompletion.eval at n+1, which proves the final equation.
For the zero ideal the systems are constant; for the unit ideal they are zero. The zero
module and empty affine open give zero modules throughout; no nonzero-ring assumption
is needed. No proper morphism or comparison map is used in this statement.
-/
theorem formalCompletion_affine_sections {Y : Scheme.{u}}
    (J : Y.IdealSheafData) (H : Y.Modules) [H.IsQuasicoherent]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    let R := Γ(Y, U)
    let I := J.ideal ⟨U, hU⟩
    let M := Γ(H, U)
    let S := formalCompletionSystem J H
    let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
    ∃ q : ∀ n : ℕ,
        ModuleCat.of R (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) ≅
          E.obj (S.obj (op n)),
      (∀ n : ℕ, ModuleCat.ofHom
        (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule R M))) ≫ (q n).hom =
          E.map (formalModuleQuotientπ J (n + 1) H)) ∧
      ∃ e : ModuleCat.of R (AdicCompletion I M) ≅ E.obj (limit S),
        ∀ n : ℕ, e.hom ≫ E.map (limit.π S (op n)) =
          ModuleCat.ofHom (AdicCompletion.eval I M (n + 1)) ≫ (q n).hom := by
  classical
  let R := Γ(Y, U)
  let I := J.ideal ⟨U, hU⟩
  let E := SheafOfModules.evaluation Y.ringCatSheaf (op U)
  let M := E.obj H
  let S := formalCompletionSystem J H
  let D := S ⋙ E
  choose q hq using quotient_sections_iso J H U hU
  let ρ : ∀ n : ℕ, M →ₗ[R] D.obj (op n) :=
    fun n ↦ (E.map (formalModuleQuotientπ J (n + 1) H)).hom
  let θ : ∀ n : ℕ, (M ⧸ (I ^ (n + 1) • (⊤ : Submodule R M))) →ₗ[R]
      D.obj (op n) := fun n ↦ (q n).hom.hom
  have hθ (n : ℕ) : (θ n).comp (Submodule.mkQ (I ^ (n + 1) • ⊤)) = ρ n :=
    congrArg ModuleCat.Hom.hom (hq n)
  have hρ (n m : ℕ) (h : n ≤ m) :
      (D.map (homOfLE h).op).hom.comp (ρ m) = ρ n := by
    change (E.map (formalModuleQuotientπ J (m + 1) H) ≫
      E.map (formalModuleQuotientMap J (𝟙 H) (Nat.succ_le_succ h))).hom = _
    rw [← E.map_comp]
    simp [formalModuleQuotientMap, formalModuleQuotientπ, ρ]
  have ht (n m : ℕ) (h : n ≤ m) :
      (D.map (homOfLE h).op).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I M (Nat.succ_le_succ h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I ^ (m + 1) • (⊤ : Submodule R M)).mkQ_surjective x
    have hleft := LinearMap.congr_fun (hθ m) y
    have hright := LinearMap.congr_fun (hθ n) y
    have hrho := LinearMap.congr_fun (hρ n m h) y
    simpa [LinearMap.comp_apply, AdicCompletion.transitionMap, Submodule.factorPow,
      Submodule.factor, Submodule.mapQ_apply] using
        (congrArg (D.map (homOfLE h).op).hom hleft).trans (hrho.trans hright.symm)
  have hk (n : ℕ) : LinearMap.ker (ρ (n + 0)) ≤ I ^ (n + 1) • (⊤ : Submodule R M) := by
    intro x hx
    have hz : θ n ((I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x) = 0 := by
      rw [← LinearMap.comp_apply, hθ]
      exact hx
    have hxq : (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ x = 0 :=
      (q n).toLinearEquiv.injective (hz.trans (map_zero _).symm)
    exact (Submodule.Quotient.mk_eq_zero _).mp hxq
  have hi (n : ℕ) : Set.range (D.map (homOfLE (Nat.le_add_right n 0)).op).hom =
      Set.range (ρ n) := by
    have hs : Function.Surjective (ρ n) := by
      rw [← hθ n]
      exact (q n).toLinearEquiv.surjective.comp
        (I ^ (n + 1) • (⊤ : Submodule R M)).mkQ_surjective
    rw [Set.range_eq_univ.mpr hs]
    have hid : (homOfLE (Nat.le_add_right n 0)).op = 𝟙 (op n) := Subsingleton.elim _ _
    rw [hid]
    have hd : D.map (𝟙 (op n)) = 𝟙 (D.obj (op n)) := D.map_id (op n)
    rw [hd]
    exact Set.range_eq_univ.mpr Function.surjective_id
  obtain ⟨e, he⟩ := adicCompletion_iso_of_stable_ranges I M D ρ θ hθ ht 0 hk hi
  let a := preservesLimitIso E S
  refine ⟨q, hq, e ≪≫ a.symm, ?_⟩
  intro n
  change (e.hom ≫ a.inv) ≫ E.map (limit.π S (op n)) = _
  rw [Category.assoc, preservesLimitIso_inv_π, he]
  rfl

end AlgebraicGeometry
