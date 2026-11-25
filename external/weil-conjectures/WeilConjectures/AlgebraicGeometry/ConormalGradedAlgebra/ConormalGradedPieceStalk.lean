/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraBasic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.AssociatedGradedRing
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.FormalPolynomialPowerLifts
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealStalkRange
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Homogeneous conormal module stalks

Source: Stacks Project, Divisors, Tag 0633; Modules, Tags 01AG and 08KS.
(blueprint: lem-pur-conormal-graded-piece-stalk).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ConormalGradedAlgebra
noncomputable section
variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

private theorem stalk_map_germ {Y : Scheme.{u}} (y : Y) {M N : Y.Modules}
    (f : M ⟶ N) (U : Y.Opens) (hy : y ∈ U) (a : M.val.obj (op U)) :
    (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).map f
        (TopCat.Presheaf.germ M.val.presheaf U y hy a) =
      TopCat.Presheaf.germ N.val.presheaf U y hy (f.val.app (op U) a) := by
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U y hy
    ((PresheafOfModules.toPresheaf _).map f.val) a

/-- Each homogeneous conormal stalk is the successive-power quotient of the actual
structure-stalk kernel, with its representative-germ formula.
Source: Stacks Project, Divisors, Tag 0633; Modules, Tags 01AG and 08KS.
(blueprint: lem-pur-conormal-graded-piece-stalk).

Proof: Apply exact stalks to the normalized closed-immersion unit quotient of I^n.
The range of the ideal stalk inclusion is the actual structure-map kernel K, and
induction on powers identifies the stalk of I^n with K^n. The inclusion is monic,
so it is an isomorphism onto this range. Transporting the product submodule
K times the stalk of I^n gives K^(n+1) inside K^n. The induced quotient equivalence
identifies the stalk of I^n/I I^n with K^n/K^(n+1). Finally the closed-embedding
pushforward stalk comparison identifies this with the stalk on Z. Every comparison
commutes with the quotient map and germs; their composite has the stated formula.
For n=0 the power inclusion is the identity and its range is the whole local ring. -/
theorem graded_piece_stalk (n : ℕ) (z : Z) :
    ∃ e : ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i n)) ≃+
        Ideal.associatedGradedPiece (RingHom.ker (i.stalkMap z).hom) n,
      ∀ (U : X.Opens) (hz : i z ∈ U) (a : (power i n).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i n).val.app (op U) a) ∈
              RingHom.ker (i.stalkMap z).hom ^ n,
          e (TopCat.Presheaf.germ (piece i n).val.presheaf (i ⁻¹ᵁ U) z hz
            (representative i n U a)) = Submodule.Quotient.mk
              ⟨X.presheaf.germ U (i z) hz ((powerInclusion i n).val.app (op U) a), h⟩ := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace (i z)
  let K := RingHom.ker (i.stalkMap z).hom
  obtain ⟨eO, heO, hI, hprod, hrange, ⟨φ, hφ⟩, hpowers⟩ :=
    Scheme.ideal_module_product_stalk i.ker.toModulesι (power i n) (i z)
  have hK := (Scheme.Modules.closedImmersion_ideal_stalk_range i (i z) eO heO).1 z rfl
  let f := (S.map (powerInclusion i n) ≫ eO.hom).hom
  have hm : Mono (powerInclusion i n) := formalPolynomial_power_mono i.ker.toModulesι n
  have hf0 : Function.Injective (S.map (powerInclusion i n)).hom := by
    have h := (RingedSpace.module_stalk_exact X.toRingedSpace (powerInclusion i n)).1
    have : Mono (S.map (powerInclusion i n)) := h (fun U ↦
      formalPolynomial_power_injective i.ker.toModulesι n U) (i z)
    exact (ModuleCat.mono_iff_injective _).mp this
  have hf : Function.Injective f := (ConcreteCategory.bijective_of_isIso eO.hom).1.comp hf0
  have hpower : f.range = K ^ n := by
    cases n with
    | zero =>
      change LinearMap.range (S.map (𝟙 _) ≫ eO.hom).hom = K ^ 0
      rw [S.map_id, Category.id_comp, pow_zero]
      rw [Ideal.one_eq_top]
      exact LinearMap.range_eq_top.mpr (ConcreteCategory.bijective_of_isIso eO.hom).2
    | succ n =>
      exact ((hpowers (n + 1) (Nat.succ_le_succ (Nat.zero_le n))).1).trans
        (congrArg (· ^ (n + 1)) hK)
  let eI : S.obj (power i n) ≃ₗ[X.presheaf.stalk (i z)] ↥(K ^ n) :=
    (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hpower)
  let eQ : (S.obj (power i n) ⧸ (LinearMap.range (S.map i.ker.toModulesι ≫ eO.hom).hom :
      Ideal (X.presheaf.stalk (i z))) • (⊤ : Submodule _ (S.obj (power i n)))) ≃ₗ[
      X.presheaf.stalk (i z)] Ideal.associatedGradedPiece K n :=
    Submodule.Quotient.equiv _ _ eI (by
      rw [Submodule.map_smul'', Submodule.map_top, eI.range]
      rw [hK]
      apply Submodule.map_injective_of_injective (K ^ n).injective_subtype
      rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype,
        Ideal.smul_eq_mul, ← pow_succ', Submodule.map_comap_eq_of_le]
      rw [Submodule.range_subtype]
      exact Ideal.pow_le_pow_right (Nat.le_succ n))
  obtain ⟨η, hη⟩ := closedImmersion_power_quotient i.ker 1 i (by simp)
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)) (power i n)
  let d := (S.mapIso η).symm
  have hh := (closedImmersion_pushforward_stalks i i.isClosedEmbedding (piece i n)).2.1 z
  let c : S.obj ((Scheme.Modules.pushforward i).obj (piece i n)) ≃+
      (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i n) :=
    AddEquiv.ofBijective
      (TopCat.Presheaf.stalkPushforward Ab i.base (piece i n).val.presheaf z).hom hh.1
  let q := φ.symm.trans eQ
  let e := (c.symm.trans d.toLinearEquiv.toAddEquiv).trans q.toAddEquiv
  refine ⟨e, ?_⟩
  intro U hz a
  let m := TopCat.Presheaf.germ (power i n).val.presheaf U (i z) hz a
  have heI : (eI m : X.presheaf.stalk (i z)) =
      X.presheaf.germ U (i z) hz ((powerInclusion i n).val.app (op U) a) := by
    change eO.hom (S.map (powerInclusion i n) m) = _
    exact (congrArg eO.hom (stalk_map_germ (i z) (powerInclusion i n) U hz a)).trans
      (heO U hz ((powerInclusion i n).val.app (op U) a))
  refine ⟨heI ▸ (eI m).2, ?_⟩
  have hc : c (TopCat.Presheaf.germ
      ((Scheme.Modules.pushforward i).obj (piece i n)).val.presheaf U (i z) hz
        (representative i n U a)) =
      TopCat.Presheaf.germ (piece i n).val.presheaf (i ⁻¹ᵁ U) z hz
        (representative i n U a) := by
    change (TopCat.Presheaf.stalkPushforward Ab i.base (piece i n).val.presheaf z)
      (TopCat.Presheaf.germ
        ((TopCat.Presheaf.pushforward Ab i.base).obj (piece i n).val.presheaf)
          U (i z) hz (representative i n U a)) = _
    exact TopCat.Presheaf.stalkPushforward_germ_apply Ab i.base
      (piece i n).val.presheaf U z hz (representative i n U a)
  rw [← hc]
  change q (d.hom (c.symm (c _))) = _
  rw [c.symm_apply_apply]
  have hunit :
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
        (power i n)) ≫ η.inv = formalModuleQuotientπ i.ker 1 (power i n) := by
    rw [← hη, Category.assoc, η.hom_inv_id, Category.comp_id]
  have hd : d.hom (TopCat.Presheaf.germ
      ((Scheme.Modules.pushforward i).obj (piece i n)).val.presheaf U (i z) hz
        (representative i n U a)) =
      (S.map (cokernel.π (Scheme.idealModuleProductι i.ker.toModulesι
        (power i n)))).hom m := by
    have hl := stalk_map_germ (i z) η.inv U hz (representative i n U a)
    have hr := stalk_map_germ (i z) (formalModuleQuotientπ i.ker 1 (power i n)) U hz a
    have hu : η.inv.val.app (op U) (representative i n U a) =
        (formalModuleQuotientπ i.ker 1 (power i n)).val.app (op U) a :=
      ConcreteCategory.congr_hom (congrArg (fun t ↦ t.val.app (op U)) hunit) a
    exact hl.trans ((congrArg
      (TopCat.Presheaf.germ (formalModuleQuotient i.ker 1 (power i n)).val.presheaf
        U (i z) hz) hu).trans hr.symm)
  rw [hd, ← hφ m]
  change eQ (φ.symm (φ (Submodule.Quotient.mk m))) = _
  rw [φ.symm_apply_apply]
  change Submodule.Quotient.mk (eI m) = _
  congr 1
  exact Subtype.ext heI

end
end AlgebraicGeometry.ConormalGradedAlgebra
