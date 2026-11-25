/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebraBasic
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPowerQuotient
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealStalkRange
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The conormal module at a closed-subscheme point

Source: Stacks Project, Divisors, Tag 0633; Modules, Tags 01AG and 08KS.
(blueprint: lem-pur-conormal-piece-stalk).
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

/-- The stalk of `i^*I` is the cotangent module of the actual closed-immersion stalk
kernel, compatibly with the quotient local ring and with germs of representatives.
Source: Stacks Project, Divisors, Tag 0633; Modules, Tags 01AG and 08KS.
(blueprint: lem-pur-conormal-piece-stalk).

Proof: The ideal-module-product stalk theorem identifies the stalk of `I/I²` with
`I_x/(I_x I_x)`. The ideal-inclusion range theorem identifies `I_x` with the kernel
of the actual structure-stalk map. Its injectivity and the quotient equivalence
therefore identify this quotient with that kernel's cotangent module. The normalized
closed-immersion unit quotient identifies `i_* i^*I` with `I/I²`; the pushforward
stalk map is bijective on the closed image. Compose these identifications. All maps
are linear over the ambient local ring, while pushforward stalks use the actual
structure-stalk map; its quotient first-isomorphism equivalence gives the stated
semilinearity. The unit quotient and stalk quotient formulas give the representative
formula. This argument also applies to the zero ring and the empty closed subscheme. -/
theorem conormal_stalk (z : Z) :
    ∃ e : ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)) ≃+
        (RingHom.ker (i.stalkMap z).hom).Cotangent,
      (∀ (r : X.presheaf.stalk (i z) ⧸ RingHom.ker (i.stalkMap z).hom)
        (x : (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1)),
        e (quotientStalk i z r • x) = r • e x) ∧
      ∀ (U : X.Opens) (hz : i z ∈ U) (a : (power i 1).val.obj (op U)),
        ∃ h : X.presheaf.germ U (i z) hz
            ((powerInclusion i 1).val.app (op U) a) ∈ RingHom.ker (i.stalkMap z).hom,
          e (TopCat.Presheaf.germ (piece i 1).val.presheaf (i ⁻¹ᵁ U) z hz
            (representative i 1 U a)) =
              (RingHom.ker (i.stalkMap z).hom).toCotangent
                ⟨X.presheaf.germ U (i z) hz ((powerInclusion i 1).val.app (op U) a), h⟩ := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace (i z)
  let K := RingHom.ker (i.stalkMap z).hom
  obtain ⟨eO, heO, hI, hprod, hrange, ⟨φ, hφ⟩, _⟩ :=
    Scheme.ideal_module_product_stalk i.ker.toModulesι (power i 1) (i z)
  have hK := (Scheme.Modules.closedImmersion_ideal_stalk_range i (i z) eO heO).1 z rfl
  let f := (S.map i.ker.toModulesι ≫ eO.hom).hom
  have hf : Function.Injective f := (ConcreteCategory.bijective_of_isIso eO.hom).1.comp hI
  let eI : S.obj (power i 1) ≃ₗ[X.presheaf.stalk (i z)] K :=
    (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ hK)
  let eQ : (S.obj (power i 1) ⧸ f.range • (⊤ : Submodule _ (S.obj (power i 1)))) ≃ₗ[
      X.presheaf.stalk (i z)] K.Cotangent :=
    Submodule.Quotient.equiv _ _ eI (by
      rw [Submodule.map_smul'', Submodule.map_top, eI.range]
      exact congrArg (fun I : Ideal (X.presheaf.stalk (i z)) ↦
        I • (⊤ : Submodule _ K)) hK)
  obtain ⟨η, hη⟩ := closedImmersion_power_quotient i.ker 1 i (by simp)
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)) (power i 1)
  let d := (S.mapIso η).symm
  have hh := (closedImmersion_pushforward_stalks i i.isClosedEmbedding (piece i 1)).2.1 z
  let c : S.obj ((Scheme.Modules.pushforward i).obj (piece i 1)) ≃+
      (RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj (piece i 1) :=
    AddEquiv.ofBijective
      (TopCat.Presheaf.stalkPushforward Ab i.base (piece i 1).val.presheaf z).hom hh.1
  let q := φ.symm.trans eQ
  let e := (c.symm.trans d.toLinearEquiv.toAddEquiv).trans q.toAddEquiv
  refine ⟨e, ?_, ?_⟩
  · intro r x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    have hc : c.symm ((i.stalkMap z).hom r • x) = r • c.symm x := by
      apply c.injective
      rw [c.apply_symm_apply]
      have h := hh.2.2 r (c.symm x)
      change c (r • c.symm x) = (i.stalkMap z).hom r • c (c.symm x) at h
      rw [c.apply_symm_apply] at h
      exact h.symm
    rw [quotientStalk, RingHom.quotientKerEquivOfSurjective_apply_mk]
    change q (d.hom (c.symm ((i.stalkMap z).hom r • x))) = _
    rw [hc, map_smul, map_smul]
    rfl
  · intro U hz a
    let m := TopCat.Presheaf.germ (power i 1).val.presheaf U (i z) hz a
    have heI : (eI m : X.presheaf.stalk (i z)) =
        X.presheaf.germ U (i z) hz ((powerInclusion i 1).val.app (op U) a) := by
      change eO.hom (S.map i.ker.toModulesι m) = _
      exact (congrArg eO.hom (stalk_map_germ (i z) i.ker.toModulesι U hz a)).trans
        (heO U hz (i.ker.toModulesι.val.app (op U) a))
    refine ⟨heI ▸ (eI m).2, ?_⟩
    have hc : c (TopCat.Presheaf.germ
        ((Scheme.Modules.pushforward i).obj (piece i 1)).val.presheaf U (i z) hz
          (representative i 1 U a)) =
        TopCat.Presheaf.germ (piece i 1).val.presheaf (i ⁻¹ᵁ U) z hz
          (representative i 1 U a) := by
      change (TopCat.Presheaf.stalkPushforward Ab i.base (piece i 1).val.presheaf z)
        (TopCat.Presheaf.germ
          ((TopCat.Presheaf.pushforward Ab i.base).obj (piece i 1).val.presheaf)
            U (i z) hz (representative i 1 U a)) = _
      exact TopCat.Presheaf.stalkPushforward_germ_apply Ab i.base
        (piece i 1).val.presheaf U z hz (representative i 1 U a)
    rw [← hc]
    change q (d.hom (c.symm (c _))) = _
    rw [c.symm_apply_apply]
    have hunit :
        ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit.app
          (power i 1)) ≫ η.inv = formalModuleQuotientπ i.ker 1 (power i 1) := by
      rw [← hη, Category.assoc, η.hom_inv_id, Category.comp_id]
    have hd : d.hom (TopCat.Presheaf.germ
        ((Scheme.Modules.pushforward i).obj (piece i 1)).val.presheaf U (i z) hz
          (representative i 1 U a)) =
        (S.map (cokernel.π (Scheme.idealModuleProductι i.ker.toModulesι
          (power i 1)))).hom m := by
      have hl := stalk_map_germ (i z) η.inv U hz (representative i 1 U a)
      have hr := stalk_map_germ (i z) (formalModuleQuotientπ i.ker 1 (power i 1)) U hz a
      have hu : η.inv.val.app (op U) (representative i 1 U a) =
          (formalModuleQuotientπ i.ker 1 (power i 1)).val.app (op U) a :=
        ConcreteCategory.congr_hom (congrArg (fun t ↦ t.val.app (op U)) hunit) a
      exact hl.trans ((congrArg
        (TopCat.Presheaf.germ (formalModuleQuotient i.ker 1 (power i 1)).val.presheaf
          U (i z) hz) hu).trans hr.symm)
    rw [hd, ← hφ m]
    change eQ (φ.symm (φ (Submodule.Quotient.mk m))) = _
    rw [φ.symm_apply_apply]
    change K.toCotangent (eI m) = _
    congr 1
    exact Subtype.ext heI

end
end AlgebraicGeometry.ConormalGradedAlgebra
