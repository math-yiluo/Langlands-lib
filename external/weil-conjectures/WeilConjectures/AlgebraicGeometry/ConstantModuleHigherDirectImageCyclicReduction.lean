/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.Algebra.FinitelyGeneratedCyclicFunctorVanishing
import WeilConjectures.AlgebraicGeometry.ConstantAbelianHigherDirectImageFilteredColimit
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Sites.Adjunction

/-!
# Reduction of constant module coefficients to cyclic abelian coefficients

Source: the coefficient reduction in
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`, using
Stacks Project, Tags 03Q8, 03Q5 and 03FD.
(blueprint: lem-sbc-constant-module-higher-direct-image-cyclic-reduction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Vanishing for every cyclic group whose order divides d implies vanishing for
constant coefficients Λ/dΛ, with no finiteness assumption on Λ.

Source: the coefficient reduction in
`Etale.isZero_higherDirectImage_constantModSheaf_of_forall_exists`, using
Stacks Project, Tags 03Q8, 03Q5 and 03FD.
(blueprint: lem-sbc-constant-module-higher-direct-image-cyclic-reduction).

Proof: Forget the module action on Λ/dΛ and express its additive group as the
filtered union of its finitely generated subgroups. If d > 0, each subgroup is a
finite abelian group killed by d, hence a finite direct sum of Z/e with e dividing
d. If d = 0, a finitely generated subgroup is a finite sum of finite cyclic groups
and copies of Z; every positive e divides zero and Z is ZMod 0 with 0 dividing 0.
Constant sheafification preserves these colimits and finite sums. Higher direct
images along the quasi-compact quasi-separated h commute with filtered colimits,
and are additive, so the higher direct image of this constant abelian sheaf is a
filtered colimit of zero objects by H, hence is zero. Finally, forgetting the
Λ-action computes higher direct images on underlying abelian sheaves: use a
module-injective resolution, whose underlying sheaves are acyclic on every
etale object, to obtain the cohomology comparison by Tag 03FD and then
the higher-direct-image comparison by Tag 03Q8. The forgetful functor
reflects zero objects, so the module higher direct image is zero as well. The
argument includes d = 1, degree zero, the zero ring, and the empty scheme. -/
theorem isZero_constantModHigherDirectImage_of_cyclic
    (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}}
    (h : Y ⟶ X) [QuasiCompact h] [QuasiSeparated h] (d q : ℕ)
    (H : ∀ e : ℕ, e ∣ d →
      IsZero ((DerivedCategory.Plus.homologyFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj (Y.constantZMod e))))) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) := by
  classical
  let R := ULift.{u + 1} ℤ
  let V := Λ ⧸ (Ideal.span {(d : Λ)} : Ideal Λ)
  let φ : R →+* Λ := (Int.castRingHom Λ).comp ULift.ringEquiv.toRingHom
  let M := (ModuleCat.restrictScalars φ).obj (ModuleCat.of Λ V)
  let T := DerivedCategory.Plus.singleFunctor
    (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h ⋙
        DerivedCategory.Plus.homologyFunctor _ (q : ℤ)
  have : T.Additive := by
    dsimp [T, rightDerivedLowerStarPlus]
    infer_instance
  let A := constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}
  let F := forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1} ⋙ A ⋙ T
  have hΛ : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).IsLeftAdjoint := by
    change (ModuleCat.restrictScalars (Int.castRingHom Λ) ⋙
      forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsLeftAdjoint
    have : (ModuleCat.restrictScalars.{u + 1} (Int.castRingHom Λ)).IsLeftAdjoint :=
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1} (Int.castRingHom Λ)).isLeftAdjoint
    infer_instance
  have : Y.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    Sheaf.preservesSheafification_of_adjunction _
      (Adjunction.ofIsLeftAdjoint (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))
  let UΛ := sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : UΛ.PreservesZeroMorphisms := ⟨fun _ _ ↦ by rfl⟩
  have hcyclic (e : ℕ) (he : e ∣ d) :
      IsZero (F.obj (ModuleCat.of R (ULift.{u + 1} (ZMod e)))) := H e he
  have hM (x : M) : d • x = 0 := by
    change d • (show V from x) = 0
    rw [← Nat.cast_smul_eq_nsmul V]
    have hd : (d : V) = 0 := by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hd, zero_smul]
  let I := {N : Submodule R M // N.FG}
  have : Nonempty I := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  let : ∀ N : I, Module R N.1 := fun N ↦ N.1.module
  let D := ModuleCat.directLimitDiagram (R := R) (fun N : I ↦ (N.1 : Type (u + 1)))
    (Module.fgSystem R M)
  let c := ModuleCat.directLimitCocone (R := R) (fun N : I ↦ (N.1 : Type (u + 1)))
    (Module.fgSystem R M)
  have : PreservesColimitsOfShape I (A ⋙ T) :=
    preservesColimitsOfShape_constantAbelianHigherDirectImage h q I
  have hc : IsColimit c := ModuleCat.directLimitIsColimit _ _
  have hz : IsZero (F.obj c.pt) := (isColimitOfPreserves F hc).isZero_pt
    ((D ⋙ F).isZero (fun N ↦ by
      have : Module.Finite R N.1 := Module.Finite.iff_fg.mpr N.2
      have : Module.Finite ℤ R := inferInstance
      have : Module.Finite ℤ N.1 := Module.Finite.trans R N.1
      have : AddGroup.FG N.1 := Module.Finite.iff_addGroup_fg.mp inferInstance
      change IsZero (F.obj (@ModuleCat.of R _ N.1 _ N.1.module))
      apply ModuleCat.isZero_obj_of_fg_of_cyclic F _ d
      · intro x
        apply Subtype.ext
        exact hM x.val
      · exact hcyclic))
  let em : c.pt ≅ M := (Module.fgSystem.equiv R M).toModuleIso
  have hm : IsZero (F.obj M) := hz.of_iso (F.mapIso em.symm)
  have hv : IsZero (T.obj (A.obj (AddCommGrpCat.of V))) := hm
  obtain ⟨iΛ⟩ := nonempty_higherDirectImage_forget_iso Λ h (q : ℤ)
    (constantModSheaf Λ Y d)
  let jΛ := (constantCommuteCompose Y.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app (ModuleCat.of Λ V)
  have hforget : IsZero (UΛ.obj (higherDirectImage Λ h q (constantModSheaf Λ Y d))) :=
    hv.of_iso (iΛ ≪≫ T.mapIso jΛ)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply UΛ.zero_of_map_zero
  rw [UΛ.map_id]
  exact (IsZero.iff_id_eq_zero _).mp hforget

end AlgebraicGeometry.Etale
