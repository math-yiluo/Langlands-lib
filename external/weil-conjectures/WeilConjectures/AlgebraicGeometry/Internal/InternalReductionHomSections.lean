/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalPerfectReductionHomData
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CountableProducts

/-! # Lifting compatible families of maps between reductions

A compatible family of maps `T_n ⟶ K_n` between the derived reductions of two integral
complexes lifts to a map `T ⟶ K` whenever `K` is derived complete. This is the surjective
half of the Milnor sequence for `Hom(T, R lim K_n)`.

## Implementation details

By adjunction the family is a compatible family of maps from `T` to the restricted
reductions of `K`, i.e. a map to their product killed by `1 - shift`. The Roos triangle
exhibits `K` as the derived limit of these reductions, so this map factors through `K`,
and the reductions of the factorization are the given maps.

## References

* [Stacks Project, Tag 09C6](https://stacks.math.columbia.edu/tag/09C6)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.ProEtale

attribute [local instance] AdicCompletion.ringMonoidalObject AdicCompletion.ringCommutative
  AdicCompletion.finiteRingMonoidalObject AdicCompletion.finiteRingCommutative
  AdicCompletion.modulesMonoidal AdicCompletion.modulesSymmetric AdicCompletion.modulesClosed
  AdicCompletion.modulesMonoidalPreadditive AdicCompletion.finiteModulesDerived
  AdicCompletion.modulesDerived
  AdicCompletion.modulesProducts AdicCompletion.complexProducts
  AdicCompletion.modulesNatProducts AdicCompletion.complexNatProducts
  AdicCompletion.complexNatLimit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The adjoint of a map between `n`-th reductions, as a map to the restricted reduction. -/
private abbrev reductionAdjoint (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ)
    (φ : internalReductionHom l E W T K n) :
    T ⟶ AdicCompletion.integralLevel l E W K n :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E W n)).homEquiv
    _ _ φ

/-- The adjoints of a compatible pair of maps between reductions are compatible with the
transition of the integral reduction tower. -/
private theorem reductionAdjoint_step (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) (n : ℕ)
    (φ : internalReductionHom l E W T K (n + 1)) :
    reductionAdjoint l E W T K (n + 1) φ ≫ AdicCompletion.integralStep l E W K n =
      reductionAdjoint l E W T K n (internalReductionHomStep l E W T K n φ) := by
  let α := AdicCompletion.reductionComp l E W n
  let b := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.transition l E W n)
  let ρ := AdicCompletion.restrictComp l E W n
  let R := AdicCompletion.restrict l E W (n + 1)
  let ψ := internalReductionHomStep l E W T K n φ
  have hα : (AdicCompletion.finiteExtend l E W n).map φ ≫ α.hom.app K = α.hom.app T ≫ ψ := by
    simp only [ψ, internalReductionHomStep, α, Iso.hom_inv_id_app_assoc]
  have hmid : R.map φ ≫ AdicCompletion.integralStep l E W K n =
      AdicCompletion.integralStep l E W T n ≫ (AdicCompletion.restrict l E W n).map ψ := by
    have hb : φ ≫ b.unit.app ((AdicCompletion.derivedReduction l E W (n + 1)).obj K) =
        b.unit.app ((AdicCompletion.derivedReduction l E W (n + 1)).obj T) ≫
          (AdicCompletion.finiteRestrict l E W n).map
            ((AdicCompletion.finiteExtend l E W n).map φ) :=
      b.unit.naturality φ
    have hρ : R.map ((AdicCompletion.finiteRestrict l E W n).map ψ) ≫
        ρ.hom.app ((AdicCompletion.derivedReduction l E W n).obj K) =
        ρ.hom.app ((AdicCompletion.derivedReduction l E W n).obj T) ≫
          (AdicCompletion.restrict l E W n).map ψ :=
      ρ.hom.naturality ψ
    dsimp only [AdicCompletion.integralStep, AdicCompletion.derivedStep]
    calc R.map φ ≫ R.map (b.unit.app ((AdicCompletion.derivedReduction l E W (n + 1)).obj K) ≫
            (AdicCompletion.finiteRestrict l E W n).map (α.hom.app K)) ≫
          ρ.hom.app ((AdicCompletion.derivedReduction l E W n).obj K)
        _ = R.map (b.unit.app ((AdicCompletion.derivedReduction l E W (n + 1)).obj T) ≫
            (AdicCompletion.finiteRestrict l E W n).map (α.hom.app T)) ≫
            R.map ((AdicCompletion.finiteRestrict l E W n).map ψ) ≫
            ρ.hom.app ((AdicCompletion.derivedReduction l E W n).obj K) := by
          rw [← Functor.map_comp_assoc, reassoc_of% hb, ← Functor.map_comp, hα]
          simp only [Functor.map_comp, Category.assoc]
        _ = _ := by rw [hρ, Category.assoc]
  have hunit := AdicCompletion.reductionUnit_compatible l E W T n
  simp only [reductionAdjoint, Adjunction.homEquiv_unit, Category.assoc]
  erw [hmid, reassoc_of% hunit]

/-- A compatible family of maps between the derived reductions of `T` and of a derived
complete `K` is the family of reductions of a single map `T ⟶ K`. -/
theorem exists_hom_of_internalReductionHomTower_sections (W : Scheme.{u})
    (T K : DerivedCategory (AdicCompletion.Modules l E W)) (hK : IsDerivedComplete l E W K)
    (s : (internalReductionHomTower l E W T K).sections) :
    ∃ g : T ⟶ K, ∀ n : ℕ, (AdicCompletion.derivedReduction l E W n).map g = s.val (op n) := by
  obtain ⟨P, hP, ⟨eP⟩, hη⟩ := hK
  let c := AdicCompletion.completionMap l E W K P eP
  have : IsIso c := by
    have : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E W P)) := hη
    dsimp only [c, AdicCompletion.completionMap]
    infer_instance
  obtain ⟨p, δ, hT, hp⟩ := AdicCompletion.roos_isDerivedLimit l E W K P hP eP
  let f : ∀ n, T ⟶ AdicCompletion.integralLevel l E W K n :=
    fun n ↦ reductionAdjoint l E W T K n (s.val (op n))
  have hstep : ∀ n, f (n + 1) ≫ AdicCompletion.integralStep l E W K n = f n := by
    intro n
    have hs := s.property (homOfLE (Nat.le_succ n)).op
    dsimp only [internalReductionHomTower] at hs
    rw [Functor.ofOpSequence_map_homOfLE_succ] at hs
    change internalReductionHomStep l E W T K n (s.val (op (n + 1))) = s.val (op n) at hs
    simp only [f, reductionAdjoint_step, hs]
  have hzero : Pi.lift f ≫ towerTransitionEndomorphism (AdicCompletion.integralStep l E W K) =
      0 := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    simp [towerTransitionEndomorphism, towerProductShift, hstep]
  obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₂ _ hT (Pi.lift f) hzero
  refine ⟨g' ≫ inv c, fun n ↦ ?_⟩
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E W n)
  apply (adj.homEquiv _ _).injective
  change _ = f n
  rw [Adjunction.homEquiv_unit]
  have hu := adj.unit.naturality (g' ≫ inv c)
  dsimp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map] at hu
  rw [← hu]
  have hπ : c ≫ p ≫ Pi.π _ n = adj.unit.app K := by
    simpa only [Category.assoc, limit.lift_π, Fan.mk_π_app] using congrArg (· ≫ Pi.π _ n) hp
  have hf : g' ≫ p ≫ Pi.π _ n = f n := by
    simpa only [Triangle.mk_mor₁, Category.assoc, limit.lift_π, Fan.mk_π_app] using
      (congrArg (· ≫ Pi.π _ n) hg').symm
  rw [← hπ, Category.assoc, IsIso.inv_hom_id_assoc, hf]

end AlgebraicGeometry.ProEtale
