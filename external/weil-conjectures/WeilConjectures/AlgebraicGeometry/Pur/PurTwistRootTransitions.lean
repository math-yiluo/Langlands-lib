/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.EpiMono

/-! # Epimorphic transitions of the prime-power root tower

## References

* Stacks Project, Tag 03PK
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

/-- The power transitions of the root tower are epimorphisms when the prime
is invertible on the base. -/
theorem purTwistRootTransitions_epi (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)] (n : ℕ) :
    Epi (proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
      (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
      (pow_dvd_pow l (Nat.le_succ (n + 1)))) := by
  classical
  have hunit : IsUnit (l : Γ(S, ⊤)) := by
    apply S.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    rw [map_natCast]
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    change (S.residue x).hom (l : S.presheaf.stalk x) ≠ 0
    simpa only [map_natCast] using (isUnit_of_invertible (l : S.residueField x)).ne_zero
  let t := proEtaleRootsOfUnityTransition S (l ^ (n + 1)) (l ^ (n + 2))
    (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
    (pow_dvd_pow l (Nat.le_succ (n + 1)))
  apply (Sheaf.isLocallySurjective_iff_epi' (AddCommGrpCat.{u + 1}) t).mp
  constructor
  intro U x
  let a : Γ(U.left, ⊤)ˣ :=
    ((proEtaleRootsOfUnityInclusion S (l ^ (n + 1))).hom.app (op U) x).down.toMul
  have hlU : IsUnit (l : Γ(U.left, ⊤)) := by
    simpa only [map_natCast] using hunit.map U.hom.appTop.hom
  obtain ⟨V, f, hf, hsurj, ω, hω⟩ :=
    exists_etale_surjective_pow_eq_appTop (Fact.out : l.Prime).ne_zero hlU a.isUnit
  let := hf
  let := hsurj
  have hw : WeaklyEtale (f ≫ U.hom) := by have := U.prop; infer_instance
  let := hw
  let W : S.ProEt := ProEt.mk (f ≫ U.hom)
  let g : W ⟶ U := MorphismProperty.Over.homMk f rfl
  have hc : Presieve.ofArrows (fun _ : PUnit.{1} ↦ W) (fun _ ↦ g) ∈
      ProEt.precoverage S U := by
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    apply etalePrecoverage_le_proetalePrecoverage
    exact (ofArrows_mem_precoverage_iff _).mpr
      ⟨fun y ↦ ⟨PUnit.unit, hsurj.surj y⟩, fun _ ↦ hf⟩
  apply GrothendieckTopology.superset_covering _ _ (Precoverage.generate_mem_toGrothendieck hc)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  have hωu : IsUnit ω :=
    (isUnit_pow_iff (Fact.out : l.Prime).ne_zero).mp (hω ▸ a.isUnit.map f.appTop.hom)
  let z : Γ(V, ⊤)ˣ := hωu.unit
  have hz : z ^ (l ^ (n + 2)) = 1 := by
    apply Units.ext
    change (hωu.unit : Γ(V, ⊤)) ^ (l ^ (n + 2)) = 1
    rw [IsUnit.unit_spec, show n + 2 = (n + 1) + 1 by omega, pow_succ', pow_mul, hω,
      ← map_pow]
    have ha : a ^ (l ^ (n + 1)) = 1 := by
      have h := (proEtaleRootsOfUnitySections S (l ^ (n + 1)) (op U) x).toMul.property
      have he :=
        (existsUnique_proEtaleRootsOfUnitySections S (l ^ (n + 1)) (op U)).exists.choose_spec x
      have he' := congrArg (fun y ↦ y.down.toMul) he
      change _ = a at he'
      rw [← he']
      exact (mem_rootsOfUnity _ _).mp h
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_one] using
      congrArg f.appTop.hom (congrArg Units.val ha)
  let e := proEtaleRootsOfUnitySections S (l ^ (n + 2)) (op W)
  let y := e.symm (Additive.ofMul ⟨z, (mem_rootsOfUnity _ _).mpr hz⟩)
  refine ⟨y, ?_⟩
  have hm : Mono (proEtaleRootsOfUnityInclusion S (l ^ (n + 1))) := by
    dsimp [proEtaleRootsOfUnityInclusion]; infer_instance
  have : Mono (proEtaleRootsOfUnityInclusion S (l ^ (n + 1))).hom :=
    (sheafToPresheaf _ _).map_mono _
  apply (AddCommGrpCat.mono_iff_injective
    ((proEtaleRootsOfUnityInclusion S (l ^ (n + 1))).hom.app (op W))).mp inferInstance
  rw [proEtaleRootsOfUnityTransition_prime S l (Fact.out : l.Prime)]
  have hn := ConcreteCategory.congr_hom
    ((proEtaleRootsOfUnityInclusion S (l ^ (n + 1))).hom.naturality g.op) x
  change (proEtaleRootsOfUnityInclusion S (l ^ (n + 1))).hom.app (op W)
      ((proEtaleRootsOfUnitySheaf S (l ^ (n + 1))).obj.map g.op x) =
    (proEtaleUnitsSheaf S).obj.map g.op
      ((proEtaleRootsOfUnityInclusion S (l ^ (n + 1))).hom.app (op U) x) at hn
  rw [hn]
  have he := (existsUnique_proEtaleRootsOfUnitySections S (l ^ (n + 2)) (op W)).exists.choose_spec y
  have hey : e y = Additive.ofMul ⟨z, (mem_rootsOfUnity _ _).mpr hz⟩ := e.apply_symm_apply _
  change ULift.up (Additive.ofMul (e y).toMul.val) = _ at he
  rw [hey] at he
  rw [← he]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change (hωu.unit : Γ(V, ⊤)) ^ l = f.appTop (a : Γ(U.left, ⊤))
  rw [IsUnit.unit_spec, hω]

end AlgebraicGeometry.Scheme
