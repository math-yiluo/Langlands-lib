/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import Mathlib.RingTheory.Flat.EquationalCriterion
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses

/-! Flat constant module sheaves on arbitrary small sites. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
/-- Constant realization takes flat modules to flat module sheaves.
Source: Stacks Project, Tags 03ET and 08FC
(auxiliary; not a blueprint node).
Proof: lift the finitely many scalars and module sections in a relation on a common
cover. Local injectivity of the module sheafification unit refines that cover so
the lifted relation holds in the original module. Flatness factors this relation
through finitely many elements with vanishing coefficient relations. Apply the
ring and module sheafification units to this factorization. The local equational
criterion gives flatness, without points or a terminal object of the site. -/
theorem isFlatOnSite_constantModule
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (R : Type (max u v)) [CommRing R] (M : ModuleCat.{max u v} R)
    (hM : Module.Flat R M) :
    SheafOfModules.IsFlatOnSite.{u, v, max u v, max u v}
      (J := J) (R := realizationRing J R)
      ((commutativeSiteConstantModuleFunctor J R).obj M) := by
  classical
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  let N := (commutativeSiteConstantModuleFunctor J R).obj M
  let P := (siteConstantModulePresheafGeneral (C := C) R).obj M
  let η := toSheafify J P.presheaf
  let α := realizationRingUnit J R
  let τ := PresheafOfModules.toSheafify α η
  have ηsurj : Presheaf.IsLocallySurjective J η := inferInstance
  have ηinj : Presheaf.IsLocallyInjective J η := inferInstance
  have αsurj : Presheaf.IsLocallySurjective J α := inferInstance
  have hn (V W : Cᵒᵖ) (f : V ⟶ W) (x : M) :
      N.val.map f (η.app V x) = η.app W x :=
    (PresheafOfModules.naturality_apply τ f x).symm
  have hr (V W : Cᵒᵖ) (f : V ⟶ W) (a : R) :
      (realizationRing J R).obj.map f (α.app V a) = α.app W a :=
    (NatTrans.naturality_apply α f a).symm
  apply SheafOfModules.isFlatOnSite_of_local_equationalCriterion (realizationRing J R) N
  intro U n a s hs
  let T : Sieve U :=
    { arrows V f := ∃ (c : Fin n → R) (x : Fin n → M),
        (∀ i, α.app (op V) (c i) = (realizationRing J R).obj.map f.op (a i)) ∧
        (∀ i, η.app (op V) (x i) = N.val.map f.op (s i)) ∧
        (∑ i, c i • x i) = 0
      downward_closed := by
        intro V W f hf g
        obtain ⟨c, x, hc, hx, hcx⟩ := hf
        refine ⟨c, x, ?_, ?_, hcx⟩
        · intro i
          rw [← hr _ _ g.op, hc]
          exact ((realizationRing J R).obj.map_comp_apply f.op g.op (a i)).symm
        · intro i
          rw [← hn _ _ g.op, hx]
          exact (N.val.map_comp_apply f.op g.op (s i)).symm }
  have hT : T ∈ J U := by
    let A : J.Cover U := Finset.univ.inf fun i : Fin n ↦
      ⟨Presheaf.imageSieve α (a i), Presheaf.imageSieve_mem J α (a i)⟩
    let B : J.Cover U := Finset.univ.inf fun i : Fin n ↦
      ⟨Presheaf.imageSieve η (s i), Presheaf.imageSieve_mem J η (s i)⟩
    apply J.transitive (J.intersection_covering A.property B.property) T
    intro V f hf
    have hliftc (i : Fin n) : ∃ c : R,
        α.app (op V) c = (realizationRing J R).obj.map f.op (a i) := by
      exact (Finset.inf_le (Finset.mem_univ i) : A ≤ _) f hf.1
    have hliftx (i : Fin n) : ∃ x : M, η.app (op V) x = N.val.map f.op (s i) := by
      exact (Finset.inf_le (Finset.mem_univ i) : B ≤ _) f hf.2
    choose c hc using hliftc
    choose x hx using hliftx
    have heq : η.app (op V) (∑ i, c i • x i) = η.app (op V) 0 := by
      change (τ.app (op V)) (∑ i, c i • x i) = (τ.app (op V)) 0
      rw [map_sum, map_zero]
      simp_rw [map_smul]
      change (∑ i, (α.app (op V) (c i)) •
        (show N.val.obj (op V) from η.app (op V) (x i))) = 0
      calc
        _ = ∑ i, (show N.val.obj (op V) from N.val.map f.op (a i • s i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hc, hx]
          exact (N.val.map_smul f.op (a i) (s i)).symm
        _ = 0 := by
          have h := (map_sum (N.val.map f.op).hom.toAddMonoidHom
            (fun i ↦ a i • s i) Finset.univ).symm
          rw [hs, map_zero] at h
          convert h using 1 <;> rfl
    apply J.superset_covering _ (Presheaf.equalizerSieve_mem J η _ _ heq)
    intro W g hg
    refine ⟨c, x, ?_, ?_, ?_⟩
    · intro i
      rw [← hr _ _ g.op, hc]
      exact ((realizationRing J R).obj.map_comp_apply f.op g.op (a i)).symm
    · intro i
      rw [← hn _ _ g.op, hx]
      exact (N.val.map_comp_apply f.op g.op (s i)).symm
    · exact hg
  refine ⟨T, hT, ?_⟩
  intro V f hf
  obtain ⟨c, x, hc, hx, hcx⟩ := hf
  let := hM
  obtain ⟨l, b, t, hb, hbt⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hcx
  refine ⟨l, fun i j ↦ α.app (op V) (b i j), fun j ↦ η.app (op V) (t j), ?_, ?_⟩
  · intro i
    rw [← hx, hb]
    change (τ.app (op V)) (∑ j, b i j • t j) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact (τ.app (op V)).hom.map_smul (b i j) (t j)
  · intro j
    simp_rw [← hc]
    simpa only [map_sum, map_mul, map_zero] using
      congrArg (fun z : R ↦ α.app (op V) z) (hbt j)

end CategoryTheory
