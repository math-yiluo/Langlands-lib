/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.Algebra.Homology.ModuleStalkExact

/-! # Power annihilation of a kernel-pullback projection cokernel

Source: Stacks Project, Tags 0889(1) and 0CYV(2).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem zero_iff_stalks {X : Scheme.{u}} (F : X.Modules) :
    IsZero F ↔ ∀ x : X,
      IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) := by
  have hf : IsZero F ↔ IsZero ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) := by
    rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero,
      ← (SheafOfModules.toSheaf X.ringCatSheaf).map_id F, Functor.map_eq_zero_iff]
  rw [hf, TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  apply forall_congr'
  intro x
  let A := forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat
  change IsZero (A.obj ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)) ↔ _
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero,
    ← A.map_id ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F),
    Functor.map_eq_zero_iff]

set_option backward.isDefEq.respectTransparency false in
private theorem power_stalk_range {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) (x : X) (k : ℕ) (hk : 1 ≤ k)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    LinearMap.range (S.map (Scheme.idealModuleProductι
      (Scheme.idealSheafPower J.toModulesι k).2 F)).hom =
      (LinearMap.range (S.map J.toModulesι ≫ e.hom).hom :
        Ideal (X.presheaf.stalk x)) ^ k • ⊤ := by
  obtain ⟨e', he', _, _, _, _, hp⟩ := Scheme.ideal_module_product_stalk J.toModulesι F x
  have ee : e' = e := by
    apply Iso.ext
    ext m
    obtain ⟨U, hx, m, rfl⟩ :=
      TopCat.Presheaf.exists_germ_eq (SheafOfModules.unit X.ringCatSheaf).val.presheaf m
    exact (he' U hx m).trans (he U hx m).symm
  subst e'
  exact (hp k hk).2.1

private theorem product_inclusion_mono {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) (k : ℕ) :
    Mono (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  dsimp [Scheme.idealModuleProductι]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem power_stalk_zero_iff {X : Scheme.{u}} (J : X.IdealSheafData)
    (F : X.Modules) (x : X) (k : ℕ) (hk : 1 ≤ k)
    (e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
        ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x))
    (he : ∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
      e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
        U x hx r) = X.presheaf.germ U x hx r) :
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    IsZero (S.obj (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F)) ↔
      ∀ r ∈ (LinearMap.range (S.map J.toModulesι ≫ e.hom).hom :
        Ideal (X.presheaf.stalk x)) ^ k, ∀ m : S.obj F, r • m = 0 := by
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  let b := Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F
  have : Mono b := product_inclusion_mono J F k
  have hr := power_stalk_range J F x k hk e he
  have hz : IsZero (S.obj (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι k).2 F)) ↔
      LinearMap.range (S.map b).hom = ⊥ := by
    rw [ModuleCat.isZero_iff_subsingleton]
    constructor
    · intro h
      let _ := h
      apply le_antisymm _ bot_le
      rintro _ ⟨m, rfl⟩
      simp [Subsingleton.elim m 0]
    · intro h
      constructor
      intro a b'
      apply (ModuleCat.mono_iff_injective _).mp
        ((RingedSpace.module_stalk_exact X.toRingedSpace b).1
          (fun U ↦ (ModuleCat.mono_iff_injective _).mp
            (Functor.map_mono (SheafOfModules.evaluation X.ringCatSheaf (op U)) b)) x)
      have ha : (S.map b).hom a = 0 := by
        have hm : (S.map b).hom a ∈ LinearMap.range (S.map b).hom := ⟨a, rfl⟩
        simpa [h] using hm
      have hb : (S.map b).hom b' = 0 := by
        have hm : (S.map b).hom b' ∈ LinearMap.range (S.map b).hom := ⟨b', rfl⟩
        simpa [h] using hm
      exact ha.trans hb.symm
  dsimp only
  rw [hz, hr, eq_bot_iff, Submodule.smul_le]
  simp only [Submodule.mem_top, Submodule.mem_bot, forall_true_left]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a pullback projection to a kernel with power-annihilated target
increases its cokernel annihilator by at most that power. Only the cokernel of a'
is used; neither its kernel nor formal compatibility is needed.

Source: Stacks Project, Tag 0889(1), comparison away from the adic closed subset;
the annihilator extension argument is the one in Tag 0CYV(2).
Proof: Work at an arbitrary stalk. Exactness of module stalks preserves the kernel
and the pullback. Write P = F ×_H F' and E = ker(d). The cokernel of P -> F embeds
into coker(a'), by sending the class of x to the class of a(x). Hence I^s kills it.
The quotient P/E embeds into the target G/I^(n+1)G, so I^(n+1) kills it. In the
cokernel C of E -> F, the image of P -> F is a quotient of P/E and is killed by
I^(n+1); the quotient by that image is coker(P -> F), killed by I^s. Multiplying
these annihilators kills C by I^(s+n+1). The ideal-product stalk formula and the
zero-stalk criterion give the stated sheaf annihilation. This includes J=0 and J=1,
zero modules and the empty scheme; it does not require finite generation.
(blueprint: lem-weil-pbc-finite-kernel-pullback-cokernel-annihilated). -/
theorem finiteKernelPullback_cokernel_annihilated
    {X : Scheme.{u}} (J : X.IdealSheafData)
    {F F' H G : X.Modules} (a : F ⟶ H) (a' : F' ⟶ H)
    (s : ℕ) (hs : 1 ≤ s)
    (hc : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι s).2 (cokernel a')))
    (n : ℕ) (d : pullback a a' ⟶ formalModuleQuotient J (n + 1) G) :
    IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower J.toModulesι (s + n + 1)).2
        (cokernel (kernel.ι d ≫ pullback.fst a a'))) := by
  let p := pullback.fst a a'
  let k := kernel.ι d
  let T := (kernelCokernelCompSequence_exact k p).sc 3
  let v : cokernel p ⟶ cokernel a' :=
    cokernel.map p a' (pullback.snd a a') a pullback.condition
  have hv : Mono v := Abelian.mono_cokernel_map_of_isPullback
    (IsPullback.of_hasPullback a a')
  let u : cokernel k ⟶ formalModuleQuotient J (n + 1) G := Abelian.factorThruCoimage d
  have hu : Mono u := inferInstanceAs (Mono (Abelian.factorThruCoimage d))
  apply (zero_iff_stalks _).mpr
  intro x
  let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
  have : S.PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms_proof X.toRingedSpace x
  obtain ⟨e, he, _, _, _, _, hp⟩ :=
    Scheme.ideal_module_product_stalk J.toModulesι G x
  let I : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map J.toModulesι ≫ e.hom).hom
  have hQ : ∀ r ∈ I ^ (n + 1),
      ∀ m : S.obj (formalModuleQuotient J (n + 1) G), r • m = 0 := by
    obtain ⟨_, _, φ, hφ⟩ := hp (n + 1) (by omega)
    intro r hr m
    obtain ⟨z, rfl⟩ := φ.surjective m
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [← φ.map_smul]
    have hz : r • (Submodule.Quotient.mk z :
        S.obj G ⧸ I ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) (S.obj G))) = 0 := by
      change Submodule.Quotient.mk (r • z) = 0
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    rw [hz, map_zero]
  have hA : ∀ r ∈ I ^ (n + 1), ∀ m : S.obj (cokernel k), r • m = 0 := by
    intro r hr m
    apply (ModuleCat.mono_iff_injective _).mp
      ((RingedSpace.module_stalk_exact X.toRingedSpace u).1
        (fun U ↦ (ModuleCat.mono_iff_injective _).mp
          (Functor.map_mono (SheafOfModules.evaluation X.ringCatSheaf (op U)) u)) x)
    rw [map_smul, map_zero]
    exact hQ r hr _
  have hC' := (power_stalk_zero_iff J (cokernel a') x s hs e he).mp
    ((zero_iff_stalks _).mp hc x)
  have hC : ∀ r ∈ I ^ s, ∀ m : S.obj (cokernel p), r • m = 0 := by
    intro r hr m
    apply (ModuleCat.mono_iff_injective _).mp
      ((RingedSpace.module_stalk_exact X.toRingedSpace v).1
        (fun U ↦ (ModuleCat.mono_iff_injective _).mp
          (Functor.map_mono (SheafOfModules.evaluation X.ringCatSheaf (op U)) v)) x)
    rw [map_smul, map_zero]
    exact hC' r hr _
  have hT : T.Exact := (kernelCokernelCompSequence_exact k p).exact 3
  have hTx : (T.map S).Exact :=
    ((RingedSpace.module_stalk_exact X.toRingedSpace T.f).2.2.2.2
      T.X₃ T.f T.g T.zero).mp hT x
  have hex := (T.map S).moduleCat_exact_iff.mp hTx
  apply (power_stalk_zero_iff J _ x (s + n + 1) (by omega) e he).mpr
  have hann : I ^ (n + 1) * I ^ s ≤
      (⊤ : Submodule (X.presheaf.stalk x) (S.obj T.X₂)).annihilator := by
    apply Ideal.mul_le.mpr
    intro r hr t ht
    apply Submodule.mem_annihilator.mpr
    intro b hb
    have hz : (S.map T.g).hom (t • b) = 0 := by
      rw [map_smul]
      exact hC t ht _
    obtain ⟨z, hz⟩ := hex (t • b) hz
    change (S.map T.f).hom z = t • b at hz
    rw [mul_smul, ← hz, ← map_smul, hA r hr z, map_zero]
  intro r hr m
  have hpow : I ^ (s + n + 1) = I ^ (n + 1) * I ^ s := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hr
  exact Submodule.mem_annihilator.mp (hann hr) m Submodule.mem_top

end AlgebraicGeometry
