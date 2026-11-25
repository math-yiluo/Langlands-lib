/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesAbelian

/-! # Epimorphisms of coherent formal modules

Source: Stacks Project, Cohomology of Schemes, Lemma 087Y
(blueprint: lem-weil-pbc-formal-systems-surjective).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Power-annihilated Nakayama on stalks; Stacks, Algebra, Lemma 00DV (9). -/
private theorem isZero_of_quotient_and_power {X : Scheme.{u}}
    (I : X.IdealSheafData) (F : X.Modules) (n : ℕ)
    (hq : Limits.IsZero (formalModuleQuotient I (n + 1) F))
    (hp : Limits.IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower I.toModulesι (n + 2)).2 F)) : Limits.IsZero F := by
  have hstalk (x : X) : Limits.IsZero ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F)
      := by
    let S := RingedSpace.moduleStalkFunctor X.toRingedSpace x
    obtain ⟨e, he, hinj, hpinj, hr, hquot, hpow⟩ :=
      Scheme.ideal_module_product_stalk I.toModulesι F x
    let J : Ideal (X.presheaf.stalk x) := LinearMap.range (S.map I.toModulesι ≫ e.hom).hom
    have ht : J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) = ⊤ := by
      obtain ⟨_, _, φ, hφ⟩ := hpow (n + 1) (by omega)
      have hz : Limits.IsZero (S.obj (formalModuleQuotient I (n + 1) F)) := S.map_isZero hq
      have : Subsingleton (S.obj (Limits.cokernel (Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 1)).2 F))) :=
        ModuleCat.subsingleton_of_isZero hz
      apply top_unique
      intro y _
      have hy : (Submodule.Quotient.mk y :
          S.obj F ⧸ J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F))) = 0 :=
        φ.injective (Subsingleton.elim _ _)
      exact (Submodule.Quotient.mk_eq_zero _).mp hy
    have hb : J ^ (n + 2) • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) = ⊥ := by
      obtain ⟨_, hrange, _⟩ := hpow (n + 2) (by omega)
      have hz : S.map (Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 2)).2 F) = 0 := by
        rw [hp.eq_zero_of_src (Scheme.idealModuleProductι
          (Scheme.idealSheafPower I.toModulesι (n + 2)).2 F), S.map_zero]
      rw [← hrange, hz]
      exact LinearMap.range_zero
    have hJ : J • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) = ⊤ := by
      apply top_unique
      calc
        ⊤ = J ^ (n + 1) • ⊤ := ht.symm
        _ ≤ J • ⊤ := Submodule.smul_mono (Ideal.pow_le_self (by omega)) le_rfl
    have htop (k : ℕ) :
        J ^ k • (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) = ⊤ := by
      induction k with
      | zero => simp [Ideal.one_eq_top]
      | succ k ih => rw [pow_succ, Submodule.mul_smul, hJ, ih]
    have htb : (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) = ⊥ :=
      (htop (n + 2)).symm.trans hb
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact ⟨fun y z ↦ by
      have hy : y = 0 := by simpa only [htb, Submodule.mem_bot] using (show y ∈
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) from Submodule.mem_top)
      have hz : z = 0 := by simpa only [htb, Submodule.mem_bot] using (show z ∈
        (⊤ : Submodule (X.presheaf.stalk x) (S.obj F)) from Submodule.mem_top)
      exact hy.trans hz.symm⟩
  apply (Limits.IsZero.iff_id_eq_zero F).mpr
  ext U s
  change s = 0
  apply TopCat.Presheaf.section_ext ⟨F.presheaf, F.isSheaf⟩ U s 0
  intro x hx
  have hs : Subsingleton ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj F) :=
    ModuleCat.subsingleton_of_isZero (hstalk x)
  exact hs.elim _ _

/-- Induction through the defining quotient isomorphisms detects the zero formal object. -/
private theorem isZero_of_first_component {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F : CoherentFormalModule X I)
    (hF : Limits.IsZero (F.obj.obj (op 0))) : Limits.IsZero F := by
  have hn (n : ℕ) : Limits.IsZero (F.obj.obj (op n)) := by
    induction n with
    | zero => exact hF
    | succ n ih =>
      obtain ⟨e, he⟩ := F.property.2.2 n
      exact isZero_of_quotient_and_power I _ n (ih.of_iso e) (F.property.2.1 (n + 1))
  apply Limits.IsZero.of_full_of_faithful_of_isZero (IsCoherentFormalModule I).ι
  exact Functor.isZero F.obj (fun n ↦ hn n.unop)

/-- A morphism in Coh(X,I) is an epimorphism exactly when its first component is an
 epimorphism of O_X-modules. In the shared indexing convention, `op 0` denotes level 1.

Source: Stacks Project, Cohomology of Schemes, Lemma 087Y
(blueprint: lem-weil-pbc-formal-systems-surjective).

Proof:
1. Take the Limits.cokernel cofork supplied by `coherentFormalModule_abelian`. Its evaluation
at each level is colimiting. The preadditive epi/Limits.cokernel criterion reduces the two
assertions to vanishing of the formal Limits.cokernel and vanishing of its first component.
2. For a module H, suppose H/I^(n+1)H is zero and I^(n+2)H is zero. At a stalk, the
ideal-product and quotient formulas give J^(n+1)H_x = H_x and J^(n+2)H_x = 0.
Since J^(n+1) is contained in J, we have JH_x = H_x. Induction using the product
of ideals gives J^k H_x = H_x for every k. Taking k = n+2 makes H_x zero.
Section extensionality makes every section zero, so the identity of H is zero.
This is the power-annihilated version
of the elementary nilpotent Nakayama argument in Stacks, Algebra, Lemma 00DV (9).
3. Starting from a zero first component, induct on n. The defining quotient
isomorphism identifies level n with level n+1 modulo I^(n+1); level n+1 is killed
by I^(n+2). Step 2 therefore makes level n+1 zero. Every component is zero,
hence the inverse system is zero; the full inclusion reflects zero objects.
4. A zero formal Limits.cokernel gives a zero first component by evaluation. Conversely,
a zero first component gives a zero formal Limits.cokernel by Step 3. Apply Step 1.
-/
theorem coherentFormalModule_epi_iff_first_component {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentFormalModule X I} (α : F ⟶ G) :
    Epi α ↔ Epi (α.hom.app (op 0)) := by
  classical
  obtain ⟨hA, hc⟩ := coherentFormalModule_abelian X I
  have : Abelian (CoherentFormalModule X I) := Classical.choice hA
  obtain ⟨c, hc, hn⟩ := hc F G α
  let T (n : ℕ) := (IsCoherentFormalModule I).ι ⋙
    (evaluation ℕᵒᵖ X.Modules).obj (op n)
  have hcn (n : ℕ) : Limits.IsColimit (c.map (T n)) :=
    (Limits.CokernelCofork.isColimitMapCoconeEquiv c (T n)).toFun (Classical.choice (hn n))
  constructor
  · intro hα
    have hz : Limits.IsZero c.pt :=
      (Preadditive.epi_iff_isZero_cokernel' c (Classical.choice hc)).mp hα
    exact (Preadditive.epi_iff_isZero_cokernel' (c.map (T 0)) (hcn 0)).mpr
      ((T 0).map_isZero hz)
  · intro hα
    have hz : Limits.IsZero ((T 0).obj c.pt) :=
      (Preadditive.epi_iff_isZero_cokernel' (c.map (T 0)) (hcn 0)).mp hα
    exact (Preadditive.epi_iff_isZero_cokernel' c (Classical.choice hc)).mpr
      (isZero_of_first_component I c.pt hz)

end AlgebraicGeometry
