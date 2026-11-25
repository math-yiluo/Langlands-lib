/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.CohomologyPowersIdealReesFinite
import WeilConjectures.Algebra.FiniteReesModuleGeneration

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- Image estimate for the transition maps, for every sufficiently large choice of c.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (1) and (2).
(blueprint: lem-weil-pbc-cohomology-powers-ideal-application-image)

Proof: Write M_r = H^q(X, J^r F) with the A-module structure in the statement.
The Rees finiteness theorem gives M = direct sum M_r finite over B = Rees(I), with
multiplication induced by scalar multiplication on the sheaves. The inclusions into F
are monic. Hence the assumed factorization identifies i with the canonical inclusions,
and cancellation of these monomorphisms proves that transition maps compose, commute
with the homogeneous products, and send the product by a in I^k to scalar multiplication
by a after transition from degree r+k to r. Applying cohomology preserves these identities.
Replace a finite generating set of M by all its nonzero homogeneous components and let
c0 bound their degrees (take c0 = 0 when M = 0). For c >= c0 and r >= c, comparing degree
r components of an expression in the generators, and factoring
I^(r-d) = I^(r-c) I^(c-d), shows M_r = B_(r-c) M_c.
Fix n,m with n+m >= c. If n >= c, this equality and the same factorization give
M_(n+m) = B_m M_n; transition takes each such product into I^m M_n.
If n < c, write k = n+m-c = m-(c-n). Generate M_(n+m) as B_k M_c and commute
transition with multiplication through M_c -> M_n. The resulting image lies in I^k M_n.
Additivity handles each finite sum. These two cases give the asserted exponent.
The argument works for every c >= c0, including m = 0, n = 0, and c = 0. -/
theorem cohomology_powers_ideal_image_bound
    (A : Type v) [CommRing A] [IsNoetherianRing A] {X : Scheme.{v}}
    (I : Ideal A) (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (q : ℕ)
    (i : ∀ (k n : ℕ), n ≤ k →
      (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι k).2 F ⟶
        Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))
    (hi : ∀ (k n : ℕ) (h : n ≤ k),
      i k n h ≫ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
        Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι k).2 F) :
    ∃ c0 : ℕ, ∀ c : ℕ, c0 ≤ c →
        (∀ (n m : ℕ), c ≤ n + m →
          LinearMap.range ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i (n + m) n (Nat.le_add_right n m)))).hom ≤
            I ^ (m - (c - n)) • (⊤ : Submodule A ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
                ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
                  (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F))))) := by
  classical
  let G := fun n ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F
  let inc := fun n ↦ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F
  let H := RingedSpace.moduleCohomology X.toRingedSpace q
  let R := ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let M := fun n ↦ (R.obj (H.obj (G n)) : Type v)
  obtain ⟨lam, hsection, hzero, mod, hfin, hact⟩ :=
    cohomology_powers_ideal_rees_finite f I J hJ F hF q
  let L := fun k n a ha ↦ (R.map (H.map (lam k n a ha))).hom
  obtain ⟨c0, hgen⟩ := finite_rees_module_single_degree_generation A I M L hzero mod hfin hact
  have hcompat (k c n : ℕ) (hn : n ≤ c) (a : A) (ha : a ∈ I ^ k) (x : M c) :
      (R.map (H.map (i (c + k) n (by omega)))).hom (L k c a ha x) =
        a • (R.map (H.map (i c n hn))).hom x := by
    have ha0 : a ∈ I ^ 0 := by simp
    have heq : lam k c a ha ≫ i (c + k) n (by omega) =
        i c n hn ≫ lam 0 n a ha0 := by
      have : Mono (inc n) := by
        dsimp [inc, Scheme.idealModuleProductι]
        infer_instance
      apply (cancel_mono (inc n)).1
      have hiinc : ∀ (r s : ℕ) (h : s ≤ r), i r s h ≫ inc s = inc r := hi
      simp only [Category.assoc, hiinc]
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext s
      have hc := hsection k c a ha U.unop s
      have hn' := hsection 0 n a ha0 U.unop ((i c n hn).val.app U s)
      have hi' := congrArg (fun g ↦ g.val.app U s) (hi c n hn)
      change (inc (c + k)).val.app U ((lam k c a ha).val.app U s) = _ at hc
      change (inc n).val.app U ((lam 0 n a ha0).val.app U
        ((i c n hn).val.app U s)) = _ at hn'
      change (inc n).val.app U ((i c n hn).val.app U s) = (inc c).val.app U s at hi'
      change (inc (c + k)).val.app U ((lam k c a ha).val.app U s) =
        (inc n).val.app U ((lam 0 n a ha0).val.app U ((i c n hn).val.app U s))
      exact hc.trans ((congrArg (fun t ↦
        (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          f.appLE ⊤ U.unop le_top).hom a) • t) hi'.symm).trans hn'.symm)
    have hx := congrArg (fun g ↦ (R.map (H.map g)).hom x) heq
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hx
    exact hx.trans (hzero n a ha0 ((R.map (H.map (i c n hn))).hom x))
  refine ⟨c0, fun c hc n m hnm ↦ ?_⟩
  let d := max c n
  have hd : c0 ≤ d := le_trans hc (le_max_left _ _)
  have hdle : d ≤ n + m := max_le hnm (Nat.le_add_right n m)
  let k := n + m - d
  have hdk : d + k = n + m := Nat.add_sub_of_le hdle
  have hk : k = m - (c - n) := by dsimp [k, d]; omega
  let t := (R.map (H.map (i (d + k) n (le_trans (le_max_right c n)
    (Nat.le_add_right d k))))).hom
  have ht : LinearMap.range t ≤ I ^ k • (⊤ : Submodule A (M n)) := by
    rw [LinearMap.range_le_iff_comap, ← top_le_iff, ← hgen d hd k]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, x⟩, rfl⟩
    change t (L k d a a.property x) ∈ I ^ k • (⊤ : Submodule A (M n))
    rw [show t (L k d a a.property x) =
      (a : A) • (R.map (H.map (i d n (le_max_right c n)))).hom x from
        hcompat k d n (le_max_right c n) a a.property x]
    exact Submodule.smul_mem_smul a.property (Submodule.mem_top)
  have hndk : n ≤ d + k := le_trans (le_max_right c n) (Nat.le_add_right d k)
  have ht' (r : ℕ) (hr : d + k = r) :
      LinearMap.range ((R.map (H.map (i r n (by omega)))).hom) ≤
        I ^ k • (⊤ : Submodule A (M n)) := by
    subst r
    exact ht
  rw [← hk]
  exact ht' (n + m) hdk

end AlgebraicGeometry
