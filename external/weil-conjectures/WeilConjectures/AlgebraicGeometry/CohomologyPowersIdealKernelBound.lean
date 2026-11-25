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
import WeilConjectures.Algebra.Module.ReesKernelGenerators

@[expose] public section

universe v

open CategoryTheory

namespace AlgebraicGeometry

/-- Kernel estimate for the transition maps, for every sufficiently large choice of c.
Source: Stacks Project, Cohomology of Schemes, Lemma 02OA, proof of (3).
(blueprint: lem-weil-pbc-cohomology-powers-ideal-application-kernel)

Proof: Set M_r = H^q(X, J^r F), B = Rees(I), and K_r = ker(M_r -> M_0).
Rees finiteness makes M = direct sum M_r a finite B-module. Cancellation of the monic
inclusions into F identifies the assumed i with the canonical transition maps and proves
composition and compatibility with homogeneous multiplication. Apply cohomology to get
these identities on M. Compatibility implies K = direct sum K_r is a B-submodule:
for a in I^k and y in K_r, the image of a*y in M_0 factors through a*(image of y in M_0),
which is zero. As B is Noetherian, K is finite. Replace its finite generators by their
nonzero homogeneous components y_j in K_(d_j) and let c0 bound all d_j, taking zero for
the empty set. Degree n components express every x in K_n as a sum b_j*y_j with
b_j in I^(n-d_j). For c >= c0 and n >= c, transition from n to n-d_j sends this term
to b_j*(image of y_j in M_0) = 0. Because d_j <= c, it therefore also vanishes after
transition to n-c. This proves K_n is contained in ker(M_n -> M_(n-c)).
The reverse inclusion follows from composition of M_n -> M_(n-c) -> M_0.
All c >= c0 work; if K = 0 the empty generating set proves the same assertion, and
at n = c the two maps have the same target and coincide. -/
theorem cohomology_powers_ideal_kernel_bound
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
(∀ n : ℕ, c ≤ n →
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map (i n 0 (Nat.zero_le n)))).hom =
          LinearMap.ker ((ModuleCat.restrictScalars
              ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
            ((RingedSpace.moduleCohomology X.toRingedSpace q).map
              (i n (n - c) (Nat.sub_le n c)))).hom) := by
  classical
  let G := fun n ↦ Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι n).2 F
  let j := fun n ↦ Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F
  let H := RingedSpace.moduleCohomology X.toRingedSpace q ⋙
    ModuleCat.restrictScalars ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let M := fun n ↦ (H.obj (G n) : Type v)
  let t := fun (k n : ℕ) (h : n ≤ k) ↦ (H.map (i k n h)).hom
  have hj (n : ℕ) : Mono (j n) := by
    dsimp [j, Scheme.idealModuleProductι]
    let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
    infer_instance
  have icomp (k m n : ℕ) (hm : m ≤ k) (hn : n ≤ m) :
      i k m hm ≫ i m n hn = i k n (hn.trans hm) := by
    let := hj n
    apply (cancel_mono (j n)).1
    change (i k m hm ≫ i m n hn) ≫
      Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F =
      i k n (hn.trans hm) ≫
        Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι n).2 F
    rw [Category.assoc, hi, hi, hi]
  have tcomp (k m n : ℕ) (hm : m ≤ k) (hn : n ≤ m) (x : M k) :
      t m n hn (t k m hm x) = t k n (hn.trans hm) x := by
    have he := congrArg H.map (icomp k m n hm hn)
    rw [H.map_comp] at he
    exact CategoryTheory.congr_fun he x
  obtain ⟨lam, hsection, _, mod, hfin, hact⟩ :=
    cohomology_powers_ideal_rees_finite f I J hJ F hF q
  let mu := fun (k m : ℕ) (a : A) (ha : a ∈ I ^ k) ↦ (H.map (lam k m a ha)).hom
  have compat (k m : ℕ) (a : A) (ha : a ∈ I ^ k) :
      lam k m a ha ≫ i (m + k) (0 + k) (by omega) =
        i m 0 (Nat.zero_le m) ≫ lam k 0 a ha := by
    let := hj (0 + k)
    apply (cancel_mono (j (0 + k))).1
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext s
    have hleft := CategoryTheory.congr_fun
      (congrArg (fun g ↦ g.val.app U) (hi (m + k) (0 + k) (by omega)))
      ((lam k m a ha).val.app U s)
    have hright := CategoryTheory.congr_fun
      (congrArg (fun g ↦ g.val.app U) (hi m 0 (Nat.zero_le m))) s
    change (j (0 + k)).val.app U
      ((i (m + k) (0 + k) _).val.app U ((lam k m a ha).val.app U s)) =
      (j (0 + k)).val.app U ((lam k 0 a ha).val.app U ((i m 0 (Nat.zero_le m)).val.app U s))
    change (j (0 + k)).val.app U
      ((i (m + k) (0 + k) _).val.app U ((lam k m a ha).val.app U s)) =
      (j (m + k)).val.app U ((lam k m a ha).val.app U s) at hleft
    change (j 0).val.app U ((i m 0 (Nat.zero_le m)).val.app U s) = (j m).val.app U s at hright
    rw [hleft]
    have hl := hsection k m a ha U.unop s
    have hr := hsection k 0 a ha U.unop ((i m 0 (Nat.zero_le m)).val.app U s)
    change (j (m + k)).val.app U ((lam k m a ha).val.app U s) =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top).hom a) •
        (j m).val.app U s at hl
    change (j (0 + k)).val.app U ((lam k 0 a ha).val.app U
      ((i m 0 (Nat.zero_le m)).val.app U s)) =
      (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top).hom a) •
        (j 0).val.app U ((i m 0 (Nat.zero_le m)).val.app U s) at hr
    rw [hl, hr, hright]
  have mucompat (k m : ℕ) (a : A) (ha : a ∈ I ^ k) (x : M m) :
      t (m + k) (0 + k) (by omega) (mu k m a ha x) =
        mu k 0 a ha (t m 0 (Nat.zero_le m) x) := by
    have he := congrArg H.map (compat k m a ha)
    simp only [H.map_comp] at he
    exact CategoryTheory.congr_fun he x
  let K := fun n ↦ LinearMap.ker (t n 0 (Nat.zero_le n))
  have hK (k m : ℕ) (a : A) (ha : a ∈ I ^ k) (y : M m) (hy : y ∈ K m) :
      mu k m a ha y ∈ K (m + k) := by
    change t (m + k) 0 _ (mu k m a ha y) = 0
    rw [← tcomp (m + k) (0 + k) 0 (by omega) (Nat.zero_le (0 + k)), mucompat]
    change t m 0 _ y = 0 at hy
    rw [hy, map_zero, map_zero]
  obtain ⟨c0, hgen⟩ := ReesAlgebra.bounded_generators A I M mu mod hfin hact K hK
  refine ⟨c0, fun c hc n hn ↦ ?_⟩
  change K n = LinearMap.ker (t n (n - c) (Nat.sub_le n c))
  apply le_antisymm
  · apply le_trans (hgen n)
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨d, k, he, hd, a, ha, y, hy, rfl⟩ := hz
    subst n
    have htarget : d + k - c ≤ 0 + k := by omega
    change t (d + k) (d + k - c) _ (mu k d a ha y) = 0
    rw [← tcomp (d + k) (0 + k) (d + k - c) (by omega) htarget,
      mucompat]
    change t d 0 _ y = 0 at hy
    rw [hy, map_zero, map_zero]
  · intro x hx
    change t n 0 _ x = 0
    rw [← tcomp n (n - c) 0 (Nat.sub_le n c) (Nat.zero_le (n - c))]
    change t n (n - c) _ x = 0 at hx
    rw [hx, map_zero]

end AlgebraicGeometry
