/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.CategoryTheory.Preadditive.FinitePowerCokernel
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatConstructibleComplex

/-! Serre closure for a finite spectral-sequence abutment. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Etale

universe u

namespace AlgebraicGeometry.Etale

/-- A constructible second page and a finite abutment filtration give constructible homology. -/
theorem constructible_spectral_abutment_object
    {Y : Scheme.{u}} {k : Type (u + 1)} [CommRing k] [Finite k]
    (E : E₂CohomologicalSpectralSequenceNat
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} k)))
    (H : ℕ → Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} k))
    (hE : ∀ p q : ℕ, Scheme.IsConstructibleSheaf ((E.page 2).X (p, q)))
    (hA : E.AbutsTo H) : ∀ n : ℕ, Scheme.IsConstructibleSheaf (H n) := by
  classical
  have hpages (r : ℤ) (hr : 2 ≤ r) :
      ∀ pq, Scheme.IsConstructibleSheaf ((E.page r hr).X pq) := by
    induction r, hr using Int.leInduction with
    | base =>
      intro pq
      exact hE pq.1 pq.2
    | succ r hr ih =>
      intro pq
      have : Scheme.IsConstructibleSheaf ((E.page r hr).sc pq).X₁ := ih _
      have : Scheme.IsConstructibleSheaf ((E.page r hr).sc pq).X₂ := ih _
      have : Scheme.IsConstructibleSheaf ((E.page r hr).sc pq).X₃ := ih _
      have : Scheme.IsConstructibleSheaf ((E.page r hr).homology pq) :=
        Scheme.IsConstructibleSheaf.homology ((E.page r hr).sc pq)
      exact Scheme.IsConstructibleSheaf.of_iso (E.iso r (r + 1) pq rfl hr)
  obtain ⟨A⟩ := hA
  intro n
  have hstep (p : ℕ) (hp : p ≤ n + 1) :
      Scheme.IsConstructibleSheaf (Subobject.underlying.obj (A.filtration n p)) := by
    induction hp using Nat.decreasingInduction with
    | self =>
      rw [A.filtration_succ_self]
      exact Scheme.IsConstructibleSheaf.of_isZero
        ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
    | of_succ p hp ih =>
      let f := Subobject.ofLE _ _ (A.filtration_succ_le n p)
      obtain ⟨e⟩ := A.nonempty_gradedIso n p (n - p) (by omega)
      have : Scheme.IsConstructibleSheaf (E.pageInfinity (p, n - p)) :=
        hpages _ (by omega) _
      have : Scheme.IsConstructibleSheaf (cokernel f) :=
        Scheme.IsConstructibleSheaf.of_iso e.symm
      have : Scheme.IsConstructibleSheaf
          (Subobject.underlying.obj (A.filtration n (p + 1))) := ih
      have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
        ⟨ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)⟩
      exact Scheme.IsConstructibleSheaf.of_shortExact hS
  have ht := hstep 0 (by omega)
  rw [A.filtration_zero] at ht
  have : Scheme.IsConstructibleSheaf
      (Subobject.underlying.obj (Subobject.mk (𝟙 (H n)))) := ht
  exact Scheme.IsConstructibleSheaf.of_iso (Subobject.underlyingIso (𝟙 (H n)))

end AlgebraicGeometry.Etale
