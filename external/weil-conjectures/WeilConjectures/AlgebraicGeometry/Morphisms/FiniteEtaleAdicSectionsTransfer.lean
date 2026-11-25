/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicUniqueLift
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsKernel

/-!
# Transfer of adic section comparison to finite étale covers

## References

* Stacks Project, Tag 0EKP, implication (1) to (3)
* Stacks Project, Tag 0EKP, implication (1) to (3), and finite affine base change for the direct
  image of the structure sheaf
-/

@[expose] public section

noncomputable section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The quotient-power thickening of an open of the ambient spectrum. -/
abbrev openThickening (f : R →+* S) (V : (Spec (.of R)).Opens) (n : ℕ) : Scheme :=
  Limits.pullback V.ι (baseMap f n)

/-- Restriction from the ambient open to its thickening. -/
abbrev openThickeningMap (f : R →+* S) (V : (Spec (.of R)).Opens) (n : ℕ) :
    openThickening f V n ⟶ V.toScheme :=
  pullback.fst V.ι (baseMap f n)

/-- Inclusion of consecutive thickenings of the ambient open. -/
noncomputable def openThickeningTransition (f : R →+* S)
    (V : (Spec (.of R)).Opens) (n : ℕ) :
    openThickening f V n ⟶ openThickening f V (n + 1) :=
  pullback.lift (openThickeningMap f V n)
    (pullback.snd V.ι (baseMap f n) ≫ baseTransition f n)
    (by rw [Category.assoc, baseTransition_comp_baseMap]; exact pullback.condition)

end AlgebraicGeometry.Scheme.FiniteEtale.Adic

namespace AlgebraicGeometry.Scheme

/-- Structure-sheaf comparison on an open of a Noetherian affine scheme implies
section comparison for every finite étale cover of that open. -/
theorem finiteEtale_adic_sections_comparison_of_structureSheaf
    {R S : Type u} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (f : R →+* S) (V : (Spec (.of R)).Opens)
    (hscalar : ∀ s : ∀ n : ℕ, Γ(FiniteEtale.Adic.openThickening f V n, ⊤),
      (∀ n, (FiniteEtale.Adic.openThickeningTransition f V n).appTop
        (s (n + 1)) = s n) →
      ∃! a : Γ(V.toScheme, ⊤), ∀ n,
        (FiniteEtale.Adic.openThickeningMap f V n).appTop a = s n)
    (P : V.toScheme.FiniteEtale)
    (s : ∀ n : ℕ, Γ(FiniteEtale.Adic.cover f V P n, ⊤))
    (hs : ∀ n, (FiniteEtale.Adic.coverTransition f V P n).appTop
      (s (n + 1)) = s n) :
    ∃! a : Γ(P.obj.left, ⊤), ∀ n,
      (FiniteEtale.Adic.coverMap f V P n).appTop a = s n := by
  classical
  obtain ⟨r, t, e, en, c, he, hen, hex, hzero, hres, htrans⟩ :=
    finiteEtale_adic_sections_kernel f V P
  have scalar_ext (a b : Γ(V.toScheme, ⊤))
      (h : ∀ n, (FiniteEtale.Adic.openThickeningMap f V n).appTop a =
        (FiniteEtale.Adic.openThickeningMap f V n).appTop b) : a = b := by
    have hb (n : ℕ) :
        (FiniteEtale.Adic.openThickeningTransition f V n).appTop
            ((FiniteEtale.Adic.openThickeningMap f V (n + 1)).appTop b) =
          (FiniteEtale.Adic.openThickeningMap f V n).appTop b := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      have hc : FiniteEtale.Adic.openThickeningTransition f V n ≫
          FiniteEtale.Adic.openThickeningMap f V (n + 1) =
          FiniteEtale.Adic.openThickeningMap f V n := by
        simp [FiniteEtale.Adic.openThickeningTransition, FiniteEtale.Adic.openThickeningMap]
      rw [hc]
    obtain ⟨z, hz, hu⟩ := hscalar
      (fun n ↦ (FiniteEtale.Adic.openThickeningMap f V n).appTop b) hb
    exact (hu a h).trans (hu b (fun _ ↦ rfl)).symm
  have hcoords (i : Fin r) (n : ℕ) :
      (FiniteEtale.Adic.openThickeningTransition f V n).appTop
        (en (n + 1) (s (n + 1)) i) = en n (s n) i := by
    change _ = en n (s n) i
    have ht := htrans n (s (n + 1)) i
    change en n ((FiniteEtale.Adic.coverTransition f V P n).appTop (s (n + 1))) i =
      (FiniteEtale.Adic.openThickeningTransition f V n).appTop
        (en (n + 1) (s (n + 1)) i) at ht
    rw [← ht, hs]
  choose x hx using fun i : Fin r ↦
    ExistsUnique.exists (hscalar (fun n ↦ en n (s n) i) (hcoords i))
  have hcx (j : Fin t) : ∑ i : Fin r, c j i * x i = 0 := by
    apply scalar_ext _ 0
    intro n
    simpa only [map_sum, map_mul, hx, map_zero] using hzero n (s n) j
  obtain ⟨a, ha⟩ := hex x hcx
  have has (n : ℕ) : (FiniteEtale.Adic.coverMap f V P n).appTop a = s n := by
    apply hen n
    funext i
    rw [hres, ha, hx]
  refine ⟨a, has, ?_⟩
  intro b hb
  apply he
  funext i
  apply scalar_ext
  intro n
  rw [← hres, ← hres, hb, has]

end AlgebraicGeometry.Scheme
