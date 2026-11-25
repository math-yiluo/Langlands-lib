/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import WeilConjectures.RingTheory.Depth
import WeilConjectures.AlgebraicGeometry.Morphisms.DepthTwoPunctureGlobalSections
import WeilConjectures.AlgebraicGeometry.Morphisms.PrincipalThickeningLocalDivision
import WeilConjectures.AlgebraicGeometry.PrincipalSectionStableAnnihilator

/-! # Eventual vanishing of scalar restriction kernels on principal punctures

## References

* Stacks Project, Tag 0H3E (the pro-isomorphism preceding the displayed diagram), and Tags 0BLD,
  0BK0 and 0AVY
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem bounded_local_division_gluing
    (X : Scheme.{u}) (g a : Γ(X, ⊤)) (c n : ℕ)
    (hkill : ∀ (V : X.Opens) (k : ℕ) (s : Γ(X, V)),
      (X.presheaf.map (homOfLE le_top).op g) ^ k * s = 0 →
      (X.presheaf.map (homOfLE le_top).op g) ^ c * s = 0)
    (hlocal : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧ ∃ b : Γ(X, V),
      X.presheaf.map (homOfLE le_top).op a =
        (X.presheaf.map (homOfLE le_top).op g) ^ (n + c + 1) * b) :
    ∃ b : Γ(X, ⊤), a = g ^ (n + 1) * b := by
  classical
  choose V hx b hb using hlocal
  let s (x : X) : Γ(X, V x) :=
    (X.presheaf.map (homOfLE le_top).op g) ^ c * b x
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hres (U V : X.Opens) (h : U ≤ V) (t : Γ(X, ⊤)) :
      X.presheaf.map (homOfLE h).op
        (X.presheaf.map (homOfLE le_top).op t) =
      X.presheaf.map (homOfLE le_top).op t := by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  have hcpt : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro x y
    let U := V x ⊓ V y
    let gx : Γ(X, U) := X.presheaf.map (homOfLE le_top).op g
    let bx : Γ(X, U) := X.presheaf.map (homOfLE inf_le_left).op (b x)
    let by' : Γ(X, U) := X.presheaf.map (homOfLE inf_le_right).op (b y)
    have he : gx ^ (n + c + 1) * bx = gx ^ (n + c + 1) * by' := by
      have hhx := congrArg (X.presheaf.map (homOfLE
        (inf_le_left : U ≤ V x)).op) (hb x)
      have hhy := congrArg (X.presheaf.map (homOfLE
        (inf_le_right : U ≤ V y)).op) (hb y)
      simp only [map_mul, map_pow, hres] at hhx hhy
      exact hhx.symm.trans hhy
    have hz : gx ^ c * (bx - by') = 0 :=
      hkill U (n + c + 1) (bx - by') (by rw [mul_sub, he, sub_self])
    have hs : gx ^ c * bx = gx ^ c * by' := by
      rwa [mul_sub, sub_eq_zero] at hz
    change X.presheaf.map (homOfLE (inf_le_left : U ≤ V x)).op (s x) =
      X.presheaf.map (homOfLE (inf_le_right : U ≤ V y)).op (s y)
    simpa only [s, map_mul, map_pow, hres] using hs
  obtain ⟨t, ht, _⟩ := (TopCat.Sheaf.existsUnique_gluing'
    ⟨X.presheaf, X.IsSheaf⟩ V ⊤ (fun _ ↦ homOfLE le_top) hcover s hcpt)
  refine ⟨t, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨X.presheaf, X.IsSheaf⟩ V ⊤
    (fun _ ↦ homOfLE le_top) hcover
  intro x
  rw [map_mul, map_pow, ht]
  dsimp only [s]
  rw [← mul_assoc, ← pow_add]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hb x

/-- A scalar vanishing on a sufficiently deep punctured thickening lies in a
prescribed power of the principal ideal. -/
theorem punctured_principal_restriction_kernel
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (g : R) (hg : g ∈ IsLocalRing.maximalIdeal R)
    (hdepth : (3 : ℕ∞) ≤ IsLocalRing.depth (R := R) R)
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    let f := Ideal.Quotient.mk (Ideal.span {g})
    let I := RingHom.ker f
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∀ a b : R,
      ((ΓSpecIso (.of R)).inv ≫
        (FiniteEtale.Adic.openThickeningMap f W m ≫ W.ι).appTop) a =
      ((ΓSpecIso (.of R)).inv ≫
        (FiniteEtale.Adic.openThickeningMap f W m ≫ W.ι).appTop) b →
      a - b ∈ I ^ (n + 1) := by
  classical
  have _ := hg
  dsimp only
  let f := Ideal.Quotient.mk (Ideal.span {g})
  let I := RingHom.ker f
  let ρ : CommRingCat.of R ⟶ Γ(W.toScheme, ⊤) :=
    (ΓSpecIso (.of R)).inv ≫ W.ι.appTop
  have htwo : (2 : ℕ∞) ≤ IsLocalRing.depth (R := R) R :=
    le_trans (by decide) hdepth
  have hρ : Function.Bijective ρ :=
    (depth_two_puncture_globalSections_bijective R htwo W hW).comp
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso (.of R)).inv)
  have : CompactSpace W := isCompact_iff_compactSpace.mp
    (TopologicalSpace.NoetherianSpace.isCompact (W : Set (Spec (.of R))))
  have : IsNoetherian W.toScheme := IsNoetherian.mk
  obtain ⟨c, hc⟩ := exists_principal_section_stable_annihilator W.toScheme (ρ g)
  intro n
  refine ⟨n + c, Nat.le_add_right n c, ?_⟩
  intro a b hab
  let t := ρ (a - b)
  have hz : (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop t = 0 := by
    have he : (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop (ρ a) =
        (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop (ρ b) := by
      simpa only [ρ, f, Scheme.Hom.comp_appTop, ← Category.assoc,
        ConcreteCategory.comp_apply]
        using hab
    change (FiniteEtale.Adic.openThickeningMap f W (n + c)).appTop (ρ (a - b)) = 0
    rw [map_sub, map_sub, he, sub_self]
  obtain ⟨s, hs⟩ := bounded_local_division_gluing W.toScheme (ρ g) t c n hc
    (principal_thickening_local_division R g W (n + c) t hz)
  obtain ⟨r, hr⟩ := hρ.surjective s
  have he : a - b = g ^ (n + 1) * r := by
    apply hρ.injective
    rw [map_mul, map_pow, hr]
    exact hs
  rw [he]
  apply Ideal.mul_mem_right
  apply Ideal.pow_mem_pow
  rw [Ideal.mk_ker]
  exact Ideal.subset_span (Set.mem_singleton g)

end AlgebraicGeometry.Scheme
