/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorOrbitComponentDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteProductPrincipalOpen
import Mathlib.Data.Fintype.EquivFin
import Mathlib.GroupTheory.GroupAction.Defs

/-! # Geometric fixed-orbit descent for affine torsors

## References

* Stacks Project, Tags 03SF and 0EYG
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Canonical orbit data for a finite permutation action.
-/
structure FixedOrbitData (G : Type u) [Group G] (d : ℕ) where
  action : G →* Equiv.Perm (Fin d)
  rel : Fin d → Fin d → Prop
  rel_spec : ∀ x y, rel x y ↔ ∃ g, action g x = y
  m : ℕ
  representative : Fin m → Fin d
  stabilizer : Fin m → Subgroup G
  complete : ∀ x, ∃ i, rel (representative i) x
  distinct : ∀ i j, rel (representative i) (representative j) → i = j
  stabilizer_spec : ∀ i g, g ∈ stabilizer i ↔ action g (representative i) = representative i

/-- Canonical quotient orbit data exists for every finite permutation action. -/
theorem fixedOrbitData_of_action
    (G : Type u) [Group G] [Finite G] (d : ℕ) (A : G →* Equiv.Perm (Fin d)) :
    ∃ D : FixedOrbitData G d, D.action = A := by
  classical
  let : MulAction G (Fin d) := MulAction.compHom (Fin d) A
  let s := MulAction.orbitRel G (Fin d)
  let Q := Quotient s
  let := Fintype.ofFinite Q
  let e := (Fintype.equivFin Q).symm
  let r : Fin (Fintype.card Q) → Fin d := fun i ↦ (e i).out
  refine ⟨{
    action := A
    rel := s
    rel_spec := ?_
    m := Fintype.card Q
    representative := r
    stabilizer := fun i ↦ MulAction.stabilizer G (r i)
    complete := ?_
    distinct := ?_
    stabilizer_spec := fun _ _ ↦ Iff.rfl }, rfl⟩
  · intro x y
    exact MulAction.mem_orbit_symm.trans MulAction.mem_orbit_iff
  · intro x
    refine ⟨e.symm (Quotient.mk s x), ?_⟩
    apply Quotient.exact
    simp only [r, Equiv.apply_symm_apply, Quotient.out_eq]
  · intro i j h
    apply e.injective
    have hq := Quotient.sound h
    simpa only [r, Quotient.out_eq] using hq

/-- Geometric fixed-orbit descent: if the orbit data `D` has the permutation action induced by
the pulled-back splitting `δ`, then the base change of `p` along `Spec H ⟶ Spec R` is isomorphic
over `Spec H` to the puncture `D(ι g)` of the spectrum of the product of the stabilizer fixed
subalgebras of `C`. -/
theorem affine_torsor_fixed_orbits_geometric
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    [IsFinite j] [Etale j]
    (hEt : Etale (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))))
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (d : ℕ) (D : FixedOrbitData G d)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (hD : D.action = fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
      p T t k hk d δ hδ) :
    let B := ∀ k : Fin D.m,
      (⨅ ζ : D.stabilizer k,
        AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  classical
  dsimp only
  let F := fun i : Fin D.m ↦
    (⨅ ζ : D.stabilizer i,
      AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  obtain ⟨e, he⟩ := affine_torsor_orbit_component_descent R H g ι C G ρ hρone hρmul
    hne p j hj hEt hrot d D.m D.representative D.stabilizer T t k hk δ hδ
    (by
      intro x
      obtain ⟨i, hi⟩ := D.complete x
      exact ⟨i, by simpa only [← hD] using (D.rel_spec _ _).mp hi⟩)
    (by
      intro i j hij
      apply D.distinct i j
      apply (D.rel_spec _ _).mpr
      simpa only [hD] using hij)
    (by
      intro i ζ
      simpa only [hD] using D.stabilizer_spec i ζ)
  obtain ⟨f, hf⟩ := finite_product_principal_open H (ι g) D.m (fun i ↦ F i)
  refine ⟨e ≪≫ f, ?_⟩
  change (e.hom ≫ f.hom) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  rw [hf]
  exact he

end AlgebraicGeometry.Scheme
