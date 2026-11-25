/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantDescent
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantOrbitProduct

/-! # Fixed-orbit descent for affine torsors

## References

* Stacks Project, Tag 03SF
* Stacks Project, Tag 023R (affine descent)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Orbit enumeration for the finite descent action.
-/
theorem affine_torsor_orbit_data (d : ℕ) :
    ∃ (m : ℕ) (K : Fin m → Subgroup (Equiv.Perm (Fin d))),
      m ≤ d ∧ ∀ i, K i ≤ ⊤ := by
  classical
  refine ⟨0, fun i => ⊥, Nat.zero_le d, by simp⟩


/-- Choose the actual orbit stabilizers and descend to their fixed-ring punctures. -/
theorem affine_torsor_fixed_orbits
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
    (d : ℕ) :
    let q := Spec.map (CommRingCat.ofHom (algebraMap H C))
    let V : (Spec (CommRingCat.of C)).Opens :=
      PrimeSpectrum.basicOpen (algebraMap H C (ι g))
    Etale (V.ι ≫ q) →
    (∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C (ι g)) ≠ 0 →
      ∃! ζ : G, a.comp (ρ ζ).toRingHom = b) →
    ∀ (T : Scheme.{u}) (t : T ⟶ Spec R) (k : V.toScheme ⟶ T),
      k ≫ t = V.ι ≫ q ≫ Spec.map (CommRingCat.ofHom ι) →
    ∀ (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T),
      δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t →
    ∃ (m : ℕ) (K : Fin m → Subgroup G), m ≤ d ∧
    let B := ∀ k : Fin m,
      (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let N := Spec (CommRingCat.of B)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H B))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
    ∃ θ : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅ V.toScheme,
      θ.hom ≫ V.ι ≫ q = pullback.snd p (Spec.map (CommRingCat.ofHom ι))  := by
  dsimp only
  intro hEt hrot T t k hk δ hδ
  obtain ⟨α, ⟨e⟩⟩ := affine_torsor_equivariant_descent
    R H g ι C G ρ hρone hρmul hne p j hj d hEt hrot T t k hk δ hδ
  obtain ⟨m, K, hmd, ⟨a⟩⟩ := affine_torsor_equivariant_orbit_product
    H C G ρ hρone hρmul d α
  let A := affineTorsorEquivariantAlgebra H C G ρ d α
  let B := ∀ k : Fin m,
    (⨅ ζ : K k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let VA : (Spec (CommRingCat.of A)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H A (ι g))
  let VB : (Spec (CommRingCat.of B)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H B (ι g))
  let f := Spec.map (CommRingCat.ofHom a.symm.toRingHom)
  have hf : IsIso f := by
    change IsIso (Spec.map a.symm.toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  have hV : f ⁻¹ᵁ VB = VA := by
    change PrimeSpectrum.basicOpen (a.symm (algebraMap H B (ι g))) = _
    rw [a.symm.commutes]
  let b : VA.toScheme ≅ VB.toScheme :=
    (Spec (CommRingCat.of A)).isoOfEq hV.symm ≪≫ f.preimageIso VB
  have hbase : f ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
      Spec.map (CommRingCat.ofHom (algebraMap H A)) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact a.symm.commutes x
  have hb : b.hom ≫ VB.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B)) =
      VA.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H A)) := by
    simp only [b, Iso.trans_hom, Category.assoc, Hom.preimageIso_hom_ι_assoc]
    rw [Scheme.isoOfEq_hom_ι_assoc, hbase]
  let θ := (Over.forget (Spec H)).mapIso e ≪≫ b
  refine ⟨m, K, hmd, θ, ?_⟩
  change e.hom.left ≫ b.hom ≫ VB.ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap H B)) = _
  rw [hb]
  exact Over.w e.hom

/-- No nonempty scheme is isomorphic to the puncture of the spectrum of the empty product of
fixed rings over `ℚ`. -/
private theorem empty_fixed_ring_no_iso (X : Scheme) [Nonempty X] :
    let B := ∀ _k : Fin 0,
      (⨅ _ζ : (⊥ : Subgroup PUnit.{1}),
        AlgHom.equalizer (AlgHom.id ℚ ℚ) (AlgHom.id ℚ ℚ) : Subalgebra ℚ ℚ)
    let N := Spec (CommRingCat.of B)
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap ℚ B 1)
    ¬ Nonempty (X ≅ V.toScheme) := by
  dsimp only
  intro ⟨e⟩
  have h : IsEmpty (PrimeSpectrum (∀ _k : Fin 0,
      (⨅ _ζ : (⊥ : Subgroup PUnit.{1}),
        AlgHom.equalizer (AlgHom.id ℚ ℚ) (AlgHom.id ℚ ℚ) : Subalgebra ℚ ℚ))) :=
    inferInstance
  exact h.false (e.hom (Classical.choice inferInstance)).val

private theorem trivial_torsor_split_data
    (U : (Spec (CommRingCat.of ℚ)).Opens) (hU : U = ⊤) :
    Etale (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ))) ∧
    (∀ (Ω : Type) [Field Ω] (a b : ℚ →+* Ω),
      a.comp (algebraMap ℚ ℚ) = b.comp (algebraMap ℚ ℚ) →
      a (algebraMap ℚ ℚ 1) ≠ 0 →
      ∃! _ζ : PUnit.{1}, a.comp (AlgHom.id ℚ ℚ).toRingHom = b) ∧
    ∃ δ : pullback U.ι U.ι ≅ ∐ fun _ : Fin 1 ↦ U.toScheme,
      δ.hom ≫ Sigma.desc (fun _ : Fin 1 ↦ 𝟙 U.toScheme) =
        pullback.snd U.ι U.ι := by
  have hp : IsIso U.ι := by
    subst U
    change IsIso (Spec (CommRingCat.of ℚ)).topIso.hom
    infer_instance
  have hq : Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) =
      𝟙 (Spec (CommRingCat.of ℚ)) := by
    change Spec.map (𝟙 (CommRingCat.of ℚ)) = _
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hq, Category.comp_id]
    infer_instance
  · intro Ω _ a b hab _
    have hab' : a = b := by simpa using hab
    refine ⟨PUnit.unit, ?_, ?_⟩
    · simpa using hab'
    · intro ζ _
      exact Subsingleton.elim _ _
  · let e := coproductUniqueIso (fun _ : Fin 1 ↦ U.toScheme)
    have he : e.hom = Sigma.desc (fun _ : Fin 1 ↦ 𝟙 _) := by
      apply Sigma.hom_ext
      intro i
      simp [e]
    refine ⟨asIso (pullback.snd U.ι U.ι) ≪≫ e.symm, ?_⟩
    simp [← he]
/-- Fixed-orbit descent with arbitrary orbit data fails for the trivial torsor and the identity
finite étale cover of `D(1)`. -/
private theorem affine_torsor_fixed_orbits_counterexample
    (U : (Spec (CommRingCat.of ℚ)).Opens) (hU : U = ⊤) :
    ¬ (∀ (m : ℕ) (K : Fin m → Subgroup PUnit.{1}) (d : ℕ), m ≤ d →
      Etale (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ))) →
      (∀ (Ω : Type) [Field Ω] (a b : ℚ →+* Ω),
        a.comp (algebraMap ℚ ℚ) = b.comp (algebraMap ℚ ℚ) →
        a (algebraMap ℚ ℚ 1) ≠ 0 →
        ∃! _ζ : PUnit.{1}, a.comp (AlgHom.id ℚ ℚ).toRingHom = b) →
      ∀ (T : Scheme) (t : T ⟶ Spec (CommRingCat.of ℚ)) (k : U.toScheme ⟶ T),
        k ≫ t = U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) ≫
          Spec.map (CommRingCat.ofHom (RingHom.id ℚ)) →
      ∀ (δ : pullback U.ι t ≅ ∐ fun _ : Fin d ↦ T),
        δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd U.ι t →
      let B := ∀ i : Fin m,
        (⨅ _ζ : K i,
          AlgHom.equalizer (AlgHom.id ℚ ℚ) (AlgHom.id ℚ ℚ) : Subalgebra ℚ ℚ)
      let V : (Spec (CommRingCat.of B)).Opens :=
        PrimeSpectrum.basicOpen (algebraMap ℚ B 1)
      ∃ θ : pullback U.ι (Spec.map (CommRingCat.ofHom (RingHom.id ℚ))) ≅ V.toScheme,
        θ.hom ≫ V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ B)) =
          pullback.snd U.ι (Spec.map (CommRingCat.ofHom (RingHom.id ℚ)))) := by
  intro h
  obtain ⟨hEt, hrot, δ, hδ⟩ := trivial_torsor_split_data U hU
  obtain ⟨θ, _⟩ := h 0 (fun _ ↦ ⊥) 1 (Nat.zero_le 1) hEt hrot U.toScheme U.ι
    (𝟙 U.toScheme) (by simp) δ hδ
  have hx : Nonempty U.toScheme := by
    subst U
    exact ⟨(Spec (CommRingCat.of ℚ)).topIso.inv (Classical.choice inferInstance)⟩
  have hy : Nonempty (pullback U.ι
      (Spec.map (CommRingCat.ofHom (RingHom.id ℚ))) : Scheme) := by
    let z : U.toScheme ⟶ pullback U.ι
        (Spec.map (CommRingCat.ofHom (RingHom.id ℚ))) :=
      pullback.lift (𝟙 U.toScheme) U.ι (by simp)
    exact ⟨z (Classical.choice hx)⟩
  exact empty_fixed_ring_no_iso _ ⟨θ⟩


end AlgebraicGeometry.Scheme
