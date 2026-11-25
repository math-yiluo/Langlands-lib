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

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSingleStabilizerComponent
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorRepresentativeComponentCover

/-! # Descent of individual orbit components of a split finite étale cover

## References

* Stacks Project, Tags 03SF and 0EYG
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Descent identifies the individual orbit components before assembling the product ring. -/
theorem affine_torsor_orbit_component_descent
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
    (d m : ℕ) (r : Fin m → Fin d) (K : Fin m → Subgroup G)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (hcomplete : ∀ x, ∃ i, ∃ ζ : G,
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ (r i) = x)
    (hdistinct : ∀ i j, (∃ ζ : G,
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ (r i) = r j) → i = j)
    (hstabilizer : ∀ i ζ, ζ ∈ K i ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ (r i) = r i) :
    let F := fun i : Fin m ↦
      (⨅ ζ : K i, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U := fun i : Fin m ↦ PrimeSpectrum.basicOpen (algebraMap H (F i) (ι g))
    ∃ e : pullback p (Spec.map (CommRingCat.ofHom ι)) ≅
        ∐ fun i : Fin m ↦ Scheme.Opens.toScheme (X := Spec (CommRingCat.of (F i))) (U i),
      e.hom ≫ Sigma.desc (fun i : Fin m ↦
        Scheme.Opens.ι (X := Spec (CommRingCat.of (F i))) (U i) ≫
          Spec.map (CommRingCat.ofHom (algebraMap H (F i)))) =
        pullback.snd p (Spec.map (CommRingCat.ofHom ι)) := by
  classical
  dsimp only
  let F := fun i : Fin m ↦
    (⨅ ζ : K i, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let U := fun i : Fin m ↦
    (PrimeSpectrum.basicOpen (algebraMap H (F i) (ι g)) :
      (Spec (CommRingCat.of (F i))).Opens)
  have hcomponents := fun i : Fin m ↦
    affine_torsor_single_stabilizer_component R H g ι C G ρ hρone hρmul hne
      p j hj hEt hrot d T t k hk δ hδ (r i) (K i) (hstabilizer i)
  choose f hopen hbase hsection using hcomponents
  let : ∀ i, IsOpenImmersion (f i) := hopen
  obtain ⟨hcover, hdisjoint⟩ := affine_torsor_representative_component_cover
    R H g ι C G ρ hρone hρmul hne p j hj hEt hrot d m r K T t k hk δ hδ
    hcomplete hdistinct hstabilizer f hbase hsection
  have hcolim := nonempty_isColimit_cofanMk_of f hcover hdisjoint
  have : IsIso (Sigma.desc f) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ f)).mp hcolim
  have hmap : Sigma.desc f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
      Sigma.desc (fun i : Fin m ↦
        Scheme.Opens.ι (X := Spec (CommRingCat.of (F i))) (U i) ≫
          Spec.map (CommRingCat.ofHom (algebraMap H (F i)))) := by
    apply Sigma.hom_ext
    intro i
    simpa only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc] using hbase i
  refine ⟨(asIso (Sigma.desc f)).symm, ?_⟩
  change inv (Sigma.desc f) ≫ _ = _
  rw [← hmap, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end AlgebraicGeometry.Scheme
