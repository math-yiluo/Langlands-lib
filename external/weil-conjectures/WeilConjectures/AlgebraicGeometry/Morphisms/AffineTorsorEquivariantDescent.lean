/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorEquivariantAlgebra
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.Mathlib.RingTheory.Flat.DescentAlgebra
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorFixedPunctureDescentGeometric
import WeilConjectures.AlgebraicGeometry.Morphisms.EquivariantOrbitModelCompatible
import WeilConjectures.AlgebraicGeometry.Morphisms.FixedOrbitProductEquiv

/-! # Descent of a split cover to its equivariant function algebra

## References

* Stacks Project, Tag 03SF (finite Galois covers)
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The equivariant function algebra is reconstructed from orbit representatives
as the product of the corresponding stabilizer equalizers. -/
theorem affine_torsor_equivariant_descent_algebra
    (H C : Type u) [CommRing H] [CommRing C] [Algebra H C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (d : ℕ) (α : G →* Equiv.Perm (Fin d)) (D : FixedOrbitData G d)
    (hD : D.action = α) :
    Nonempty ((affineTorsorEquivariantAlgebra H C G ρ d α) ≃ₐ[H]
      (∀ k : Fin D.m,
        (⨅ ζ : D.stabilizer k,
          AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C))) := by
  obtain ⟨m, K, eA, hcompat⟩ :=
    equivariant_orbit_model_compatible H C G ρ hρmul d α D hD
  obtain ⟨eD⟩ := fixed_orbit_product_equiv H C G ρ hρmul d α D hD m K hcompat
  obtain ⟨eA⟩ := eA
  exact ⟨eA.trans eD⟩

/-- A finite étale cover `p` of `D(g)` that splits into `d` copies after base change along `t`
descends: for some permutation action `α` of `G` on `Fin d`, the base change of `p` along
`Spec H ⟶ Spec R` is isomorphic over `Spec H` to the puncture `D(ι g)` of the spectrum of the
equivariant function algebra `affineTorsorEquivariantAlgebra H C G ρ d α`. -/
theorem affine_torsor_equivariant_descent
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
    ∃ α : G →* Equiv.Perm (Fin d),
      let A := affineTorsorEquivariantAlgebra H C G ρ d α
      let V : (Spec (CommRingCat.of A)).Opens :=
        PrimeSpectrum.basicOpen (algebraMap H A (ι g))
      Nonempty (Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
        Over.mk (V.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H A)))) := by
  classical
  dsimp only
  intro hEt hrot T t k hk δ hδ
  let α := fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne p T t k hk d δ hδ
  have ha := fixedPunctureLabel_laws R H g ι C G ρ hρone hρmul hne p T t k hk d δ hδ
  obtain ⟨D, hD⟩ := fixedOrbitData_of_action G d α
  obtain ⟨θ, hθ⟩ := affine_torsor_fixed_orbits_geometric
    R H g ι C G ρ hρone hρmul hne p j hj hEt hrot d D T t k hk δ hδ hD
  obtain ⟨a⟩ := affine_torsor_equivariant_descent_algebra H C G ρ hρmul d α D hD
  let A := affineTorsorEquivariantAlgebra H C G ρ d α
  let B := ∀ k : Fin D.m,
    (⨅ ζ : D.stabilizer k, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let VA : (Spec (CommRingCat.of A)).Opens := PrimeSpectrum.basicOpen (algebraMap H A (ι g))
  let VB : (Spec (CommRingCat.of B)).Opens := PrimeSpectrum.basicOpen (algebraMap H B (ι g))
  let f := Spec.map (CommRingCat.ofHom a.symm.toRingHom)
  have hf : IsIso f := by
    change IsIso (Spec.map (a.symm.toRingEquiv.toCommRingCatIso.hom))
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
  refine ⟨α, ?_⟩
  change Nonempty (Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
    Over.mk (VA.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H A))))
  let eθ : Over.mk (pullback.snd p (Spec.map (CommRingCat.ofHom ι))) ≅
      Over.mk (VB.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B))) :=
    Over.isoMk θ hθ
  let eb : Over.mk (VB.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H B))) ≅
      Over.mk (VA.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap H A))) :=
    Over.isoMk b.symm (by
      change b.symm.hom ≫ VA.ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap H A)) = _
      rw [← hb]
      simp)
  exact ⟨eθ ≪≫ eb⟩

end AlgebraicGeometry.Scheme
