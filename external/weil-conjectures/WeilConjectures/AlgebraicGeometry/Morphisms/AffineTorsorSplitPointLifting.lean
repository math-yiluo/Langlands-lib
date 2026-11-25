/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Point lifting along a split faithfully flat puncture cover

## References

* Stacks Project, Tag 03SF
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Compatibility of the explicit split section with a second base.
Substitute the section's structural-map equation
and then the supplied equality of the two maps to S. -/
theorem fixedSplitSectionOver_compat {Y S T V W : Scheme.{u}}
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (v : V ⟶ W) (w : W ⟶ S)
    (hk : k ≫ t = v ≫ w) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) : fixedSplitSection p t k d δ x ≫ p = v ≫ w := by
  rw [fixedSplitSection_base p t k d δ hδ, hk]

/-- The split section, retaining its structural map to a second base.
This is a pullback lift of two explicit morphisms; no witness is chosen. -/
noncomputable def fixedSplitSectionOver {Y S T V W : Scheme.{u}}
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (v : V ⟶ W) (w : W ⟶ S)
    (hk : k ≫ t = v ≫ w) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) : V ⟶ pullback p w :=
  pullback.lift (fixedSplitSection p t k d δ x) v
    (fixedSplitSectionOver_compat p t k v w hk d δ hδ x)

/-- Every point above H lifts to one of the explicit split sections above C. -/
theorem affine_torsor_split_point_lifting
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [Module.FaithfullyFlat H C]
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (j : Y ⟶ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g))
    (hj : j ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen g) = p)
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t) :
    ∀ z : (pullback p (Spec.map (CommRingCat.ofHom ι)) : Scheme.{u}),
      ∃ x : Fin d, ∃ a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g))),
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ x a = z := by
  classical
  let w := Spec.map (CommRingCat.ofHom ι)
  let cMap := Spec.map (CommRingCat.ofHom (algebraMap H C))
  let V : Scheme.{u} := Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))
  let vι : V ⟶ Spec (CommRingCat.of C) := Scheme.Opens.ι _
  let v := vι ≫ cMap
  let Z : Scheme.{u} := pullback (pullback.snd p w) cMap
  let b : Z ⟶ pullback p w := pullback.fst _ _
  let c : Z ⟶ Spec (CommRingCat.of C) := pullback.snd _ _
  let y := b ≫ pullback.fst p w
  have hcbase : c ≫ cMap ≫ w = y ≫ p := by
    dsimp only [c, y, b]
    rw [← pullback.condition_assoc, Category.assoc, pullback.condition]
  have hcrange : Set.range c ⊆ Set.range vι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hy : p (y z) ∈ PrimeSpectrum.basicOpen g := by
      rw [← hj, Scheme.Hom.comp_apply]
      exact (j (y z)).property
    rw [← Scheme.Hom.comp_apply, ← hcbase, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply] at hy
    exact hy
  let a : Z ⟶ V := IsOpenImmersion.lift vι c hcrange
  have ha : a ≫ vι = c := IsOpenImmersion.lift_fac _ _ _
  have hya : y ≫ p = (a ≫ k) ≫ t := by
    rw [Category.assoc a k t, hk]
    change y ≫ p = a ≫ vι ≫ cMap ≫ w
    rw [← Category.assoc a vι, ha]
    exact hcbase.symm
  let M := pullback.lift y (a ≫ k) hya ≫ δ.hom
  have hM : M ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = a ≫ k := by
    simp only [M, Category.assoc, hδ, pullback.lift_snd]
  have hff : Surjective cMap := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap H C))).mpr
      ((RingHom.faithfullyFlat_algebraMap_iff).mpr inferInstance) |>.2
  let : Surjective cMap := hff
  let : Surjective b := inferInstance
  intro z
  obtain ⟨z', hz'⟩ := b.surjective z
  let x := (sigmaOpenCover (fun _ : Fin d ↦ T)).idx (M z')
  have hx : M z' ∈ Set.range (Sigma.ι (fun _ : Fin d ↦ T) x) :=
    (sigmaOpenCover (fun _ : Fin d ↦ T)).covers (M z')
  obtain ⟨z'', hz''⟩ : ∃ z'' : (pullback M (Sigma.ι (fun _ : Fin d ↦ T) x) : Scheme),
      pullback.fst M (Sigma.ι (fun _ : Fin d ↦ T) x) z'' = z' := by
    apply (Scheme.Pullback.range_fst (f := M)
      (g := Sigma.ι (fun _ : Fin d ↦ T) x)).ge hx
  let l := pullback.fst M (Sigma.ι (fun _ : Fin d ↦ T) x)
  let n := pullback.snd M (Sigma.ι (fun _ : Fin d ↦ T) x)
  have hn : n = l ≫ a ≫ k := by
    have e := congrArg (fun f ↦ f ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T))
      (pullback.condition (f := M) (g := Sigma.ι (fun _ : Fin d ↦ T) x))
    simpa only [Category.assoc, hM, Sigma.ι_comp_desc, Category.comp_id] using e.symm
  have hly : l ≫ y = l ≫ a ≫ fixedSplitSection p t k d δ x := by
    have e := congrArg (fun f ↦ f ≫ δ.inv ≫ pullback.fst p t)
      (pullback.condition (f := M) (g := Sigma.ι (fun _ : Fin d ↦ T) x))
    change (l ≫ M) ≫ δ.inv ≫ pullback.fst p t =
      (n ≫ Sigma.ι (fun _ : Fin d ↦ T) x) ≫ δ.inv ≫ pullback.fst p t at e
    rw [hn] at e
    simpa only [M, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst,
      fixedSplitSection] using e
  have hlb : l ≫ b = l ≫ a ≫ fixedSplitSectionOver p t k v w hk d δ hδ x := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, fixedSplitSectionOver, pullback.lift_fst] using hly
    · simp only [Category.assoc, fixedSplitSectionOver, pullback.lift_snd]
      rw [← Category.assoc a vι, ha]
      dsimp only [b, c]
      rw [pullback.condition]
  refine ⟨x, a (l z''), ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hlb,
    Scheme.Hom.comp_apply, hz'', hz']

end AlgebraicGeometry.Scheme
