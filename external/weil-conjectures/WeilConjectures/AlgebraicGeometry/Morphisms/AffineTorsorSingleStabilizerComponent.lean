/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorStabilizerSectionOpen
import WeilConjectures.AlgebraicGeometry.Morphisms.AffineInvariantBasicOpenDescent
import Mathlib.Topology.Connected.Clopen
import Mathlib.AlgebraicGeometry.Properties

/-! # Stabilizer components of a split affine torsor cover

## References

* Stacks Project, Tag 03SF (finite Galois covers and permutation sets)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem descent_split_ι_clopen (T : Scheme.{u}) (d : ℕ) (i : Fin d) :
    IsClopen (Set.range (Sigma.ι (fun _ : Fin d ↦ T) i)) := by
  have hc : (Set.range (Sigma.ι (fun _ : Fin d ↦ T) i))ᶜ =
      ⋃ j : {j : Fin d // j ≠ i}, Set.range (Sigma.ι (fun _ : Fin d ↦ T) j.1) := by
    ext z
    constructor
    · intro hz
      let j := (sigmaOpenCover (fun _ : Fin d ↦ T)).idx z
      have hj : j ≠ i := by
        intro he
        exact hz (he ▸ (sigmaOpenCover (fun _ : Fin d ↦ T)).covers z)
      exact Set.mem_iUnion.mpr ⟨⟨j, hj⟩, (sigmaOpenCover (fun _ : Fin d ↦ T)).covers z⟩
    · intro hz hi
      obtain ⟨j, y, hy⟩ := Set.mem_iUnion.mp hz
      obtain ⟨w, hw⟩ := hi
      exact j.2 (congrArg Sigma.fst
        ((sigmaι_eq_iff (fun _ : Fin d ↦ T) _ _ _ _).mp (hy.trans hw.symm)))
  refine ⟨?_, IsOpenImmersion.isOpen_range _⟩
  rw [← isOpen_compl_iff, hc]
  exact isOpen_iUnion fun _ ↦ IsOpenImmersion.isOpen_range _

private theorem descent_section_reconstruction {Y S T V : Scheme.{u}} [ConnectedSpace V]
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (d : ℕ)
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (s : V ⟶ Y) (hs : s ≫ p = k ≫ t) (x : V) :
    s = fixedSplitSection p t k d δ (fixedSplitLabel p t k d δ s hs x) := by
  let f := pullback.lift s k hs ≫ δ.hom
  let i := fixedSplitLabel p t k d δ s hs x
  have hrange : Set.range f ⊆ Set.range (Sigma.ι (fun _ : Fin d ↦ T) i) :=
    (isConnected_range f.continuous).isPreconnected.subset_isClopen (descent_split_ι_clopen T d i)
      ⟨f x, ⟨x, rfl⟩, (sigmaOpenCover (fun _ : Fin d ↦ T)).covers (f x)⟩
  let l := IsOpenImmersion.lift (Sigma.ι (fun _ : Fin d ↦ T) i) f hrange
  have hl : l ≫ Sigma.ι (fun _ : Fin d ↦ T) i = f :=
    IsOpenImmersion.lift_fac _ _ _
  have hlk : l = k := by
    have he := congrArg (fun a ↦ a ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T)) hl
    simpa only [f, Category.assoc, Sigma.ι_comp_desc, Category.comp_id, hδ,
      pullback.lift_snd] using he
  dsimp only [fixedSplitSection]
  have he := congrArg (fun a ↦ a ≫ δ.inv ≫ pullback.fst p t) hl
  simpa only [hlk, f, Category.assoc, Iso.hom_inv_id_assoc,
    pullback.lift_fst] using he.symm


-- The shorter affine argument does not need every torsor hypothesis in this fixed interface.
set_option linter.unusedVariables false
/-- The split section labelled `x` descends to the stabilizer quotient: if `K` is the stabilizer
of `x`, there is a morphism `s` over `Spec R` from the puncture `D(ι g)` of `Spec C^K` to `Y`
whose composite with the quotient map `q` is the split section labelled `x`. -/
theorem affine_torsor_single_stabilizer_component_section
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
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∃ s : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶ Y,
      s ≫ p = (Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
        Spec.map (CommRingCat.ofHom (algebraMap H F))) ≫
          Spec.map (CommRingCat.ofHom ι) ∧
      q ≫ s = fixedSplitSection p t k d δ x := by
  classical
  dsimp only
  let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let U : (Spec (CommRingCat.of F)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H F (ι g))
  let V := Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))
  let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
    U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
      change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
        PrimeSpectrum.basicOpen (algebraMap H C (ι g))
      rfl)
  let b := (Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
    Spec.map (CommRingCat.ofHom (algebraMap H F))) ≫ Spec.map (CommRingCat.ofHom ι)
  let z : V := fixedPunctureGeneric C (algebraMap H C (ι g)) hne
  have : Nonempty V := ⟨z⟩
  have : IrreducibleSpace (Spec (CommRingCat.of C) : Scheme) := inferInstance
  have : IrreducibleSpace V :=
    (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))).isOpenEmbedding.irreducibleSpace
  have hfix : ∀ ζ : K,
      fixedPunctureDeck H C (ι g) G ρ ζ.val ≫ fixedSplitSection p t k d δ x =
        fixedSplitSection p t k d δ x := by
    intro ζ
    have hl := (hK ζ.val).mp ζ.property
    change fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ ζ.val x = x at hl
    have hr : fixedPunctureDeck H C (ι g) G ρ ζ.val ≫ fixedSplitSection p t k d δ x =
        fixedSplitSection p t k d δ
          (fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ ζ.val x) := by
      unfold fixedPunctureLabel
      exact descent_section_reconstruction p t k d δ hδ _ _ z
    exact hr.trans (congrArg (fixedSplitSection p t k d δ) hl)
  have : IsAffine (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen g)) :=
    IsAffineOpen.Spec_basicOpen g
  have : IsAffine Y := isAffine_of_isAffineHom j
  obtain ⟨s, hs, _⟩ := affine_invariant_basic_open_descent
    H C (ι g) hne G ρ K (fixedSplitSection p t k d δ x) hfix
  have hqb : q ≫ b = k ≫ t := by
    dsimp only [q, b]
    rw [hk]
    simp only [Category.assoc, Hom.resLE_comp_ι_assoc]
    rw [← Spec.map_comp_assoc]
    rfl
  have hbasefix : ∀ ζ : K, fixedPunctureDeck H C (ι g) G ρ ζ.val ≫ (k ≫ t) = k ≫ t := by
    intro ζ
    rw [hk]
    simpa only [Category.assoc] using congrArg
      (fun a ↦ a ≫ Spec.map (CommRingCat.ofHom ι))
      (fixedPunctureDeck_base H C (ι g) G ρ ζ.val)
  obtain ⟨sbase, _, huniq⟩ := affine_invariant_basic_open_descent
    H C (ι g) hne G ρ K (k ≫ t) hbasefix
  have hsp : q ≫ (s ≫ p) = k ≫ t := by
    rw [← Category.assoc, hs, fixedSplitSection_base p t k d δ hδ]
  exact ⟨s, (huniq (s ≫ p) hsp).trans (huniq b hqb).symm, hs⟩


/-- Open/base-map part of stabilizer descent. -/
theorem affine_torsor_single_stabilizer_component_open
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
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let _q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∃ f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι)),
      IsOpenImmersion f ∧
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) := by
  classical
  dsimp only
  let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let U : (Spec (CommRingCat.of F)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H F (ι g))
  let b := Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
    Spec.map (CommRingCat.ofHom (algebraMap H F))
  obtain ⟨s, hsbase, hssection⟩ := affine_torsor_single_stabilizer_component_section
    R H g ι C G ρ hρone hρmul hne p j hj hEt hrot d T t k hk δ hδ x K hK
  let f := pullback.lift s b hsbase
  have hbase : f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) = b := by
    exact pullback.lift_snd s b hsbase
  have hsection : (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl) ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
      fixedSplitSection p t k d δ x := by
    simpa only [f, pullback.lift_fst] using hssection
  have hopen : IsOpenImmersion f := affine_torsor_stabilizer_section_open
    R H g ι C G ρ hρone hρmul hne p j hj hEt hrot d T t k hk δ hδ x K hK f hbase hsection
  exact ⟨f, hopen, hbase⟩

/-- A single representative section descends to an open component. -/
theorem affine_torsor_single_stabilizer_component
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
    (d : ℕ)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫
      Spec.map (CommRingCat.ofHom ι))
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : Fin d) (K : Subgroup G)
    (hK : ∀ ζ, ζ ∈ K ↔
      fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x) :
    let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
    let U : (Spec (CommRingCat.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
    let q := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl)
    ∃ f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι)),
      IsOpenImmersion f ∧
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) ∧
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x := by
  classical
  dsimp only
  let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let U : (Spec (CommRingCat.of F)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H F (ι g))
  let b := Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
    Spec.map (CommRingCat.ofHom (algebraMap H F))
  obtain ⟨s, hsbase, hssection⟩ := affine_torsor_single_stabilizer_component_section
    R H g ι C G ρ hρone hρmul hne p j hj hEt hrot d T t k hk δ hδ x K hK
  let f := pullback.lift s b hsbase
  have hbase : f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) = b := by
    exact pullback.lift_snd s b hsbase
  have hsection : (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
        change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
          PrimeSpectrum.basicOpen (algebraMap H C (ι g))
        rfl) ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
      fixedSplitSection p t k d δ x := by
    simpa only [f, pullback.lift_fst] using hssection
  have hopen : IsOpenImmersion f := affine_torsor_stabilizer_section_open
    R H g ι C G ρ hρone hρmul hne p j hj hEt hrot d T t k hk δ hδ x K hK f hbase hsection
  exact ⟨f, hopen, hbase, hsection⟩

end AlgebraicGeometry.Scheme
