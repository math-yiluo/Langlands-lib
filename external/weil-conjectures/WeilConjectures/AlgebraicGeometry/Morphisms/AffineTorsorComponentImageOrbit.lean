/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitPointLifting

import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Images of single stabilizer components

## References

* Stacks Project, Tag 03SF, stabilizer quotients of Galois covers
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem orbit_split_ι_clopen (T : Scheme.{u}) (d : ℕ) (i : Fin d) :
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

private theorem orbit_section_reconstruction {Y S T V : Scheme.{u}} [ConnectedSpace V]
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (d : ℕ)
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (s : V ⟶ Y) (hs : s ≫ p = k ≫ t) (x : V) :
    s = fixedSplitSection p t k d δ (fixedSplitLabel p t k d δ s hs x) := by
  let f := pullback.lift s k hs ≫ δ.hom
  let i := fixedSplitLabel p t k d δ s hs x
  have hrange : Set.range f ⊆ Set.range (Sigma.ι (fun _ : Fin d ↦ T) i) :=
    (isConnected_range f.continuous).isPreconnected.subset_isClopen (orbit_split_ι_clopen T d i)
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


private theorem orbit_deck_cover
    (H : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra H C]
    (h : H) (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C h) ≠ 0 → ∃! ζ : G, a.comp (ρ ζ).toRingHom = b) :
    let V := Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))
    let v : V ⟶ Spec (CommRingCat.of H) := Scheme.Opens.ι _ ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C))
    ∀ z : (pullback v v : Scheme), ∃ (ζ : G) (a : V),
      pullback.lift (fixedPunctureDeck H C h G ρ ζ) (𝟙 V)
        (by
          exact (fixedPunctureDeck_base H C h G ρ ζ).trans (Category.id_comp v).symm)
        a = z := by
  dsimp only
  let V := Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C h))
  let i : V ⟶ Spec (CommRingCat.of C) := Scheme.Opens.ι _
  let v := i ≫ Spec.map (CommRingCat.ofHom (algebraMap H C))
  intro z
  let L := (pullback v v).residueField z
  let e := (pullback v v).fromSpecResidueField z
  let a := e ≫ pullback.snd v v
  let b := e ≫ pullback.fst v v
  obtain ⟨α, hα⟩ := Spec.map_surjective (a ≫ i)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (b ≫ i)
  have hab : α.hom.comp (algebraMap H C) = β.hom.comp (algebraMap H C) := by
    have heq : CommRingCat.ofHom (algebraMap H C) ≫ α =
        CommRingCat.ofHom (algebraMap H C) ≫ β := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, hα, hβ]
      change a ≫ v = b ≫ v
      simp only [a, b, Category.assoc, pullback.condition]
    exact congrArg CommRingCat.Hom.hom heq
  have hαne : α.hom (algebraMap H C h) ≠ 0 := by
    have ha := (a (⊥ : PrimeSpectrum L)).property
    change algebraMap H C h ∉ (i (a (⊥ : PrimeSpectrum L))).asIdeal at ha
    rw [← Hom.comp_apply, ← hα] at ha
    change α.hom (algebraMap H C h) ∉ (⊥ : PrimeSpectrum L).asIdeal at ha
    simpa using ha
  obtain ⟨ζ, hζ, -⟩ := hrot L α.hom β.hom hab hαne
  have he : a ≫ fixedPunctureDeck H C h G ρ ζ = b := by
    apply (cancel_mono i).mp
    dsimp only [i]
    simp only [fixedPunctureDeck, Category.assoc, Hom.resLE_comp_ι]
    rw [← Category.assoc, ← hα, ← Spec.map_comp, ← hβ]
    congr 1
    exact CommRingCat.hom_ext hζ
  let γ : V ⟶ pullback v v := pullback.lift
    (fixedPunctureDeck H C h G ρ ζ) (𝟙 V)
    (by simpa using fixedPunctureDeck_base H C h G ρ ζ)
  have heg : a ≫ γ = e := by
    apply pullback.hom_ext
    · simpa only [γ, Category.assoc, pullback.lift_fst] using he
    · simp only [γ, Category.assoc, pullback.lift_snd, Category.comp_id, a]
  refine ⟨ζ, a (⊥ : PrimeSpectrum L), ?_⟩
  change γ (a (⊥ : PrimeSpectrum L)) = z
  rw [← Hom.comp_apply, heg]
  dsimp only [e]
  simp

set_option linter.unusedVariables false in
/-- Membership in one descended component is exactly membership in its label orbit. -/
theorem affine_torsor_component_image_orbit
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
    ∀ (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι))) [IsOpenImmersion f],
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      ∀ (y : Fin d) (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))),
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ y a ∈ f.opensRange ↔
          ∃ ζ : G, fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x = y := by
  classical
  dsimp only
  let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let U : (Spec (CommRingCat.of F)).Opens :=
    PrimeSpectrum.basicOpen (algebraMap H F (ι g))
  let V := Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))
  let i : V ⟶ Spec (CommRingCat.of C) := Scheme.Opens.ι _
  let v := i ≫ Spec.map (CommRingCat.ofHom (algebraMap H C))
  let w := Spec.map (CommRingCat.ofHom ι)
  let Z := pullback p w
  let b : Z ⟶ Spec (CommRingCat.of H) := pullback.snd p w
  let q : V ⟶ U.toScheme := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
    U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
      change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
        PrimeSpectrum.basicOpen (algebraMap H C (ι g))
      rfl)
  let s := fixedSplitSectionOver p t k v w hk d δ hδ
  let A := fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
    p T t k hk d δ hδ
  have hq : Function.Surjective q := by
    have : Module.Finite F C := Module.Finite.of_restrictScalars_finite H F C
    have : Algebra.IsIntegral F C := inferInstance
    have hs := (algebraMap_isIntegral_iff (R := F) (A := C)).mpr
      (inferInstance : Algebra.IsIntegral F C)
    have hsur := hs.comap_surjective (fun a b h ↦ Subtype.ext h)
    intro a
    obtain ⟨c, hc⟩ := hsur a.val
    have hcmem : c ∈ PrimeSpectrum.basicOpen (algebraMap H C (ι g)) := by
      change algebraMap H C (ι g) ∉ c.asIdeal
      have ha := a.property
      change algebraMap H F (ι g) ∉ a.val.asIdeal at ha
      rw [← hc] at ha
      exact ha
    refine ⟨⟨c, hcmem⟩, ?_⟩
    apply Subtype.ext
    have he : q ≫ U.ι = i ≫ Spec.map (CommRingCat.ofHom F.val.toRingHom) :=
      Hom.resLE_comp_ι _ _
    have he' := congrArg (fun m ↦ m ⟨c, hcmem⟩) he
    exact he'.trans hc
  intro f _ hf hfx y a
  have hqf : q ≫ f = s x := by
    apply pullback.hom_ext
    · rw [Category.assoc, show s x ≫ pullback.fst p w =
          fixedSplitSection p t k d δ x from pullback.lift_fst _ _ _]
      exact hfx
    · rw [Category.assoc, hf]
      rw [show s x ≫ pullback.snd p w = v from pullback.lift_snd _ _ _]
      dsimp only [q, v, i]
      rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, ← Spec.map_comp]
      rfl
  have hrange : Set.range f = Set.range (s x) := by
    ext z
    constructor
    · rintro ⟨c, hc⟩
      obtain ⟨a, ha⟩ := hq c
      refine ⟨a, ?_⟩
      rw [← hqf, Hom.comp_apply, ha]
      exact hc
    · rintro ⟨a, ha⟩
      refine ⟨q a, ?_⟩
      rw [← Hom.comp_apply, hqf]
      exact ha
  let vg := fixedPunctureGeneric C (algebraMap H C (ι g)) hne
  have : Nonempty V := ⟨vg⟩
  have : IrreducibleSpace (Spec (CommRingCat.of C) : Scheme) := inferInstance
  have : IrreducibleSpace V := i.isOpenEmbedding.irreducibleSpace
  have hdeck (ζ : G) :
      fixedPunctureDeck H C (ι g) G ρ ζ ≫ fixedSplitSection p t k d δ x =
        fixedSplitSection p t k d δ (A ζ x) := by
    change _ = fixedSplitSection p t k d δ
      (fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ ζ x)
    dsimp only [fixedPunctureLabel]
    exact orbit_section_reconstruction p t k d δ hδ _ _ vg
  let Q := pullback b v
  let l : Fin d → (V ⟶ Q) := fun z ↦ pullback.lift (s z) (𝟙 V)
    (by rw [Category.id_comp]; exact pullback.lift_snd _ _ _)
  have hbase : (s x) ≫ b = v := pullback.lift_snd _ _ _
  let r : pullback v v ⟶ Q := pullback.map v v b v (s x) (𝟙 V) (𝟙 (Spec (CommRingCat.of H)))
    (by simpa only [Category.comp_id] using hbase.symm) (by simp)
  have hr : Set.range r = (pullback.fst b v) ⁻¹' Set.range (s x) := by
    have hid : Set.range (𝟙 V : V ⟶ V) = Set.univ :=
      Set.range_eq_univ.mpr (fun a ↦ ⟨a, rfl⟩)
    simpa only [r, hid, Set.preimage_univ, Set.inter_univ] using
      (Pullback.range_map v v b v (s x) (𝟙 V) (𝟙 (Spec (CommRingCat.of H)))
        (by simpa only [Category.comp_id] using hbase.symm) (by simp))
  have hgraph (ζ : G) :
      pullback.lift (fixedPunctureDeck H C (ι g) G ρ ζ) (𝟙 V)
        (by rw [Category.id_comp]; exact
          fixedPunctureDeck_base H C (ι g) G ρ ζ) ≫ r = l (A ζ x) := by
    apply pullback.hom_ext
    · simp only [r, l, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
      apply pullback.hom_ext
      · simpa only [s, fixedSplitSectionOver, Category.assoc, pullback.lift_fst]
          using hdeck ζ
      · simp only [s, fixedSplitSectionOver, Category.assoc, pullback.lift_snd]
        exact fixedPunctureDeck_base H C (ι g) G ρ ζ
    · simp only [r, l, Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
  have hdisjoint (z z' : Fin d) (c c' : V) (he : l z c = l z' c') : z = z' := by
    have hpb : (pullback.fst b v ≫ pullback.fst p w) ≫ p =
        (pullback.snd b v ≫ k) ≫ t := by
      calc
        _ = pullback.fst b v ≫ b ≫ w := by
          dsimp only [b]
          rw [Category.assoc, pullback.condition]
        _ = pullback.snd b v ≫ v ≫ w := by
          rw [← Category.assoc, pullback.condition, Category.assoc]
        _ = _ := by
          rw [Category.assoc (pullback.snd b v) k t, hk]
          rfl
    let m : Q ⟶ pullback p t := pullback.lift
      (pullback.fst b v ≫ pullback.fst p w) (pullback.snd b v ≫ k) hpb
    have hm (z : Fin d) : l z ≫ m ≫ δ.hom =
        k ≫ Sigma.ι (fun _ : Fin d ↦ T) z := by
      have heq : l z ≫ m = k ≫ Sigma.ι (fun _ : Fin d ↦ T) z ≫ δ.inv := by
        apply pullback.hom_ext
        · rw [Category.assoc, show m ≫ pullback.fst p t =
              pullback.fst b v ≫ pullback.fst p w from pullback.lift_fst _ _ _,
            ← Category.assoc, show l z ≫ pullback.fst b v = s z from
              pullback.lift_fst _ _ _]
          rw [show s z ≫ pullback.fst p w = fixedSplitSection p t k d δ z from
            pullback.lift_fst _ _ _]
          simp only [fixedSplitSection, Category.assoc]
        · have hi : δ.inv ≫ pullback.snd p t =
              Sigma.desc (fun _ : Fin d ↦ 𝟙 T) := by
            rw [← hδ, ← Category.assoc, δ.inv_hom_id, Category.id_comp]
          rw [Category.assoc, show m ≫ pullback.snd p t =
              pullback.snd b v ≫ k from pullback.lift_snd _ _ _,
            ← Category.assoc, show l z ≫ pullback.snd b v = 𝟙 V from
              pullback.lift_snd _ _ _, Category.id_comp]
          simp only [Category.assoc, hi, Sigma.ι_comp_desc, Category.comp_id]
      rw [← Category.assoc, heq]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh := congrArg (fun c ↦ (m ≫ δ.hom) c) he
    change (l z ≫ m ≫ δ.hom) c = (l z' ≫ m ≫ δ.hom) c' at hh
    rw [hm, hm] at hh
    simp only [Hom.comp_apply] at hh
    exact congrArg Sigma.fst
      ((sigmaι_eq_iff (fun _ : Fin d ↦ T) _ _ _ _).mp hh)
  change s y a ∈ f.opensRange ↔ ∃ ζ : G, A ζ x = y
  change s y a ∈ Set.range f ↔ ∃ ζ : G, A ζ x = y
  rw [hrange]
  constructor
  · intro ha
    have hla : l y a ∈ Set.range r := by
      rw [hr]
      change (l y ≫ pullback.fst b v) a ∈ Set.range (s x)
      rw [show l y ≫ pullback.fst b v = s y from pullback.lift_fst _ _ _]
      exact ha
    obtain ⟨z, hz⟩ := hla
    obtain ⟨ζ, c, hc⟩ := orbit_deck_cover H C (ι g) G ρ hrot z
    refine ⟨ζ, ?_⟩
    apply hdisjoint (A ζ x) y c a
    rw [← hgraph, Hom.comp_apply, hc, hz]
  · rintro ⟨ζ, hζ⟩
    have hla : l y a ∈ Set.range r := by
      rw [← hζ, ← hgraph, Hom.comp_apply]
      exact ⟨_, rfl⟩
    rw [hr] at hla
    change (l y ≫ pullback.fst b v) a ∈ Set.range (s x) at hla
    rw [show l y ≫ pullback.fst b v = s y from pullback.lift_fst _ _ _] at hla
    exact hla

/-- Forward half of the orbit criterion: if the split section labelled `y` lies in the range of
the descended component `f`, then `y = A(ζ) x` for some deck label `ζ`. -/
theorem affine_torsor_component_image_orbit_forward
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
    ∀ (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι))) [IsOpenImmersion f],
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      ∀ (y : Fin d) (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))),
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ y a ∈ f.opensRange →
          ∃ ζ : G, fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x = y := by
  dsimp only
  intro f _ hbase hsection y a
  exact (affine_torsor_component_image_orbit R H g ι C G ρ hρone hρmul hne
    p j hj hEt hrot d T t k hk δ hδ x K hK f hbase hsection y a).mp




/-- Backward half of the orbit criterion: if `y = A(ζ) x` for some deck label `ζ`, then the split
section labelled `y` lies in the range of the descended component `f` at every point `a`. -/
theorem affine_torsor_component_image_orbit_backward
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
    ∀ (f : Scheme.Opens.toScheme (X := Spec (CommRingCat.of F)) U ⟶
        pullback p (Spec.map (CommRingCat.ofHom ι))) [IsOpenImmersion f],
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      ∀ (y : Fin d) (a : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))),
        (∃ ζ : G, fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x = y) →
        fixedSplitSectionOver p t k
          (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
            (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
            Spec.map (CommRingCat.ofHom (algebraMap H C)))
          (Spec.map (CommRingCat.ofHom ι)) hk d δ hδ y a ∈ f.opensRange := by
  dsimp only
  intro f _ hbase hsection y a
  exact (affine_torsor_component_image_orbit R H g ι C G ρ hρone hρmul hne
    p j hj hEt hrot d T t k hk δ hδ x K hK f hbase hsection y a).mpr




end AlgebraicGeometry.Scheme
