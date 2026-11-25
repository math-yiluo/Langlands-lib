/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorSplitAction

import WeilConjectures.AlgebraicGeometry.Morphisms.AffineTorsorInvariantPunctureEtale


/-! # Monomorphy of a selected stabilizer section

## References

* Stacks Project, Tag 03SF
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem split_ι_clopen (T : Scheme.{u}) (d : ℕ) (i : Fin d) :
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

private theorem split_section_reconstruction {Y S T V : Scheme.{u}} [ConnectedSpace V]
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (d : ℕ)
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (s : V ⟶ Y) (hs : s ≫ p = k ≫ t) (x : V) :
    s = fixedSplitSection p t k d δ (fixedSplitLabel p t k d δ s hs x) := by
  let f := pullback.lift s k hs ≫ δ.hom
  let i := fixedSplitLabel p t k d δ s hs x
  have hrange : Set.range f ⊆ Set.range (Sigma.ι (fun _ : Fin d ↦ T) i) :=
    (isConnected_range f.continuous).isPreconnected.subset_isClopen (split_ι_clopen T d i)
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

private theorem split_label_injective_at {Y S T V : Scheme.{u}}
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (d : ℕ)
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (Ω : Type u) [Field Ω] (a : Spec (.of Ω) ⟶ V) (i j : Fin d)
    (h : a ≫ fixedSplitSection p t k d δ i = a ≫ fixedSplitSection p t k d δ j) :
    i = j := by
  have hi : δ.inv ≫ pullback.snd p t = Sigma.desc (fun _ : Fin d ↦ 𝟙 T) := by
    rw [← hδ, ← Category.assoc, δ.inv_hom_id, Category.id_comp]
  have he : a ≫ k ≫ Sigma.ι (fun _ : Fin d ↦ T) i ≫ δ.inv =
      a ≫ k ≫ Sigma.ι (fun _ : Fin d ↦ T) j ≫ δ.inv := by
    apply pullback.hom_ext
    · exact h
    · simp only [Category.assoc, hi, Sigma.ι_comp_desc, Category.comp_id]
  have he' := congrArg (fun m ↦ m ≫ δ.hom) he
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at he'
  have hp := congrArg (fun m : Spec (.of Ω) ⟶ ∐ (fun _ : Fin d ↦ T) ↦ m default) he'
  simp only [Hom.comp_apply] at hp
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp hp)

private theorem subalgebra_puncture_surjective
    (H : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra H C]
    [Module.Finite H C] (F : Subalgebra H C) (h : H) :
    Surjective ((Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
      (PrimeSpectrum.basicOpen (algebraMap H F h))
      (PrimeSpectrum.basicOpen (algebraMap H C h)) (by
        change PrimeSpectrum.basicOpen (algebraMap H C h) ≤
          PrimeSpectrum.basicOpen (algebraMap H C h)
        rfl)) := by
  have hint : F.val.toRingHom.IsIntegral := by
    intro c
    exact (Algebra.IsIntegral.isIntegral (R := H) c).tower_top
  have hs := hint.comap_surjective Subtype.val_injective
  constructor
  intro z
  obtain ⟨y, hy⟩ := hs z.val
  have hymem : y ∈ PrimeSpectrum.basicOpen (algebraMap H C h) := by
    change algebraMap H C h ∉ y.asIdeal
    have hz := z.property
    rw [← hy] at hz
    exact hz
  refine ⟨⟨y, hymem⟩, ?_⟩
  apply Subtype.ext
  rw [Hom.coe_resLE_apply]
  exact hy

private theorem puncture_rotation
    (H : CommRingCat.{u}) (C : Type u) [CommRing C] [Algebra H C]
    (h : H) (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hrot : ∀ (Ω : Type u) [Field Ω] (a b : C →+* Ω),
      a.comp (algebraMap H C) = b.comp (algebraMap H C) →
      a (algebraMap H C h) ≠ 0 → ∃! ζ : G, a.comp (ρ ζ).toRingHom = b)
    (Ω : Type u) [Field Ω]
    (a b : Spec (.of Ω) ⟶ Scheme.Opens.toScheme (X := Spec (.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h)))
    (hab : a ≫ Scheme.Opens.ι _ ≫ Spec.map (CommRingCat.ofHom (algebraMap H C)) =
      b ≫ Scheme.Opens.ι _ ≫ Spec.map (CommRingCat.ofHom (algebraMap H C))) :
    ∃ ζ : G, a ≫ fixedPunctureDeck H C h G ρ ζ = b := by
  let i := Scheme.Opens.ι (X := Spec (.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C h))
  obtain ⟨α, hα⟩ := Spec.map_surjective (a ≫ i)
  obtain ⟨β, hβ⟩ := Spec.map_surjective (b ≫ i)
  have heq : CommRingCat.ofHom (algebraMap H C) ≫ α =
      CommRingCat.ofHom (algebraMap H C) ≫ β := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hα, hβ]
    exact hab
  have hαne : α.hom (algebraMap H C h) ≠ 0 := by
    have ha := (a (⊥ : PrimeSpectrum Ω)).property
    change algebraMap H C h ∉ (i (a (⊥ : PrimeSpectrum Ω))).asIdeal at ha
    rw [← Hom.comp_apply, ← hα] at ha
    change α.hom (algebraMap H C h) ∉ (⊥ : PrimeSpectrum Ω).asIdeal at ha
    simpa using ha
  obtain ⟨ζ, hζ, -⟩ := hrot Ω α.hom β.hom (congrArg CommRingCat.Hom.hom heq) hαne
  refine ⟨ζ, ?_⟩
  apply (cancel_mono i).mp
  dsimp only [i]
  simp only [fixedPunctureDeck, Category.assoc, Hom.resLE_comp_ι]
  rw [← Category.assoc, ← hα, ← Spec.map_comp, ← hβ]
  congr 1
  exact CommRingCat.hom_ext hζ

/-- Exact stabilizers make a selected descended section a monomorphism. -/
theorem affine_torsor_stabilizer_section_mono
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    [Module.Finite H C] [Module.FaithfullyFlat H C]
    (G : Type u) [Group G] [Finite G]
    (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
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
        pullback p (Spec.map (CommRingCat.ofHom ι))),
      f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι)) =
        Scheme.Opens.ι (X := Spec (CommRingCat.of F)) U ≫
          Spec.map (CommRingCat.ofHom (algebraMap H F)) →
      q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
        fixedSplitSection p t k d δ x →
      Mono f := by
  dsimp only
  intro f hbase hsection
  let F := (⨅ ζ : K, AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) : Subalgebra H C)
  let U : (Spec (.of F)).Opens := PrimeSpectrum.basicOpen (algebraMap H F (ι g))
  let V : Scheme.{u} := Scheme.Opens.toScheme (X := Spec (.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))
  let q : V ⟶ U.toScheme := (Spec.map (CommRingCat.ofHom F.val.toRingHom)).resLE
    U (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) (by
      change PrimeSpectrum.basicOpen (algebraMap H C (ι g)) ≤
        PrimeSpectrum.basicOpen (algebraMap H C (ι g))
      rfl)
  let v : V ⟶ Spec H := Scheme.Opens.ι _ ≫
    Spec.map (CommRingCat.ofHom (algebraMap H C))
  let u : U.toScheme ⟶ Spec H := U.ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap H F))
  have hqu : q ≫ u = v := by
    dsimp only [q, u, v]
    rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, ← Spec.map_comp]
    rfl
  have hfix (ζ : K) : fixedPunctureDeck H C (ι g) G ρ ζ.val ≫ q = q := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, q, Hom.resLE_comp_ι]
    dsimp only [fixedPunctureDeck]
    rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, ← Spec.map_comp]
    congr 2
    ext c
    have hc : c.val ∈ AlgHom.equalizer (ρ ζ.val) (AlgHom.id H C) :=
      (iInf_le (fun ξ : K ↦ AlgHom.equalizer (ρ ξ.val) (AlgHom.id H C)) ζ) c.property
    exact hc
  have hq : Surjective q := subalgebra_puncture_surjective H C F (ι g)
  have : Surjective q := hq
  have hr (ζ : G) :
      fixedPunctureDeck H C (ι g) G ρ ζ ≫ fixedSplitSection p t k d δ x =
        fixedSplitSection p t k d δ
          (fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
            p T t k hk d δ hδ ζ x) := by
    let z : V := fixedPunctureGeneric C (algebraMap H C (ι g)) hne
    have : Nonempty V := ⟨z⟩
    have : IrreducibleSpace (Spec (.of C) : Scheme) := inferInstance
    have : IrreducibleSpace V :=
      (Scheme.Opens.ι (X := Spec (.of C))
        (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))).isOpenEmbedding.irreducibleSpace
    change _ = fixedSplitSection p t k d δ
      (fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ ζ x)
    dsimp only [fixedPunctureLabel]
    exact split_section_reconstruction p t k d δ hδ _ _ z
  have hpoints (Ω : Type u) [Field Ω] (a b : Spec (.of Ω) ⟶ V)
      (hab : a ≫ q ≫ f = b ≫ q ≫ f) : a ≫ q = b ≫ q := by
    have habase : a ≫ v = b ≫ v := by
      have he := congrArg
        (fun m ↦ m ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι))) hab
      simpa only [Category.assoc, hbase, ← hqu] using he
    obtain ⟨ζ, hζ⟩ := puncture_rotation H C (ι g) G ρ hrot Ω a b habase
    change q ≫ f ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι)) =
      fixedSplitSection p t k d δ x at hsection
    have hs : a ≫ fixedSplitSection p t k d δ x =
        b ≫ fixedSplitSection p t k d δ x := by
      simpa only [Category.assoc, hsection] using congrArg
        (fun m ↦ m ≫ pullback.fst p (Spec.map (CommRingCat.ofHom ι))) hab
    have hlabel : fixedPunctureDescentAction R H g ι C G ρ hρone hρmul hne
        p T t k hk d δ hδ ζ x = x := by
      apply split_label_injective_at p t k d δ hδ Ω a
      rw [← hr, ← Category.assoc, hζ]
      exact hs.symm
    have hζK : ζ ∈ K := (hK ζ).mpr hlabel
    rw [← hζ, Category.assoc, hfix ⟨ζ, hζK⟩]
  have hdiag : Surjective (pullback.diagonal f) := by
    let P := pullback f f
    let E := pullback q (pullback.fst f f)
    let e : E ⟶ P := pullback.snd q (pullback.fst f f)
    let W := pullback q (e ≫ pullback.snd f f)
    let w : W ⟶ E := pullback.snd q (e ≫ pullback.snd f f)
    let A : W ⟶ V := w ≫ pullback.fst q (pullback.fst f f)
    let B : W ⟶ V := pullback.fst q (e ≫ pullback.snd f f)
    have hA : A ≫ q = w ≫ e ≫ pullback.fst f f := by
      dsimp only [A, e]
      rw [Category.assoc, pullback.condition, ← Category.assoc]
    have hB : B ≫ q = w ≫ e ≫ pullback.snd f f := pullback.condition
    have : Surjective e := inferInstance
    have : Surjective w := inferInstance
    constructor
    intro z
    obtain ⟨zE, hzE⟩ := e.surjective z
    obtain ⟨zW, hzW⟩ := w.surjective zE
    let Ω := W.residueField zW
    let φ := W.fromSpecResidueField zW
    have hab : (φ ≫ A) ≫ q ≫ f = (φ ≫ B) ≫ q ≫ f := by
      rw [Category.assoc φ A, ← Category.assoc A q, hA,
        Category.assoc φ B, ← Category.assoc B q, hB]
      simp only [Category.assoc, pullback.condition]
    have heq := hpoints Ω (φ ≫ A) (φ ≫ B) hab
    have hφ : φ ≫ w ≫ e = (φ ≫ A ≫ q) ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
        exact congrArg (fun m ↦ φ ≫ m) hA.symm
      · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
        calc
          φ ≫ w ≫ e ≫ pullback.snd f f = φ ≫ B ≫ q :=
            congrArg (fun m ↦ φ ≫ m) hB.symm
          _ = φ ≫ A ≫ q := by simpa only [Category.assoc] using heq.symm
    refine ⟨(φ ≫ A ≫ q) (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← Hom.comp_apply, ← hφ]
    simpa only [Hom.comp_apply, φ, Scheme.fromSpecResidueField_apply, hzW] using hzE
  have hu : Etale u := affine_torsor_invariant_puncture_etale H (ι g) C G ρ
    hρone hρmul hne hEt hrot K
  have : Etale (f ≫ pullback.snd p (Spec.map (CommRingCat.ofHom ι))) := by
    rw [hbase]
    exact hu
  have : FormallyUnramified f :=
    FormallyUnramified.of_comp f (pullback.snd p (Spec.map (CommRingCat.ofHom ι)))
  have : LocallyOfFiniteType f :=
    locallyOfFiniteType_of_comp f (pullback.snd p (Spec.map (CommRingCat.ofHom ι)))
  have : IsIso (pullback.diagonal f) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hdiag⟩
  exact (pullback.isIso_diagonal_iff f).mp inferInstance


end AlgebraicGeometry.Scheme
