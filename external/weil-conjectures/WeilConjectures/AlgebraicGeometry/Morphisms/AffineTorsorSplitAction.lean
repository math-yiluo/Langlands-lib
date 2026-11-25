/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Connected.Clopen
import Mathlib.AlgebraicGeometry.Properties

/-! # The action on labels of a pulled-back splitting

## References

* Stacks Project, Tag 03SF, finite Galois covers and their permutation sets
* Stacks Project, Tag 03SF (connected cover)
* Stacks Project, Tag 03SF, the equivalence with finite permutation sets
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Restrict the contravariant automorphism induced by `ρ ζ` to D(h).
The element h comes from H and is therefore fixed by every H-algebra homomorphism. -/
noncomputable def fixedPunctureDeck (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (ζ : G) :
    (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) ⟶
      (Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C h))) :=
  (Spec.map (CommRingCat.ofHom (ρ ζ).toRingHom)).resLE
    (PrimeSpectrum.basicOpen (algebraMap H C h))
    (PrimeSpectrum.basicOpen (algebraMap H C h)) (by
    change PrimeSpectrum.basicOpen (algebraMap H C h) ≤
      PrimeSpectrum.basicOpen ((ρ ζ) (algebraMap H C h))
    rw [AlgHom.commutes])

/-- Restriction of a deck map preserves the structural map to Spec H. -/
theorem fixedPunctureDeck_base (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (ζ : G) :
    fixedPunctureDeck H C h G ρ ζ ≫
        (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C h))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H C)) =
      (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
          (PrimeSpectrum.basicOpen (algebraMap H C h))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap H C)) := by
  dsimp only [fixedPunctureDeck]
  rw [← Category.assoc, Hom.resLE_comp_ι, Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  exact (ρ ζ).commutes x

private theorem puncture_deck_one (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C) (hρone : ρ 1 = AlgHom.id H C) :
    fixedPunctureDeck H C h G ρ 1 = 𝟙 _ := by
  apply (cancel_mono (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C h)))).mp
  simp only [fixedPunctureDeck, Hom.resLE_comp_ι, hρone, Category.id_comp]
  change _ ≫ Spec.map (𝟙 (CommRingCat.of C)) = _
  rw [Spec.map_id, Category.comp_id]

private theorem puncture_deck_mul (H : CommRingCat.{u}) (C : Type u)
    [CommRing C] [Algebra H C] (h : H) (G : Type u) [Group G]
    (ρ : G → C →ₐ[H] C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) (a b : G) :
    fixedPunctureDeck H C h G ρ (a * b) =
      fixedPunctureDeck H C h G ρ a ≫ fixedPunctureDeck H C h G ρ b := by
  apply (cancel_mono (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C h)))).mp
  simp only [fixedPunctureDeck, Category.assoc, Hom.resLE_comp_ι,
    Hom.resLE_comp_ι_assoc, ← Spec.map_comp, hρmul]
  congr 2

/-- The zero prime is an actual point of D(h), since h is nonzero. -/
def fixedPunctureGeneric (C : Type u) [CommRing C] [IsDomain C]
    (h : C) (hne : h ≠ 0) :
    Scheme.Opens.toScheme (X := Spec (CommRingCat.of C)) (PrimeSpectrum.basicOpen h) :=
  by
    change {x : PrimeSpectrum C // x ∈ PrimeSpectrum.basicOpen h}
    exact ⟨⊥, by simpa using hne⟩

/-- Pull the i-th split section back along k, retaining the map to Y. -/
noncomputable def fixedSplitSection {Y S T V : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (k : V ⟶ T) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (i : Fin d) : V ⟶ Y :=
  k ≫ Sigma.ι (fun _ : Fin d ↦ T) i ≫ δ.inv ≫ pullback.fst p t

/-- The pulled-back split sections lie over k. -/
theorem fixedSplitSection_base {Y S T V : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (k : V ⟶ T) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (i : Fin d) : fixedSplitSection p t k d δ i ≫ p = k ≫ t := by
  have hi : δ.inv ≫ pullback.snd p t = Sigma.desc (fun _ : Fin d ↦ 𝟙 T) := by
    rw [← hδ, ← Category.assoc, δ.inv_hom_id, Category.id_comp]
  simp only [fixedSplitSection, Category.assoc]
  rw [pullback.condition, ← Category.assoc δ.inv, hi]
  simp

/-- Read the label of a section in the splitting at the specified point.
This is an evaluation, not an arbitrary choice of an orbit or a component. -/
noncomputable def fixedSplitLabel {Y S T V : Scheme.{u}} (p : Y ⟶ S) (t : T ⟶ S)
    (k : V ⟶ T) (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (s : V ⟶ Y) (hs : s ≫ p = k ≫ t) (x : V) : Fin d :=
  (sigmaOpenCover (fun _ : Fin d ↦ T)).idx ((pullback.lift s k hs ≫ δ.hom) x)

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

private theorem split_section_injective {Y S T V : Scheme.{u}}
    (p : Y ⟶ S) (t : T ⟶ S) (k : V ⟶ T) (d : ℕ)
    (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (x : V) : Function.Injective (fixedSplitSection p t k d δ) := by
  intro i j hij
  have hinv : δ.inv ≫ pullback.snd p t = Sigma.desc (fun _ : Fin d ↦ 𝟙 T) := by
    rw [← hδ, ← Category.assoc, δ.inv_hom_id, Category.id_comp]
  have he : k ≫ Sigma.ι (fun _ : Fin d ↦ T) i ≫ δ.inv =
      k ≫ Sigma.ι (fun _ : Fin d ↦ T) j ≫ δ.inv := by
    apply pullback.hom_ext
    · exact hij
    · simp only [Category.assoc, hinv, Sigma.ι_comp_desc, Category.comp_id]
  have he' : k ≫ Sigma.ι (fun _ : Fin d ↦ T) i =
      k ≫ Sigma.ι (fun _ : Fin d ↦ T) j := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun a ↦ a ≫ δ.hom) he
  exact congrArg Sigma.fst
    ((sigmaι_eq_iff (fun _ : Fin d ↦ T) _ _ _ _).mp (congrArg (fun a ↦ a x) he'))

/-- The label obtained by precomposing a split section with the deck map of `ρ ζ`. -/
noncomputable def fixedPunctureLabel
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t)
    (ζ : G) (i : Fin d) : Fin d :=
  fixedSplitLabel p t k d δ
    (fixedPunctureDeck H C (ι g) G ρ ζ ≫ fixedSplitSection p t k d δ i)
    (by
      rw [Category.assoc, fixedSplitSection_base p t k d δ hδ, hk]
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ Spec.map (CommRingCat.ofHom ι))
        (fixedPunctureDeck_base H C (ι g) G ρ ζ))
    (fixedPunctureGeneric C (algebraMap H C (ι g)) hne)

/-- The explicit label evaluation satisfies the identity and cocycle laws. -/
theorem fixedPunctureLabel_laws
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t) :
    let a := fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ
    (∀ i, a 1 i = i) ∧ (∀ ζ ξ i, a (ζ * ξ) i = a ζ (a ξ i)) := by
  let V := Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
    (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))
  let x : V := fixedPunctureGeneric C (algebraMap H C (ι g)) hne
  have : Nonempty V := ⟨x⟩
  have : IrreducibleSpace (Spec (CommRingCat.of C) : Scheme) := inferInstance
  have : IrreducibleSpace V :=
    (Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g)))).isOpenEmbedding.irreducibleSpace
  let a := fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ
  have hr (ζ : G) (i : Fin d) :
      fixedPunctureDeck H C (ι g) G ρ ζ ≫ fixedSplitSection p t k d δ i =
        fixedSplitSection p t k d δ (a ζ i) := by
    dsimp only [a, fixedPunctureLabel]
    exact split_section_reconstruction p t k d δ hδ _ _ x
  have hinj := split_section_injective p t k d δ hδ x
  constructor
  · intro i
    apply hinj
    rw [← hr, puncture_deck_one H C (ι g) G ρ hρone, Category.id_comp]
  · intro ζ ξ i
    apply hinj
    rw [← hr, ← hr, ← hr, puncture_deck_mul H C (ι g) G ρ hρmul,
      Category.assoc]

/-- The concrete descent action; its underlying function is label evaluation.
The law theorem supplies proofs only; no component data are chosen from it. -/
noncomputable def fixedPunctureDescentAction
    (R H : CommRingCat.{u}) (g : R) (ι : R →+* H)
    (C : Type u) [CommRing C] [Algebra H C] [IsDomain C]
    (G : Type u) [Group G] (ρ : G → C →ₐ[H] C)
    (hρone : ρ 1 = AlgHom.id H C)
    (hρmul : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b))
    (hne : algebraMap H C (ι g) ≠ 0)
    {Y : Scheme.{u}} (p : Y ⟶ Spec R)
    (T : Scheme.{u}) (t : T ⟶ Spec R)
    (k : Scheme.Opens.toScheme (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ⟶ T)
    (hk : k ≫ t = Scheme.Opens.ι (X := Spec (CommRingCat.of C))
      (PrimeSpectrum.basicOpen (algebraMap H C (ι g))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap H C)) ≫ Spec.map (CommRingCat.ofHom ι))
    (d : ℕ) (δ : pullback p t ≅ ∐ fun _ : Fin d ↦ T)
    (hδ : δ.hom ≫ Sigma.desc (fun _ : Fin d ↦ 𝟙 T) = pullback.snd p t) :
    G →* Equiv.Perm (Fin d) := by
  let a := fixedPunctureLabel R H g ι C G ρ hne p T t k hk d δ hδ
  have hl : (∀ i, a 1 i = i) ∧ (∀ ζ ξ i, a (ζ * ξ) i = a ζ (a ξ i)) :=
    fixedPunctureLabel_laws R H g ι C G ρ hρone hρmul hne p T t k hk d δ hδ
  let e : G → Equiv.Perm (Fin d) := fun ζ ↦
    { toFun := a ζ
      invFun := a ζ⁻¹
      left_inv := fun i ↦ by rw [← hl.2, inv_mul_cancel, hl.1]
      right_inv := fun i ↦ by rw [← hl.2, mul_inv_cancel, hl.1] }
  exact
    { toFun := e
      map_one' := by apply Equiv.ext; intro i; exact hl.1 i
      map_mul' := fun ζ ξ ↦ by apply Equiv.ext; intro i; exact hl.2 ζ ξ i }

end AlgebraicGeometry.Scheme
