/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSplitResiduePoints
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import all WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Étale splitting of an integral morphism with finite fibre

## References

* Stacks Project, More on Morphisms, Tag 0BSR, with finite residue extensions
* Stacks Project, Tag 0BSR, first proof
* Stacks Project, More on Morphisms, Tag 0BSR
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem exists_singleton_fibre_affine_model
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    (p : PrimeSpectrum A) (hfibre : Set.Finite {q : PrimeSpectrum B |
      PrimeSpectrum.comap (algebraMap A B) q = p})
    (q : PrimeSpectrum B) (hq : PrimeSpectrum.comap (algebraMap A B) q = p) :
    ∃ (C : Subalgebra A B) (_ : Module.Finite A C),
      ∀ q' : PrimeSpectrum B,
        PrimeSpectrum.comap (algebraMap A B) q' = p →
        PrimeSpectrum.comap C.val.toRingHom q' = PrimeSpectrum.comap C.val.toRingHom q →
          q' = q := by
  classical
  let F := {q' : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) q' = p ∧ q' ≠ q}
  have : Finite F := (hfibre.subset (fun _ h ↦ h.1)).to_subtype
  let : Fintype F := Fintype.ofFinite F
  have hsep (q' : F) : ∃ b : B, b ∈ q'.val.asIdeal ∧ b ∉ q.asIdeal := by
    have hnot : ¬ q'.val.asIdeal ≤ q.asIdeal := by
      intro hle
      have hne : q'.val.asIdeal ≠ q.asIdeal := fun h ↦ q'.property.2 (PrimeSpectrum.ext h)
      have hlt := Ideal.IsIntegral.under_lt_under (R := A) (lt_of_le_of_ne hle hne)
      have heq : q'.val.asIdeal.comap (algebraMap A B) =
          q.asIdeal.comap (algebraMap A B) :=
        congrArg PrimeSpectrum.asIdeal (q'.property.1.trans hq.symm)
      exact hlt.ne heq
    obtain ⟨b, hb, hbq⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
    exact ⟨b, hb, hbq⟩
  choose b hb hbq using hsep
  let C := Algebra.adjoin A (Set.range b)
  have hC : Module.Finite A C := Algebra.finite_adjoin_of_finite_of_isIntegral
    (Set.finite_range b) (fun z _ ↦ Algebra.IsIntegral.isIntegral z)
  refine ⟨C, hC, ?_⟩
  intro q' hq' heq
  by_contra hne
  let t : F := ⟨q', hq', hne⟩
  let c : C := ⟨b t, Algebra.subset_adjoin ⟨t, rfl⟩⟩
  have hm : c ∈ (PrimeSpectrum.comap C.val.toRingHom q').asIdeal := hb t
  rw [heq] at hm
  exact hbq t hm

private theorem exists_etale_clopen_singleton_fibre_affine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) [IsIntegralHom f] (s : S)
    (hfibre : Set.Finite {z : X | f z = s}) (x : X) (hx : f x = s) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      IsAffine U ∧ Etale g ∧ g u = s ∧ IsIso (g.residueFieldMap u) ∧
      ∃ V : (pullback f g).Opens, IsClosed (V : Set ↥(pullback f g)) ∧
        ∀ w : ↥(pullback f g), pullback.snd f g w = u →
          (w ∈ V ↔ pullback.fst f g w = x) := by
  classical
  let A := Γ(S, ⊤)
  let B := Γ(X, ⊤)
  let : Algebra A B := f.appTop.hom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨f.isIntegral_app ⊤ (isAffineOpen_top S)⟩
  let p : PrimeSpectrum A := S.isoSpec.hom s
  let q : PrimeSpectrum B := X.isoSpec.hom x
  have hpoint (z : X) :
      PrimeSpectrum.comap (algebraMap A B) (X.isoSpec.hom z) = S.isoSpec.hom (f z) := by
    change (X.isoSpec.hom ≫ Spec.map f.appTop) z = (f ≫ S.isoSpec.hom) z
    rw [Scheme.isoSpec_hom_naturality]
  have hq : PrimeSpectrum.comap (algebraMap A B) q = p := by
    rw [hpoint, hx]
  have hf : Set.Finite {q' : PrimeSpectrum B |
      PrimeSpectrum.comap (algebraMap A B) q' = p} := by
    apply (hfibre.image X.isoSpec.hom).subset
    intro q' hq'
    let z := X.isoSpec.inv q'
    have hzq : X.isoSpec.hom z = q' := by simp [z, ← Scheme.Hom.comp_apply]
    refine ⟨z, ?_, hzq⟩
    apply S.isoSpec.hom.homeomorph.injective
    change S.isoSpec.hom (f z) = S.isoSpec.hom s
    rw [← hpoint, hzq]
    exact hq'
  obtain ⟨C, hC, hsingleton⟩ := exists_singleton_fibre_affine_model p hf q hq
  let : Module.Finite A C := hC
  let ρ : X ⟶ Spec (.of C) := X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom C.val.toRingHom)
  let h : Spec (.of C) ⟶ S :=
    Spec.map (CommRingCat.ofHom (algebraMap A C)) ≫ S.isoSpec.inv
  have hρ : ρ ≫ h = f := by
    simp only [ρ, h, Category.assoc]
    rw [← Spec.map_comp_assoc]
    change X.isoSpec.hom ≫ Spec.map f.appTop ≫ S.isoSpec.inv = f
    rw [Scheme.isoSpec_hom_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsFinite h := by
    have : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A C))) :=
      (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hC)
    infer_instance
  let z := ρ x
  have hz : h z = s := by rw [← Scheme.Hom.comp_apply, hρ, hx]
  have hsingleton' (y : X) (hy : f y = s) (hyz : ρ y = z) : y = x := by
    apply X.isoSpec.hom.homeomorph.injective
    change X.isoSpec.hom y = X.isoSpec.hom x
    apply hsingleton (X.isoSpec.hom y)
    · rw [hpoint, hy]
    · exact hyz
  obtain ⟨U₀, g₀, u₀, hg₀, hu₀, hres₀, W₀, hWfinite, v₀, hv₀, huniq₀, hproj₀, _⟩ :=
    exists_etale_finite_open_of_isolated_fiber_point h z (isOpen_discrete _)
  have : Etale g₀ := hg₀
  have : IsIso (g₀.residueFieldMap u₀) := hres₀
  have : IsFinite (W₀.ι ≫ pullback.snd h g₀) := hWfinite
  have : IsProper W₀.ι := IsProper.of_comp W₀.ι (pullback.snd h g₀)
  have hWclosed : IsClosed (W₀ : Set ↥(pullback h g₀)) := by
    simpa only [Scheme.Opens.range_ι] using W₀.ι.isClosedMap.isClosed_range
  obtain ⟨A₀, hA₀, huA₀, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := U₀) (x := u₀) (U := ⊤) trivial
  let g := A₀.ι ≫ g₀
  let u : A₀.toScheme := ⟨u₀, huA₀⟩
  let k : pullback f g ⟶ pullback h g₀ :=
    pullback.lift (pullback.fst f g ≫ ρ) (pullback.snd f g ≫ A₀.ι) (by
      simp only [Category.assoc, hρ]
      exact pullback.condition)
  have hkp : k ≫ pullback.fst h g₀ = pullback.fst f g ≫ ρ := by simp [k]
  have hkq : k ≫ pullback.snd h g₀ = pullback.snd f g ≫ A₀.ι := by simp [k]
  have hu : g u = s := hu₀.trans hz
  have hres : IsIso (g.residueFieldMap u) := by
    rw [Scheme.residueFieldMap_comp]
    change IsIso (g₀.residueFieldMap u₀ ≫ A₀.ι.residueFieldMap u)
    infer_instance
  refine ⟨A₀.toScheme, g, u, hA₀, inferInstance, hu, hres, k ⁻¹ᵁ W₀,
    hWclosed.preimage k.continuous, ?_⟩
  intro w hw
  have hkw : pullback.snd h g₀ (k w) = u₀ := by
    rw [← Scheme.Hom.comp_apply, hkq, Scheme.Hom.comp_apply, hw]
    rfl
  have hfw : f (pullback.fst f g w) = s := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw, hu]
  constructor
  · intro hmem
    have heq : (⟨k w, hmem⟩ : W₀.toScheme) = v₀ := huniq₀ _ hkw
    apply hsingleton' _ hfw
    have hp := congrArg (fun t ↦ (W₀.ι ≫ pullback.fst h g₀) t) heq
    change pullback.fst h g₀ (k w) = _ at hp
    rw [← Scheme.Hom.comp_apply, hkp, Scheme.Hom.comp_apply] at hp
    exact hp.trans hproj₀
  · intro hwx
    have heq : k w = W₀.ι v₀ := by
      apply pullback_point_unique h g₀
      · rw [← Scheme.Hom.comp_apply, hkp, Scheme.Hom.comp_apply, hwx]
        exact hproj₀.symm
      · exact hkw.trans hv₀.symm
      · change IsIso (g₀.residueFieldMap ((W₀.ι ≫ pullback.snd h g₀) v₀))
        rw [hv₀]
        exact hres₀
    change k w ∈ W₀
    rw [heq]
    exact v₀.property

/-- A finite intermediate algebra separates the selected prime from the other primes in
its fibre. Apply the elementary finite-neighbourhood theorem to this finite model, and
pull its clopen neighbourhood back to the original integral scheme. Affine shrinking
handles a non-affine base. -/
private theorem exists_etale_clopen_singleton_fibre
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f] (s : S)
    (hfibre : Set.Finite {z : X | f z = s}) (x : X) (hx : f x = s) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      IsAffine U ∧ Etale g ∧ g u = s ∧ IsIso (g.residueFieldMap u) ∧
      ∃ V : (pullback f g).Opens, IsClosed (V : Set ↥(pullback f g)) ∧
        ∀ w : ↥(pullback f g), pullback.snd f g w = u →
          (w ∈ V ↔ pullback.fst f g w = x) := by
  classical
  obtain ⟨A, hA, hsA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := s) (U := ⊤) trivial
  have : IsAffine A.toScheme := hA
  let sA : A.toScheme := ⟨s, hsA⟩
  let f' := pullback.snd f A.ι
  obtain ⟨x', hx', hxs'⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := A.ι) x sA hx
  have hfinite : Set.Finite {z : ↥(pullback f A.ι) | f' z = sA} := by
    apply (hfibre.preimage (pullback.fst f A.ι).isOpenEmbedding.injective.injOn).subset
    intro z hz
    change f (pullback.fst f A.ι z) = s
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [show pullback.snd f A.ι z = sA from hz]
    rfl
  obtain ⟨U, g₀, u, hU, hg₀, hgu, hres₀, W, hW, hmem⟩ :=
    exists_etale_clopen_singleton_fibre_affine f' sA hfinite x' hxs'
  have : Etale g₀ := hg₀
  have : IsIso (g₀.residueFieldMap u) := hres₀
  let g := g₀ ≫ A.ι
  let e := pullbackLeftPullbackSndIso f A.ι g₀
  let a := e.inv ≫ pullback.fst f' g₀
  have hap : a ≫ pullback.fst f A.ι = pullback.fst f g := by
    simp [a, e, f', g]
  have haq : e.inv ≫ pullback.snd f' g₀ = pullback.snd f g := by
    simp [e, f', g]
  have hres : IsIso (g.residueFieldMap u) := by
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  refine ⟨U, g, u, hU, inferInstance, ?_, hres, e.inv ⁻¹ᵁ W,
    hW.preimage e.inv.continuous, ?_⟩
  · exact congrArg A.ι hgu
  · intro w hw
    have hw' : pullback.snd f' g₀ (e.inv w) = u := by
      rw [← Scheme.Hom.comp_apply, haq]
      exact hw
    rw [show w ∈ e.inv ⁻¹ᵁ W ↔ e.inv w ∈ W from Iff.rfl, hmem _ hw']
    change a w = x' ↔ pullback.fst f g w = x
    constructor
    · intro heq
      rw [← hap, Scheme.Hom.comp_apply, heq, hx']
    · intro heq
      apply (pullback.fst f A.ι).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hap, heq, hx']

/-- After a pointed affine étale neighbourhood of `s` with trivial residue extension, the
finitely many points `x i` of the fibre over `s` lie in pairwise disjoint clopens `V i` of the
base change, with `V i` meeting the fibre exactly in the point over `x i`. -/
private theorem exists_etale_clopen_fibre_separation
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f]
    (s : S) (n : ℕ) (x : Fin n → X) (hx : Function.Injective x)
    (hxs : ∀ i, f (x i) = s)
    (hex : ∀ z : X, f z = s → ∃ i, z = x i) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      IsAffine U ∧ Etale g ∧ g u = s ∧ IsIso (g.residueFieldMap u) ∧
      ∃ V : Fin n → (pullback f g).Opens,
        (∀ i, IsClosed (V i : Set ↥(pullback f g))) ∧
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
        ∀ (i : Fin n) (w : ↥(pullback f g)), pullback.snd f g w = u →
          (w ∈ V i ↔ pullback.fst f g w = x i) := by
  classical
  have hfibre : Set.Finite {z : X | f z = s} := by
    apply (Set.finite_range x).subset
    intro z hz
    obtain ⟨i, hi⟩ := hex z hz
    exact ⟨i, hi.symm⟩
  have hfamily : ∀ (n : ℕ) (x : Fin n → X), Function.Injective x →
      (∀ i, f (x i) = s) →
      ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
        IsAffine U ∧ Etale g ∧ g u = s ∧ IsIso (g.residueFieldMap u) ∧
        ∃ V : Fin n → (pullback f g).Opens,
          (∀ i, IsClosed (V i : Set ↥(pullback f g))) ∧
          Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
          ∀ (i : Fin n) (w : ↥(pullback f g)), pullback.snd f g w = u →
            (w ∈ V i ↔ pullback.fst f g w = x i) := by
    intro n
    induction n with
    | zero =>
      intro x _ _
      obtain ⟨A, hA, hsA, _⟩ := exists_isAffineOpen_mem_and_subset
        (X := S) (x := s) (U := ⊤) trivial
      have : IsAffine A.toScheme := hA
      exact ⟨A.toScheme, A.ι, ⟨s, hsA⟩, hA, inferInstance, rfl, inferInstance,
        Fin.elim0, by simp, by simp [_root_.Pairwise], by simp⟩
    | succ n ih =>
      intro x hx hxs
      obtain ⟨U₀, g₀, u₀, hU₀, hg₀, hu₀, hres₀, V₀, hclosed₀, hdisj₀, hmem₀⟩ :=
        ih (fun i ↦ x i.castSucc) (hx.comp (Fin.castSucc_injective n))
          (fun i ↦ hxs i.castSucc)
      obtain ⟨U₁, g₁, u₁, _, hg₁, hu₁, hres₁, W₁, hclosed₁, hmem₁⟩ :=
        exists_etale_clopen_singleton_fibre f s hfibre (x (Fin.last n)) (hxs _)
      have : Etale g₀ := hg₀
      have : Etale g₁ := hg₁
      have : IsIso (g₀.residueFieldMap u₀) := hres₀
      have : IsIso (g₁.residueFieldMap u₁) := hres₁
      obtain ⟨p, hp₀, hp₁⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := g₀) (g := g₁) u₀ u₁ (hu₀.trans hu₁.symm)
      obtain ⟨A, hA, hpA, _⟩ := exists_isAffineOpen_mem_and_subset
        (X := pullback g₀ g₁) (x := p) (U := ⊤) trivial
      let u : A.toScheme := ⟨p, hpA⟩
      let b₀ := A.ι ≫ pullback.fst g₀ g₁
      let b₁ := A.ι ≫ pullback.snd g₀ g₁
      let g := b₀ ≫ g₀
      have hg₁eq : b₁ ≫ g₁ = g := by simp [g, b₀, b₁, pullback.condition]
      have hbu₀ : b₀ u = u₀ := hp₀
      have hbu₁ : b₁ u = u₁ := hp₁
      have hu : g u = s := by rw [Scheme.Hom.comp_apply, hbu₀, hu₀]
      have hres : IsIso (g.residueFieldMap u) := by
        have : IsIso ((pullback.fst g₀ g₁).residueFieldMap p) :=
          pullback_fst_residue_iso g₀ g₁ p (hp₁.symm ▸ hres₁)
        rw [Scheme.residueFieldMap_comp]
        have : IsIso (b₀.residueFieldMap u) := by
          rw [Scheme.residueFieldMap_comp]
          change IsIso ((pullback.fst g₀ g₁).residueFieldMap p ≫ A.ι.residueFieldMap u)
          infer_instance
        have : IsIso (g₀.residueFieldMap (b₀ u)) := hbu₀.symm ▸ hres₀
        infer_instance
      let k₀ : pullback f g ⟶ pullback f g₀ :=
        pullback.map f g f g₀ (𝟙 X) b₀ (𝟙 S) (by simp) (by simp [g])
      let k₁ : pullback f g ⟶ pullback f g₁ :=
        pullback.map f g f g₁ (𝟙 X) b₁ (𝟙 S) (by simp)
          (by simpa using hg₁eq.symm)
      have hk₀ (w : ↥(pullback f g)) :
          pullback.snd f g₀ (k₀ w) = b₀ (pullback.snd f g w) := by
        change (k₀ ≫ pullback.snd f g₀) w = (pullback.snd f g ≫ b₀) w
        congr 1
        simp [k₀]
      have hk₁ (w : ↥(pullback f g)) :
          pullback.snd f g₁ (k₁ w) = b₁ (pullback.snd f g w) := by
        change (k₁ ≫ pullback.snd f g₁) w = (pullback.snd f g ≫ b₁) w
        congr 1
        simp [k₁]
      have hkp₀ (w : ↥(pullback f g)) :
          pullback.fst f g₀ (k₀ w) = pullback.fst f g w := by
        change (k₀ ≫ pullback.fst f g₀) w = _
        simp [k₀]
      have hkp₁ (w : ↥(pullback f g)) :
          pullback.fst f g₁ (k₁ w) = pullback.fst f g w := by
        change (k₁ ≫ pullback.fst f g₁) w = _
        simp [k₁]
      let W := k₁ ⁻¹ᵁ W₁
      have hW : IsClosed (W : Set ↥(pullback f g)) := hclosed₁.preimage k₁.continuous
      let C : (pullback f g).Opens := ⟨(W : Set _)ᶜ, hW.isOpen_compl⟩
      let V : Fin (n + 1) → (pullback f g).Opens :=
        Fin.lastCases W (fun i ↦ (k₀ ⁻¹ᵁ V₀ i) ⊓ C)
      have hmemW (w : ↥(pullback f g)) (hw : pullback.snd f g w = u) :
          w ∈ W ↔ pullback.fst f g w = x (Fin.last n) := by
        have h := hmem₁ (k₁ w) (by rw [hk₁, hw, hbu₁])
        change w ∈ W ↔ _ at h
        rwa [hkp₁] at h
      have hmemV (i : Fin n) (w : ↥(pullback f g)) (hw : pullback.snd f g w = u) :
          w ∈ k₀ ⁻¹ᵁ V₀ i ↔ pullback.fst f g w = x i.castSucc := by
        have h := hmem₀ i (k₀ w) (by rw [hk₀, hw, hbu₀])
        change w ∈ k₀ ⁻¹ᵁ V₀ i ↔ _ at h
        rwa [hkp₀] at h
      have : IsAffine A.toScheme := hA
      refine ⟨A.toScheme, g, u, hA, inferInstance, hu, hres, V, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa only [V, Fin.lastCases_last] using hW
        | cast i =>
          simp only [V, Fin.lastCases_castSucc]
          change IsClosed ((k₀ ⁻¹' (V₀ i : Set _)) ∩ (W : Set _)ᶜ)
          exact ((hclosed₀ i).preimage k₀.continuous).inter W.isOpen.isClosed_compl
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact False.elim (hij rfl)
          | cast j =>
            apply disjoint_iff.mpr
            apply le_antisymm _ bot_le
            intro w hw
            simp only [V, Fin.lastCases_last, Fin.lastCases_castSucc] at hw
            exact hw.2.2 hw.1
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            apply disjoint_iff.mpr
            apply le_antisymm _ bot_le
            intro w hw
            simp only [V, Fin.lastCases_last, Fin.lastCases_castSucc] at hw
            exact hw.1.2 hw.2
          | cast j =>
            simp only [V, Fin.lastCases_castSucc]
            apply Disjoint.mono inf_le_left inf_le_left
            rw [disjoint_iff, ← Scheme.Hom.preimage_inf,
              (hdisj₀ (fun h ↦ hij (congrArg Fin.castSucc h))).eq_bot]
            rfl
      · intro i w hw
        induction i using Fin.lastCases with
        | last => simpa only [V, Fin.lastCases_last] using hmemW w hw
        | cast i =>
          simp only [V, Fin.lastCases_castSucc]
          change (w ∈ k₀ ⁻¹ᵁ V₀ i ∧ w ∉ W) ↔ _
          rw [hmemV i w hw, hmemW w hw]
          exact ⟨And.left, fun h ↦ ⟨h, fun h' ↦
            Fin.castSucc_ne_last i (hx (h.symm.trans h'))⟩⟩
  exact hfamily n x hx hxs

private theorem finite_purelyInseparable_fibre_neighbourhood
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S)
    (hfibre : Set.Finite {x : X | f x = s})
    (hresidue : ∀ x : X, f x = s → (f.residueFieldMap x).hom.Finite) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U), Etale g ∧ g u = s ∧
      Set.Finite {w : ↥(pullback f g) | pullback.snd f g w = u} ∧
      ∀ w : ↥(pullback f g), pullback.snd f g w = u →
        @IsPurelyInseparable
          (U.residueField (pullback.snd f g w)) ((pullback f g).residueField w) _ _
          ((pullback.snd f g).residueFieldMap w).hom.toAlgebra := by
  classical
  let F := {x : X // f x = s}
  have : Finite F := hfibre
  let e : Fin (Nat.card F) ≃ F := (Finite.equivFin F).symm
  let x : Fin (Nat.card F) → X := fun i ↦ (e i).val
  have hx (i) : f (x i) = s := (e i).property
  have hfin (i) : letI := (f.residueFieldMap (x i)).hom.toAlgebra
      Module.Finite (S.residueField (f (x i))) (X.residueField (x i)) :=
    hresidue (x i) (hx i)
  obtain ⟨U, g, u, hg, hu, m, y, _, hfst, hsnd, hcover⟩ :=
    exists_etale_split_residue_points f s (Nat.card F) x hx hfin
  have hindex (w : ↥(pullback f g)) (hw : pullback.snd f g w = u) :
      ∃ i j, w = y i j := by
    have hfw : f (pullback.fst f g w) = s := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hw, hu]
    let i := e.symm ⟨pullback.fst f g w, hfw⟩
    have hi : pullback.fst f g w = x i := by
      exact (congrArg Subtype.val (e.apply_symm_apply
        ⟨pullback.fst f g w, hfw⟩)).symm
    obtain ⟨j, hj⟩ := hcover i w hw hi
    exact ⟨i, j, hj⟩
  refine ⟨U, g, u, hg, hu, ?_, ?_⟩
  · apply (Set.finite_range (fun ij : (i : Fin (Nat.card F)) × Fin (m i) ↦
      y ij.1 ij.2)).subset
    intro w hw
    obtain ⟨i, j, rfl⟩ := hindex w hw
    exact ⟨⟨i, j⟩, rfl⟩
  · intro w hw
    obtain ⟨i, j, rfl⟩ := hindex w hw
    obtain ⟨h, _, hpure⟩ := hsnd i j
    cases h
    exact hpure

private theorem clopen_integral {X S : Scheme.{u}} (q : X ⟶ S)
    [IsIntegralHom q] (V : X.Opens) (hV : IsClosed (V : Set X)) :
    IsIntegralHom (V.ι ≫ q) := by
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion V.ι
    (by simpa only [Scheme.Opens.range_ι] using hV)
  infer_instance

private theorem integral_fibre_partition
    {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegralHom f] (s : S)
    (hfibre : Set.Finite {x : X | f x = s}) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      IsAffine U ∧ Etale g ∧ g u = s ∧
      ∃ (m : ℕ) (V : Fin m → (pullback f g).Opens),
        (∀ i, IsClosed (V i : Set ↥(pullback f g))) ∧
        (∀ i, IsAffineOpen (V i)) ∧
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
        (⨆ i, V i) = ⊤ ∧
        ∀ i, IsIntegralHom ((V i).ι ≫ pullback.snd f g) ∧
          ∃ v : (V i).toScheme,
            ((V i).ι ≫ pullback.snd f g) v = u ∧
            (∀ w : (V i).toScheme, ((V i).ι ≫ pullback.snd f g) w = u → w = v) ∧
            IsIso (((V i).ι ≫ pullback.fst f g).residueFieldMap v) := by
  classical
  let F := {x : X // f x = s}
  have : Finite F := hfibre
  let e : Fin (Nat.card F) ≃ F := (Finite.equivFin F).symm
  let x : Fin (Nat.card F) → X := fun i ↦ (e i).val
  have hx : Function.Injective x := Subtype.val_injective.comp e.injective
  have hxs (i) : f (x i) = s := (e i).property
  have hex (z : X) (hz : f z = s) : ∃ i, z = x i := by
    exact ⟨e.symm ⟨z, hz⟩, (congrArg Subtype.val (e.apply_symm_apply ⟨z, hz⟩)).symm⟩
  obtain ⟨U₀, g₀, u₀, hU₀, hg₀, hu₀, hres₀, V₀, hclosed₀, hdisj₀, hmem₀⟩ :=
    exists_etale_clopen_fibre_separation f s (Nat.card F) x hx hxs hex
  have : IsAffine U₀ := hU₀
  have : Etale g₀ := hg₀
  have : IsIso (g₀.residueFieldMap u₀) := hres₀
  let q₀ := pullback.snd f g₀
  let Z : Set ↥(pullback f g₀) := (⨆ i, V₀ i : (pullback f g₀).Opens)ᶜ
  have hZ : IsClosed Z := (⨆ i, V₀ i).isOpen.isClosed_compl
  have huZ : u₀ ∉ q₀ '' Z := by
    rintro ⟨z, hz, hzu⟩
    have hfx : f (pullback.fst f g₀ z) = s := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply,
        show pullback.snd f g₀ z = u₀ from hzu, hu₀]
    obtain ⟨i, hi⟩ := hex _ hfx
    exact hz (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, (hmem₀ i z hzu).mpr hi⟩)
  let B : U₀.Opens := ⟨(q₀ '' Z)ᶜ, (q₀.isClosedMap Z hZ).isOpen_compl⟩
  obtain ⟨A, hA, huA, hAB⟩ := exists_isAffineOpen_mem_and_subset
    (X := U₀) (x := u₀) (U := B) huZ
  let g := A.ι ≫ g₀
  let u : A.toScheme := ⟨u₀, huA⟩
  let k : pullback f g ⟶ pullback f g₀ :=
    pullback.map f g f g₀ (𝟙 X) A.ι (𝟙 S) (by simp) (by simp [g])
  have hkp : k ≫ pullback.fst f g₀ = pullback.fst f g := by simp [k]
  have hkq : k ≫ q₀ = pullback.snd f g ≫ A.ι := by simp [k, q₀]
  let V := fun i ↦ k ⁻¹ᵁ V₀ i
  have hclosed (i) : IsClosed (V i : Set ↥(pullback f g)) :=
    (hclosed₀ i).preimage k.continuous
  have hu : g u = s := hu₀
  have hres : IsIso (g.residueFieldMap u) := by
    rw [Scheme.residueFieldMap_comp]
    change IsIso (g₀.residueFieldMap u₀ ≫ A.ι.residueFieldMap u)
    infer_instance
  have hcover : (⨆ i, V i) = ⊤ := by
    apply top_unique
    intro z _
    by_contra hz
    have hzZ : k z ∈ Z := by
      intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h
      exact hz (TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩)
    have hnot : A.ι (pullback.snd f g z) ∉ q₀ '' Z :=
      hAB (pullback.snd f g z).property
    apply hnot
    exact ⟨k z, hzZ, congrArg (fun h ↦ h z) hkq⟩
  have : IsAffine A.toScheme := hA
  refine ⟨A.toScheme, g, u, inferInstance, inferInstance, hu, Nat.card F, V,
    hclosed, ?_, ?_, hcover, ?_⟩
  · intro i
    have : IsIntegralHom ((V i).ι ≫ pullback.snd f g) :=
      clopen_integral _ _ (hclosed i)
    exact isAffine_of_isAffineHom ((V i).ι ≫ pullback.snd f g)
  · intro i j hij
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (hdisj₀ hij).eq_bot]
    rfl
  · intro i
    refine ⟨clopen_integral _ _ (hclosed i), ?_⟩
    obtain ⟨z, hzx, hzu⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) (x i) u
      ((hxs i).trans hu.symm)
    have hku : q₀ (k z) = u₀ := by
      rw [← Scheme.Hom.comp_apply, hkq, Scheme.Hom.comp_apply, hzu]
      rfl
    have hkx : pullback.fst f g₀ (k z) = x i := by
      rw [← Scheme.Hom.comp_apply, hkp, hzx]
    have hzV : z ∈ V i := (hmem₀ i (k z) hku).mpr hkx
    let v : (V i).toScheme := ⟨z, hzV⟩
    have hv : ((V i).ι ≫ pullback.snd f g) v = u := hzu
    refine ⟨v, hv, ?_, ?_⟩
    · intro w hw
      apply Subtype.ext
      apply pullback_point_unique f g
      · have hkw : q₀ (k ((V i).ι w)) = u₀ := by
          rw [← Scheme.Hom.comp_apply, hkq, Scheme.Hom.comp_apply,
            show pullback.snd f g ((V i).ι w) = u from hw]
          rfl
        have hwx := (hmem₀ i (k ((V i).ι w)) hkw).mp w.property
        rw [← Scheme.Hom.comp_apply, hkp] at hwx
        exact hwx.trans hzx.symm
      · exact hw.trans hzu.symm
      · change IsIso (g.residueFieldMap (pullback.snd f g z))
        rw [hzu]
        exact hres
    · rw [Scheme.residueFieldMap_comp]
      have : IsIso ((pullback.fst f g).residueFieldMap ((V i).ι v)) := by
        change IsIso ((pullback.fst f g).residueFieldMap z)
        apply pullback_fst_residue_iso
        rw [hzu]
        exact hres
      infer_instance

private theorem purelyInseparable_residue_square
    {Y X T S : Scheme.{u}} (a : Y ⟶ X) (r : Y ⟶ T) (q : X ⟶ S) (ψ : T ⟶ S)
    (hsq : a ≫ q = r ≫ ψ) (v : Y) [IsIso (a.residueFieldMap v)]
    (h : @IsPurelyInseparable (S.residueField (q (a v))) (X.residueField (a v)) _ _
      (q.residueFieldMap (a v)).hom.toAlgebra) :
    @IsPurelyInseparable (T.residueField (r v)) (Y.residueField v) _ _
      (r.residueFieldMap v).hom.toAlgebra := by
  let k := S.residueField (q (a v))
  let K := X.residueField (a v)
  let k' := T.residueField (r v)
  let K' := Y.residueField v
  let b := (q.residueFieldMap (a v)).hom
  let c := (r.residueFieldMap v).hom
  let e := (asIso (a.residueFieldMap v)).commRingCatIsoToRingEquiv
  have hb : q (a v) = ψ (r v) :=
    congrArg (fun f : Y ⟶ S ↦ f v) hsq
  let d := ((S.residueFieldCongr hb).hom ≫ ψ.residueFieldMap (r v)).hom
  have he : e.toRingHom.comp b = c.comp d := by
    have H := Scheme.Hom.residueFieldMap_congr hsq v
    simp only [Scheme.residueFieldMap_comp] at H
    exact congrArg CommRingCat.Hom.hom H
  let := b.toAlgebra
  let := c.toAlgebra
  let := d.toAlgebra
  let := (e.toRingHom.comp b).toAlgebra
  let E : K ≃ₐ[k] K' := { __ := e, commutes' := fun _ ↦ rfl }
  have : IsPurelyInseparable k K := h
  have : IsPurelyInseparable k K' := E.isPurelyInseparable
  have : IsScalarTower k k' K' := IsScalarTower.of_algebraMap_eq' he
  exact IsPurelyInseparable.tower_top k k' K'

/-- An integral morphism of affine schemes with finite fibre and finite residue extensions
splits after a pointed affine étale base change into clopen affine pieces with singleton,
purely inseparable fibres. The base field in the last clause is written at the image of `v`;
the preceding equality identifies that image with `u`. The number of pieces may be zero.
-/
theorem exists_integral_fibre_etale_splitting
    {T S : Scheme.{u}} [IsAffine T] [IsAffine S] (π : T ⟶ S) [IsIntegralHom π]
    (s : S) (hfibre : Set.Finite {b : T | π b = s})
    (hresidue : ∀ b : T, π b = s → (π.residueFieldMap b).hom.Finite) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S) (u : U),
      IsAffine U ∧ Etale g ∧ g u = s ∧
      ∃ (m : ℕ) (V : Fin m → (pullback π g).Opens),
        (∀ i, IsClosed (V i : Set ↥(pullback π g))) ∧
        (∀ i, IsAffineOpen (V i)) ∧
        Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
        (⨆ i, V i) = ⊤ ∧
        ∀ i, IsIntegralHom ((V i).ι ≫ pullback.snd π g) ∧
          ∃ v : (V i).toScheme,
            ((V i).ι ≫ pullback.snd π g) v = u ∧
            (∀ w : (V i).toScheme, ((V i).ι ≫ pullback.snd π g) w = u → w = v) ∧
            @IsPurelyInseparable
              (U.residueField (((V i).ι ≫ pullback.snd π g) v))
              ((V i).toScheme.residueField v) _ _
              (((V i).ι ≫ pullback.snd π g).residueFieldMap v).hom.toAlgebra := by
  classical
  obtain ⟨U₀, g₀, u₀, hg₀, hu₀, hf₀, hpure₀⟩ :=
    finite_purelyInseparable_fibre_neighbourhood π s hfibre hresidue
  have : Etale g₀ := hg₀
  let q := pullback.snd π g₀
  obtain ⟨U, ψ, u, hU, hψ, hψu, m, W, hWclosed, hWaffine, hWdisj, hWcover, hW⟩ :=
    integral_fibre_partition q u₀ hf₀
  have : IsAffine U := hU
  have : Etale ψ := hψ
  let g := ψ ≫ g₀
  let e := pullbackLeftPullbackSndIso π g₀ ψ
  let V := fun i ↦ e.inv ⁻¹ᵁ W i
  let d := fun i ↦ e.inv.preimageIso (W i)
  let a := e.inv ≫ pullback.fst q ψ
  let r := pullback.snd π g
  have har : a ≫ q = r ≫ ψ := by simp [a, r, e, q, g]
  have hri (i) : (V i).ι ≫ r = (d i).hom ≫ (W i).ι ≫ pullback.snd q ψ := by
    simp [V, d, r, e, q, g]
  have hai (i) : (V i).ι ≫ a = (d i).hom ≫ (W i).ι ≫ pullback.fst q ψ := by
    simp [V, d, a]
  refine ⟨U, g, u, hU, inferInstance, ?_, m, V, ?_, ?_, ?_, ?_, ?_⟩
  · exact (congrArg g₀ hψu).trans hu₀
  · intro i
    exact (hWclosed i).preimage e.inv.continuous
  · intro i
    exact (hWaffine i).preimage_of_isIso e.inv
  · intro i j hij
    rw [disjoint_iff, ← Scheme.Hom.preimage_inf, (hWdisj hij).eq_bot]
    rfl
  · rw [← Scheme.Hom.preimage_iSup, hWcover]
    rfl
  · intro i
    have : IsIntegralHom ((W i).ι ≫ pullback.snd q ψ) := (hW i).1
    have hi : IsIntegralHom ((V i).ι ≫ r) := by
      rw [hri]
      infer_instance
    obtain ⟨w, hw, hwuniq, hwres⟩ := (hW i).2
    let v := (d i).inv w
    have hvw : (d i).hom v = w := by simp [v, ← Scheme.Hom.comp_apply]
    have hv : ((V i).ι ≫ r) v = u := by
      rw [hri, Scheme.Hom.comp_apply, hvw]
      exact hw
    refine ⟨hi, v, hv, ?_, ?_⟩
    · intro z hz
      apply (d i).hom.homeomorph.injective
      change (d i).hom z = (d i).hom v
      rw [hvw]
      apply hwuniq
      rw [hri, Scheme.Hom.comp_apply] at hz
      exact hz
    · have : IsIso (((V i).ι ≫ a).residueFieldMap v) := by
        rw [hai, Scheme.residueFieldMap_comp]
        have : IsIso (((W i).ι ≫ pullback.fst q ψ).residueFieldMap ((d i).hom v)) :=
          hvw.symm ▸ hwres
        infer_instance
      apply purelyInseparable_residue_square ((V i).ι ≫ a) ((V i).ι ≫ r) q ψ
        (by simp only [Category.assoc, har]) v
      apply hpure₀
      change (((V i).ι ≫ a) ≫ q) v = u₀
      rw [Category.assoc, har, ← Category.assoc, Scheme.Hom.comp_apply, hv, hψu]

end AlgebraicGeometry
