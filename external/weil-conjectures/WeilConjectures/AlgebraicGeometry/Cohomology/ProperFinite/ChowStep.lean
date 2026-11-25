/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma.EmbeddingOver
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProperFinite.Devissage
public import WeilConjectures.AlgebraicGeometry.Cohomology.RelativeSerre
public import WeilConjectures.AlgebraicGeometry.Modules.Annihilator
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Koszul

/-!
# The Chow step of the finiteness theorem

Let `A` be a noetherian ring, `Y` a nonempty proper scheme over `Spec A` and `𝒢` a coherent
`𝒪_Y`-module. Then there are a coherent `𝒪_Y`-module `𝒢'` with finite cohomology over `A` and
a morphism `𝒢 ⟶ 𝒢'` which is an isomorphism over a nonempty open subset of `Y`
(`AlgebraicGeometry.Scheme.Modules.exists_hasFiniteH_hom_isIso_restrict`).

By Chow's lemma there is a proper surjective `π : Y' ⟶ Y`, an isomorphism over a dense open
`U` of `Y`, with `Y'` closed both in `ℙ(N; Y)` and in `ℙ(N; Spec A)`. For `d ≫ 0` the higher
direct images of `π^* 𝒢(d)` vanish (relative Serre vanishing), so the cohomology of
`𝒢' = π_* (π^* 𝒢(d))` is that of `π^* 𝒢(d)` on the projective `A`-scheme `Y'`, which is finite.
The morphism `𝒢 ⟶ π_* π^* 𝒢 ⟶ π_* (π^* 𝒢(d))`, the second map being multiplication by `T_i^d`,
is an isomorphism over the open subset of `U` over which `T_i` does not vanish.

This is the projective input of [Stacks, Tag 02O6].
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section Restrict

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism which is an isomorphism over an open `W` is bijective on sections over every
open contained in `W`. -/
lemma bijective_app_of_isIso_restrict (φ : M ⟶ N) {W V : X.Opens}
    [IsIso ((restrictFunctor W.ι).map φ)] (hV : V ≤ W) : Function.Bijective (φ.app V) := by
  obtain ⟨V', rfl⟩ : ∃ V' : W.toScheme.Opens, W.ι ''ᵁ V' = V :=
    ⟨W.ι ⁻¹ᵁ V, by rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hV]⟩
  exact ConcreteCategory.bijective_of_isIso (((restrictFunctor W.ι).map φ).app V')

/-- A morphism which is bijective on sections over the affine opens contained in an open `W`
is an isomorphism over `W`. -/
lemma isIso_restrict_of_bijective_app (φ : M ⟶ N) (W : X.Opens)
    (h : ∀ V : X.Opens, IsAffineOpen V → V ≤ W → Function.Bijective (φ.app V)) :
    IsIso ((restrictFunctor W.ι).map φ) :=
  isIso_of_bijective_app_of_isAffineOpen _ fun V hV ↦
    h _ (hV.image_of_isOpenImmersion W.ι) ((W.ι.image_le_opensRange V).trans (by simp))

end Restrict

/-- **Pulling back sections along an isomorphism over an open.** Let `π : X ⟶ Y` be an
isomorphism over the open `U` of `Y` and `𝒢` a quasi-coherent `𝒪_Y`-module. For every affine
open `V ⊆ U`, pulling back sections `Γ(Y, V; 𝒢) ⟶ Γ(X, π⁻¹ V; π^* 𝒢)` is bijective: `π⁻¹ V` is
affine with ring of functions `Γ(Y, V)`, and the sections of `π^* 𝒢` over it are
`Γ(Y, V) ⊗[Γ(Y, V)] Γ(𝒢, V)`. -/
lemma bijective_pullbackSection_of_isIso_morphismRestrict {X Y : Scheme.{u}} (π : X ⟶ Y)
    {U : Y.Opens} [IsIso (π ∣_ U)] (G : Y.Modules) [G.IsQuasicoherent] {V : Y.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ U) :
    Function.Bijective (pullbackSection π : Γ(G, V) → Γ((pullback π).obj G, π ⁻¹ᵁ V)) := by
  obtain ⟨V', rfl⟩ : ∃ V' : U.toScheme.Opens, U.ι ''ᵁ V' = V :=
    ⟨U.ι ⁻¹ᵁ V, by
      rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.2 hVU]⟩
  have hV' : IsAffineOpen V' := (U.ι.isAffineOpen_iff_of_isOpenImmersion).1 hV
  have hpre : (π ⁻¹ᵁ U).ι ''ᵁ ((π ∣_ U) ⁻¹ᵁ V') = π ⁻¹ᵁ (U.ι ''ᵁ V') :=
    image_morphismRestrict_preimage π U V'
  have hA : IsAffineOpen (π ⁻¹ᵁ (U.ι ''ᵁ V')) :=
    hpre ▸ (hV'.preimage (π ∣_ U)).image_of_isOpenImmersion _
  have hbij : Function.Bijective (π.appLE (U.ι ''ᵁ V') (π ⁻¹ᵁ (U.ι ''ᵁ V')) le_rfl) := by
    have h₁ : Function.Bijective (π.appLE (U.ι ''ᵁ V') ((π ⁻¹ᵁ U).ι ''ᵁ ((π ∣_ U) ⁻¹ᵁ V'))
        (image_morphismRestrict_preimage π U V').le) := by
      have := ConcreteCategory.bijective_of_isIso ((π ∣_ U).app V')
      rwa [morphismRestrict_app'] at this
    have h₂ : Function.Bijective (X.presheaf.map (homOfLE hpre.ge).op) := by
      have : ∀ {A B : X.Opens} (h : B ≤ A), A = B → IsIso (X.presheaf.map (homOfLE h).op) := by
        rintro A B h rfl
        rw [Subsingleton.elim (homOfLE h) (𝟙 _), op_id, X.presheaf.map_id]
        infer_instance
      have := this hpre.ge hpre
      exact ConcreteCategory.bijective_of_isIso _
    rw [← π.appLE_map (image_morphismRestrict_preimage π U V').le (homOfLE hpre.ge).op]
    rw [CategoryTheory.hom_comp]
    exact h₂.comp h₁
  obtain ⟨e, he⟩ := exists_linearEquiv_pullback_sections π G hV hA le_rfl
  let := (π.appLE (U.ι ''ᵁ V') (π ⁻¹ᵁ (U.ι ''ᵁ V')) le_rfl).hom.toAlgebra
  have hb := TensorProduct.bijective_one_tmul_of_surjective (M := Γ(G, U.ι ''ᵁ V'))
    (S := Γ(X, π ⁻¹ᵁ (U.ι ''ᵁ V'))) hbij.2 fun a ha m ↦ by
      rw [show a = 0 from hbij.1 ((RingHom.mem_ker.1 ha).trans (map_zero _).symm), zero_smul]
  have hid : (homOfLE (le_rfl : π ⁻¹ᵁ (U.ι ''ᵁ V') ≤ π ⁻¹ᵁ (U.ι ''ᵁ V'))).op = 𝟙 _ :=
    Subsingleton.elim _ _
  have key : (pullbackSection π : Γ(G, U.ι ''ᵁ V') → _) =
      e ∘ fun m ↦ (1 : Γ(X, π ⁻¹ᵁ (U.ι ''ᵁ V'))) ⊗ₜ[Γ(Y, U.ι ''ᵁ V')] m := by
    funext m
    rw [Function.comp_apply, he, hid, CategoryTheory.Functor.map_id]
    rfl
  rw [key]
  exact e.bijective.comp hb

namespace ProjectiveSpace

/-- The global section `Tᵢ^d` of `𝒪(d)` on `ℙ(n; S)`, as a morphism `𝒪 ⟶ 𝒪(d)`. -/
def twistPowSection (n : Type u) (S : Scheme.{u}) (i : n) :
    (d : ℕ) → (𝟙_ (ℙ(n; S)).Modules ⟶ ProjectiveSpace.twist n S d)
  | 0 => (ProjectiveSpace.unitIsoTwistZero n S).hom ≫ eqToHom (by rw [Nat.cast_zero])
  | d + 1 => twistPowSection n S i d ≫ ProjectiveSpace.twistMulX n S i d ≫
      eqToHom (by rw [Nat.cast_succ])

/-- The section `Tᵢ^d` of `𝒪(d)` is an isomorphism `𝒪 ≅ 𝒪(d)` over the standard open
`D₊(Tᵢ)`. -/
instance isIso_restrict_twistPowSection (n : Type u) (S : Scheme.{u}) (i : n) (d : ℕ) :
    IsIso ((restrictFunctor (ProjectiveSpace.standardOpen n S i).ι).map
      (twistPowSection n S i d)) := by
  induction d with
  | zero =>
    rw [twistPowSection, Functor.map_comp]
    infer_instance
  | succ d ih =>
    rw [twistPowSection, Functor.map_comp, Functor.map_comp]
    infer_instance

end ProjectiveSpace

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **The Chow step.** Let `A` be noetherian, `p : Y ⟶ Spec A` proper with `Y` nonempty and `𝒢`
a coherent `𝒪_Y`-module. There are a coherent `𝒪_Y`-module `𝒢'` with finite cohomology over `A`
and a morphism `φ : 𝒢 ⟶ 𝒢'` which is an isomorphism over a nonempty open subset of `Y`.

With `π : Y' ⟶ Y` the Chow modification of `p`, `e : Y' ⟶ ℙ(N; Y)` its closed embedding over
`Y` and `d ≫ 0`, one takes `𝒢' = π_* (π^* 𝒢 ⊗ e^* 𝒪(d))` and for `φ` the composite of the unit
`𝒢 ⟶ π_* π^* 𝒢` with the pushforward of multiplication by `Tᵢ^d`. -/
theorem exists_hasFiniteH_hom_isIso_restrict {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A)) [IsProper p]
    [Nonempty Y] (G : Y.Modules) [SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G]
    [SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) G] :
    ∃ (G' : Y.Modules) (_ : SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf) G')
      (_ : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) G') (φ : G ⟶ G')
      (W : Y.Opens), (W : Set Y).Nonempty ∧ IsIso ((restrictFunctor W.ι).map φ) ∧
        HasFiniteH p G' := by
  classical
  have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  -- the Chow modification
  let π := ChowModification.modificationMap p
  let e := ChowModification.toProjectiveSpaceSource p
  have he : e ≫ ℙ(ChowModification.index p; Y) ↘ Y = π :=
    ChowModification.toProjectiveSpaceSource_over p
  have := isGrothendieckAbelian (ChowModification p)
  let F := (pullback π).obj G
  -- relative Serre vanishing
  obtain ⟨m₀, hm₀⟩ := exists_isZero_higherDirectImage_tensorObj_twistRestrict he F
  let d : ℕ := m₀.toNat
  have hd : m₀ ≤ (d : ℤ) := Int.self_le_toNat m₀
  let L := ProjectiveSpace.twistRestrict e d
  have : L.IsInvertible := IsInvertible.pullback e _
  have := isQuasicoherent_tensorObj F L
  have := isFinitePresentation_tensorObj F L
  -- the open where `π` is an isomorphism and `Tᵢ` does not vanish
  obtain ⟨U, hUd, hU⟩ := ChowModification.exists_dense_isIso_restrict p
  obtain ⟨y, hyU⟩ : (U : Set Y).Nonempty := hUd.nonempty
  obtain ⟨x, rfl⟩ := π.surjective y
  obtain ⟨i, hi⟩ : ∃ i, e x ∈ ProjectiveSpace.standardOpen (ChowModification.index p) Y i :=
    TopologicalSpace.Opens.mem_iSup.1 ((ProjectiveSpace.iSup_standardOpen _ Y).symm ▸ trivial :
      e x ∈ ⨆ i, ProjectiveSpace.standardOpen (ChowModification.index p) Y i)
  let O := e ⁻¹ᵁ ProjectiveSpace.standardOpen (ChowModification.index p) Y i
  let W : Y.Opens := U ⊓ ⟨(π '' (O : Set (ChowModification p))ᶜ)ᶜ,
    (π.isClosedMap _ O.isOpen.isClosed_compl).isOpen_compl⟩
  have hinj {a b : ChowModification p} (ha : π a ∈ U) (hb : π b ∈ U) (hab : π a = π b) :
      a = b := by
    have := (π ∣_ U).isOpenEmbedding.injective (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩)
      (Subtype.ext (by simpa using hab))
    exact congrArg Subtype.val this
  have hWO : π ⁻¹ᵁ W ≤ O := fun z hz ↦ by
    by_contra hzO
    exact hz.2 ⟨z, hzO, rfl⟩
  have hxW : π x ∈ W := ⟨hyU, fun ⟨z, hzO, hzx⟩ ↦ hzO
    (hinj (hzx ▸ hyU) hyU hzx ▸ hi)⟩
  -- the morphism `G ⟶ π_* (π^* G ⊗ L)`
  let s : 𝟙_ _ ⟶ L := (pullbackObjUnitIso e).inv ≫
    (pullback e).map (ProjectiveSpace.twistPowSection _ Y i d)
  have : IsIso ((restrictFunctor O.ι).map s) :=
    isIso_restrictFunctor_map_pullbackObjUnitIso_inv_comp _
  let ψ : F ⟶ F ⊗ L := (ρ_ F).inv ≫ (F ◁ s)
  have : IsIso ((restrictFunctor O.ι).map ψ) := by
    have := isIso_restrictFunctor_map_whiskerLeft s F (U := O)
    rw [Functor.map_comp]
    infer_instance
  let φ : G ⟶ (pushforward π).obj (F ⊗ L) :=
    (pullbackPushforwardAdjunction π).unit.app G ≫ (pushforward π).map ψ
  -- coherence of `π_* (π^* G ⊗ L)`
  have := (pullbackPushforwardAdjunction π).rightAdjoint_preservesLimits.{0, 0}
  let E := (Functor.rightDerivedZeroIsoSelf (pushforward π)).app (F ⊗ L)
  have hqc : ((pushforward π).obj (F ⊗ L)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso E
      (isQuasicoherent_higherDirectImage π (F ⊗ L) 0)
  have : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf)
      (((pushforward π).rightDerived 0).obj (F ⊗ L)) :=
    isFinitePresentation_higherDirectImage_zero_of_projectiveSpace he (F ⊗ L)
  have hfp : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf)
      ((pushforward π).obj (F ⊗ L)) := isFinitePresentation_of_iso E
  refine ⟨_, hqc, hfp, φ, W, ⟨_, hxW⟩, ?_, ?_⟩
  · refine isIso_restrict_of_bijective_app φ W fun V hV hVW ↦ ?_
    have h₁ := bijective_pullbackSection_of_isIso_morphismRestrict π G hV (hVW.trans inf_le_left)
    have h₂ := bijective_app_of_isIso_restrict ψ ((π.preimage_mono hVW).trans hWO)
    exact h₂.comp h₁
  · refine (hasFiniteH_pushforward_iff_of_isZero π p (F ⊗ L) fun q ↦ hm₀ d hd q).2 fun q ↦ ?_
    have h := finite_H_of_isClosedImmersion A (ChowModification.toProjectiveSpace p) (F ⊗ L) q
    rwa [ChowModification.toProjectiveSpace_over] at h

end AlgebraicGeometry.Scheme.Modules
