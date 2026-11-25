/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# A section generating at a point of a trivial integral fibre generates near the fibre

Let `f : P ⟶ T` be universally closed with geometrically integral fibres, let `L` be an invertible
module on `P` which is trivial on the fibre `P_t`, and let `s` be a global section of `L` which
generates `L` at some point of `P_t`. Then `s` generates `L` over `f⁻¹ U` for an open
neighbourhood `U` of `t`.

The restriction of `s` to `P_t` is a function on the integral scheme `P_t`, proper over `κ(t)`,
which does not vanish at a point. As `Γ(P_t, 𝒪)` is a field it is a unit, so `s` generates `L`
along all of `P_t`. The locus where `s` does not generate is closed, and so is its image under the
closed map `f`, which misses `t`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.generatesAt_of_isFreeGenerator_pullbackSection`: a section
  generates at the image of a point at which its pullback generates.
- `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_preimage_of_generatesAt`: the
  statement above.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- If the pullback of a global section `s` of an invertible module along `g` is a free
generator near a point `x`, then `s` generates at `g x`. -/
lemma generatesAt_of_isFreeGenerator_pullbackSection (g : X ⟶ Y) (L : Y.Modules)
    [L.IsInvertible] (s : Γ(L, ⊤)) {x : X} {W : X.Opens} (hxW : x ∈ W)
    (hs : IsFreeGenerator (((Modules.pullback g).obj L).presheaf.map
      (homOfLE (le_top : W ≤ g ⁻¹ᵁ ⊤)).op (pullbackSection g s))) :
    GeneratesAt s (g x) := by
  have := IsInvertible.sheafOfModules_isInvertible L
  obtain ⟨V, hxV, -, ℓ, hℓ⟩ := exists_isFreeGenerator L (TopologicalSpace.Opens.mem_top (g x))
  obtain ⟨a, ha⟩ := hℓ.exists_smul_eq (L.presheaf.map (homOfLE le_top).op s)
  refine generatesAt_of_mem_basicOpen hℓ ha.symm ?_
  -- on `W ⊓ g⁻¹ V`, the pullback of `s` is `g^♯ a` times a free generator
  set W' := W ⊓ g ⁻¹ᵁ V.1
  have hW'V : W' ≤ g ⁻¹ᵁ V.1 := inf_le_right
  have hℓ' := (hℓ.pullback_unit_app g).map hW'V
  have h1 : ((Modules.pullback g).obj L).presheaf.map (homOfLE (le_top : W' ≤ g ⁻¹ᵁ ⊤)).op
      (pullbackSection g s) = X.presheaf.map (homOfLE hW'V).op (g.app V.1 a) •
        ((Modules.pullback g).obj L).presheaf.map (homOfLE hW'V).op (pullbackSection g ℓ) := by
    rw [← presheaf_map_homOfLE_map_homOfLE (le_top : g ⁻¹ᵁ V.1 ≤ g ⁻¹ᵁ ⊤) hW'V]
    erw [← pullbackSection_map g (le_top : V.1 ≤ ⊤)]
    rw [← ha, pullbackSection_smul, map_smul]
  obtain ⟨u, hu⟩ := hℓ'.exists_unit_smul_eq
    (show IsFreeGenerator (((Modules.pullback g).obj L).presheaf.map
      (homOfLE (le_top : W' ≤ g ⁻¹ᵁ ⊤)).op (pullbackSection g s)) by
      have := hs.map (inf_le_left : W' ≤ W)
      rwa [presheaf_map_homOfLE_map_homOfLE] at this)
  rw [h1] at hu
  have hua : X.presheaf.map (homOfLE hW'V).op (g.app V.1 a) = u.1 :=
    hℓ'.smul_left_injective hu
  have hmem : x ∈ X.basicOpen (X.presheaf.map (homOfLE hW'V).op (g.app V.1 a)) := by
    rw [hua, X.basicOpen_of_isUnit u.isUnit]
    exact ⟨hxW, hxV⟩
  rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen] at hmem
  exact hmem.2

variable {P T : Scheme.{u}}

/-- **A section generating at a point of a trivial integral fibre generates near the fibre.**
Let `f : P ⟶ T` be universally closed with geometrically integral fibres, `L` an invertible
module on `P` which is trivial on the fibre `P_t`, and `s` a global section of `L` generating `L`
at a point `p` of `P_t`. Then `s` is a free generator of `L` over `f⁻¹ U` for an open
neighbourhood `U` of `t`. -/
theorem exists_isFreeGenerator_preimage_of_generatesAt (f : P ⟶ T) [UniversallyClosed f]
    [GeometricallyIntegral f] (L : P.Modules) [L.IsInvertible] (t : T)
    (hL : Nonempty ((Modules.pullback (f.fiberι t)).obj L ≅ 𝟙_ (f.fiber t).Modules))
    (s : Γ(L, ⊤)) {p : P} (hp : f p = t) (hs : GeneratesAt s p) :
    ∃ U : T.Opens, t ∈ U ∧
      IsFreeGenerator (L.presheaf.map (homOfLE (le_top : f ⁻¹ᵁ U ≤ ⊤)).op s) := by
  obtain ⟨e⟩ := hL
  set g := f.fiberι t
  have : UniversallyClosed (f.fiberToSpecResidueField t) :=
    inferInstanceAs (UniversallyClosed (Limits.pullback.snd f (T.fromSpecResidueField t)))
  have hfield : IsField Γ(f.fiber t, ⊤) :=
    isField_of_universallyClosed (T.residueField t) (f.fiberToSpecResidueField t)
  let := hfield.toField
  set s' : Γ((Modules.pullback g).obj L, ⊤) := pullbackSection g s
  -- the pullback of `s` generates near a point `q₀` of the fibre over `p`
  obtain ⟨q₀, hq₀⟩ : p ∈ Set.range g.base := by
    rw [Scheme.Hom.range_fiberι]
    exact hp
  obtain ⟨W, hpW, hW⟩ := hs
  have hW' : IsFreeGenerator (((Modules.pullback g).obj L).presheaf.map
      (homOfLE (g.preimage_mono (le_top : W ≤ ⊤))).op s') := by
    rw [← pullbackSection_map]
    exact hW.pullback_unit_app g
  have : Nonempty (g ⁻¹ᵁ W) := ⟨⟨q₀, by simpa [hq₀] using hpW⟩⟩
  -- so the function corresponding to `s'` is nonzero, hence a unit
  set c : Γ(f.fiber t, ⊤) := e.hom.app ⊤ s'
  have hs'0 : s' ≠ 0 := by
    intro h0
    exact one_ne_zero (hW'.smul_left_injective (a₁ := 1) (a₂ := 0) (by simp [h0]))
  have hc0 : c ≠ 0 := fun h0 ↦ hs'0 ((bijective_app_of_iso e ⊤).1 (h0.trans (map_zero _).symm))
  have hs' : IsFreeGenerator s' := by
    have h1 : IsFreeGenerator (M := 𝟙_ (f.fiber t).Modules) c := by
      have h := (isFreeGenerator_one (⊤ : (f.fiber t).Opens)).units_smul (Units.mk0 c hc0)
      have hc1 : ((Units.mk0 c hc0 : Γ(f.fiber t, ⊤)) • (1 : Γ(f.fiber t, ⊤)) :
        Γ(f.fiber t, ⊤)) = c := mul_one c
      exact cast (congrArg _ hc1) h
    have h2 := h1.app_hom e.symm
    convert h2 using 1
    change _ = (e.hom.app ⊤ ≫ e.inv.app ⊤) _
    rw [← Hom.comp_app, e.hom_inv_id, Hom.id_app, ConcreteCategory.id_apply]
  -- `s` generates along the whole fibre
  have hfib : f ⁻¹' {t} ⊆ generatingLocus s := by
    intro p' hp'
    rw [← Scheme.Hom.range_fiberι] at hp'
    obtain ⟨q, rfl⟩ := hp'
    refine generatesAt_of_isFreeGenerator_pullbackSection g L s (TopologicalSpace.Opens.mem_top q)
      ?_
    convert hs' using 1
    exact presheaf_map_id_apply _ _
  -- the closed map `f` keeps the non-generating locus away from `t`
  have hC : IsClosed (f.base '' (generatingLocus s : Set P)ᶜ) :=
    f.isClosedMap _ (generatingLocus s).isOpen.isClosed_compl
  refine ⟨⟨_, hC.isOpen_compl⟩, fun ⟨p', hp', hft⟩ ↦ hp' (hfib hft), ?_⟩
  have hle : f ⁻¹ᵁ ⟨_, hC.isOpen_compl⟩ ≤ generatingLocus s := fun p' hp' ↦ by
    by_contra h
    exact hp' ⟨p', h, rfl⟩
  have := (isFreeGenerator_generatingLocus s).map hle
  rwa [presheaf_map_homOfLE_map_homOfLE] at this

/-- **A section generating after pullback generates near the image.** Let `ℓ` be a free generator
of `L` on `O` and `s` a section of `L` over `O` whose pullback along `σ` is a free generator.
Then `s` is a free generator on an open neighbourhood of every point `σ q` in `O`. -/
lemma exists_isFreeGenerator_of_isFreeGenerator_pullbackSection {A : Scheme.{u}} (σ : A ⟶ P)
    {L : P.Modules} {O : P.Opens} {ℓ : Γ(L, O)} (hℓ : IsFreeGenerator ℓ) {s : Γ(L, O)}
    (hs : IsFreeGenerator (pullbackSection σ s)) {q : A} (hq : σ q ∈ O) :
    ∃ (W : P.Opens) (hW : W ≤ O), σ q ∈ W ∧
      IsFreeGenerator (L.presheaf.map (homOfLE hW).op s) := by
  obtain ⟨a, rfl⟩ := hℓ.exists_smul_eq s
  rw [pullbackSection_smul] at hs
  have hℓ' := hℓ.pullback_unit_app σ
  obtain ⟨u, hu⟩ := hℓ'.exists_unit_smul_eq hs
  have hau : σ.app O a = u.1 := hℓ'.smul_left_injective hu
  have hle : P.basicOpen a ≤ O := P.basicOpen_le a
  refine ⟨P.basicOpen a, hle, ?_, ?_⟩
  · have hq' : q ∈ σ ⁻¹ᵁ P.basicOpen a := by
      rw [Scheme.preimage_basicOpen, hau, A.basicOpen_of_isUnit u.isUnit]
      exact hq
    exact hq'
  · have hunit : IsUnit (P.presheaf.map (homOfLE hle).op a) :=
      P.toRingedSpace.isUnit_res_basicOpen a
    rw [map_smul]
    exact (hℓ.map hle).units_smul hunit.unit


end AlgebraicGeometry.Scheme.Modules
