/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator

/-!
# Rigidified trivialisations of modules glue

Let `π : P ⟶ B` be a morphism of schemes with a section `σ`, such that `π` induces surjections
`Γ(B, V) ⟶ Γ(P, π⁻¹ V)` on all opens `V` (e.g. `P = X ×_k B` for a proper geometrically
integral `k`-scheme `X`). An `𝒪_P`-module which is trivial over the preimages of an open cover of
`B` and whose pullback along `σ` is trivial, is trivial. This is the last step of the proof of
the theorem of the cube (Stacks, Tag 0BF4).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_top_of_comp_eq_id`: the gluing
  statement, in terms of free generators.
- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.of_iSup`: being a free generator can be
  checked on an open cover.
- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_of_tensorObj_dual_iso_unit`: `M ≅ N` as soon as
  `M ⊗ Nᵛ` is trivial, for `N` invertible.

## References

* [Stacks: Tag 0BF4](https://stacks.math.columbia.edu/tag/0BF4)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A section whose restrictions to the members of an open cover are free generators is a free
generator. -/
lemma IsFreeGenerator.of_iSup {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}
    (e : Γ(M, U)) {ι : Type*} (W : ι → X.Opens) (hW : ∀ i, W i ≤ U) (hcov : U ≤ ⨆ i, W i)
    (h : ∀ i, IsFreeGenerator (M.presheaf.map (homOfLE (hW i)).op e)) : IsFreeGenerator e := by
  let S : Sieve U := ⟨fun {V} _ ↦ ∃ i, V ≤ W i, fun ⟨i, hi⟩ g ↦ ⟨i, (leOfHom g).trans hi⟩⟩
  refine isFreeGenerator_of_mem e (S := S) (fun x hx ↦ ?_) fun V f ⟨i, hi⟩ ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov hx)
    exact ⟨W i, homOfLE (hW i), ⟨i, le_rfl⟩, hi⟩
  · have := (h i).map hi
    rw [presheaf_map_map_apply] at this
    rwa [Subsingleton.elim f (homOfLE hi ≫ homOfLE (hW i))]

/-- **Rigidified local generators glue.** Let `π : P ⟶ B` be a morphism with a section `σ` such
that `π` induces surjections `Γ(B, V) ⟶ Γ(P, π⁻¹ V)` for all opens `V`. Let `L` be an
`𝒪_P`-module with free generators on the members `π⁻¹ V i` of an open cover pulled back from
`B`, and such that `σ^* L` has a global free generator `γ`. Then `L` has a global free
generator. -/
theorem exists_isFreeGenerator_top_of_comp_eq_id {P B : Scheme.{u}} (π : P ⟶ B)
    (σ : B ⟶ P) (hσ : σ ≫ π = 𝟙 B) (hπ : ∀ V : B.Opens, Function.Surjective (π.app V))
    (L : P.Modules) {ι : Type*} (V : ι → B.Opens) (hV : ⨆ i, V i = ⊤)
    (e : ∀ i, Γ(L, π ⁻¹ᵁ V i)) (he : ∀ i, IsFreeGenerator (e i))
    {γ : Γ((Scheme.Modules.pullback σ).obj L, ⊤)} (hγ : IsFreeGenerator γ) :
    ∃ g : Γ(L, ⊤), IsFreeGenerator g := by
  have hle (W : B.Opens) : W ≤ σ ⁻¹ᵁ π ⁻¹ᵁ W := by
    rw [← Scheme.Hom.comp_preimage, hσ]
    exact le_rfl
  have hge (W : B.Opens) : σ ⁻¹ᵁ π ⁻¹ᵁ W ≤ W := by
    rw [← Scheme.Hom.comp_preimage, hσ]
    exact le_rfl
  have gen (f : B ⟶ B) (hf : f = 𝟙 B) (W W' : B.Opens) (hW : W' ≤ f ⁻¹ᵁ W) (hW' : W' ≤ W)
      (a : Γ(B, W)) : B.presheaf.map (homOfLE hW).op (f.app W a) =
        B.presheaf.map (homOfLE hW').op a := by
    subst hf
    rfl
  have key (W W' : B.Opens) (hW : W' ≤ σ ⁻¹ᵁ π ⁻¹ᵁ W) (hW' : W' ≤ W) (a : Γ(B, W)) :
      B.presheaf.map (homOfLE hW).op (σ.app _ (π.app W a)) = B.presheaf.map (homOfLE hW').op a :=
    gen (σ ≫ π) hσ W W' hW hW' a
  -- Rigidify the generators along `σ`.
  have hs (i : ι) : IsFreeGenerator (pullbackSection σ (e i)) := (he i).pullback_unit_app σ
  choose u hu using fun i ↦ (hs i).exists_unit_smul_eq
    (hγ.map (le_top : σ ⁻¹ᵁ π ⁻¹ᵁ V i ≤ ⊤))
  let c (i : ι) : Γ(B, V i)ˣ :=
    Units.map (B.presheaf.map (homOfLE (hle (V i))).op).hom.toMonoidHom (u i)
  let e' (i : ι) : Γ(L, π ⁻¹ᵁ V i) := π.app (V i) (c i).1 • e i
  have he' (i : ι) : IsFreeGenerator (e' i) :=
    (he i).units_smul (Units.map (π.app (V i)).hom.toMonoidHom (c i))
  have hσe' (i : ι) : pullbackSection σ (e' i) =
      ((Scheme.Modules.pullback σ).obj L).presheaf.map
        (homOfLE (le_top : σ ⁻¹ᵁ π ⁻¹ᵁ V i ≤ ⊤)).op γ := by
    rw [pullbackSection_smul, hu i]
    congr 1
    have h1 := key (V i) _ le_rfl (hge _) (c i).1
    rw [Scheme.presheaf_map_id_apply] at h1
    rw [h1]
    change B.presheaf.map _ (B.presheaf.map _ _) = _
    rw [Scheme.presheaf_map_map_apply, Scheme.presheaf_map_id_apply]
  -- The rigidified generators agree on overlaps.
  have hcompat : TopCat.Presheaf.IsCompatible L.presheaf (fun i ↦ π ⁻¹ᵁ V i) e' := by
    intro i j
    have hri := (he' i).map (inf_le_left : π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j ≤ _)
    have hrj := (he' j).map (inf_le_right : π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j ≤ _)
    obtain ⟨w, hw⟩ := hri.exists_unit_smul_eq hrj
    have h2 := congrArg (pullbackSection σ) hw
    rw [pullbackSection_smul, pullbackSection_map, pullbackSection_map, hσe' i, hσe' j,
      presheaf_map_map_apply, presheaf_map_map_apply] at h2
    have hγO := hγ.map (le_top : σ ⁻¹ᵁ (π ⁻¹ᵁ V i ⊓ π ⁻¹ᵁ V j) ≤ ⊤)
    have h3 : σ.app _ w.1 = 1 := by
      refine hγO.smul_left_injective ?_
      dsimp only
      rw [one_smul]
      convert h2.symm using 3
    obtain ⟨a, ha⟩ := hπ (V i ⊓ V j) w.1
    have ha1 : a = 1 := by
      have h4 := key (V i ⊓ V j) (V i ⊓ V j) (hle _) le_rfl a
      rw [Scheme.presheaf_map_id_apply] at h4
      rw [← h4]
      erw [ha, h3]
      exact map_one _
    have hw1 : w.1 = 1 := by
      rw [← ha, ha1]
      exact map_one _
    rw [hw1, one_smul] at hw
    exact hw.symm
  -- Glue them.
  have hcov : (⊤ : P.Opens) ≤ ⨆ i, π ⁻¹ᵁ V i := by
    intro x _
    have : π x ∈ ⨆ i, V i := hV ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp this
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' ⟨L.presheaf, L.isSheaf⟩
    (fun i ↦ π ⁻¹ᵁ V i) ⊤ (fun _ ↦ homOfLE le_top) hcov e' hcompat
  exact ⟨g, IsFreeGenerator.of_iSup g _ (fun _ ↦ le_top) hcov fun i ↦ (hg i).symm ▸ he' i⟩

/-- If `g^* M ≅ g^* N` for an invertible `N`, then `g^* (M ⊗ Nᵛ)` is trivial. -/
lemma nonempty_pullback_tensorObj_dual_iso_unit {A C : Scheme.{u}} (g : A ⟶ C)
    (M N : C.Modules) [N.IsInvertible]
    (e : (Scheme.Modules.pullback g).obj M ≅ (Scheme.Modules.pullback g).obj N) :
    Nonempty ((Scheme.Modules.pullback g).obj (M ⊗ Nᵛ) ≅ 𝟙_ A.Modules) := by
  obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso g M Nᵛ
  obtain ⟨t'⟩ := nonempty_pullback_tensorObj_iso g N Nᵛ
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit N
  exact ⟨t ≪≫ whiskerRightIso e _ ≪≫ t'.symm ≪≫ (Scheme.Modules.pullback g).mapIso d ≪≫
    pullbackObjUnitIso g⟩

/-- If `M ⊗ Nᵛ` is trivial for an invertible `N`, then `M ≅ N`. -/
lemma nonempty_iso_of_tensorObj_dual_iso_unit {X : Scheme.{u}} (M N : X.Modules)
    [N.IsInvertible] (e : M ⊗ Nᵛ ≅ 𝟙_ X.Modules) : Nonempty (M ≅ N) := by
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit N
  exact ⟨(ρ_ M).symm ≪≫ (Iso.refl M ⊗ᵢ ((β_ _ _) ≪≫ d).symm) ≪≫ (α_ _ _ _).symm ≪≫
    (e ⊗ᵢ Iso.refl N) ≪≫ λ_ N⟩

/-- A trivialisation of `M` over an open `U` gives a free generator of `M` on `U`. -/
lemma exists_isFreeGenerator_of_pullback_ι_iso {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (e : (Scheme.Modules.pullback U.ι).obj M ≅ 𝟙_ U.toScheme.Modules) :
    ∃ m : Γ(M, U), IsFreeGenerator m := by
  let e' : M.restrict U.ι ≅ Modules.unit U := (restrictFunctorIsoPullback U.ι).app M ≪≫ e
  have h := (isFreeGenerator_one (⊤ : U.toScheme.Opens)).app_hom e'.symm
  exact ⟨_, ((isFreeGenerator_restrict_iff U.ι M _).mp h).map (Scheme.Opens.ι_image_top U).ge⟩

end AlgebraicGeometry.Scheme.Modules
