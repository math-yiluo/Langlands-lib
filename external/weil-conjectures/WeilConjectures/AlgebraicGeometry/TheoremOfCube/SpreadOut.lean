/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.TheoremOfCube.CrossIdeal

/-!
# Triviality on a fibre spreads out (Stacks, Tag 0BF3)

Let `X`, `Y` be proper and geometrically integral over a field `K` with `K`-points `x`, `y`, and
let `L` be an invertible module on `X ×_K Y ×_K Z` which is trivial on the slices
`{x} × Y × Z` and `X × {y} × Z` and on the fibre over a point `t` of `Z`. Then `L` is trivial
over the preimage of a neighbourhood of `t`.

The twist `𝒢 = pr^* J ⊗ L` by the cross ideal `J` of `X × Y` is flat over `Z` with vanishing
fibre cohomology in degree one at `t` (Künneth), so `H¹(f⁻¹ V, 𝒢) = 0` for affine opens `V`
near `t` (`AlgebraicGeometry.Scheme.Modules.exists_subsingleton_H_preimage_of_hFiber_eq_zero`).
Local lifts of rigidified trivialisations of `L` on the two slices differ by sections of `𝒢`, so
they can be corrected to glue to a section of `L` over `f⁻¹ V`
(`AlgebraicGeometry.Scheme.Modules.exists_forall_exists_app_eq_sub_of_subsingleton_H_one`). This
section generates `L` along the slice, hence at a point of the fibre over `t`, hence over the
preimage of a neighbourhood of `t`
(`AlgebraicGeometry.Scheme.Modules.exists_isFreeGenerator_preimage_of_generatesAt`).

## Main statements

- `AlgebraicGeometry.TheoremOfCube.exists_mem_isFreeGenerator`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

namespace TheoremOfCube

variable {K : Type u} [Field K] (X Y Z : Over (Spec (.of K)))

/-- Glue affine local sections modulo a quasi-coherent module with vanishing first cohomology.
Keeping the cover and its restriction maps over arbitrary schemes avoids unfolding the products
used to construct the local sections. -/
private theorem exists_section_of_affine_local_lifts {A B : Scheme.{u}} (f : A ⟶ B)
    {V : B.Opens} (hV : IsAffineOpen V) [IsSeparated (f ∣_ V)]
    {G L : A.Modules} [G.IsQuasicoherent] (η : G ⟶ L)
    (hH : Subsingleton (((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj G).H 1))
    {σ : Type u} (O : σ → A.Opens) (hO : ∀ i, IsAffineOpen (O i))
    (hOS : ∀ i, O i ≤ f ⁻¹ᵁ V)
    (hcov : ∀ q : (f ⁻¹ᵁ V).toScheme, ∃ i, (f ⁻¹ᵁ V).ι q ∈ O i)
    (sq : ∀ i, Γ(L, O i))
    (hinj : ∀ i {U : A.Opens}, IsAffineOpen U → U ≤ O i → Function.Injective (η.app U))
    (hs : ∀ i j {U : A.Opens}, IsAffineOpen U → ∀ (hi : U ≤ O i) (hj : U ≤ O j),
      ∃ b : Γ(G, U), η.app U b =
        L.presheaf.map (homOfLE hj).op (sq j) - L.presheaf.map (homOfLE hi).op (sq i)) :
    ∃ t : Γ(L, f ⁻¹ᵁ V), ∀ i, ∃ b : Γ(G, O i),
      η.app (O i) b = L.presheaf.map (homOfLE (hOS i)).op t - sq i := by
  let S := f ⁻¹ᵁ V
  have : IsAffine V.toScheme := hV
  have : IsSeparated (terminal.from S.toScheme) := by
    rw [← terminal.comp_from (f ∣_ V)]
    infer_instance
  let Ω (i : σ) : S.toScheme.Opens := S.ι ⁻¹ᵁ O i
  have hΩim (i : σ) : S.ι ''ᵁ Ω i = O i := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr (hOS i)]
  have hΩ (i : σ) : IsAffineOpen (Ω i) :=
    (hO i).preimage_of_isOpenImmersion S.ι (by rw [Scheme.Opens.opensRange_ι]; exact hOS i)
  have hcover : iSup Ω = ⊤ := eq_top_iff.mpr fun q _ ↦
    TopologicalSpace.Opens.mem_iSup.mpr (hcov q)
  let η' := (Scheme.Modules.restrictFunctor S.ι).map η
  have : SheafOfModules.IsQuasicoherent (R := S.toScheme.ringCatSheaf) (G.restrict S.ι) :=
    (SheafOfModules.isQuasicoherent S.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app G).symm
      (inferInstance : SheafOfModules.IsQuasicoherent (R := S.toScheme.ringCatSheaf)
        ((Scheme.Modules.pullback S.ι).obj G))
  have hH' : Subsingleton ((G.restrict S.ι).H 1) :=
    (Scheme.Modules.H.mapLinearEquiv
      ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app G) 1).toEquiv.subsingleton
  let s' (i : σ) : Γ(L.restrict S.ι, Ω i) :=
    L.presheaf.map (homOfLE (hΩim i).le).op (sq i)
  have hinter {n : ℕ} (y : Fin (n + 1) → σ) :
      IsAffineOpen (S.ι ''ᵁ ⨅ l, Ω (y l)) :=
    (IsAffineOpen.iInf fun l ↦ hΩ (y l)).image_of_isOpenImmersion S.ι
  have hle {n : ℕ} (y : Fin (n + 1) → σ) (i : Fin (n + 1)) :
      S.ι ''ᵁ ⨅ l, Ω (y l) ≤ O (y i) :=
    (S.ι.image_mono (iInf_le _ i)).trans (hΩim (y i)).le
  have hinj' (y : Fin 3 → σ) : Function.Injective (η'.app (⨅ l, Ω (y l))) :=
    hinj (y 0) (hinter y) (hle y 0)
  have hs' (y : Fin 2 → σ) : ∃ b : Γ(G.restrict S.ι, ⨅ l, Ω (y l)),
      η'.app _ b = (L.restrict S.ι).presheaf.map
        (homOfLE (iInf_le (fun l ↦ Ω (y l)) 1)).op (s' (y 1)) -
        (L.restrict S.ι).presheaf.map
          (homOfLE (iInf_le (fun l ↦ Ω (y l)) 0)).op (s' (y 0)) := by
    have e (i : Fin 2) : (L.restrict S.ι).presheaf.map
        (homOfLE (iInf_le (fun l ↦ Ω (y l)) i)).op (s' (y i)) =
        L.presheaf.map (homOfLE (hle y i)).op (sq (y i)) := by
      rw [Scheme.Modules.restrict_map]
      exact Scheme.Modules.presheaf_map_presheaf_map_apply _ _ _ _ _
    rw [e 1, e 0]
    exact hs (y 0) (y 1) (hinter y) (hle y 0) (hle y 1)
  obtain ⟨t, ht⟩ := Scheme.Modules.exists_forall_exists_app_eq_sub_of_subsingleton_H_one
    (f ∣_ V) η' hH' Ω hΩ hcover hinj' s' hs'
  have hSS : S.ι ''ᵁ ⊤ = S := Scheme.Opens.ι_image_top S
  refine ⟨L.presheaf.map (homOfLE hSS.ge).op t, fun i ↦ ?_⟩
  obtain ⟨b, hb⟩ := ht i
  have hb' : η.app (S.ι ''ᵁ Ω i) b =
      L.presheaf.map (homOfLE (S.ι.image_mono le_top)).op t -
        L.presheaf.map (homOfLE (hΩim i).le).op (sq i) := hb
  refine ⟨G.presheaf.map (homOfLE (hΩim i).ge).op b, ?_⟩
  rw [Scheme.Modules.Hom.app_presheaf_map, hb', map_sub,
    Scheme.Modules.presheaf_map_homOfLE_map_homOfLE,
    Scheme.Modules.presheaf_map_homOfLE_map_homOfLE,
    Scheme.Modules.presheaf_map_homOfLE_map_homOfLE,
    Scheme.Modules.presheaf_map_id_apply]

set_option backward.isDefEq.respectTransparency false in
/-- **Gluing the local lifts.** If `H¹` of the twist `𝒢` vanishes over `f⁻¹ V` for an affine
open `V` of `Z`, there is a section of `L` over `f⁻¹ V` generating `L` along the slice
`{x} × Y × Z`. -/
theorem exists_section_isFreeGenerator (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) [L.IsInvertible]
    {ex : Γ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L, ⊤)}
    {ey : Γ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L, ⊤)}
    (hex : Scheme.Modules.IsFreeGenerator ex)
    (hC : (sliceComparison X Y Z x y L).hom.app ⊤ (Scheme.Modules.pullbackSection _ ex) =
      Scheme.Modules.pullbackSection _ ey)
    {V : Z.left.Opens} (hV : IsAffineOpen V) [IsSeparated ((snd (X ⊗ Y) Z).left ∣_ V)]
    (hH : Subsingleton (((Scheme.Modules.pullback ((snd (X ⊗ Y) Z).left ⁻¹ᵁ V).ι).obj
      (twist X Y Z x y L)).H 1)) :
    ∃ s : Γ(L, (snd (X ⊗ Y) Z).left ⁻¹ᵁ V), ∀ q : (Y ⊗ Z).left,
      sliceX X Y Z x q ∈ (snd (X ⊗ Y) Z).left ⁻¹ᵁ V →
      ∃ (W : ((X ⊗ Y) ⊗ Z).left.Opens) (hW : W ≤ (snd (X ⊗ Y) Z).left ⁻¹ᵁ V),
        sliceX X Y Z x q ∈ W ∧
          Scheme.Modules.IsFreeGenerator (L.presheaf.map (homOfLE hW).op s) := by
  classical
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  have := Scheme.Modules.isQuasicoherent_toModules (crossIdeal X Y x y)
  have : (twist X Y Z x y L).IsQuasicoherent := Scheme.Modules.isQuasicoherent_tensorObj _ L
  let S := ((snd (X ⊗ Y) Z).left ⁻¹ᵁ V)
  have : IsAffine V.toScheme := hV
  -- the data of the cover
  have hdata (q : S.toScheme) : ∃ (UW : (X ⊗ Y).left.Opens) (O : ((X ⊗ Y) ⊗ Z).left.Opens)
      (ℓ : Γ(L, O)) (sq : Γ(L, O)), IsAffineOpen UW ∧ IsAffineOpen O ∧ S.ι q ∈ O ∧ O ≤ S ∧
      O ≤ (fst (X ⊗ Y) Z).left ⁻¹ᵁ UW ∧ Scheme.Modules.IsFreeGenerator ℓ ∧
      Scheme.Modules.pullbackSection (sliceX X Y Z x) sq =
        ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex ∧
      Scheme.Modules.pullbackSection (sliceY X Y Z y) sq =
        ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey := by
    obtain ⟨UW, hUW, hqUW, -⟩ := exists_isAffineOpen_mem_and_subset
      (x := (fst (X ⊗ Y) Z).left (S.ι q)) (U := ⊤) trivial
    have hqS : S.ι q ∈ S := by
      have h := Scheme.Opens.range_ι S
      exact (Set.ext_iff.mp h _).mp ⟨q, rfl⟩
    obtain ⟨O, hpO, hOle, ℓ, hℓ⟩ := Scheme.Modules.exists_isFreeGenerator L
      (W := S ⊓ (fst (X ⊗ Y) Z).left ⁻¹ᵁ UW) ⟨hqS, hqUW⟩
    obtain ⟨sq, hsx, hsy⟩ := exists_lift X Y Z x y L O.2 hℓ ex ey hC
    exact ⟨UW, O.1, ℓ, sq, hUW, O.2, hpO, hOle.trans inf_le_left, hOle.trans inf_le_right, hℓ,
      hsx, hsy⟩
  choose UW O ℓ sq hUW hO hqO hOS hOπ hℓ hsx hsy using hdata
  have hpx (q : S.toScheme) {W : ((X ⊗ Y) ⊗ Z).left.Opens} (hW : W ≤ O q) :
      Scheme.Modules.pullbackSection (sliceX X Y Z x) (L.presheaf.map (homOfLE hW).op (sq q)) =
        ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex := by
    rw [Scheme.Modules.pullbackSection_map, hsx q, Scheme.Modules.presheaf_map_homOfLE_map_homOfLE]
  have hpy (q : S.toScheme) {W : ((X ⊗ Y) ⊗ Z).left.Opens} (hW : W ≤ O q) :
      Scheme.Modules.pullbackSection (sliceY X Y Z y) (L.presheaf.map (homOfLE hW).op (sq q)) =
        ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L).presheaf.map (homOfLE le_top).op ey := by
    rw [Scheme.Modules.pullbackSection_map, hsy q, Scheme.Modules.presheaf_map_homOfLE_map_homOfLE]
  have hsub {A : Scheme.{u}} (g : A ⟶ ((X ⊗ Y) ⊗ Z).left) {W : ((X ⊗ Y) ⊗ Z).left.Opens}
      (a b : Γ(L, W)) : Scheme.Modules.pullbackSection g (a - b) =
        Scheme.Modules.pullbackSection g a - Scheme.Modules.pullbackSection g b :=
    map_sub _ _ _
  have hinj (q : S.toScheme) {U : ((X ⊗ Y) ⊗ Z).left.Opens}
      (hU : IsAffineOpen U) (hle : U ≤ O q) :
      Function.Injective ((twistι X Y Z x y L).app U) :=
    injective_twistι_app X Y Z x y L hU (hUW q) (hle.trans (hOπ q)) ((hℓ q).map hle)
  have hs (i j : S.toScheme) {U : ((X ⊗ Y) ⊗ Z).left.Opens}
      (hU : IsAffineOpen U) (hi : U ≤ O i) (hj : U ≤ O j) :
      ∃ b : Γ(twist X Y Z x y L, U), (twistι X Y Z x y L).app U b =
        L.presheaf.map (homOfLE hj).op (sq j) - L.presheaf.map (homOfLE hi).op (sq i) :=
    mem_range_twistι_app X Y Z x y L hU (hUW i) (hi.trans (hOπ i)) ((hℓ i).map hi)
      (by rw [hsub, hpx, hpx, sub_self]) (by rw [hsub, hpy, hpy, sub_self])
  obtain ⟨t, ht⟩ := exists_section_of_affine_local_lifts (snd (X ⊗ Y) Z).left hV
    (twistι X Y Z x y L) hH O hO hOS (fun q ↦ ⟨q, hqO q⟩) sq hinj hs
  refine ⟨t, fun q₀ hq₀ ↦ ?_⟩
  obtain ⟨q, hq⟩ : sliceX X Y Z x q₀ ∈ Set.range S.ι := by
    have h := Scheme.Opens.range_ι S
    exact (Set.ext_iff.mp h _).mpr hq₀
  obtain ⟨b, hb⟩ := ht q
  have hb' : L.presheaf.map (homOfLE (hOS q)).op t =
      (twistι X Y Z x y L).app (O q) b + sq q := eq_add_of_sub_eq hb.symm
  have hpb : Scheme.Modules.pullbackSection (sliceX X Y Z x)
      (L.presheaf.map (homOfLE (hOS q)).op t) =
      ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L).presheaf.map (homOfLE le_top).op ex := by
    rw [hb', Scheme.Modules.pullbackSection_add,
      (pullbackSection_twistι_app_eq_zero X Y Z x y L (hO q) (hUW q) (hOπ q) (hℓ q) b).1,
      zero_add, hsx]
  have hgen : Scheme.Modules.IsFreeGenerator (Scheme.Modules.pullbackSection (sliceX X Y Z x)
      (L.presheaf.map (homOfLE (hOS q)).op t)) := by
    rw [hpb]
    exact hex.map le_top
  have hq₀' : sliceX X Y Z x q₀ ∈ O q := hq ▸ hqO q
  obtain ⟨W, hW, hqW, hWgen⟩ :=
    Scheme.Modules.exists_isFreeGenerator_of_isFreeGenerator_pullbackSection (sliceX X Y Z x)
      (hℓ q) hgen hq₀'
  refine ⟨W, hW.trans (hOS q), hqW, ?_⟩
  rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at hWgen
  exact hWgen



/-- **Triviality on a fibre spreads out** (Stacks, Tag 0BF3), in terms of one invertible module.
Let `X`, `Y` be proper and geometrically integral over `K` with `K`-points `x`, `y`, and let `L`
be an invertible module on `X ×_K Y ×_K Z` which is trivial on the slices `{x} × Y × Z` and
`X × {y} × Z` and on the fibre over `t ∈ Z`. Then `L` has a free generator over the preimage of
an open neighbourhood of `t`. -/
theorem exists_mem_isFreeGenerator [IsProper X.hom] [GeometricallyIntegral X.hom]
    [IsProper Y.hom] [GeometricallyIntegral Y.hom] (x : 𝟙_ _ ⟶ X) (y : 𝟙_ _ ⟶ Y)
    (L : ((X ⊗ Y) ⊗ Z).left.Modules) [L.IsInvertible]
    (hx : Nonempty ((Scheme.Modules.pullback (sliceX X Y Z x)).obj L ≅ 𝟙_ _))
    (hy : Nonempty ((Scheme.Modules.pullback (sliceY X Y Z y)).obj L ≅ 𝟙_ _)) (t : Z.left)
    (ht : Nonempty ((Scheme.Modules.pullback ((snd (X ⊗ Y) Z).left.fiberι t)).obj L ≅
      𝟙_ ((snd (X ⊗ Y) Z).left.fiber t).Modules)) :
    ∃ U : Z.left.Opens, t ∈ U ∧ ∃ m : Γ(L, (snd (X ⊗ Y) Z).left ⁻¹ᵁ U),
      Scheme.Modules.IsFreeGenerator m := by
  have : IsProper (X ⊗ Y).hom :=
    inferInstanceAs (IsProper (Limits.pullback.fst X.hom Y.hom ≫ X.hom))
  have : GeometricallyIntegral (X ⊗ Y).hom :=
    GeometricallyIntegral.comp_of_flat (Limits.pullback.fst X.hom Y.hom) X.hom
  have : IsProper (snd (X ⊗ Y) Z).left :=
    inferInstanceAs (IsProper (Limits.pullback.snd (X ⊗ Y).hom Z.hom))
  have : LocallyOfFinitePresentation (snd (X ⊗ Y) Z).left :=
    inferInstanceAs (LocallyOfFinitePresentation (Limits.pullback.snd (X ⊗ Y).hom Z.hom))
  have : GeometricallyIntegral (snd (X ⊗ Y) Z).left :=
    inferInstanceAs (GeometricallyIntegral (Limits.pullback.snd (X ⊗ Y).hom Z.hom))
  have : SheafOfModules.IsInvertible.{u, u, u} L :=
    Scheme.Modules.IsInvertible.sheafOfModules_isInvertible L
  -- the twist `𝒢` has vanishing `H¹` over affine opens near `t`
  have := isFinitePresentation_crossIdeal X Y x y
  have := Scheme.Modules.isQuasicoherent_toModules (crossIdeal X Y x y)
  have : (twist X Y Z x y L).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_tensorObj _ L
  have hflat : (twist X Y Z x y L).IsFlatOver (snd (X ⊗ Y) Z).left :=
    Scheme.Modules.isFlatOver_pullback_fst_tensorObj (X ⊗ Y).hom Z.hom _ L
  obtain ⟨U₁, htU₁, hU₁⟩ := Scheme.Modules.exists_subsingleton_H_preimage_of_hFiber_eq_zero
    (snd (X ⊗ Y) Z).left (twist X Y Z x y L) hflat 1 t (hFiber_twist_eq_zero X Y Z x y L t ht)
  obtain ⟨V, hV, htV, hVU₁⟩ := exists_isAffineOpen_mem_and_subset htU₁
  -- a section generating along the slice `{x} × Y × Z` over `V`
  obtain ⟨ex, ey, hex, -, hC⟩ := exists_isFreeGenerator_slices X Y Z x y L hx hy
  obtain ⟨s, hs⟩ := exists_section_isFreeGenerator X Y Z x y L hex hC hV (hU₁ V hV hVU₁)
  -- pass to the open subscheme `S = f⁻¹ V` over `V`
  let S := (snd (X ⊗ Y) Z).left ⁻¹ᵁ V
  let f' := (snd (X ⊗ Y) Z).left ∣_ V
  have : (L.restrict S.ι).IsInvertible :=
    Scheme.Modules.IsInvertible.of_iso ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app L).symm
  let t' : V.toScheme := ⟨t, htV⟩
  have ht' : Nonempty ((Scheme.Modules.pullback (f'.fiberι t')).obj (L.restrict S.ι) ≅
      𝟙_ (f'.fiber t').Modules) := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_iso_unit_fiber_morphismRestrict
      (snd (X ⊗ Y) Z).left L V t' ht
    exact ⟨(Scheme.Modules.pullback _).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback S.ι).app L) ≪≫ e⟩
  have hSS : S.ι ''ᵁ ⊤ = S := Scheme.Opens.ι_image_top S
  let s' : Γ(L.restrict S.ι, ⊤) := L.presheaf.map (homOfLE hSS.le).op s
  -- the point `(x, y, t)`
  set q₀ := (slicePt Z y).base t
  have hq₀ : sliceX X Y Z x q₀ ∈ S := by
    change (snd (X ⊗ Y) Z).left (sliceX X Y Z x ((slicePt Z y) t)) ∈ V
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Over.comp_left, ← Over.comp_left]
    simpa using htV
  obtain ⟨W, hWS, hqW, hWgen⟩ := hs q₀ hq₀
  obtain ⟨p', hp'⟩ : sliceX X Y Z x q₀ ∈ Set.range S.ι := by
    have h := Scheme.Opens.range_ι S
    exact (Set.ext_iff.mp h _).mpr hq₀
  have hgen : Scheme.Modules.GeneratesAt s' p' := by
    refine ⟨S.ι ⁻¹ᵁ W, show S.ι p' ∈ W from hp' ▸ hqW, ?_⟩
    rw [Scheme.Modules.isFreeGenerator_restrict_iff]
    have hWeq : S.ι ''ᵁ (S.ι ⁻¹ᵁ W) = W := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hWS]
    have h := hWgen.map hWeq.le
    rw [Scheme.Modules.presheaf_map_homOfLE_map_homOfLE] at h
    convert h using 1
    rw [Scheme.Modules.restrict_map]
    exact Scheme.Modules.presheaf_map_presheaf_map_apply _ _ _ _ _
  have hfp' : f' p' = t' := by
    refine Subtype.ext ?_
    rw [morphismRestrict_base_coe]
    change (snd (X ⊗ Y) Z).left (S.ι p') = t
    rw [hp']
    have hcomp : slicePt Z y ≫ sliceX X Y Z x ≫ (snd (X ⊗ Y) Z).left = 𝟙 Z.left := by
      rw [← Over.comp_left, ← Over.comp_left]
      simp
    change (slicePt Z y ≫ sliceX X Y Z x ≫ (snd (X ⊗ Y) Z).left) t = t
    rw [hcomp]
    rfl
  obtain ⟨U', htU', hU'⟩ := Scheme.Modules.exists_isFreeGenerator_preimage_of_generatesAt f'
    (L.restrict S.ι) t' ht' s' hfp' hgen
  refine ⟨V.ι ''ᵁ U', ⟨t', htU', rfl⟩, ?_⟩
  have heq := image_morphismRestrict_preimage (snd (X ⊗ Y) Z).left V U'
  rw [Scheme.Modules.isFreeGenerator_restrict_iff] at hU'
  exact ⟨_, hU'.map heq.ge⟩

end TheoremOfCube

end AlgebraicGeometry
