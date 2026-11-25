/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.Mathlib.RingTheory.Ideal.Maps
public import WeilConjectures.Mathlib.RingTheory.Localization.Finiteness

/-!

# Finite-type extension of quasi-coherent ideal sheaves

This file proves the ideal-sheaf form of Stacks Project Tag 01PF: on a quasi-compact
quasi-separated scheme, a finite-type ideal sheaf on a quasi-compact open `W` extends to a
finite-type ideal sheaf on the whole scheme, and the extension can be taken inside any
prescribed ambient ideal sheaf restricting to it
(blueprint: `lemma:nagata-extend-finite-type-ideal`).

The proof enlarges the open on which the ideal sheaf is of finite type one affine open at a
time (`Scheme.IdealSheafData.exists_le_ofFiniteTypeOn_sup`), and a finite induction over an
affine cover concludes. The binary gluing step is order-theoretic: the glued ideal sheaf is
the intersection of the maximal quasi-coherent extensions
(`Scheme.IdealSheafData.map` along the two inclusions) of the current ideal sheaf and of a
finitely generated approximation on the new affine piece, intersected with the ambient
ideal sheaf. Its restrictions are computed by flat base change of scheme-theoretic images
(`Scheme.IdealSheafData.map_comap_of_isPullback`). The approximation on the new affine
piece is produced by clearing denominators on a finite basic-open cover of the overlap
(`Ideal.exists_fg_le_map_eq`).

## Main definitions

- `Scheme.IdealSheafData.ofFiniteTypeOn I O`: the ideals of sections on the affine opens
  contained in `O` are finitely generated;
- `Scheme.IdealSheafData.ofFiniteType`: `I` is of finite type on the whole scheme.

The zero and unit ideal sheaves are of finite type (`Scheme.IdealSheafData.ofFiniteType_bot`
and `Scheme.IdealSheafData.ofFiniteType_top`).

## Main results

- `Scheme.IdealSheafData.ofFiniteTypeOn_iff_comap`: finite-typeness on `O` is
  finite-typeness of the restriction to `O`;
- `Scheme.IdealSheafData.ofFiniteTypeOn.sup` and
  `Scheme.IdealSheafData.ofFiniteTypeOn.iSup`: finite-typeness is local on the target;
- `Scheme.IdealSheafData.ofFiniteType.comap`: finite-typeness is stable under pullback
  along an arbitrary morphism of schemes;
- `Scheme.IdealSheafData.exists_le_ofFiniteTypeOn_sup`: the binary gluing step;
- `Scheme.IdealSheafData.exists_finiteType_le_comap_eq_of_le`,
  `Scheme.IdealSheafData.exists_finiteType_le_comap_eq` and
  `Scheme.IdealSheafData.exists_finiteType_comap_eq`: the three forms of Tag 01PF;
- `Scheme.IdealSheafData.exists_finiteType_le_comap_eq_of_isAffineHom`: the variant of
  Tag 01PF prescribing the pullback along an affine morphism instead of the restriction to
  a quasi-compact open;
- `Scheme.IdealSheafData.exists_finiteType_le_comap_eq_disjoint_support`: the form used to
  transport a blow-up centre along a closed immersion, which additionally keeps the support
  away from a prescribed quasi-compact open
  (blueprint: `lemma:nagata-finite-type-ideal-extension-closed`).

The affine-morphism variant is proved by covering `X` by finitely many affine opens `W`,
choosing on each of them finitely many sections of the ambient ideal sheaf which already
generate its pullback over the affine open `j ⁻¹ᵁ W` of the source, extending the ideal
sheaf they span to a finite-type ideal sheaf inside the ambient one by Tag 01PF, and
summing over the cover.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

section FiniteType

/-- An ideal sheaf is of finite type on an open `O` if its ideal of sections on every
affine open contained in `O` is finitely generated. -/
def ofFiniteTypeOn (I : X.IdealSheafData) (O : X.Opens) : Prop :=
  ∀ U : X.affineOpens, ↑U ≤ O → (I.ideal U).FG

/-- An ideal sheaf is of finite type if its ideal of sections on every affine open is
finitely generated. -/
def ofFiniteType (I : X.IdealSheafData) : Prop :=
  I.ofFiniteTypeOn ⊤

lemma ofFiniteType_iff (I : X.IdealSheafData) :
    I.ofFiniteType ↔ ∀ U : X.affineOpens, (I.ideal U).FG :=
  ⟨fun h U ↦ h U le_top, fun h U _ ↦ h U⟩

/-- On a locally Noetherian scheme, every quasi-coherent ideal sheaf is of finite
type. -/
lemma ofFiniteType_of_isLocallyNoetherian [IsLocallyNoetherian X] (I : X.IdealSheafData) :
    I.ofFiniteType := fun U _ ↦
  have := IsLocallyNoetherian.component_noetherian (X := X) U
  IsNoetherian.noetherian (I.ideal U)

/-- The unit ideal sheaf is of finite type. -/
lemma ofFiniteType_top : (⊤ : X.IdealSheafData).ofFiniteType := fun U _ ↦ by
  have h : (⊤ : X.IdealSheafData).ideal U = ⊤ := rfl
  rw [h]
  exact ⟨{1}, by simp⟩

/-- The zero ideal sheaf is of finite type. -/
lemma ofFiniteType_bot : (⊥ : X.IdealSheafData).ofFiniteType := fun _ _ ↦ Submodule.fg_bot

/-- A sum of two finite-type ideal sheaves is of finite type. -/
lemma ofFiniteType.sup {I J : X.IdealSheafData} (hI : I.ofFiniteType) (hJ : J.ofFiniteType) :
    (I ⊔ J).ofFiniteType := fun U _ ↦ Submodule.FG.sup (hI U le_top) (hJ U le_top)

/-- Finite-typeness on an open `O` is finite-typeness of the restriction to `O`. -/
theorem ofFiniteTypeOn_iff_comap (I : X.IdealSheafData) (O : X.Opens) :
    I.ofFiniteTypeOn O ↔ (I.comap O.ι).ofFiniteType := by
  constructor
  · intro h U' _
    rw [fg_ideal_comap_iff]
    exact h _ (O.ι_image_le U'.1)
  · intro h U hU
    have hle : U.1 ≤ O.ι.opensRange := by rwa [Scheme.Opens.opensRange_ι]
    have himg : O.ι ''ᵁ (O.ι ⁻¹ᵁ U.1) = U.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hU]
    have hcongr : (⟨O.ι ''ᵁ (O.ι ⁻¹ᵁ U.1),
        (U.2.preimage_of_isOpenImmersion O.ι hle).image_of_isOpenImmersion O.ι⟩ :
        X.affineOpens) = U := Subtype.ext himg
    have hfg := (fg_ideal_comap_iff O.ι I
      ⟨O.ι ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion O.ι hle⟩).mp (h _ le_top)
    rwa [hcongr] at hfg

/-- Locality of finite-typeness: an ideal sheaf which is of finite type on two opens is
of finite type on their union. -/
theorem ofFiniteTypeOn.sup {I : X.IdealSheafData} {O₁ O₂ : X.Opens}
    (h₁ : I.ofFiniteTypeOn O₁) (h₂ : I.ofFiniteTypeOn O₂) :
    I.ofFiniteTypeOn (O₁ ⊔ O₂) := by
  intro U hU
  -- on a straddling affine open, the ideal of sections is finitely generated because its
  -- localizations at a spanning family of sections are
  have hspan : Ideal.span {f : Γ(X, U.1) | X.basicOpen f ≤ O₁ ∨ X.basicOpen f ≤ O₂} = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hxU
    rcases TopologicalSpace.Opens.mem_sup.mp (hU hxU) with hx | hx
    · obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le (⟨x, hx⟩ : O₁) hxU
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, Or.inl hf⟩, hxf⟩
    · obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le (⟨x, hx⟩ : O₂) hxU
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, Or.inr hf⟩, hxf⟩
  refine Ideal.fg_of_localizationSpan _ hspan fun g ↦ ?_
  have hfg : (I.ideal (X.affineBasicOpen g.1)).FG := by
    rcases g.2 with hg | hg
    · exact h₁ (X.affineBasicOpen g.1) ((X.affineBasicOpen_coe g.1).trans_le hg)
    · exact h₂ (X.affineBasicOpen g.1) ((X.affineBasicOpen_coe g.1).trans_le hg)
  have := U.2.isLocalization_basicOpen g.1
  refine Ideal.FG.map_localizationAway (S := Γ(X, X.basicOpen g.1)) ?_
  rwa [algebraMap_basicOpen_eq, I.map_ideal_basicOpen U g.1]

/-- Locality of finite-typeness: an ideal sheaf which is of finite type on every member of
a family of opens is of finite type on their supremum. -/
theorem ofFiniteTypeOn.iSup {I : X.IdealSheafData} {ι : Type*} {O : ι → X.Opens}
    (h : ∀ i, I.ofFiniteTypeOn (O i)) : I.ofFiniteTypeOn (⨆ i, O i) := by
  intro U hU
  -- on a straddling affine open, the ideal of sections is finitely generated because its
  -- localizations at a spanning family of sections are
  have hspan : Ideal.span {f : Γ(X, U.1) | ∃ i, X.basicOpen f ≤ O i} = ⊤ := by
    rw [← U.2.self_le_iSup_basicOpen_iff]
    intro x hxU
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU hxU)
    obtain ⟨f, hf, hxf⟩ := U.2.exists_basicOpen_le (⟨x, hx⟩ : O i) hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨f, i, hf⟩, hxf⟩
  refine Ideal.fg_of_localizationSpan _ hspan fun g ↦ ?_
  obtain ⟨i, hg⟩ := g.2
  have hfg : (I.ideal (X.affineBasicOpen g.1)).FG :=
    h i (X.affineBasicOpen g.1) ((X.affineBasicOpen_coe g.1).trans_le hg)
  have := U.2.isLocalization_basicOpen g.1
  refine Ideal.FG.map_localizationAway (S := Γ(X, X.basicOpen g.1)) ?_
  rwa [algebraMap_basicOpen_eq, I.map_ideal_basicOpen U g.1]

/-- **Finite-typeness is stable under pullback**: the inverse image of a finite-type ideal
sheaf along an arbitrary morphism of schemes is of finite type. Over an affine open `V` of
the source lying over an affine open `U` of the target, the inverse image ideal is the
extension of `I.ideal U` along `f.appLE U V`, and the opens `f ⁻¹ᵁ U` cover the source. -/
theorem ofFiniteType.comap {Z : Scheme.{u}} {I : X.IdealSheafData} (hI : I.ofFiniteType)
    (f : Z ⟶ X) : (I.comap f).ofFiniteType := by
  have hOn : ∀ U : X.affineOpens, (I.comap f).ofFiniteTypeOn (f ⁻¹ᵁ U.1) := by
    intro U V hV
    rw [ideal_comap_appLE I f U V hV]
    exact (hI U le_top).map _
  have htop : ⨆ U : X.affineOpens, f ⁻¹ᵁ (U : X.Opens) = ⊤ :=
    f.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)
  simpa only [ofFiniteType, htop] using ofFiniteTypeOn.iSup hOn

end FiniteType

/-- The union of a quasi-compact open with the supremum of a finite family of affine opens
is quasi-compact. -/
theorem isCompact_sup_finsetSup {O : X.Opens} (hO : IsCompact (O : Set X))
    (t : Finset X.affineOpens) :
    IsCompact (((O ⊔ t.sup fun V ↦ V.1 : X.Opens) : X.Opens) : Set X) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hO
  | insert V t hV IH =>
    have hsup : O ⊔ (insert V t).sup (fun V ↦ V.1) = (O ⊔ t.sup fun V ↦ V.1) ⊔ V.1 := by
      rw [Finset.sup_insert, sup_comm V.1 (t.sup fun V ↦ V.1), ← sup_assoc]
    rw [hsup, TopologicalSpace.Opens.coe_sup]
    exact IH.union V.2.isCompact

section Gluing

variable [QuasiSeparatedSpace X]

/-- The binary gluing step of the finite-type extension theorem (Stacks Project
Tag 01PF): if `I₀ ≤ H₀` is of finite type on a quasi-compact open `O`, there is an
`I ≤ H₀` of finite type on `O ⊔ V`, for `V` affine, with the same restriction to `O`. -/
theorem exists_le_ofFiniteTypeOn_sup {H₀ I₀ : X.IdealSheafData} {O : X.Opens}
    (hO : IsCompact (O : Set X)) (V : X.affineOpens) (hle : I₀ ≤ H₀)
    (hft : I₀.ofFiniteTypeOn O) :
    ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.ofFiniteTypeOn (O ⊔ V.1) ∧
      I.comap O.ι = I₀.comap O.ι := by
  classical
  have : CompactSpace O.toScheme := isCompact_iff_compactSpace.mp hO
  have : CompactSpace V.1.toScheme := isCompact_iff_compactSpace.mp V.2.isCompact
  have : IsAffine V.1.toScheme := V.2
  -- a finite basic-open cover of the overlap `O ⊓ V`
  have hOV : IsCompact ((O ⊓ V.1 : X.Opens) : Set X) := by
    rw [TopologicalSpace.Opens.coe_inf]
    exact QuasiSeparatedSpace.inter_isCompact _ _ O.isOpen hO V.1.isOpen V.2.isCompact
  obtain ⟨s0, hs0⟩ := hOV.elim_finite_subcover
    (fun f : {f : Γ(X, V.1) // X.basicOpen f ≤ O ⊓ V.1} ↦ (X.basicOpen f.1 : Set X))
    (fun f ↦ (X.basicOpen f.1).isOpen)
    (by
      intro x hx
      obtain ⟨f, hf, hxf⟩ := V.2.exists_basicOpen_le (⟨x, hx⟩ : (O ⊓ V.1 : X.Opens))
        (TopologicalSpace.Opens.mem_inf.mp hx).2
      exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hxf⟩)
  set s : Finset Γ(X, V.1) := s0.image (·.1)
  have hsub : ∀ f ∈ s, X.basicOpen f ≤ O ⊓ V.1 := by
    intro f hf
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hf
    exact g.2
  -- clearing denominators: a finitely generated `N' ≤ I₀(V)` with the same restriction to
  -- every basic open of the cover
  have hlocfg : ∀ f ∈ s,
      ((I₀.ideal V).map (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom).FG := by
    intro f hf
    rw [I₀.map_ideal_basicOpen V f]
    exact hft (X.affineBasicOpen f)
      ((X.affineBasicOpen_coe f).trans_le ((hsub f hf).trans inf_le_left))
  obtain ⟨N', hN'le, hN'fg, hN'loc⟩ :=
    Ideal.exists_fg_le_map_eq (I₀.ideal V) s (fun f ↦ Γ(X, X.basicOpen f))
      (fun f ↦ (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom) hlocfg
  -- the finite-type ideal sheaf on `V` generated by `N'`
  have htop : (⊤ : V.1.toScheme.Opens) ≤ V.1.ι ⁻¹ᵁ V.1 := V.1.ι_preimage_self.ge
  have hK'ideal : ∀ U'' : V.1.toScheme.affineOpens,
      (ofIdealTop (N'.map (V.1.ι.appLE V.1 ⊤ htop).hom)).ideal U'' =
        N'.map (V.1.ι.appLE V.1 U''.1 (le_top.trans htop)).hom := by
    intro U''
    rw [ofIdealTop_ideal, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.Hom.appLE_map]
  set K' : V.1.toScheme.IdealSheafData :=
    ofIdealTop (N'.map (V.1.ι.appLE V.1 ⊤ htop).hom)
  have hIdealV : ∀ (L : X.IdealSheafData) (U'' : V.1.toScheme.affineOpens),
      (L.comap V.1.ι).ideal U'' =
        (L.ideal V).map (V.1.ι.appLE V.1 U''.1 (le_top.trans htop)).hom :=
    fun L U'' ↦ ideal_comap_eq_map_appLE V.1.ι L V U'' (le_top.trans htop)
  have hK'le : K' ≤ I₀.comap V.1.ι := by
    refine le_of_isAffine ?_
    rw [hK'ideal ⟨⊤, isAffineOpen_top _⟩, hIdealV I₀ ⟨⊤, isAffineOpen_top _⟩]
    exact Ideal.map_mono hN'le
  -- the comparison on the overlap: `I₀` and `K'` restrict to the same ideal sheaf
  have hpre : IsAffineOpen (V.1.ι ⁻¹ᵁ V.1) :=
    V.2.preimage_of_isOpenImmersion V.1.ι (by rw [Scheme.Opens.opensRange_ι])
  -- the restriction to a basic open of `V` factors through the restriction to the
  -- corresponding basic open of `X`
  have hcomp : ∀ f : Γ(X, V.1),
      (V.1.ι.appLE V.1 (V.1.toScheme.basicOpen (V.1.ι.app V.1 f))
          (le_top.trans htop)).hom =
        (V.1.ι.appLE (X.basicOpen f) (V.1.toScheme.basicOpen (V.1.ι.app V.1 f))
            (Scheme.preimage_basicOpen V.1.ι f).ge).hom.comp
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom := by
    intro f
    rw [← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  have hoverlap : (I₀.comap V.1.ι).comap (V.1.ι ⁻¹ᵁ O).ι ≤ K'.comap (V.1.ι ⁻¹ᵁ O).ι := by
    refine comap_le_comap_of_ideal_le _
      (fun f : s ↦ ⟨V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1),
        hpre.basicOpen (V.1.ι.app V.1 f.1)⟩) (fun f ↦ ?_) ?_ fun f ↦ ?_
    · have hf : V.1.toScheme.basicOpen (V.1.ι.app V.1 f.1) ≤ V.1.ι ⁻¹ᵁ O := by
        rw [← Scheme.preimage_basicOpen]
        intro x hx
        exact ((hsub f.1 f.2).trans inf_le_left) hx
      rw [Scheme.Opens.opensRange_ι]
      exact hf
    · rw [Scheme.Opens.opensRange_ι]
      intro x hx
      have hxV : V.1.ι x ∈ (V.1 : Set X) := by
        rw [← Scheme.Opens.range_ι (U := V.1)]
        exact Set.mem_range_self x
      obtain ⟨g, hg0, hxg⟩ := Set.mem_iUnion₂.mp (hs0 ⟨hx, hxV⟩)
      refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨g.1, Finset.mem_image_of_mem _ hg0⟩, ?_⟩
      have hmem : x ∈ V.1.ι ⁻¹ᵁ X.basicOpen g.1 := hxg
      rw [Scheme.preimage_basicOpen] at hmem
      exact hmem
    · rw [hIdealV I₀, hK'ideal]
      refine le_of_eq ?_
      rw [hcomp f.1, ← Ideal.map_map, ← Ideal.map_map, hN'loc f.1 f.2]
  -- the two maximal extensions and the candidate ideal sheaf
  set F₁ : X.IdealSheafData := (I₀.comap O.ι).map O.ι
  set F₂ : X.IdealSheafData := K'.map V.1.ι
  have hAleF₂ : I₀.comap O.ι ≤ F₂.comap O.ι := by
    have hcomp : (I₀.comap O.ι).comap (V.1.ι ∣_ O) =
        (I₀.comap V.1.ι).comap (V.1.ι ⁻¹ᵁ O).ι := by
      rw [← comap_comp, ← comap_comp, morphismRestrict_ι]
    rw [map_comap_opens V.1.ι K' O, le_map_iff_comap_le, hcomp]
    exact hoverlap
  have hcomapO : (F₁ ⊓ F₂ ⊓ H₀).comap O.ι = I₀.comap O.ι := by
    rw [comap_inf_of_isOpenImmersion, comap_inf_of_isOpenImmersion, comap_map,
      inf_eq_left.mpr hAleF₂, inf_eq_left.mpr (comap_mono O.ι hle)]
  have hcomapV : (F₁ ⊓ F₂ ⊓ H₀).comap V.1.ι = K' := by
    rw [comap_inf_of_isOpenImmersion, comap_inf_of_isOpenImmersion, comap_map]
    have h₁ : K' ≤ F₁.comap V.1.ι :=
      hK'le.trans (comap_mono V.1.ι (le_map_comap I₀ O.ι))
    have h₂ : K' ≤ H₀.comap V.1.ι := hK'le.trans (comap_mono V.1.ι hle)
    rw [inf_eq_right.mpr h₁, inf_eq_left.mpr h₂]
  refine ⟨F₁ ⊓ F₂ ⊓ H₀, inf_le_right, ofFiniteTypeOn.sup ?_ ?_, hcomapO⟩
  · rw [ofFiniteTypeOn_iff_comap, hcomapO, ← ofFiniteTypeOn_iff_comap]
    exact hft
  · rw [ofFiniteTypeOn_iff_comap, hcomapV]
    intro U'' _
    rw [hK'ideal U'']
    exact Ideal.FG.map hN'fg _

/-- **Existence of a finite-type ideal sheaf with prescribed restriction** (Stacks
Project Tag 01PF, relative order-theoretic form; blueprint:
`lemma:nagata-extend-finite-type-ideal`). -/
theorem exists_finiteType_le_comap_eq_of_le [CompactSpace X] {H₀ I₀ : X.IdealSheafData}
    (hle : I₀ ≤ H₀) (W : X.Opens) (hW : IsCompact (W : Set X)) (hJ : I₀.ofFiniteTypeOn W) :
    ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.ofFiniteType ∧ I.comap W.ι = I₀.comap W.ι := by
  classical
  -- enlarge the open of finite-typeness one affine open at a time
  have key : ∀ t : Finset X.affineOpens,
      ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.ofFiniteTypeOn (W ⊔ t.sup fun V ↦ V.1) ∧
        I.comap W.ι = I₀.comap W.ι := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty, sup_bot_eq]
      exact ⟨I₀, hle, hJ, rfl⟩
    | insert V t hV IH =>
      obtain ⟨I₁, hle₁, hft₁, hcomap⟩ := IH
      have hsup : W ⊔ (insert V t).sup (fun V ↦ V.1) = (W ⊔ t.sup fun V ↦ V.1) ⊔ V.1 := by
        rw [Finset.sup_insert, sup_comm V.1 (t.sup fun V ↦ V.1), ← sup_assoc]
      obtain ⟨I, hIle, hIft, hIcomap⟩ :=
        exists_le_ofFiniteTypeOn_sup (isCompact_sup_finsetSup hW t) V hle₁ hft₁
      refine ⟨I, hIle, by rwa [hsup], ?_⟩
      have hWle : W ≤ W ⊔ t.sup fun V ↦ V.1 := le_sup_left
      have h₁ : I.comap W.ι = (I.comap (W ⊔ t.sup fun V ↦ V.1).ι).comap (X.homOfLE hWle) := by
        rw [← comap_comp, Scheme.homOfLE_ι]
      have h₂ : I₁.comap W.ι =
          (I₁.comap (W ⊔ t.sup fun V ↦ V.1).ι).comap (X.homOfLE hWle) := by
        rw [← comap_comp, Scheme.homOfLE_ι]
      rw [h₁, hIcomap, ← h₂, hcomap]
  have hcov : (Set.univ : Set X) ⊆ ⋃ V : X.affineOpens, (V.1 : Set X) := by
    intro x _
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx
    obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨V, hV⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) hcov
  obtain ⟨I, hle, hft, hcomap⟩ := key t
  refine ⟨I, hle, ?_, hcomap⟩
  refine fun U _ ↦ hft U fun x _ ↦ ?_
  obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact (le_sup_right : (t.sup fun V ↦ V.1) ≤ W ⊔ t.sup fun V ↦ V.1)
    ((Finset.le_sup (f := fun V ↦ V.1) hVt) hxV)

/-- Existence of a finite-type ideal sheaf with prescribed restriction (Stacks Project
Tag 01PF, order-theoretic form): on a quasi-compact quasi-separated scheme, every ideal
sheaf `H₀` whose restriction to a quasi-compact open `W` is of finite type contains a
finite-type ideal sheaf with the same restriction to `W`.
(Blueprint: `lemma:nagata-extend-finite-type-ideal`.) -/
theorem exists_finiteType_le_comap_eq [CompactSpace X] (H₀ : X.IdealSheafData) (W : X.Opens)
    (hW : IsCompact (W : Set X)) (hJ : H₀.ofFiniteTypeOn W) :
    ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.ofFiniteType ∧ I.comap W.ι = H₀.comap W.ι :=
  exists_finiteType_le_comap_eq_of_le le_rfl W hW hJ

/-- Extension of a finite-type ideal sheaf from a quasi-compact open (Stacks Project
Tag 01PF): on a quasi-compact quasi-separated scheme, every finite-type ideal sheaf on a
quasi-compact open extends to a finite-type ideal sheaf on the whole scheme.
(Blueprint: `lemma:nagata-extend-finite-type-ideal`.) -/
theorem exists_finiteType_comap_eq [CompactSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) (J : W.toScheme.IdealSheafData) (hJ : J.ofFiniteType) :
    ∃ I : X.IdealSheafData, I.ofFiniteType ∧ I.comap W.ι = J := by
  have : CompactSpace W.toScheme := isCompact_iff_compactSpace.mp hW
  have hJ' : (J.map W.ι).ofFiniteTypeOn W := by
    rw [ofFiniteTypeOn_iff_comap, comap_map]
    exact hJ
  obtain ⟨I, -, hft, hcomap⟩ := exists_finiteType_le_comap_eq (J.map W.ι) W hW hJ'
  exact ⟨I, hft, by rw [hcomap, comap_map]⟩

/-- **Extension of a finite-type centre along an affine morphism.**

The pullback along `j` is computed on the affine opens `j ⁻¹ᵁ W` for `W` affine in `X`, and
there it is generated by the image of `H₀.ideal W`. Finitely many sections of `H₀` over `W`
already generate it, and the finite-type ideal sheaf they span on `W` extends to a
finite-type ideal sheaf `G` inside `H₀` on all of `X` by Tag 01PF
(`exists_finiteType_le_comap_eq`). Summing the `G` over a finite affine cover of `X` gives
the desired ideal sheaf. -/
theorem exists_finiteType_le_comap_eq_of_isAffineHom [CompactSpace X] {Z : Scheme.{u}}
    (H₀ : X.IdealSheafData) (j : Z ⟶ X) [IsAffineHom j] (hj : (H₀.comap j).ofFiniteType) :
    ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.ofFiniteType ∧ I.comap j = H₀.comap j := by
  classical
  -- over a single affine open `W` of `X`, a finite-type `G ≤ H₀` already generating the
  -- pullback of `H₀` to `Z` there
  have hpiece : ∀ W : X.affineOpens, ∃ G : X.IdealSheafData, G ≤ H₀ ∧ G.ofFiniteType ∧
      (H₀.ideal W).map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom ≤
        (G.ideal W).map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom := by
    intro W
    have : IsAffine W.1.toScheme := W.2
    have : CompactSpace W.1.toScheme := isCompact_iff_compactSpace.mp W.2.isCompact
    -- clearing denominators: finitely many sections of `H₀` over `W` generate the pullback
    have hfg : ((H₀.ideal W).map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom).FG := by
      rw [← ideal_comap_appLE H₀ j W ⟨j ⁻¹ᵁ W.1, W.2.preimage j⟩ le_rfl]
      exact hj _ le_top
    obtain ⟨T, hTsub, hTspan⟩ := Ideal.exists_finset_subset_span_image_eq _ _ hfg
    set N : Ideal Γ(X, W.1) := Ideal.span (T : Set Γ(X, W.1)) with hNdef
    have hNfg : N.FG := ⟨T, rfl⟩
    have hNle : N ≤ H₀.ideal W := Ideal.span_le.mpr hTsub
    have hNmap : N.map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom =
        (H₀.ideal W).map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom := by
      rw [hNdef, Ideal.map_span, hTspan]
    -- the ideal sheaf on `W` generated by `N`, and its maximal extension to `X`
    set K : W.1.toScheme.IdealSheafData := ofIdealTop (N.map W.1.topIso.inv.hom) with hKdef
    have hKideal : K.ideal ⟨⊤, isAffineOpen_top _⟩ = N.map W.1.topIso.inv.hom := by
      simp only [hKdef, ofIdealTop_ideal, homOfLE_refl, op_id, CategoryTheory.Functor.map_id,
        CommRingCat.hom_id, Ideal.map_id]
    have hH₀ideal : (H₀.comap W.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
        (H₀.ideal W).map W.1.topIso.inv.hom := by
      rw [← map_topIso_ideal_top_comap_ι H₀ W, Ideal.map_map, ← CommRingCat.hom_comp,
        Iso.hom_inv_id, CommRingCat.hom_id, Ideal.map_id]
    have hKle : K ≤ H₀.comap W.1.ι :=
      le_of_isAffine (by rw [hKideal, hH₀ideal]; exact Ideal.map_mono hNle)
    have hcomapK : (K.map W.1.ι ⊓ H₀).comap W.1.ι = K := by
      rw [comap_inf_of_isOpenImmersion, comap_map, inf_eq_left.mpr hKle]
    have hftK : (K.map W.1.ι ⊓ H₀).ofFiniteTypeOn W.1 := by
      rw [ofFiniteTypeOn_iff_comap, hcomapK]
      intro U _
      rw [hKdef, ofIdealTop_ideal]
      exact Ideal.FG.map (Ideal.FG.map hNfg _) _
    obtain ⟨G, hGle, hGft, hGcomap⟩ :=
      exists_finiteType_le_comap_eq (K.map W.1.ι ⊓ H₀) W.1 W.2.isCompact hftK
    have hGideal : G.ideal W = N := by
      rw [← map_topIso_ideal_top_comap_ι G W, hGcomap, hcomapK, hKideal, Ideal.map_map,
        ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]
    exact ⟨G, hGle.trans inf_le_right, hGft, le_of_eq (by rw [hGideal, hNmap])⟩
  choose G hGle hGft hGideal using hpiece
  -- sum the pieces over a finite family of affine opens
  have key : ∀ t : Finset X.affineOpens, ∃ I : X.IdealSheafData, I ≤ H₀ ∧ I.ofFiniteType ∧
      ∀ W ∈ t, (H₀.ideal W).map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom ≤
        (I.ideal W).map (j.appLE W.1 (j ⁻¹ᵁ W.1) le_rfl).hom := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨⊥, bot_le, ofFiniteType_bot, by simp⟩
    | insert W t hW IH =>
      obtain ⟨I, hIle, hIft, hI⟩ := IH
      refine ⟨I ⊔ G W, sup_le hIle (hGle W), ?_, fun W' hW' ↦ ?_⟩
      · exact hIft.sup (hGft W)
      · rcases Finset.mem_insert.mp hW' with rfl | hW'
        · refine (hGideal W').trans (Ideal.map_mono ?_)
          simp only [ideal_sup, Pi.sup_apply]
          exact le_sup_right
        · refine (hI W' hW').trans (Ideal.map_mono ?_)
          simp only [ideal_sup, Pi.sup_apply]
          exact le_sup_left
  have hcov : (Set.univ : Set X) ⊆ ⋃ W : X.affineOpens, (W.1 : Set X) := by
    intro x _
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← iSup_affineOpens_eq_top X] at hx
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨W, hW⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun W : X.affineOpens ↦ (W.1 : Set X)) (fun W ↦ W.1.isOpen) hcov
  obtain ⟨I, hIle, hIft, hI⟩ := key t
  refine ⟨I, hIle, hIft, le_antisymm (comap_mono j hIle) ?_⟩
  refine le_of_iSup_eq_top (fun W : t ↦ ⟨j ⁻¹ᵁ (W : X.affineOpens).1,
    (W : X.affineOpens).2.preimage j⟩) ?_ fun W ↦ ?_
  · rw [eq_top_iff]
    intro z _
    obtain ⟨W, hWt, hW⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (j z)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hWt⟩, hW⟩
  · rw [ideal_comap_appLE H₀ j (W : X.affineOpens) _ le_rfl,
      ideal_comap_appLE I j (W : X.affineOpens) _ le_rfl]
    exact hI _ W.2

/-- **Transport of a blow-up centre along an affine morphism** (Stacks Project Tag 080E,
ideal-sheaf input; blueprint: `lemma:nagata-finite-type-ideal-extension-closed`).

In the application `j` is a closed immersion: applied to the preimage of a finite-type
ideal sheaf `I` on `Z` under `𝒪_X ↠ 𝒪_Z`, this produces the finite-type ideal sheaf `J`
on `X` with `J · 𝒪_Z = I` and `V(J) ∩ V = ∅`. -/
theorem exists_finiteType_le_comap_eq_disjoint_support [CompactSpace X] {Z : Scheme.{u}}
    (H₀ : X.IdealSheafData) (j : Z ⟶ X) [IsAffineHom j] (V : X.Opens)
    (hV : IsCompact (V : Set X)) (hj : (H₀.comap j).ofFiniteType)
    (hVH₀ : Disjoint (V : Set X) (H₀.support : Set X)) :
    ∃ J : X.IdealSheafData, J ≤ H₀ ∧ J.ofFiniteType ∧ J.comap j = H₀.comap j ∧
      Disjoint (V : Set X) (J.support : Set X) := by
  have hcomapV : H₀.comap V.ι = ⊤ := (disjoint_support_iff_comap_ι_eq_top H₀ V).mp hVH₀
  -- the piece taking care of the support condition
  have hftV : H₀.ofFiniteTypeOn V := by
    rw [ofFiniteTypeOn_iff_comap, hcomapV]
    exact ofFiniteType_top
  obtain ⟨J₁, hJ₁le, hJ₁ft, hJ₁comap⟩ := exists_finiteType_le_comap_eq H₀ V hV hftV
  have hJ₁disj : Disjoint (V : Set X) (J₁.support : Set X) :=
    (disjoint_support_iff_comap_ι_eq_top J₁ V).mpr (by rw [hJ₁comap, hcomapV])
  -- the piece taking care of the pullback along `j`
  obtain ⟨J₂, hJ₂le, hJ₂ft, hJ₂comap⟩ := exists_finiteType_le_comap_eq_of_isAffineHom H₀ j hj
  refine ⟨J₁ ⊔ J₂, sup_le hJ₁le hJ₂le, hJ₁ft.sup hJ₂ft, ?_, ?_⟩
  · refine le_antisymm (comap_mono j (sup_le hJ₁le hJ₂le)) ?_
    rw [← hJ₂comap]
    exact comap_mono j le_sup_right
  · exact hJ₁disj.mono_right (by rw [coe_support_sup]; exact Set.inter_subset_left)


/-- **Gluing finite type ideal sheaves along a quasi-compact open cover**: let `U` and `W` be
quasi-compact opens of a quasi-separated scheme `X`, and let `I_U ⊆ 𝒪_U`, `I_W ⊆ 𝒪_W` be
quasi-coherent ideal sheaves of finite type which agree on the overlap `U ∩ W = U ×_X W`. Then
there is a quasi-coherent ideal sheaf on `X`, of finite type on `U ∪ W`, restricting to `I_U` on
`U` and to `I_W` on `W`. It is the intersection of the maximal quasi-coherent extensions of
`I_U` and `I_W`, whose restrictions are computed by flat base change of scheme-theoretic images.
(blueprint: `lemma-products-composites-u-admissible-blow--3`) -/
theorem exists_ofFiniteTypeOn_sup_comap_eq {U W : X.Opens} (hU : IsCompact (U : Set X))
    (hW : IsCompact (W : Set X)) {IU : U.toScheme.IdealSheafData}
    {IW : W.toScheme.IdealSheafData} (hIU : IU.ofFiniteType) (hIW : IW.ofFiniteType)
    (h : IU.comap (pullback.fst U.ι W.ι) = IW.comap (pullback.snd U.ι W.ι)) :
    ∃ I : X.IdealSheafData, I.ofFiniteTypeOn (U ⊔ W) ∧ I.comap U.ι = IU ∧ I.comap W.ι = IW := by
  have : QuasiCompact U.ι := Scheme.Opens.quasiCompact_ι U hU
  have : QuasiCompact W.ι := Scheme.Opens.quasiCompact_ι W hW
  have hU' : (IU.map U.ι ⊓ IW.map W.ι).comap U.ι = IU := by
    rw [comap_inf_of_isOpenImmersion, comap_map, inf_eq_left,
      map_comap_of_isPullback IW (IsPullback.of_hasPullback U.ι W.ι).flip,
      le_map_iff_comap_le]
    exact h.le
  have hW' : (IU.map U.ι ⊓ IW.map W.ι).comap W.ι = IW := by
    rw [comap_inf_of_isOpenImmersion, comap_map, inf_eq_right,
      map_comap_of_isPullback IU (IsPullback.of_hasPullback U.ι W.ι), le_map_iff_comap_le]
    exact h.ge
  refine ⟨IU.map U.ι ⊓ IW.map W.ι, ofFiniteTypeOn.sup ?_ ?_, hU', hW'⟩
  · rw [ofFiniteTypeOn_iff_comap, hU']
    exact hIU
  · rw [ofFiniteTypeOn_iff_comap, hW']
    exact hIW

end Gluing

end AlgebraicGeometry.Scheme.IdealSheafData
