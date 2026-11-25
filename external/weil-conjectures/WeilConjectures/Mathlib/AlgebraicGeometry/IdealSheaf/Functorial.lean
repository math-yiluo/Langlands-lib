/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer

/-!
# Complements on pullback and pushforward of ideal sheaves

Three groups of complements to `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`.

The first computes the pullback of an ideal sheaf along the inclusion of its own closed
subscheme, which vanishes; as a consequence a morphism is scheme-theoretically dense in
its own scheme-theoretic image.

The second describes the pullback of an ideal sheaf along an open immersion on affine
opens, where it is the transport of the ideal of sections along the isomorphism of section
rings, and gives the resulting comparison criteria.

The third is flat base change: for a quasi-compact `g` and a cartesian square with flat
right-hand edge, pushforward along `g` commutes with pullback along the base change. This
is `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` in `map`/`comap` language.

## Main results

- `AlgebraicGeometry.Scheme.IdealSheafData.coe_support_comap`: the set-level form of
  `support_comap`, `(I.comap f).support = f ⁻¹' I.support` as sets;
- `AlgebraicGeometry.Scheme.Hom.comap_ker_self`: `j.ker.comap j = ⊥` for every `j`, and its
  converse `AlgebraicGeometry.Scheme.IdealSheafData.le_ker_of_comap_eq_bot`: an ideal sheaf
  pulling back to zero is contained in the kernel;
- `AlgebraicGeometry.Scheme.IdealSheafData.fg_ideal_comap_iff`: finite generation of the
  ideal of sections transfers across an open immersion;
- `AlgebraicGeometry.Scheme.IdealSheafData.comap_mul`: pullback of ideal sheaves is
  multiplicative;
- `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback`: flat base change, with
  `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_opens` (restriction to an open) and
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_map` (a quasi-compact flat monomorphism)
  as special cases;
- `AlgebraicGeometry.Scheme.IdealSheafData.comap_iInf_of_flat`: flat pullback commutes with
  finite intersections, and `AlgebraicGeometry.Scheme.IdealSheafData.comap_iInf_map_of_flat`:
  descent of ideal sheaves along a finite family of flat quasi-compact morphisms;
- `AlgebraicGeometry.Scheme.IdealSheafData.exists_comap_ι_eq`: ideal sheaves on the affine opens
  compatible with restriction to basic opens glue;
- `AlgebraicGeometry.Scheme.IdealSheafData.eq_of_forall_le_ker_iff`: on an affine scheme, an
  ideal sheaf is determined by the morphisms from affine schemes whose kernel contains it;
- `AlgebraicGeometry.Scheme.IdealSheafData.le_of_forall_comap_le`: an inclusion of ideal sheaves
  may be checked on an open cover.

The last section computes sections of the inverse image ideal sheaf:
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_map_appLE_le_ideal_comap` and
`AlgebraicGeometry.Scheme.Hom.mem_ker_comp`.

For closed subschemes `V(s)` cut out by global sections:
`AlgebraicGeometry.Scheme.isPullback_zeroLocusSubschemeι` (base change of `V(s)`),
`AlgebraicGeometry.Scheme.span_eq_of_isPullback_zeroLocusSubschemeι` (the ideal is determined
by a flat pullback of `V(s)` on an affine scheme) and
`AlgebraicGeometry.Scheme.mem_basicOpen_of_isUnit_mk` (a unit modulo `(s)` is invertible near
`V(s)`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

section Support

/-- The underlying set of the support of the pullback of an ideal sheaf is the preimage
of the underlying set of its support: the set-level form of
`AlgebraicGeometry.Scheme.IdealSheafData.support_comap`. -/
lemma coe_support_comap (I : Y.IdealSheafData) (f : X ⟶ Y) :
    ((I.comap f).support : Set X) = f ⁻¹' (I.support : Set Y) := by
  rw [support_comap, TopologicalSpace.Closeds.coe_preimage]

/-- An ideal sheaf has support disjoint from an open exactly when it restricts to the unit
ideal sheaf on that open. -/
lemma disjoint_support_iff_comap_ι_eq_top (I : X.IdealSheafData) (V : X.Opens) :
    Disjoint (V : Set X) (I.support : Set X) ↔ I.comap V.ι = ⊤ := by
  rw [← support_eq_bot_iff, TopologicalSpace.Closeds.ext_iff, coe_support_comap]
  simp [Set.preimage_eq_empty_iff, Scheme.Opens.range_ι, disjoint_comm]

end Support

section Subscheme

/-- An ideal sheaf pulls back to zero along the inclusion of the closed subscheme it cuts
out: the inclusion is a monomorphism, so it is its own kernel pair. -/
lemma comap_subschemeι (I : X.IdealSheafData) : I.comap I.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso (pullback.fst I.subschemeι I.subschemeι)

/-- The ideal `I` is contained in the pushforward of the zero ideal along `V(I) ⟶ X`. -/
lemma le_map_bot_subschemeι (I : X.IdealSheafData) :
    I ≤ (⊥ : I.subscheme.IdealSheafData).map I.subschemeι := by
  rw [map_bot, ker_subschemeι]

/-- Every morphism is scheme-theoretically dense in its scheme-theoretic image: the ideal
sheaf cutting the image out pulls back to zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.comap_ker_self (j : X ⟶ Y) : j.ker.comap j = ⊥ := by
  have hfac : j.ker.comap j = (j.ker.comap j.imageι).comap j.toImage := by
    rw [← comap_comp, j.toImage_imageι]
  rw [hfac, comap_subschemeι, comap_bot]

/-- **The kernel is the largest ideal sheaf pulling back to zero**: an ideal sheaf whose
inverse image along a morphism vanishes is contained in the kernel of that morphism. This
is the Galois connection `le_map_iff_comap_le` at the zero ideal sheaf, whose pushforward
is the kernel. -/
theorem le_ker_of_comap_eq_bot {J : Y.IdealSheafData} (g : X ⟶ Y) (h : J.comap g = ⊥) :
    J ≤ g.ker := by
  rw [← map_bot g]
  exact le_map_iff_comap_le.mpr h.le

end Subscheme

section OpenImmersion

variable {Z T : Scheme.{u}} (j : Z ⟶ T) [IsOpenImmersion j] (I : T.IdealSheafData)

/-- Pullback of ideal sheaves along an open immersion commutes with intersections. -/
lemma comap_inf_of_isOpenImmersion (K : T.IdealSheafData) :
    (I ⊓ K).comap j = I.comap j ⊓ K.comap j := by
  ext U : 2
  simp only [ideal_inf, Pi.inf_apply, ideal_comap_of_isOpenImmersion, Ideal.comap_inf]

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion is the
transport of the ideal of sections on the image along the isomorphism of section rings. -/
lemma ideal_comap_eq_map_appIso (U : Z.affineOpens) :
    (I.comap j).ideal U =
      (I.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩).map (j.appIso U.1).hom.hom := by
  rw [ideal_comap_of_isOpenImmersion, CommRingCat.comap_inv_eq_map]

/-- Finite generation of the ideal of sections is detected on either side of an open
immersion. -/
lemma fg_ideal_comap_iff (U : Z.affineOpens) :
    ((I.comap j).ideal U).FG ↔
      (I.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩).FG := by
  rw [ideal_comap_eq_map_appIso]
  refine ⟨fun h ↦ ?_, fun h ↦ h.map _⟩
  have h' := h.map (j.appIso U.1).inv.hom
  rwa [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id] at h'

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion,
computed on an affine open of the source lying over an affine open `V` of the target: it
is the extension of the ideal of sections on `V` along the restriction map `appLE`. -/
lemma ideal_comap_eq_map_appLE (V : T.affineOpens) (U : Z.affineOpens)
    (h : U.1 ≤ j ⁻¹ᵁ V.1) :
    (I.comap j).ideal U = (I.ideal V).map (j.appLE V.1 U.1 h).hom := by
  have himg : (⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ : T.affineOpens) ≤ V :=
    Subtype.coe_le_coe.mp <| (j.image_mono h).trans <| by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_le_right
  rw [ideal_comap_eq_map_appIso, ← map_ideal I himg, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- To compare two pullbacks of ideal sheaves along an open immersion, it suffices to
compare the ideals of sections on a family of affine opens contained in the range whose
preimages cover the source. -/
lemma comap_le_comap_of_ideal_le {I K : T.IdealSheafData} {ι : Type*} (U : ι → T.affineOpens)
    (hran : ∀ i, (U i).1 ≤ j.opensRange) (hcov : j.opensRange ≤ ⨆ i, (U i).1)
    (H : ∀ i, I.ideal (U i) ≤ K.ideal (U i)) :
    I.comap j ≤ K.comap j := by
  refine le_of_iSup_eq_top
    (fun i ↦ ⟨j ⁻¹ᵁ (U i).1, (U i).2.preimage_of_isOpenImmersion j (hran i)⟩) ?_ fun i ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov ⟨x, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion]
    refine Ideal.comap_mono ?_
    have himg : j ''ᵁ (j ⁻¹ᵁ (U i).1) = (U i).1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hran i)]
    have hcongr : (⟨j ''ᵁ (j ⁻¹ᵁ (U i).1),
        ((U i).2.preimage_of_isOpenImmersion j (hran i)).image_of_isOpenImmersion j⟩ :
        T.affineOpens) = U i := Subtype.ext himg
    have hle := H i
    rw [← hcongr] at hle
    exact hle

end OpenImmersion

section FlatBaseChange

/-- Flat base change for pushforward of ideal sheaves: for a cartesian square whose
right-hand edge `q` is flat and whose left-hand edge `g` is quasi-compact, pushing forward
along `g` and then restricting along `q` is restricting along `p` and then pushing forward
along `g'`. This is `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` in `map`/`comap`
language (Stacks Project Tag 081I). -/
theorem map_comap_of_isPullback {X' Y' : Scheme.{u}} (B : Y.IdealSheafData) {g : Y ⟶ X}
    [QuasiCompact g] {q : X' ⟶ X} [Flat q] {g' : Y' ⟶ X'} {p : Y' ⟶ Y}
    (h : IsPullback p g' g q) : (B.map g).comap q = (B.comap p).map g' := by
  have hker : ∀ {Z W : Scheme.{u}} (C : Z.IdealSheafData) (φ : Z ⟶ W),
      C.map φ = (C.subschemeι ≫ φ).ker := fun C φ ↦ by
    rw [Scheme.Hom.ker_comp, ker_subschemeι]
  -- paste the defining square of `B.comap p` onto the given cartesian square
  have H := ((IsPullback.of_hasPullback p B.subschemeι).paste_horiz h.flip).flip
  have hsub : (B.comap p).subschemeι = (B.comapIso p).hom ≫ pullback.fst p B.subschemeι :=
    (comapIso_hom_fst _ _).symm
  rw [hker B g, hker (B.comap p) g', ← Scheme.Hom.ker_pullback_snd (B.subschemeι ≫ g) q,
    hsub, Category.assoc, Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

/-- Restriction of a pushforward to an open subscheme, the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the open immersion
`O.ι`, which is flat. -/
theorem map_comap_opens (g : Y ⟶ X) [QuasiCompact g] (B : Y.IdealSheafData) (O : X.Opens) :
    (B.map g).comap O.ι = (B.comap (g ⁻¹ᵁ O).ι).map (g ∣_ O) :=
  map_comap_of_isPullback B (isPullback_morphismRestrict g O).flip

/-- The pushforward of an ideal sheaf along a quasi-compact flat monomorphism — for
instance the inclusion of a quasi-compact open — restricts back to the original ideal
sheaf. This is the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the kernel pair of a
monomorphism. -/
theorem comap_map (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Mono f] (J : X.IdealSheafData) :
    (J.map f).comap f = J := by
  rw [map_comap_of_isPullback J (IsKernelPair.id_of_mono f), comap_id, map_id]

end FlatBaseChange

section FlatPullback

/-- Pullback of ideal sheaves along a flat morphism commutes with finite intersections: on affine
opens it is the extension of ideals along a flat ring map (`Ideal.map_iInf_of_flat`). -/
lemma comap_iInf_of_flat (f : X ⟶ Y) [Flat f] {ι : Type*} [Finite ι]
    (I : ι → Y.IdealSheafData) : (⨅ i, I i).comap f = ⨅ i, (I i).comap f := by
  refine ext_of_iSup_eq_top (ι := {p : Y.affineOpens × X.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1})
    (fun p ↦ p.1.2) ?_ fun p ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) hxV (f ⁻¹ᵁ V).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hxW⟩
  · obtain ⟨⟨V, W⟩, h⟩ := p
    have := f.flat_appLE V.2 W.2 h
    algebraize [(f.appLE V.1 W.1 h).hom]
    simp only [ideal_iInf, iInf_apply, ideal_comap_appLE _ f V W h]
    exact Ideal.map_iInf_of_flat (S := Γ(X, W.1)) _

/-- **Descent of ideal sheaves along a finite flat quasi-compact family.** Let `q k : W k ⟶ V`
be finitely many flat quasi-compact morphisms and `I k` ideal sheaves on the `W k` whose
pullbacks to every `W k ×_V W l` agree. Then the pullback of `⨅ k, (I k).map (q k)` along
each `q l` is `I l`.

This is the effectivity step "descending the quotients" of the proof of
`theorem-hilbert-schemes-points-smooth-curve--1`, in the form of an explicit formula: it uses
flat base change (`map_comap_of_isPullback`) and that flat pullback commutes with finite
intersections (`comap_iInf_of_flat`). -/
theorem comap_iInf_map_of_flat {V : Scheme.{u}} {κ : Type*} [Finite κ] {W : κ → Scheme.{u}}
    (q : ∀ k, W k ⟶ V) [∀ k, Flat (q k)] [∀ k, QuasiCompact (q k)]
    (I : ∀ k, (W k).IdealSheafData)
    (hcompat : ∀ k l, (I k).comap (pullback.fst (q k) (q l)) =
      (I l).comap (pullback.snd (q k) (q l))) (l : κ) :
    (⨅ k, (I k).map (q k)).comap (q l) = I l := by
  refine le_antisymm ((comap_mono _ (iInf_le _ l)).trans (comap_map_le _ _)) ?_
  rw [comap_iInf_of_flat]
  refine le_iInf fun k ↦ ?_
  rw [map_comap_of_isPullback (I k) (IsPullback.of_hasPullback (q k) (q l)), hcompat]
  exact le_map_comap _ _

end FlatPullback

section Gluing

/-- Two ideal sheaves on `Z` coincide as soon as their restrictions to every affine open of `Z`
mapping into an affine open of `Y` along `f : Z ⟶ Y` coincide. -/
theorem eq_of_comap_ι_eq {Z : Scheme.{u}} (f : Z ⟶ Y) {A B : Z.IdealSheafData}
    (H : ∀ (U : Y.affineOpens) (W : Z.affineOpens), W.1 ≤ f ⁻¹ᵁ U.1 →
      A.comap W.1.ι = B.comap W.1.ι) : A = B := by
  refine ext_of_iSup_eq_top (ι := {p : Y.affineOpens × Z.affineOpens // p.2.1 ≤ f ⁻¹ᵁ p.1.1})
    (fun p ↦ p.1.2) ?_ fun p ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) hxV (f ⁻¹ᵁ V).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨W, hW⟩), hWV⟩, hxW⟩
  · obtain ⟨⟨U, W⟩, h⟩ := p
    rw [← map_topIso_ideal_top_comap_ι A W, ← map_topIso_ideal_top_comap_ι B W, H U W h]

/-- **Gluing ideal sheaves.** A family of ideal sheaves `K U` on the affine opens `U` of `X`
which is compatible with restriction to basic opens is the family of restrictions of a single
ideal sheaf on `X`. -/
theorem exists_comap_ι_eq (K : ∀ U : X.affineOpens, U.1.toScheme.IdealSheafData)
    (hK : ∀ (U : X.affineOpens) (f : Γ(X, U)),
      (K U).comap (X.homOfLE (X.basicOpen_le f)) = K (X.affineBasicOpen f)) :
    ∃ J : X.IdealSheafData, ∀ U, J.comap U.1.ι = K U := by
  have (U : X.affineOpens) : IsAffine U.1.toScheme := U.2
  have key (U V : X.affineOpens) (h : V.1 ≤ U.1) :
      (((K U).comap (X.homOfLE h)).ideal ⟨⊤, isAffineOpen_top _⟩).map V.1.topIso.hom.hom =
        (((K U).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom).map
          (X.presheaf.map (homOfLE h).op).hom := by
    rw [ideal_comap_appLE _ _ ⟨⊤, isAffineOpen_top _⟩ ⟨⊤, isAffineOpen_top _⟩
      (X.homOfLE h).preimage_top.ge, Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp]
    congr 2
    simp only [Scheme.Opens.topIso_hom]
    rw [Scheme.homOfLE_appLE]
    exact (X.presheaf.map_comp _ _).symm.trans
      ((congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _))
  let J : X.IdealSheafData :=
    { ideal U := ((K U).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom
      map_ideal_basicOpen U f := by
        have := key U (X.affineBasicOpen f) (X.basicOpen_le f)
        have e : (K U).comap (X.homOfLE (show (X.affineBasicOpen f).1 ≤ U.1 from
          X.basicOpen_le f)) = K (X.affineBasicOpen f) := hK U f
        rw [e] at this
        exact this.symm }
  refine ⟨J, fun U ↦ ext_of_isAffine ?_⟩
  have h : ((J.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom =
      ((K U).ideal ⟨⊤, isAffineOpen_top _⟩).map U.1.topIso.hom.hom :=
    map_topIso_ideal_top_comap_ι J U
  have := congrArg (Ideal.map U.1.topIso.inv.hom) h
  rwa [Ideal.map_map, Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id, Ideal.map_id] at this

end Gluing

section Sections

/-- Sections of an ideal sheaf `K` over an affine open `V` restrict into the ideal of the
pullback `K.comap g` over every affine open `U ≤ g ⁻¹ᵁ V`. -/
lemma ideal_map_appLE_le_ideal_comap (K : Y.IdealSheafData) (g : X ⟶ Y) (V : Y.affineOpens)
    (U : X.affineOpens) (h : U.1 ≤ g ⁻¹ᵁ V.1) :
    (K.ideal V).map (g.appLE V.1 U.1 h).hom ≤ (K.comap g).ideal U := by
  have hK : K ≤ ((K.comap g).subschemeι ≫ g).ker := by
    rw [← subschemeMap_subschemeι (K.comap g) K g (K.le_map_comap g)]
    exact le_of_eq_of_le K.ker_subschemeι.symm (Scheme.Hom.le_ker_comp _ K.subschemeι)
  rw [Ideal.map_le_iff_le_comap]
  intro s hs
  have h1 : ((((K.comap g).subschemeι ≫ g).app V.1)).hom s = 0 :=
    RingHom.mem_ker.mp (Scheme.Hom.ideal_ker_le _ V (le_def.mp hK V hs))
  have key := Scheme.Hom.appLE_comp_appLE (K.comap g).subschemeι g V.1 U.1
    ((K.comap g).subschemeι ⁻¹ᵁ U.1) h le_rfl
  rw [Ideal.mem_comap, ← ker_subschemeι_app, RingHom.mem_ker, ← CommRingCat.comp_apply,
    Scheme.Hom.app_eq_appLE, key]
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, h1, map_zero]

/-- Membership in the kernel ideal of a composite `w ≫ g` over an affine open `V` is
detected on the preimage `g ⁻¹ᵁ V`, provided the latter is affine. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.mem_ker_comp {W : Scheme.{u}} (w : W ⟶ X) (g : X ⟶ Y)
    [QuasiCompact w] [QuasiCompact g] (V : Y.affineOpens) (hV : IsAffineOpen (g ⁻¹ᵁ V.1))
    (s : Γ(Y, V.1)) :
    s ∈ (w ≫ g).ker.ideal V ↔ (g.app V.1).hom s ∈ w.ker.ideal ⟨g ⁻¹ᵁ V.1, hV⟩ := by
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, RingHom.mem_ker, RingHom.mem_ker,
    Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  exact Iff.rfl

end Sections

section Mul

/-- **Pullback of ideal sheaves is multiplicative.** On affine opens `V ⊆ f ⁻¹ᵁ U` the pullback
of an ideal sheaf is the extension of its ideal of sections along `Γ(Y, U) ⟶ Γ(X, V)`, and
extension of ideals is multiplicative. -/
theorem comap_mul (f : X ⟶ Y) (I J : Y.IdealSheafData) :
    (I * J).comap f = I.comap f * J.comap f := by
  let ι := Σ' (U : Y.affineOpens) (V : X.affineOpens), V.1 ≤ f ⁻¹ᵁ U.1
  refine ext_of_iSup_eq_top (ι := ι) (fun i ↦ i.2.1) ?_ fun ⟨U, V, e⟩ ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (ou := (f ⁻¹ᵁ U).2) hxU
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, hVU⟩, hxV⟩
  · simp only [ideal_mul, Pi.mul_apply]
    rw [ideal_comap_appLE _ f U V e, ideal_comap_appLE _ f U V e, ideal_comap_appLE _ f U V e,
      ideal_mul, Pi.mul_apply, Ideal.map_mul]

/-- **Pullback of ideal sheaves commutes with powers**, by `comap_mul` and `comap_top`. -/
theorem comap_pow (f : X ⟶ Y) (J : Y.IdealSheafData) (n : ℕ) :
    (J ^ n).comap f = J.comap f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact comap_top f
  | succ n ih => rw [pow_succ, comap_mul, ih, pow_succ]

end Mul

section OpenImmersion

variable {U : Scheme.{u}} (j : U ⟶ Y)

/-- If the closed subscheme of `J` stays closed in `Y` under a monomorphism `j : U ⟶ Y`, then
pulling back the pushforward of `J` along `j` recovers `J`. -/
lemma comap_map_of_isClosedImmersion [Mono j] (J : U.IdealSheafData)
    [IsClosedImmersion (J.subschemeι ≫ j)] : (J.map j).comap j = J := by
  have h : IsPullback (𝟙 _) J.subschemeι (J.subschemeι ≫ j) j :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  rw [map, ← ker_fst_of_isClosedImmersion, ← h.flip.isoPullback_inv_fst,
    Scheme.Hom.ker_comp_of_isIso, ker_subschemeι]

/-- The support of the pushforward of `J` along `j` lies in the range of `j`, provided the
closed subscheme of `J` stays closed in `Y`. -/
lemma support_map_subset_range (J : U.IdealSheafData) [IsClosedImmersion (J.subschemeι ≫ j)] :
    ((J.map j).support : Set Y) ⊆ Set.range j := by
  rw [map, Scheme.Hom.support_ker,
    (J.subschemeι ≫ j).isClosedEmbedding.isClosed_range.closure_eq, Scheme.Hom.comp_base,
    TopCat.coe_comp, Set.range_comp]
  exact Set.image_subset_range _ _

/-- An ideal sheaf whose support lies in the range of an open immersion `j` is the pushforward
of its pullback along `j`. -/
lemma map_comap_of_subset_range [IsOpenImmersion j] (I : Y.IdealSheafData)
    (hI : (I.support : Set Y) ⊆ Set.range j) : (I.comap j).map j = I := by
  have hI' : Set.range I.subschemeι ⊆ Set.range j := by rwa [range_subschemeι]
  have h : IsPullback (IsOpenImmersion.lift j I.subschemeι hI') (𝟙 _) j I.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  rw [comap, ← h.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso, map_ker,
    IsOpenImmersion.lift_fac, ker_subschemeι]

end OpenImmersion

section Pullback

open Limits

/-- The base change of the closed subscheme of `I` along `h : Y' ⟶ Y` is the closed subscheme of
the pulled back ideal sheaf `I.comap h`. -/
lemma isPullback_comap {Y Y' : Scheme.{u}} (I : Y.IdealSheafData) (h : Y' ⟶ Y) :
    IsPullback (I.comap h).subschemeι ((I.comapIso h).hom ≫ pullback.snd h I.subschemeι) h
      I.subschemeι :=
  IsPullback.of_iso_pullback ⟨by simp⟩ (I.comapIso h) (by simp) rfl

end Pullback

section Kernel

/-- The pullback of `K` along `h` is contained in the kernel of `a` if and only if `K` is
contained in the kernel of `a ≫ h`. -/
lemma comap_le_ker_iff {W : Scheme.{u}} (K : Y.IdealSheafData) (h : X ⟶ Y) (a : W ⟶ X) :
    K.comap h ≤ a.ker ↔ K ≤ (a ≫ h).ker := by
  rw [← map_bot a, ← map_bot (a ≫ h), le_map_iff_comap_le, le_map_iff_comap_le, comap_comp]

/-- An ideal sheaf on an affine scheme is determined by the morphisms from affine schemes whose
kernel contains it: test with the inclusions of the closed subschemes. -/
lemma eq_of_forall_le_ker_iff [IsAffine X] {K₁ K₂ : X.IdealSheafData}
    (H : ∀ (W : Scheme.{u}) [IsAffine W] (a : W ⟶ X), K₁ ≤ a.ker ↔ K₂ ≤ a.ker) : K₁ = K₂ := by
  have (K : X.IdealSheafData) : IsAffine K.subscheme := isAffine_of_isAffineHom K.subschemeι
  refine le_antisymm ?_ ?_
  · simpa only [ker_subschemeι] using (H _ K₂.subschemeι).2 (ker_subschemeι K₂).ge
  · simpa only [ker_subschemeι] using (H _ K₁.subschemeι).1 (ker_subschemeι K₁).ge

/-- An inclusion of ideal sheaves can be checked after pullback along a family of open
immersions jointly covering the scheme. -/
lemma le_of_forall_comap_le {ι : Type*} {Z : ι → Scheme.{u}} (j : ∀ i, Z i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hj : ⨆ i, (j i).opensRange = ⊤) {A B : X.IdealSheafData}
    (H : ∀ i, A.comap (j i) ≤ B.comap (j i)) : A ≤ B := by
  refine le_of_iSup_eq_top (ι := Σ i, (Z i).affineOpens)
    (fun p ↦ ⟨j p.1 ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion _⟩) ?_ fun p ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, z, rfl⟩ := TopologicalSpace.Opens.mem_iSup.mp (hj.ge (Set.mem_univ x))
    obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ :=
      (Z i).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, ⟨W, hW⟩⟩, ⟨z, hzW, rfl⟩⟩
  · have h := H p.1 p.2
    rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion] at h
    exact (Ideal.comap_le_comap_iff_of_surjective _
      (j p.1 |>.appIso p.2.1).commRingCatIsoToRingEquiv.symm.surjective _ _).mp h

end Kernel

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}
/-- The map `V(f^* s) ⟶ V(s)` between the closed subschemes cut out by global sections `s` of
`X` and by their pullbacks along `f : Y ⟶ X`. The pulled back sections may be given as any set
`s'` equal to `f^* s`. -/
noncomputable def Hom.zeroLocusSubschemeMap (f : Y ⟶ X) (s : Set Γ(X, ⊤))
    (s' : Set Γ(Y, ⊤) := f.appTop '' s) (hs : f.appTop '' s = s' := by rfl) :
    Y.zeroLocusSubscheme s' ⟶ X.zeroLocusSubscheme s :=
  IsClosedImmersion.lift (X.zeroLocusSubschemeι s) (Y.zeroLocusSubschemeι s' ≫ f)
    (IdealSheafData.le_ker_of_comap_eq_bot _ (by
      rw [IdealSheafData.ker_subschemeι, IdealSheafData.comap_comp,
        IdealSheafData.comap_ofIdealTop, Ideal.map_span, hs, ← IdealSheafData.ker_subschemeι
          (IdealSheafData.ofIdealTop (Ideal.span s'))]
      exact Hom.comap_ker_self _))

@[reassoc (attr := simp)]
lemma Hom.zeroLocusSubschemeMap_zeroLocusSubschemeι (f : Y ⟶ X) (s : Set Γ(X, ⊤))
    (s' : Set Γ(Y, ⊤) := f.appTop '' s) (hs : f.appTop '' s = s' := by rfl) :
    f.zeroLocusSubschemeMap s s' hs ≫ X.zeroLocusSubschemeι s = Y.zeroLocusSubschemeι s' ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

/-- **Base change of the closed subscheme cut out by global sections**: the closed subscheme of
`Y` cut out by the pullbacks `f^* s` is the base change of `V(s) ⊆ X` along `f`. -/
lemma isPullback_zeroLocusSubschemeι (f : Y ⟶ X) (s : Set Γ(X, ⊤))
    (s' : Set Γ(Y, ⊤) := f.appTop '' s) (hs : f.appTop '' s = s' := by rfl) :
    IsPullback (f.zeroLocusSubschemeMap s s' hs) (Y.zeroLocusSubschemeι s')
      (X.zeroLocusSubschemeι s) f :=
  (isPullback_of_isClosedImmersion _ _ _ _
    (f.zeroLocusSubschemeMap_zeroLocusSubschemeι s s' hs).symm
    (by rw [IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι,
      IdealSheafData.comap_ofIdealTop, Ideal.map_span, hs])).flip

/-- Two sets of functions on an affine scheme cutting out the same pullback of a closed
subscheme along a flat morphism generate the same ideal. -/
lemma span_eq_of_isPullback_zeroLocusSubschemeι {Z : Scheme.{u}} [IsAffine Y]
    {i : Z ⟶ X} [IsClosedImmersion i] {φ : Y ⟶ X} [Flat φ] {s t : Set Γ(Y, ⊤)}
    {g₁ : Y.zeroLocusSubscheme s ⟶ Z}
    {g₂ : Y.zeroLocusSubscheme t ⟶ Z} (h₁ : IsPullback g₁ (Y.zeroLocusSubschemeι s) i φ)
    (h₂ : IsPullback g₂ (Y.zeroLocusSubschemeι t) i φ) :
    Ideal.span s = Ideal.span t := by
  have h := (Scheme.Hom.ker_of_isPullback i φ h₁).trans (Scheme.Hom.ker_of_isPullback i φ h₂).symm
  rw [IdealSheafData.ker_subschemeι, IdealSheafData.ker_subschemeι] at h
  rw [← IdealSheafData.ideal_top_ofIdealTop (Ideal.span s),
    ← IdealSheafData.ideal_top_ofIdealTop (Ideal.span t), h]

/-- An element which is a unit modulo the ideal generated by `s` is invertible near the zero
locus of `s`. -/
lemma mem_basicOpen_of_isUnit_mk {s : Set Γ(Y, ⊤)} {d : Γ(Y, ⊤)}
    (hd : IsUnit (Ideal.Quotient.mk (Ideal.span s) d)) {y : Y} (hy : y ∈ Y.zeroLocus s) :
    y ∈ Y.basicOpen d := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : Γ(Y, ⊤) ⧸ Ideal.span s)
  have hmem : d * b - 1 ∈ Ideal.span s := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hb, ← hu]
    simp
  have hy' : y ∉ Y.basicOpen (d * b - 1) := by
    rw [← Y.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hy
    exact hy _ hmem
  rw [Y.mem_basicOpen_top] at hy' ⊢
  by_contra hd'
  apply hy'
  have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
    (mem_nonunits_iff.mpr fun h ↦ hd' (isUnit_of_mul_isUnit_left h) :
      Y.presheaf.germ ⊤ y trivial d * Y.presheaf.germ ⊤ y trivial b ∈ nonunits _)
  rw [map_sub, map_mul, map_one]
  simpa [neg_sub] using this.neg

end AlgebraicGeometry.Scheme
