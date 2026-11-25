/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningCartesianAtlas

/-!
# The scheme obtained by gluing local universal thickenings

Source: Stacks Project, More on Morphisms, Lemma 37.7.1 (Tag 04F3),
paragraph beginning "Choose an affine open covering".
(blueprint: lem-weil-pbc-universal-first-order-thickening-glued-atlas)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Changing the source by an isomorphism preserves the square-zero kernel. -/
private theorem firstOrderThickening_iso_source
    {T U V : Scheme.{u}} (e : T ≅ U) (i : U ⟶ V)
    (hi : IsFirstOrderThickening i) : IsFirstOrderThickening (e.hom ≫ i) := by
  have : IsClosedImmersion i := hi.1
  exact ⟨inferInstance, by rw [Scheme.Hom.ker_comp_of_isIso, hi.2]⟩

/-- Universality is unchanged when the source is identified by an isomorphism. -/
private theorem universalThickening_iso_source
    {T U V X : Scheme.{u}} (e : T ≅ U) (h : U ⟶ X) (i : U ⟶ V) (p : V ⟶ X)
    (H : IsUniversalFirstOrderThickening h i p) :
    IsUniversalFirstOrderThickening (e.hom ≫ h) (e.hom ≫ i) p := by
  refine ⟨firstOrderThickening_iso_source e i H.1, ?_, ?_⟩
  · rw [Category.assoc, H.2.1]
  · intro S S' t b a ht hab
    obtain ⟨c, hc, huniq⟩ := H.2.2 t b (a ≫ e.hom) ht
      (by simpa only [Category.assoc] using hab)
    refine ⟨c, ?_, ?_⟩
    · simpa only [Category.assoc] using hc
    · intro d hd
      exact huniq d (by simpa only [Category.assoc] using hd)

/-- Square-zero closed immersions can be checked on an open cover of the target. -/
private theorem firstOrderThickening_of_cover
    {Z W : Scheme.{u}} (j : Z ⟶ W) (D : W.OpenCover.{u})
    (H : ∀ k, IsFirstOrderThickening (D.pullbackHom j k)) :
    IsFirstOrderThickening j := by
  have : IsClosedImmersion j :=
    (IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion) D).mpr
      (fun k ↦ (H k).1)
  refine ⟨inferInstance, ?_⟩
  let U : (Σ k, (D.X k).affineOpens) → W.affineOpens := fun a ↦
    ⟨D.f a.1 ''ᵁ a.2, a.2.2.image_of_isOpenImmersion (D.f a.1)⟩
  have hU : ⨆ a, (U a).1 = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨k, z, rfl⟩ := D.exists_eq w
    have hz : z ∈ ⨆ V : (D.X k).affineOpens, V.1 := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨V, hzV⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨⟨k, V⟩, ⟨z, hzV, rfl⟩⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
  rintro ⟨k, V⟩
  have hz := congrArg (fun I ↦ I.ideal V) (H k).2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hz ⊢
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j (D.pullbackHom j k)
    ((D.pullback₁ j).f k) (D.f k) (IsPullback.of_hasPullback j (D.f k)).flip] at hz
  have hs := (ConcreteCategory.bijective_of_isIso ((D.f k).appIso V).inv).2
  have hm := congrArg (Ideal.map ((D.f k).appIso V).inv.hom) hz
  simpa only [Ideal.map_pow, Ideal.map_comap_of_surjective _ hs, Ideal.map_bot] using hm

/-- Glue the schemes of local universal thickenings. The conclusion provides a
first order thickening and its universal charts; global universality is not asserted.

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraph beginning "Choose an affine open covering", up to "is a universal
first order thickening of Z_i over X".
(blueprint: lem-weil-pbc-universal-first-order-thickening-glued-atlas)

Proof:
1. On each overlap of `C`, restrict the two local thickenings using the first and
   second clauses of `universalFirstOrderThickening_open_pieces` (whole base open).
   They are universal thickenings of the same overlap over `X`.
2. The uniqueness theorem for universal thickenings supplies a unique isomorphism
   between them over `X` and fixing the overlap. On triple intersections both
   composites have these same properties, so uniqueness proves the cocycle equation.
3. Form the scheme glue data of these open overlaps and isomorphisms and take its
   glued scheme `W`. Its open immersions give an open cover `D`. The local maps to
   `X` agree on overlaps and glue to `p`. The maps from the source cover into `W`
   also agree, hence glue to `j : Z ⟶ W`. Check `j ≫ p = h` on `C`.
4. The inverse image under `j` of each glued chart is the corresponding source
   chart. Indeed membership may be checked in a source chart, where the gluing
   equivalence identifies exactly the prescribed open overlap. Thus the pullback
   of `j` to each chart of `D` identifies with its given local immersion.
5. Closed immersion is local on the target. The local defining ideals square to
   zero and are restrictions of the global kernel ideal, so this ideal also squares
   to zero. Therefore `j` is a first order thickening. By the pullback identifications
   in step 4, the universality of each given chart is precisely the final clause. -/
theorem universalFirstOrderThickening_gluedAtlas
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (j : Z ⟶ W) (p : W ⟶ X) (D : W.OpenCover.{u}),
      IsFirstOrderThickening j ∧ j ≫ p = h ∧
        ∀ k, IsUniversalFirstOrderThickening ((D.pullback₁ j).f k ≫ h)
          (D.pullbackHom j k) (D.f k ≫ p) := by
  obtain ⟨W, j, p, e, he, hcover, hjp, hep, hcart⟩ :=
    universalFirstOrderThickening_cartesianAtlas h C Z' i h' H
  let D : W.OpenCover.{u} := Scheme.Cover.mkOfCovers C.I₀ Z' e hcover he
  have HD (k : D.I₀) :
      IsUniversalFirstOrderThickening ((D.pullback₁ j).f k ≫ h)
        (D.pullbackHom j k) (D.f k ≫ p) := by
    let a := (hcart k).flip.isoPullback
    have ha₁ : a.inv ≫ C.f k = (D.pullback₁ j).f k :=
      (hcart k).flip.isoPullback_inv_fst
    have ha₂ : a.inv ≫ i k = D.pullbackHom j k :=
      (hcart k).flip.isoPullback_inv_snd
    have HK := universalThickening_iso_source a.symm (C.f k ≫ h) (i k) (h' k) (H k)
    have hp : D.f k ≫ p = h' k := hep k
    rw [hp]
    simpa only [Iso.symm_hom, ← Category.assoc a.inv (C.f k) h, ha₁, ha₂] using HK
  exact ⟨W, j, p, D, firstOrderThickening_of_cover j D (fun k ↦ (HD k).1), hjp, HD⟩

end AlgebraicGeometry
