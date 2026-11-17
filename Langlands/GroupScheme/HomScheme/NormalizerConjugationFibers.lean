import Langlands.GroupScheme.HomScheme.NormalizerConjugation

/-! # Normalizer cosets and source automorphisms of two conjugation families -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.HomScheme

private theorem exists_iso_precomp_iff_comp_inv
    {C : Type u} [Category.{v} C] {H G : C} (f j : H ⟶ G) (c : G ≅ G) :
    (∃ a : H ≅ H, f = a.hom ≫ j ≫ c.hom) ↔
      (∃ a : H ≅ H, f ≫ c.inv = a.hom ≫ j) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [ha]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    apply (cancel_mono c.inv).mp
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using ha

variable {S : Scheme.{u}} {G : GroupScheme S} {H : CommGroupScheme S}
  (i : H.toGrp ⟶ G) {T : Over S}

private theorem conjugationComposite_inv_mul
    {B : Scheme.{u}} {K L : GroupScheme B} (j : K ⟶ L)
    {P : Type v} [Group P] (p : P →* (Over.mk (𝟙 B) ⟶ L.X)) (g h : P) :
    j ≫ (L.innerIso (p (h⁻¹ * g))).hom =
      (j ≫ (L.innerIso (p g)).hom) ≫ (L.innerIso (p h)).inv := by
  have hm : p (h⁻¹ * g) = (p h)⁻¹ * p g :=
    (p.map_mul _ _).trans (congrArg (fun z => z * p g) (map_inv p h))
  have hi : (L.innerIso (p (h⁻¹ * g))).hom =
      (L.innerIso (p g)).hom ≫ (L.innerIso (p h)).inv :=
    (congrArg (fun z => (L.innerIso z).hom) hm).trans
      ((L.innerIso_mul_hom _ _).trans
        (congrArg (fun z => (L.innerIso (p g)).hom ≫ z) (L.innerIso_inv_hom (p h))))
  exact (congrArg (fun z => j ≫ z) hi).trans (Category.assoc _ _ _).symm

theorem conjugationFamily_inv_mul (g h : T ⟶ G.X) :
    conjugationFamily i (h⁻¹ * g) = conjugationFamily i g ≫
      (((GroupScheme.baseChange T.hom).obj G).innerIso
        (RelativeLevi.pulledBackPoint G T h)).inv :=
  conjugationComposite_inv_mul ((GroupScheme.baseChange T.hom).map i)
    (RelativeLevi.pulledBackPointHom G T) g h

/-- Two conjugation families differ by a source automorphism exactly on a full
normalizer coset, on every scheme test. -/
theorem exists_sourceIso_conjugationFamily_eq_iff [Mono i.hom.hom.left]
    (g h : T ⟶ G.X) :
    (∃ e : (GroupScheme.baseChange T.hom).obj H.toGrp ≅
        (GroupScheme.baseChange T.hom).obj H.toGrp,
      conjugationFamily i g = e.hom ≫ conjugationFamily i h) ↔
        g⁻¹ * h ∈ (torusNormalizer i).carrier T := by
  let C := ((GroupScheme.baseChange T.hom).obj G).innerIso
    (RelativeLevi.pulledBackPoint G T h)
  have hf := exists_iso_precomp_iff_comp_inv (conjugationFamily i g)
    ((GroupScheme.baseChange T.hom).map i) C
  change (∃ e : (GroupScheme.baseChange T.hom).obj H.toGrp ≅
      (GroupScheme.baseChange T.hom).obj H.toGrp,
    conjugationFamily i g = e.hom ≫ conjugationFamily i h) ↔
    (∃ e : (GroupScheme.baseChange T.hom).obj H.toGrp ≅
      (GroupScheme.baseChange T.hom).obj H.toGrp,
    conjugationFamily i g ≫ C.inv = e.hom ≫ (GroupScheme.baseChange T.hom).map i) at hf
  have hc : conjugationFamily i (h⁻¹ * g) = conjugationFamily i g ≫ C.inv :=
    conjugationFamily_inv_mul i g h
  rw [← hc] at hf
  have hn : h⁻¹ * g ∈ (torusNormalizer i).carrier T ↔
      g⁻¹ * h ∈ (torusNormalizer i).carrier T := by
    have heq : h⁻¹ * g = (g⁻¹ * h)⁻¹ := by group
    rw [heq]
    exact (torusNormalizer i).carrier T |>.inv_mem_iff
  exact hf.trans ((exists_sourceIso_conjugationFamily_iff i (h⁻¹ * g)).trans hn)

/-- Choose the actual source automorphism identifying the two families. -/
def normalizerPairSourceIso [Mono i.hom.hom.left] (g h : T ⟶ G.X)
    (hg : g⁻¹ * h ∈ (torusNormalizer i).carrier T) :
    {e : (GroupScheme.baseChange T.hom).obj H.toGrp ≅
        (GroupScheme.baseChange T.hom).obj H.toGrp //
      conjugationFamily i g = e.hom ≫ conjugationFamily i h} :=
  ⟨_, ((exists_sourceIso_conjugationFamily_eq_iff i g h).mpr hg).choose_spec⟩

end Langlands.GroupScheme.HomScheme
