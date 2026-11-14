import Langlands.GroupScheme.Torus.PointedEtaleCocharacterLift
import Langlands.GroupScheme.Dynamic.LocalPresentation
import Langlands.GroupScheme.Dynamic.ParabolicCharacters

/-! # Comparisons for prescribed dynamic presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.Dynamic

variable {S T U : Scheme.{u}} {G H : GroupScheme S}

theorem baseChangeCocharacter_comp_hom (p : T ⟶ S)
    (χ : (Gm S).toGrp ⟶ H) (i : H ⟶ G) :
    baseChangeCocharacter p (χ ≫ i) =
      baseChangeCocharacter p χ ≫ (baseChange p).map i := by
  simp only [baseChangeCocharacter, Functor.map_comp, Category.assoc]

/-- The normalized cocharacter respects the actual pullback tower comparison. -/
theorem baseChangeCocharacter_tower (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (h : q ≫ p = r) (χ : (Gm S).toGrp ⟶ G) :
    baseChangeCocharacter q (baseChangeCocharacter p χ) ≫
        (Descent.pullbackComparison p q r h G).hom =
      baseChangeCocharacter r χ := by
  apply (cancel_epi ((baseChange q).map (Gm.baseChangeIso p).hom ≫
    (Gm.baseChangeIso q).hom)).mp
  simp only [baseChangeCocharacter, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [← Category.assoc, Descent.gmBaseChange_tower p q r h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact Descent.pullbackComparison_naturality p q r h χ

/-- A dynamic presentation is preserved and reflected by an ambient isomorphism. -/
theorem range_eq_parabolic_comp_iso_iff {G' : GroupScheme S}
    (i : H ⟶ G) (χ : (Gm S).toGrp ⟶ G) (e : G ≅ G') :
    SubgroupFunctor.range (i ≫ e.hom) = parabolic (χ ≫ e.hom) ↔
      SubgroupFunctor.range i = parabolic χ := by
  constructor
  · intro h
    rw [parabolic_eq_comap_of_iso χ e, ← h]
    ext T x
    simp only [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap,
      Grp.comp_hom_hom, ← Category.assoc]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg (fun z => z ≫ e.hom.hom.hom) hy⟩,
      fun ⟨y, hy⟩ => ⟨y, (cancel_mono e.hom.hom.hom).mp hy⟩⟩
  · intro h
    have h' : SubgroupFunctor.range ((i ≫ e.hom) ≫ e.inv) =
        parabolic ((χ ≫ e.hom) ≫ e.inv) := by
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h
    rw [parabolic_eq_comap_of_iso (χ ≫ e.hom) e.symm]
    change SubgroupFunctor.range (i ≫ e.hom) =
      (parabolic ((χ ≫ e.hom) ≫ e.inv)).comap e.inv
    rw [← h']
    ext T x
    simp only [SubgroupFunctor.mem_range, SubgroupFunctor.mem_comap,
      Grp.comp_hom_hom, ← Category.assoc]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, congrArg (fun z => z ≫ e.inv.hom.hom) hy⟩,
      fun ⟨y, hy⟩ => ⟨y, (cancel_mono e.inv.hom.hom).mp hy⟩⟩

/-- Exact recovery of a subgroup cocharacter also recovers its ambient composite. -/
theorem ambient_cocharacter_recovers
    (p : T ⟶ S) (b : U ⟶ T) (a : U ⟶ S) (hb : b ≫ p = a)
    (i : H ⟶ G) (χ : (Gm T).toGrp ⟶ (baseChange p).obj H)
    (χ₀ : (Gm U).toGrp ⟶ (baseChange a).obj H)
    (hχ : baseChangeCocharacter b χ ≫
      (Descent.pullbackComparison p b a hb H).hom = χ₀) :
    baseChangeCocharacter b (χ ≫ (baseChange p).map i) ≫
      (Descent.pullbackComparison p b a hb G).hom = χ₀ ≫ (baseChange a).map i := by
  rw [baseChangeCocharacter_comp_hom, Category.assoc,
    Descent.pullbackComparison_naturality, ← Category.assoc, hχ]

/-- A recovered fibre cocharacter presents the iterated fibre of its subgroup. -/
theorem fibre_presentation_of_recovers
    (p : T ⟶ S) (b : U ⟶ T) (a : U ⟶ S) (hb : b ≫ p = a)
    (i : H ⟶ G) (χ : (Gm T).toGrp ⟶ (baseChange p).obj H)
    (ν : (Gm U).toGrp ⟶ (baseChange a).obj G)
    (hν : SubgroupFunctor.range ((baseChange a).map i) = parabolic ν)
    (hχ : baseChangeCocharacter b (χ ≫ (baseChange p).map i) ≫
      (Descent.pullbackComparison p b a hb G).hom = ν) :
    SubgroupFunctor.range ((baseChange b).map ((baseChange p).map i)) =
      parabolic (baseChangeCocharacter b (χ ≫ (baseChange p).map i)) := by
  apply (range_eq_parabolic_comp_iso_iff _ _
    (Descent.pullbackComparison p b a hb G)).mp
  rw [hχ, Descent.pullbackComparison_naturality,
    SubgroupFunctor.range_iso_comp, hν]

/-- Pull an actual cocharacter back and express its target as the direct pullback. -/
def pullbackCocharacter (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (h : q ≫ p = r) (χ : (Gm T).toGrp ⟶ (baseChange p).obj G) :
    (Gm U).toGrp ⟶ (baseChange r).obj G :=
  baseChangeCocharacter q χ ≫ (Descent.pullbackComparison p q r h G).hom

/-- A supplied dynamic presentation pulls back to the direct pullback inclusion. -/
theorem pullbackCocharacter_presents (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S)
    (h : q ≫ p = r) (i : H ⟶ G)
    (χ : (Gm T).toGrp ⟶ (baseChange p).obj G)
    (hχ : SubgroupFunctor.range ((baseChange p).map i) = parabolic χ) :
    SubgroupFunctor.range ((baseChange r).map i) =
      parabolic (pullbackCocharacter p q r h χ) := by
  have hh : SubgroupFunctor.range ((baseChange q).map ((baseChange p).map i)) =
      parabolic (baseChangeCocharacter q χ) := by
    rw [SubgroupFunctor.range_baseChangeHom, hχ, parabolic_baseChange]
  have hh' := (range_eq_parabolic_comp_iso_iff _ _
    (Descent.pullbackComparison p q r h G)).mpr hh
  rw [Descent.pullbackComparison_naturality, SubgroupFunctor.range_iso_comp] at hh'
  exact hh'

@[reassoc] private theorem baseChange_map_fst (p : T ⟶ S) (i : H ⟶ G) :
    ((baseChange p).map i).hom.hom.left ≫ pullback.fst G.X.hom p =
      pullback.fst H.X.hom p ≫ i.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- Canonical direct-pullback comparisons agree around a three-step tower. -/
theorem pullbackComparison_tower {V : Scheme.{u}}
    (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ p = r)
    (c : V ⟶ U) (b : V ⟶ T) (a : V ⟶ S)
    (hcb : c ≫ q = b) (hba : b ≫ p = a) (hca : c ≫ r = a) :
    (baseChange c).map (Descent.pullbackComparison p q r h G).hom ≫
        (Descent.pullbackComparison r c a hca G).hom =
      (Descent.pullbackComparison q c b hcb ((baseChange p).obj G)).hom ≫
        (Descent.pullbackComparison p b a hba G).hom := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Grp.comp_hom_hom, Over.comp_left, Category.assoc,
      Descent.pullbackComparison_hom_fst, baseChange_map_fst_assoc,
      Descent.pullbackComparison_hom_fst_assoc]
  · exact (Over.w _).trans (Over.w _).symm

/-- Direct pullback of a cocharacter retains its exact value at a specified point. -/
theorem pullbackCocharacter_recovers {V : Scheme.{u}}
    (p : T ⟶ S) (q : U ⟶ T) (r : U ⟶ S) (h : q ≫ p = r)
    (c : V ⟶ U) (b : V ⟶ T) (a : V ⟶ S)
    (hcb : c ≫ q = b) (hba : b ≫ p = a) (hca : c ≫ r = a)
    (χ : (Gm T).toGrp ⟶ (baseChange p).obj G) :
    baseChangeCocharacter c (pullbackCocharacter p q r h χ) ≫
        (Descent.pullbackComparison r c a hca G).hom =
      baseChangeCocharacter b χ ≫ (Descent.pullbackComparison p b a hba G).hom := by
  rw [pullbackCocharacter, baseChangeCocharacter_comp_hom, Category.assoc,
    pullbackComparison_tower p q r h c b a hcb hba hca,
    ← Category.assoc, baseChangeCocharacter_tower]

end Langlands.GroupScheme.Dynamic
