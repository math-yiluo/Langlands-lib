import Langlands.Global.AdelicStandardLeviNormalizedMinima
import Langlands.GroupScheme.Rational.StandardLeviIntersectionReduction
import Langlands.GroupScheme.Rational.StandardLeviFamilyRestriction

/-! # Actual minimal-parabolic coordinates inside a canonical standard Levi -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.Standard

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)

/-- The actual inclusion of the original minimal standard Levi into any
canonical standard Levi. -/
def minimalLeviToLevi : leviScheme i ν ∅ ⟶ leviScheme i ν J :=
  (isRepresentedBy_leviHom i ν ∅).inclusionHom (isRepresentedBy_leviHom i ν J)
    ((((standardParabolicOrder F G hG T i hi ν hν).1 ∅ J
      (Set.empty_subset _) hJ).2 (Set.empty_subset _)).1)

@[simp] theorem minimalLeviToLevi_comp :
    minimalLeviToLevi i ν hG hi hν J hJ ≫ leviHom i ν J = leviHom i ν ∅ :=
  SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _

end Langlands.GroupScheme.Standard

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (ν : cocharacterLattice T)

local instance (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  (Standard.isClosedSubgroup_leviHom i ν J).isAffineHom_source

/-- An actual minimal unipotent adelic point splits into the image of the
intrinsic minimal unipotent of a standard Levi followed by its outer
unipotent. The intersection comparison is on the full adele test algebra. -/
theorem exists_standardLevi_minimal_unipotent_factors
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)) :
    let iL := standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
    ∃ (y : AdelicGroupPoints F (Standard.unipotentScheme iL ν ∅))
      (z : AdelicGroupPoints F (Standard.unipotentScheme i ν J)),
      map F _ G (Standard.unipotentHom i ν ∅) x =
        map F _ G (Standard.leviHom i ν J)
          (map F _ _ (Standard.unipotentHom iL ν ∅) y) *
            map F _ G (Standard.unipotentHom i ν J) z := by
  intro iL
  let Q := (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))
  have horder := (standardParabolicOrder F G hG T i hi ν hν).1 ∅ J
    (Set.empty_subset _) hJ
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G hG T i hi ν hν J hJ
  obtain ⟨_, hM, hU⟩ := hcompare ζ hζ
  have hsplit := StandardLeviIntersection.standardUnipotent_eq_leviInter_mul i ν
    ⟨hζ, hM.ge, hU.ge⟩ (horder.1.1 (Set.empty_subset _))
    ((horder.2 (Set.empty_subset _)).2) Q
  have hx : x ≫ (Standard.unipotentHom i ν ∅).hom.hom ∈
      (standardUnipotent i ν ∅).carrier Q := by
    rw [← (Standard.isRepresentedBy_unipotentHom i ν ∅).2]
    exact ⟨x, rfl⟩
  change x ≫ (Standard.unipotentHom i ν ∅).hom.hom ∈
    (↑((standardUnipotent i ν ∅).carrier Q) : Set (Q ⟶ G.X)) at hx
  rw [hsplit] at hx
  obtain ⟨a, ⟨haL, haU⟩, b, hbU, hab⟩ := Set.mem_mul.mp hx
  rw [← (Standard.isRepresentedBy_leviHom i ν J).2] at haL
  obtain ⟨aL, haL⟩ := haL
  change Q ⟶ (Standard.leviScheme i ν J).X at aL
  change aL ≫ (Standard.leviHom i ν J).hom.hom = a at haL
  have hinner :
      standardUnipotent iL ν ∅ =
        (standardUnipotent i ν ∅).comap (Standard.leviHom i ν J) := by
    simpa only [Set.inter_empty] using
      (standardLeviStandardFamilies_inter_canonical i ν hG hi hν J ∅ hJ
        (Set.empty_subset _)).2.2
  have haInner : aL ∈ (standardUnipotent iL ν ∅).carrier Q := by
    rw [hinner, SubgroupFunctor.mem_comap, haL]
    exact haU
  rw [← (Standard.isRepresentedBy_unipotentHom iL ν ∅).2] at haInner
  obtain ⟨y, hy⟩ := haInner
  change AdelicGroupPoints F (Standard.unipotentScheme iL ν ∅) at y
  change y ≫ (Standard.unipotentHom iL ν ∅).hom.hom = aL at hy
  rw [← (Standard.isRepresentedBy_unipotentHom i ν J).2] at hbU
  obtain ⟨z, hz⟩ := hbU
  change AdelicGroupPoints F (Standard.unipotentScheme i ν J) at z
  change z ≫ (Standard.unipotentHom i ν J).hom.hom = b at hz
  refine ⟨y, z, ?_⟩
  change x ≫ (Standard.unipotentHom i ν ∅).hom.hom =
    ((y ≫ (Standard.unipotentHom iL ν ∅).hom.hom) ≫
      (Standard.leviHom i ν J).hom.hom) *
        (z ≫ (Standard.unipotentHom i ν J).hom.hom)
  rw [hy, haL, hz]
  exact hab.symm

/-- Transport the original intrinsic norm-one minimal Levi factor by the
actual inclusion, and split the right unipotent factor. This constructs
a raw standard-Levi factor with the same original torus coordinate. -/
theorem exists_standardLevi_minimal_coordinates
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)
    (m : normOneSubgroup F (Standard.leviScheme i ν ∅))
    (s : AdelicGroupPoints F T.toGrp)
    (x : AdelicGroupPoints F (Standard.unipotentScheme i ν ∅)) :
    let L := Standard.leviScheme i ν J
    let iL := standardLeviTorusFactor i ν J (Standard.isRepresentedBy_leviHom i ν J)
    let mL := mapNormOne F _ L (Standard.minimalLeviToLevi i ν hG hi hν J hJ) m
    ∃ (y : AdelicGroupPoints F (Standard.unipotentScheme iL ν ∅))
      (z : AdelicGroupPoints F (Standard.unipotentScheme i ν J)),
      map F _ G (Standard.leviHom i ν ∅) m * map F _ G i s *
          map F _ G (Standard.unipotentHom i ν ∅) x =
        map F L G (Standard.leviHom i ν J)
          ((mL : AdelicGroupPoints F L) * map F _ L iL s *
            map F _ L (Standard.unipotentHom iL ν ∅) y) *
              map F _ G (Standard.unipotentHom i ν J) z := by
  intro L iL mL
  obtain ⟨y, z, hx⟩ :=
    exists_standardLevi_minimal_unipotent_factors F G T i ν hG hi hν J hJ x
  have hm :
      map F L G (Standard.leviHom i ν J) (mL : AdelicGroupPoints F L) =
        map F _ G (Standard.leviHom i ν ∅) m := by
    change (m.val ≫ (Standard.minimalLeviToLevi i ν hG hi hν J hJ).hom.hom) ≫
      (Standard.leviHom i ν J).hom.hom = m.val ≫ (Standard.leviHom i ν ∅).hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, Standard.minimalLeviToLevi_comp]
  have hs :
      map F L G (Standard.leviHom i ν J) (map F _ L iL s) =
        map F _ G i s := by
    change (s ≫ iL.hom.hom) ≫ (Standard.leviHom i ν J).hom.hom = s ≫ i.hom.hom
    rw [Category.assoc, ← Grp.comp_hom_hom, standardLeviTorusFactor_comp]
  refine ⟨y, z, ?_⟩
  rw [map_mul, map_mul, hm, hs, hx]
  simp only [L, iL, mul_assoc]

end Langlands.Global.RepresentationGrowth
