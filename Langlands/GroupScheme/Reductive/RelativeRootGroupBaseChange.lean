import Langlands.GroupScheme.Reductive.LocalRootGroupParam
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Arbitrary scalar extension of actual dynamic root groups -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.LocalRootGroup
open Corepresented

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The actual dynamic root group represents the intersection of the
centralizer of `mu` with the unipotent subgroup of `nu`. -/
theorem isRepresentedBy_incl :
    ((Dynamic.centralizer (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter _ I mu) ≫ i)) ⊓
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter _ I nu) ≫ i))).IsRepresentedBy
      (incl i mu nu) := by
  let j := jZ i mu ≫ (AffineCoordinates.groupSchemeIso G).hom
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom
      (splitTorus.exponentCocharacter _ I mu) ≫ i)).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom _
  have hU := Corepresented.isRepresentedBy_unipotentHom (unipCochar i mu nu)
  have : Mono j.hom.hom := hZ.1
  have : Mono (jU i mu nu).hom.hom := hU.1
  have hχ : unipCochar i mu nu ≫ j =
      CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫ i := by
    rw [unipCochar, Category.assoc, ← Category.assoc (torusZ i mu), torusZ_comp,
      modelTorus, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  refine ⟨inferInstanceAs (Mono ((jU i mu nu).hom.hom ≫ j.hom.hom)), ?_⟩
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · rw [← hZ.2]
      change ∃ z : T ⟶ (Zc i mu).X,
        z ≫ j.hom.hom = y ≫ (incl i mu nu).hom.hom
      exact ⟨y ≫ (jU i mu nu).hom.hom, by
        simp only [incl, j, Grp.comp_hom_hom, Category.assoc]⟩
    · have hy : y ≫ (jU i mu nu).hom.hom ∈
          (Dynamic.unipotent (unipCochar i mu nu)).carrier T := by
        rw [← hU.2]
        exact ⟨y, rfl⟩
      have h := Dynamic.unipotent_le_comap (unipCochar i mu nu) j T hy
      rw [SubgroupFunctor.mem_comap, hχ] at h
      exact h
  · rintro ⟨hc, hu⟩
    obtain ⟨z, hz⟩ := exists_centralizer_point i mu hc
    have hzU := mem_unipotent_of i mu nu hu hz
    obtain ⟨y, hy⟩ : ∃ y, y ≫ (jU i mu nu).hom.hom = z := by
      rw [← SubgroupFunctor.mem_range, hU.2]
      exact hzU
    refine ⟨y, ?_⟩
    rw [incl, Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, hy,
      ← Category.assoc, hz, Category.assoc, ← Grp.comp_hom_hom,
      Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

variable (A : Type u) [CommRing A] [Algebra R A]

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap R A)).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap R A)))

/-- Both the scalar extension of the actual group and its new construction
represent the same dynamic intersection. -/
theorem isRepresentedBy_baseChange_incl :
    ((Dynamic.centralizer (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter _ I mu) ≫
          splitTorus.baseChangeHom (K := A) G I i)) ⊓
      (Dynamic.unipotent (CommGroupScheme.groupHom
        (splitTorus.exponentCocharacter _ I nu) ≫
          splitTorus.baseChangeHom (K := A) G I i))).IsRepresentedBy
      ((GroupScheme.baseChange (algebraBaseMap R A)).map (incl i mu nu)) := by
  have h := (isRepresentedBy_incl i mu nu).baseChange (algebraBaseMap R A)
  rw [SubgroupFunctor.inf_baseChange, ← Dynamic.centralizer_baseChange,
    ← Dynamic.unipotent_baseChange, baseChangeCocharacter_groupHom_comp,
    baseChangeCocharacter_groupHom_comp] at h
  exact h

/-- The construction of the actual dynamic root group commutes with every
extension of commutative rings. -/
def rootGroupBaseChangeIso :
    (GroupScheme.baseChange (algebraBaseMap R A)).obj (Uc i mu nu) ≅
      Uc (splitTorus.baseChangeHom (K := A) G I i) mu nu :=
  (isRepresentedBy_baseChange_incl i mu nu A).isoOfIsRepresentedBy
    (isRepresentedBy_incl (splitTorus.baseChangeHom (K := A) G I i) mu nu)

theorem rootGroupBaseChangeIso_hom_comp :
    (rootGroupBaseChangeIso i mu nu A).hom ≫
        incl (splitTorus.baseChangeHom (K := A) G I i) mu nu =
      (GroupScheme.baseChange (algebraBaseMap R A)).map (incl i mu nu) :=
  SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp _ _

end Langlands.GroupScheme.LocalRootGroup
