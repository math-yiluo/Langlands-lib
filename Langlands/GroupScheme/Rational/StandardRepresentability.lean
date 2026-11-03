import Langlands.GroupScheme.CorepresentedIntersection
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Rational.StandardParabolic
import Langlands.GroupScheme.RepresentedSubgroup

/-! # Closed representatives of the standard rational subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SubgroupFunctor.IsRepresentedBy

variable {S : Scheme.{u}} {G H K : GroupScheme S}
  {F F' : SubgroupFunctor G} {j : H ⟶ G} {j' : K ⟶ G}

/-- An inclusion of represented subgroup functors gives an actual group-scheme homomorphism. -/
def inclusionHom (hj : F.IsRepresentedBy j) (hj' : F'.IsRepresentedBy j')
    (h : F ≤ F') : H ⟶ K :=
  hj.lift hj' (fun Q => Subgroup.inclusion (h Q)) (fun _ _ => rfl)

@[simp] theorem inclusionHom_comp (hj : F.IsRepresentedBy j) (hj' : F'.IsRepresentedBy j')
    (h : F ≤ F') : inclusionHom hj hj' h ≫ j' = j :=
  lift_comp_eq _ _ _ (fun _ _ => rfl) (fun _ _ => rfl)

end Langlands.GroupScheme.SubgroupFunctor.IsRepresentedBy

namespace Langlands.GroupScheme.Standard

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) (J : Set (characterLattice T))

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The family of cocharacters used by the choice-free standard subgroup definitions. -/
abbrev indices := {ζ : cocharacterLattice T // IsStandardCocharacter i ν J ζ}

/-- The coordinate cocharacter corresponding to a member of the standard family. -/
def coordinateCocharacter (ζ : indices i ν J) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶
      Corepresented.groupScheme (AffineCoordinates.functor G)
        (AffineCoordinates.corepresentation G) :=
  Dynamic.Affine.cocharacter (CommGroupScheme.groupHom ζ.val ≫ i)

/-- The closed affine representative of the choice-free standard parabolic functor. -/
def parabolicScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.intersectionScheme
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_parabolic
      (coordinateCocharacter i ν J ζ))

/-- The closed affine representative of the choice-free standard Levi functor. -/
def leviScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.intersectionScheme
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_centralizer
      (coordinateCocharacter i ν J ζ))

/-- The closed affine representative of the choice-free standard unipotent functor. -/
def unipotentScheme : GroupScheme (Spec (CommRingCat.of k)) :=
  Corepresented.intersectionScheme
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_unipotent
      (coordinateCocharacter i ν J ζ))

/-- The inclusion of the standard parabolic representative in the original group. -/
def parabolicHom : parabolicScheme i ν J ⟶ G :=
  Corepresented.intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_parabolic
      (coordinateCocharacter i ν J ζ)) ≫ (AffineCoordinates.groupSchemeIso G).hom

/-- The inclusion of the standard Levi representative in the original group. -/
def leviHom : leviScheme i ν J ⟶ G :=
  Corepresented.intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_centralizer
      (coordinateCocharacter i ν J ζ)) ≫ (AffineCoordinates.groupSchemeIso G).hom

/-- The inclusion of the standard unipotent representative in the original group. -/
def unipotentHom : unipotentScheme i ν J ⟶ G :=
  Corepresented.intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_unipotent
      (coordinateCocharacter i ν J ζ)) ≫ (AffineCoordinates.groupSchemeIso G).hom

theorem parabolic_eq_comap_intersection :
    standardParabolic i ν J =
      (SubgroupFunctor.intersection fun ζ : indices i ν J =>
        Dynamic.parabolic (coordinateCocharacter i ν J ζ)).comap
          (AffineCoordinates.groupSchemeIso G).inv := by
  apply SubgroupFunctor.ext
  intro Q
  apply Subgroup.ext
  intro x
  rw [mem_standardParabolic, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_intersection]
  constructor
  · intro hx ζ
    have h := hx ζ.val ζ.property
    rw [Dynamic.parabolic_eq_comap_of_iso _ (AffineCoordinates.groupSchemeIso G).symm] at h
    exact h
  · intro hx ζ hζ
    rw [Dynamic.parabolic_eq_comap_of_iso _ (AffineCoordinates.groupSchemeIso G).symm]
    exact hx ⟨ζ, hζ⟩

theorem levi_eq_comap_intersection :
    standardLevi i ν J =
      (SubgroupFunctor.intersection fun ζ : indices i ν J =>
        Dynamic.centralizer (coordinateCocharacter i ν J ζ)).comap
          (AffineCoordinates.groupSchemeIso G).inv := by
  apply SubgroupFunctor.ext
  intro Q
  apply Subgroup.ext
  intro x
  rw [mem_standardLevi, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_intersection]
  constructor
  · intro hx ζ
    have h := hx ζ.val ζ.property
    rw [Dynamic.centralizer_eq_comap_of_iso _ (AffineCoordinates.groupSchemeIso G).symm] at h
    exact h
  · intro hx ζ hζ
    rw [Dynamic.centralizer_eq_comap_of_iso _ (AffineCoordinates.groupSchemeIso G).symm]
    exact hx ⟨ζ, hζ⟩

theorem unipotent_eq_comap_intersection :
    standardUnipotent i ν J =
      (SubgroupFunctor.intersection fun ζ : indices i ν J =>
        Dynamic.unipotent (coordinateCocharacter i ν J ζ)).comap
          (AffineCoordinates.groupSchemeIso G).inv := by
  apply SubgroupFunctor.ext
  intro Q
  apply Subgroup.ext
  intro x
  rw [mem_standardUnipotent, SubgroupFunctor.mem_comap, SubgroupFunctor.mem_intersection]
  constructor
  · intro hx ζ
    have h := hx ζ.val ζ.property
    rw [Dynamic.unipotent_eq_comap_of_iso _ (AffineCoordinates.groupSchemeIso G).symm] at h
    exact h
  · intro hx ζ hζ
    rw [Dynamic.unipotent_eq_comap_of_iso _ (AffineCoordinates.groupSchemeIso G).symm]
    exact hx ⟨ζ, hζ⟩

/-- Equality with the standard parabolic functor holds on every test scheme. -/
theorem isRepresentedBy_parabolicHom :
    (standardParabolic i ν J).IsRepresentedBy (parabolicHom i ν J) := by
  rw [parabolic_eq_comap_intersection]
  exact (Corepresented.isRepresentedBy_intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_parabolic
      (coordinateCocharacter i ν J ζ))).comp_iso (AffineCoordinates.groupSchemeIso G)

/-- Equality with the standard Levi functor holds on every test scheme. -/
theorem isRepresentedBy_leviHom :
    (standardLevi i ν J).IsRepresentedBy (leviHom i ν J) := by
  rw [levi_eq_comap_intersection]
  exact (Corepresented.isRepresentedBy_intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_centralizer
      (coordinateCocharacter i ν J ζ))).comp_iso (AffineCoordinates.groupSchemeIso G)

/-- Equality with the standard unipotent functor holds on every test scheme. -/
theorem isRepresentedBy_unipotentHom :
    (standardUnipotent i ν J).IsRepresentedBy (unipotentHom i ν J) := by
  rw [unipotent_eq_comap_intersection]
  exact (Corepresented.isRepresentedBy_intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_unipotent
      (coordinateCocharacter i ν J ζ))).comp_iso (AffineCoordinates.groupSchemeIso G)

theorem isClosedSubgroup_parabolicHom : IsClosedSubgroup (parabolicHom i ν J) :=
  (Corepresented.isClosedSubgroup_intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_parabolic
      (coordinateCocharacter i ν J ζ))).comp_iso (AffineCoordinates.groupSchemeIso G)

theorem isClosedSubgroup_leviHom : IsClosedSubgroup (leviHom i ν J) :=
  (Corepresented.isClosedSubgroup_intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_centralizer
      (coordinateCocharacter i ν J ζ))).comp_iso (AffineCoordinates.groupSchemeIso G)

theorem isClosedSubgroup_unipotentHom : IsClosedSubgroup (unipotentHom i ν J) :=
  (Corepresented.isClosedSubgroup_intersectionHom
    (fun ζ : indices i ν J => Corepresented.isAffineCutOutBy_unipotent
      (coordinateCocharacter i ν J ζ))).comp_iso (AffineCoordinates.groupSchemeIso G)

/-- The actual morphism from the standard Levi into the standard parabolic. -/
def leviToParabolic : leviScheme i ν J ⟶ parabolicScheme i ν J :=
  (isRepresentedBy_leviHom i ν J).inclusionHom (isRepresentedBy_parabolicHom i ν J)
    (standardLevi_le_standardParabolic i ν J)

/-- The actual morphism from the standard unipotent group into the standard parabolic. -/
def unipotentToParabolic : unipotentScheme i ν J ⟶ parabolicScheme i ν J :=
  (isRepresentedBy_unipotentHom i ν J).inclusionHom (isRepresentedBy_parabolicHom i ν J)
    (standardUnipotent_le_standardParabolic i ν J)

@[simp] theorem leviToParabolic_comp :
    leviToParabolic i ν J ≫ parabolicHom i ν J = leviHom i ν J :=
  SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _

@[simp] theorem unipotentToParabolic_comp :
    unipotentToParabolic i ν J ≫ parabolicHom i ν J = unipotentHom i ν J :=
  SubgroupFunctor.IsRepresentedBy.inclusionHom_comp _ _ _

end Langlands.GroupScheme.Standard
