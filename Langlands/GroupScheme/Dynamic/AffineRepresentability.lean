import Langlands.GroupScheme.AffineCorepresented
import Langlands.GroupScheme.Dynamic.Representability
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Closed dynamic subgroup schemes of arbitrary affine groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {K H G : GroupScheme S} {F : SubgroupFunctor H} {i : K ⟶ H}

/-- Transport a represented subgroup along an isomorphism of the ambient group. -/
theorem IsRepresentedBy.comp_iso (hi : F.IsRepresentedBy i) (e : H ≅ G) :
    (F.comap e.inv).IsRepresentedBy (i ≫ e.hom) := by
  have : Mono i.hom.hom := hi.1
  have : IsIso e.hom.hom.hom :=
    (inferInstance : IsIso ((Grp.forget _).mapIso e).hom)
  have eh : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 H.X :=
    congrArg (fun f : H ⟶ H => f.hom.hom) e.hom_inv_id
  have ei : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G.X :=
    congrArg (fun f : G ⟶ G => f.hom.hom) e.inv_hom_id
  refine ⟨?_, ?_⟩
  · change Mono (i.hom.hom ≫ e.hom.hom.hom)
    infer_instance
  · refine SubgroupFunctor.ext fun T => Subgroup.ext fun x => ?_
    rw [mem_comap, ← hi.2, mem_range, mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨y, ?_⟩
      change y ≫ i.hom.hom = (y ≫ (i.hom.hom ≫ e.hom.hom.hom)) ≫ e.inv.hom.hom
      simp only [Category.assoc, eh, Category.comp_id]
    · rintro ⟨y, hy⟩
      refine ⟨y, ?_⟩
      change y ≫ (i.hom.hom ≫ e.hom.hom.hom) = x
      rw [← Category.assoc, hy, Category.assoc, ei, Category.comp_id]

end SubgroupFunctor

namespace Dynamic.Affine

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (χ : (Gm (Spec R)).toGrp ⟶ G)

/-- The cocharacter in the chosen corepresented coordinates of an affine group. -/
def cocharacter : (Gm (Spec R)).toGrp ⟶
    Corepresented.groupScheme (AffineCoordinates.functor G) (AffineCoordinates.corepresentation G) :=
  χ ≫ (AffineCoordinates.groupSchemeIso G).inv

/-- A closed group scheme representing the actual orbit-extension functor `P_G(χ)`. -/
abbrev parabolicScheme : GroupScheme (Spec R) :=
  Corepresented.parabolicScheme (cocharacter χ)

/-- A closed group scheme representing the actual centralizer functor `Z_G(χ)`. -/
abbrev centralizerScheme : GroupScheme (Spec R) :=
  Corepresented.centralizerScheme (cocharacter χ)

/-- A closed group scheme representing the actual orbit-contraction functor `U_G(χ)`. -/
abbrev unipotentScheme : GroupScheme (Spec R) :=
  Corepresented.unipotentScheme (cocharacter χ)

/-- The inclusion of the dynamic parabolic into the original affine group. -/
def parabolicHom : parabolicScheme χ ⟶ G :=
  Corepresented.parabolicHom (cocharacter χ) ≫ (AffineCoordinates.groupSchemeIso G).hom

/-- The inclusion of the dynamic centralizer into the original affine group. -/
def centralizerHom : centralizerScheme χ ⟶ G :=
  Corepresented.centralizerHom (cocharacter χ) ≫ (AffineCoordinates.groupSchemeIso G).hom

/-- The inclusion of the dynamic unipotent subgroup into the original affine group. -/
def unipotentHom : unipotentScheme χ ⟶ G :=
  Corepresented.unipotentHom (cocharacter χ) ≫ (AffineCoordinates.groupSchemeIso G).hom

/-- The chosen parabolic represents `P_G(χ)` on every test scheme. -/
theorem isRepresentedBy_parabolicHom : (parabolic χ).IsRepresentedBy (parabolicHom χ) := by
  rw [parabolic_eq_comap_of_iso χ (AffineCoordinates.groupSchemeIso G).symm]
  exact (Corepresented.isRepresentedBy_parabolicHom (cocharacter χ)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

/-- The chosen centralizer represents `Z_G(χ)` on every test scheme. -/
theorem isRepresentedBy_centralizerHom : (centralizer χ).IsRepresentedBy (centralizerHom χ) := by
  rw [centralizer_eq_comap_of_iso χ (AffineCoordinates.groupSchemeIso G).symm]
  exact (Corepresented.isRepresentedBy_centralizerHom (cocharacter χ)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

/-- The chosen unipotent subgroup represents `U_G(χ)` on every test scheme. -/
theorem isRepresentedBy_unipotentHom : (unipotent χ).IsRepresentedBy (unipotentHom χ) := by
  rw [unipotent_eq_comap_of_iso χ (AffineCoordinates.groupSchemeIso G).symm]
  exact (Corepresented.isRepresentedBy_unipotentHom (cocharacter χ)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

theorem isClosedSubgroup_parabolicHom : IsClosedSubgroup (parabolicHom χ) :=
  (Corepresented.isClosedSubgroup_parabolicHom (cocharacter χ)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

theorem isClosedSubgroup_centralizerHom : IsClosedSubgroup (centralizerHom χ) :=
  (Corepresented.isClosedSubgroup_centralizerHom (cocharacter χ)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

theorem isClosedSubgroup_unipotentHom : IsClosedSubgroup (unipotentHom χ) :=
  (Corepresented.isClosedSubgroup_unipotentHom (cocharacter χ)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

end Dynamic.Affine

end Langlands.GroupScheme
