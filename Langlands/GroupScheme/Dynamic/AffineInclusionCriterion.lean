import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Affine tests detect inclusions from affine represented subgroup functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H : GroupScheme S}

/-- The spectrum of the global coordinate ring of an affine group, as a test over its base. -/
def affineUniversalTest (H : GroupScheme S) [IsAffine H.X.left] : Over S :=
  Over.mk (H.X.left.isoSpec.inv ≫ H.X.hom)

/-- The universal point on the affine coordinate spectrum. -/
def affineUniversalPoint (H : GroupScheme S) [IsAffine H.X.left] :
    affineUniversalTest H ⟶ H.X :=
  Over.homMk H.X.left.isoSpec.inv rfl

/-- An affine group's image lies in a subgroup functor if this holds on every spectrum test. -/
theorem range_le_of_affine_tests (i : H ⟶ G) [IsAffine H.X.left]
    (F : SubgroupFunctor G)
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S)
      (x : Over.mk f ⟶ G.X), x ∈ (range i).carrier (Over.mk f) →
        x ∈ F.carrier (Over.mk f)) :
    range i ≤ F := by
  have huniv : affineUniversalPoint H ≫ i.hom.hom ∈
      F.carrier (affineUniversalTest H) :=
    h _ _ _ (mem_range.mpr ⟨affineUniversalPoint H, rfl⟩)
  let a : H.X ⟶ affineUniversalTest H :=
    Over.homMk H.X.left.isoSpec.hom (by simp only [affineUniversalTest,
      Over.mk_hom, Iso.hom_inv_id_assoc])
  have ha : a ≫ (affineUniversalPoint H ≫ i.hom.hom) = i.hom.hom := by
    apply Over.OverMorphism.ext
    change H.X.left.isoSpec.hom ≫ (H.X.left.isoSpec.inv ≫ i.hom.hom.left) = _
    simp only [Iso.hom_inv_id_assoc]
  have hi : i.hom.hom ∈ F.carrier H.X := by
    have hh := F.comp_mem a huniv
    rwa [ha] at hh
  intro T x hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  exact F.comp_mem y hi

/-- Inclusions from an affine represented functor are detected on all affine spectrum tests. -/
theorem le_of_isRepresentedBy_of_affine_tests {E F : SubgroupFunctor G}
    (i : H ⟶ G) [IsAffine H.X.left] (hi : E.IsRepresentedBy i)
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S)
      (x : Over.mk f ⟶ G.X), x ∈ E.carrier (Over.mk f) →
        x ∈ F.carrier (Over.mk f)) :
    E ≤ F := by
  rw [← hi.2]
  apply range_le_of_affine_tests
  simpa only [hi.2] using h

/-- A closed represented subgroup of an affine group has its inclusions detected on spectra. -/
theorem le_of_closed_isRepresentedBy_of_affine_tests {E F : SubgroupFunctor G}
    [IsAffine G.X.left] (i : H ⟶ G) (hi : E.IsRepresentedBy i)
    (hic : IsClosedSubgroup i)
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S)
      (x : Over.mk f ⟶ G.X), x ∈ E.carrier (Over.mk f) →
        x ∈ F.carrier (Over.mk f)) :
    E ≤ F := by
  let : IsClosedImmersion i.hom.hom.left := hic
  let : IsAffine H.X.left := isAffine_of_isAffineHom i.hom.hom.left
  exact le_of_isRepresentedBy_of_affine_tests i hi h

end SubgroupFunctor

namespace Dynamic

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- A dynamic parabolic's inclusion is detected on arbitrary affine spectrum tests. -/
theorem parabolic_le_of_affine_tests (χ : (Gm (Spec R)).toGrp ⟶ G)
    (F : SubgroupFunctor G)
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ Spec R)
      (x : Over.mk f ⟶ G.X), x ∈ (parabolic χ).carrier (Over.mk f) →
        x ∈ F.carrier (Over.mk f)) :
    parabolic χ ≤ F :=
  SubgroupFunctor.le_of_closed_isRepresentedBy_of_affine_tests
    (Affine.parabolicHom χ) (Affine.isRepresentedBy_parabolicHom χ)
    (Affine.isClosedSubgroup_parabolicHom χ) h

/-- A dynamic centralizer's inclusion is detected on arbitrary affine spectrum tests. -/
theorem centralizer_le_of_affine_tests (χ : (Gm (Spec R)).toGrp ⟶ G)
    (F : SubgroupFunctor G)
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ Spec R)
      (x : Over.mk f ⟶ G.X), x ∈ (centralizer χ).carrier (Over.mk f) →
        x ∈ F.carrier (Over.mk f)) :
    centralizer χ ≤ F :=
  SubgroupFunctor.le_of_closed_isRepresentedBy_of_affine_tests
    (Affine.centralizerHom χ) (Affine.isRepresentedBy_centralizerHom χ)
    (Affine.isClosedSubgroup_centralizerHom χ) h

/-- A dynamic unipotent subgroup's inclusion is detected on arbitrary affine spectrum tests. -/
theorem unipotent_le_of_affine_tests (χ : (Gm (Spec R)).toGrp ⟶ G)
    (F : SubgroupFunctor G)
    (h : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ Spec R)
      (x : Over.mk f ⟶ G.X), x ∈ (unipotent χ).carrier (Over.mk f) →
        x ∈ F.carrier (Over.mk f)) :
    unipotent χ ≤ F :=
  SubgroupFunctor.le_of_closed_isRepresentedBy_of_affine_tests
    (Affine.unipotentHom χ) (Affine.isRepresentedBy_unipotentHom χ)
    (Affine.isClosedSubgroup_unipotentHom χ) h

end Dynamic

end Langlands.GroupScheme
