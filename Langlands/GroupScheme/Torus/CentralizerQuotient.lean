import Langlands.GroupScheme.HomScheme.ConjugationMap
import Langlands.GroupScheme.HomScheme.SmoothRelativeSourceRepresentability
import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.GroupScheme.OpenSubgroupQuotientEtale

/-! # Smooth scheme quotients by torus centralizers -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace TorusCentralizerQuotient
open HomScheme HomogeneousQuotientFromEmbedding

variable {S : Scheme.{u}} {A : CommGroupScheme S} {G N Z : GroupScheme S}

/-- Conjugation restricted to a supplied group detects exactly the represented
preimage of the centralizer. -/
theorem conjugationMap_fibers (t : A.toGrp ⟶ G) (n : N ⟶ G)
    (c : Z ⟶ N) (hc : ((torusCentralizer t).comap n).IsRepresentedBy c)
    {Y : Over S} (i : RelativeHom A.toGrp G Y) (hi : IsUniversal i)
    (U : Over S) (g h : U ⟶ N.X) :
    g ≫ conjugationParameter t i hi n.hom.hom =
        h ≫ conjugationParameter t i hi n.hom.hom ↔
      g⁻¹ * h ∈ (SubgroupFunctor.range c).carrier U := by
  rw [conjugationParameter_comp, conjugationParameter_comp,
    conjugationParameter_eq_iff, hc.2]
  change (g ≫ n.hom.hom)⁻¹ * (h ≫ n.hom.hom) ∈ (torusCentralizer t).carrier U ↔
    (g⁻¹ * h) ≫ n.hom.hom ∈ (torusCentralizer t).carrier U
  rw [MonObj.mul_comp, GrpObj.inv_comp]

/-- A represented smooth preimage of a relative torus centralizer has an
actual smooth-surjective scheme quotient with all-test coset fibers. -/
theorem exists_smooth_quotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth N.X.hom]
    (t : A.toGrp ⟶ G) (hA : RelativeTorus.IsTorus A.toGrp) (n : N ⟶ G)
    (c : Z ⟶ N) (hc : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (hZ : Smooth Z.X.hom) :
    ∃ (Q : Over S) (q : N.X ⟶ Q), Smooth q.left ∧ Surjective q.left ∧
      ∀ (U : Over S) (g h : U ⟶ N.X),
        g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range c).carrier U := by
  let : Mono c.hom.hom := hc.1
  obtain ⟨Y, i, hi, _⟩ := exists_smooth_universal_of_relativeTorus (G := G) hA
  let r : N.X ⟶ Y := conjugationParameter t i hi n.hom.hom
  have hker : ∀ (U : Over S) (g h : U ⟶ N.X),
      g ≫ r = h ≫ r ↔ relation (arrowSpace c) (source c) (target c) U ⟨g⟩ ⟨h⟩ := by
    intro U g h
    exact (conjugationMap_fibers t n c hc i hi U g h).trans (relation_iff c U g h).symm
  let D := schemeQuotientOfMapKernel (isEquivalenceRelation c)
    (hasSmoothProjections c hZ) (inferInstance : LocallyOfFiniteType N.X.hom) Y r hker
  exact ⟨D.scheme, D.projection, D.smooth_projection, D.surjective_projection,
    fun U g h => (D.fibers U g h).trans (relation_iff c U g h)⟩

/-- A quotient with exact coset fibers by a closed subgroup is separated. -/
theorem separated_of_closed_subgroup_quotient
    (c : Z ⟶ N) [Mono c.hom.hom] (hc : IsClosedSubgroup c)
    {Q : Over S} (q : N.X ⟶ Q) [Smooth q.left] [Surjective q.left]
    (hfib : ∀ (U : Over S) (g h : U ⟶ N.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range c).carrier U) :
    IsSeparated Q.hom := by
  have hrel : IsClosedImmersion (HomogeneousCosetRelation.inclusion c).left :=
    HomogeneousCosetRelation.inclusion_isClosedImmersion c hc
  have hcover :
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        (q ⊗ₘ q).left := by
    exact MorphismProperty.pullbackMap
      (P := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
      (Over.w q).symm (Over.w q).symm
  have hdiag : IsClosedImmersion
      (CategoryTheory.CartesianMonoidalCategory.lift (𝟙 Q) (𝟙 Q)).left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsClosedImmersion) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      ((HomogeneousCosetRelation.isPullback_diagonal_of_fibers c q hfib).map
        (Over.forget S)).flip hcover hrel
  exact ⟨hdiag⟩

/-- Quasi-compactness of a structure map descends along a surjective map. -/
theorem quasiCompact_of_surjective_comp {X Y B : Scheme.{u}} (q : X ⟶ Y) (f : Y ⟶ B)
    [Surjective q] [QuasiCompact (q ≫ f)] : QuasiCompact f := by
  constructor
  intro U hU hcU
  have hc := QuasiCompact.isCompact_preimage (f := q ≫ f) U hU hcU
  have he : q '' ((q ≫ f) ⁻¹' U) = f ⁻¹' U := by
    change q '' (q ⁻¹' (f ⁻¹' U)) = _
    exact Set.image_preimage_eq _ q.surjective
  rw [← he]
  exact hc.image q.continuous

/-- Every smooth quotient constructed above has the separated and
quasi-compact geometry of a homogeneous quotient if the subgroup is closed
and the source relatively affine. -/
theorem exists_homogeneous_quotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth N.X.hom] [IsAffineHom N.X.hom]
    (t : A.toGrp ⟶ G) (hA : RelativeTorus.IsTorus A.toGrp) (n : N ⟶ G)
    (c : Z ⟶ N) (hc : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (hcclosed : IsClosedSubgroup c) (hZ : Smooth Z.X.hom) :
    Nonempty (HomogeneousQuotient c) := by
  let : Mono c.hom.hom := hc.1
  obtain ⟨Q, q, hsm, hsurj, hfib⟩ := exists_smooth_quotient t hA n c hc hZ
  let := hsm
  let := hsurj
  let hsep := separated_of_closed_subgroup_quotient c hcclosed q hfib
  let : IsSeparated Q.hom := hsep
  have hqccomp : QuasiCompact (q.left ≫ Q.hom) := by rw [Over.w q]; infer_instance
  let := hqccomp
  have hqc : QuasiCompact Q.hom := quasiCompact_of_surjective_comp q.left Q.hom
  have hfp : LocallyOfFinitePresentation Q.hom := by
    have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by rw [Over.w q]; infer_instance
    exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.left Q.hom
  let := hfp
  exact ⟨⟨Q, q, hsep, inferInstance, hqc, hsm, hsurj,
    QuasiCompact.of_comp q.left Q.hom, hfib⟩⟩

/-- Choose the actual smooth separated quasi-compact coset quotient. -/
def homogeneousQuotient
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [Smooth N.X.hom] [IsAffineHom N.X.hom]
    (t : A.toGrp ⟶ G) (hA : RelativeTorus.IsTorus A.toGrp) (n : N ⟶ G)
    (c : Z ⟶ N) (hc : ((torusCentralizer t).comap n).IsRepresentedBy c)
    (hcclosed : IsClosedSubgroup c) (hZ : Smooth Z.X.hom) : HomogeneousQuotient c :=
  Classical.choice (exists_homogeneous_quotient t hA n c hc hcclosed hZ)

end TorusCentralizerQuotient
end Langlands.GroupScheme
