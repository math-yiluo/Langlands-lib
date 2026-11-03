import Langlands.GroupScheme.Rational.SemigroupImageTransport
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport

/-! # Semigroup functoriality from pointed images and coordinate containment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The two independent source obligations used in the image proof of general
semigroup functoriality. Neither is assumed by the semigroup construction. -/
def SemigroupImageTransportPrerequisites : Prop :=
  PointedImageGenerationStatement.{u} ∧
    CoordinateWeights.AugmentationLieContainmentStatement.{u}

/-- General equivariant functoriality follows from pointed-image generation and
coordinate/Lie semigroup containment, with no separability assumption on the map. -/
theorem semigroupFunctoriality_of_imageGeneration_and_containment
    (hGeneration : PointedImageGenerationStatement.{u})
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u}) :
    SemigroupFunctorialityStatement.{u} := by
  intro k _ H G _hH hG hAffH hAffG S hS c b f hf
  let : IsAffineHom H.X.hom := hAffH
  let : IsAffineHom G.X.hom := hAffG
  intro A
  apply SubgroupFunctor.map_le_iff_le_comap.mpr
  apply (semigroupSubgroup_le_iff c A _).mpr
  intro F hF
  obtain ⟨K, i, hi, hic, hKs, hKc⟩ := hF.1
  let : IsAffineHom K.X.hom := hic.isAffineHom
  let : Smooth K.X.hom := hKs
  let d : AutomorphicAction S.toGrp K :=
    c.onRepresentedSubgroup i hi hF.2.1
  have hdi : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ K.X), d.act s x ≫ i.hom.hom = c.act s (x ≫ i.hom.hom) :=
    fun _ s x => c.onRepresentedSubgroup_act_comp i hi hF.2.1 s x
  have htop : (⊤ : SubgroupFunctor K).map i = F := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    rw [← hi.2]
    constructor
    · rintro ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subgroup.mem_top _, rfl⟩
  have hdA : actionWeightSupport d ⊤ ⊆ A := by
    rw [← actionWeightSupport_map i hi.1 d c hdi, htop]
    exact hF.2.2
  have hKint : GeometricallyIntegral K.X.hom :=
    smoothConnectedAffineGeometry.1 k K hKs inferInstance hKc
  have horigin : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X) ≫
      (i ≫ f).hom.hom = 1 := MonObj.one_comp _
  obtain ⟨D, hD⟩ := hGeneration k G hG hAffG K.X inferInstance inferInstance
    hKint 1 (i ≫ f).hom.hom horigin
  have hif : d.toPointwiseSchemeAction.IsEquivariant b.toPointwiseSchemeAction
      (i ≫ f).hom.hom := by
    intro T s x
    change d.act s x ≫ (i.hom.hom ≫ f.hom.hom) =
      b.act s (x ≫ (i.hom.hom ≫ f.hom.hom))
    rw [← Category.assoc, hdi, hf, Category.assoc]
  have hStable : b.IsStable (closedImageEnvelope (i ≫ f).hom.hom) :=
    b.closedImageEnvelope_isStable hS.isAffineHom d.toPointwiseSchemeAction _ hif
  let e : AutomorphicAction S.toGrp D.group := D.action b hStable
  let : IsAffineHom D.group.X.hom := hD.2.1
  let : GeometricallyConnected D.group.X.hom := hD.2.2.1
  have hDc : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  have hfactor : CoordinateWeights.IsEquivariant d e
      (D.factorGroupHom (i ≫ f)).hom.hom := by
    rw [D.factorGroupHom_hom]
    exact D.factor_equivariant b hStable d.toPointwiseSchemeAction hif
  obtain ⟨n, _hn, hDom⟩ := hD.2.2.2
  have heA : actionWeightSupport e ⊤ ⊆ A :=
    actionWeightSupport_subset_of_dominant hContain hKs hD.1 hKc hDc hS d e
      (D.factorGroupHom (i ≫ f)) hfactor
      (D.factorGroupHom_isDominant (i ≫ f) n hDom) A hdA
  have hDtop : (⊤ : SubgroupFunctor D.group).map D.inclusion =
      SubgroupFunctor.range D.inclusion := by
    apply SubgroupFunctor.ext
    intro T
    apply Subgroup.ext
    intro x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, Subgroup.mem_top _, rfl⟩
  have hDgen : IsSemigroupGenerator b A (SubgroupFunctor.range D.inclusion) := by
    refine ⟨⟨D.group, D.inclusion, ⟨D.represents.1, rfl⟩, D.closed, hD.1, hDc⟩, ?_, ?_⟩
    · rw [D.represents.2]
      exact hStable
    · rw [← hDtop, actionWeightSupport_map D.inclusion D.represents.1 e b
        (D.inclusion_equivariant b hStable)]
      exact heA
  intro T x hx
  have hxrange : x ∈ (SubgroupFunctor.range i).carrier T := by
    rw [hi.2]
    exact hx
  obtain ⟨y, rfl⟩ := hxrange
  change T ⟶ K.X at y
  apply generator_le_semigroupSubgroup b A (SubgroupFunctor.range D.inclusion) hDgen T
  refine ⟨y ≫ (D.factorGroupHom (i ≫ f)).hom.hom, ?_⟩
  change (y ≫ (D.factorGroupHom (i ≫ f)).hom.hom) ≫ D.inclusion.hom.hom =
    (y ≫ i.hom.hom) ≫ f.hom.hom
  have hcomp := congrArg (fun a => y ≫ a.hom.hom) (D.factorGroupHom_comp (i ≫ f))
  change y ≫ ((D.factorGroupHom (i ≫ f)).hom.hom ≫ D.inclusion.hom.hom) =
    y ≫ (i.hom.hom ≫ f.hom.hom) at hcomp
  simpa only [Category.assoc] using hcomp

end Langlands.GroupScheme.RelativeRoot
