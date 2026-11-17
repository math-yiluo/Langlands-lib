import Langlands.GroupScheme.RelativeIdentityComponent.ClopenQuotientStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedEtaleSchemeStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothPresentationDiagonal
import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentableTransport
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Clopen subgroup quotients from separated etale algebraic-space schemehood -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothRelationQuotient

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.RelativeIdentityComponent

namespace ClopenQuotient

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)

/-- Compare the chosen Cartesian product with the categorical binary product. -/
def pairIso : G.X ⊗ G.X ≅ G.X ⨯ G.X where
  hom := prod.lift (CartesianMonoidalCategory.fst G.X G.X)
    (CartesianMonoidalCategory.snd G.X G.X)
  inv := CartesianMonoidalCategory.lift prod.fst prod.snd
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by
    apply prod.hom_ext <;> simp

/-- The categorical pairing of the relation endpoints differs from the
actual coset inclusion only by the product comparison isomorphism. -/
theorem pair_eq_inclusion :
    prod.lift (HomogeneousCosetRelation.source i) (HomogeneousCosetRelation.target i) =
      HomogeneousCosetRelation.inclusion i ≫ (pairIso (G := G)).hom := by
  apply prod.hom_ext <;> simp [pairIso]

/-- Smooth clopen subgroups have actual homogeneous quotient schemes,
assuming the general separated etale algebraic-space schemehood theorem. -/
theorem nonempty_quotient_of_separatedEtaleScheme
    (hScheme : SeparatedEtaleSchemeStatement.{u})
    [Smooth G.X.hom] [QuasiCompact G.X.hom]
    [Smooth H.X.hom]
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion i.hom.hom.left)
    (hc : _root_.AlgebraicGeometry.IsClosedImmersion i.hom.hom.left) :
    Nonempty (HomogeneousQuotientFromEmbedding.HomogeneousQuotient i) := by
  let : _root_.AlgebraicGeometry.IsOpenImmersion i.hom.hom.left := hi
  let : _root_.AlgebraicGeometry.IsClosedImmersion i.hom.hom.left := hc
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let Y := schemeYoneda S
  let R := HomogeneousQuotientFromEmbedding.arrowSpace i
  let s := HomogeneousQuotientFromEmbedding.source i
  let t := HomogeneousQuotientFromEmbedding.target i
  let he := HomogeneousQuotientFromEmbedding.isEquivalenceRelation i
  obtain ⟨hF, hd, hker, hqsm, hqsurj, V, a, ha, hs, _⟩ :=
    smoothRelationQuotient S G.X R s t he
      (HomogeneousQuotientFromEmbedding.hasSmoothProjections i inferInstance) inferInstance
  let X : Langlands.AlgebraicGeometry.AlgebraicSpace S :=
    ⟨⟨(quotientSheaf R s t he).obj, hF⟩, hd, V, a, ha, hs⟩
  let q₀ : Y.obj G.X ⟶ X.presheaf := quotientMap R s t he
  have hrel : IsPullback (Y.map (HomogeneousCosetRelation.source i))
      (Y.map (HomogeneousCosetRelation.target i)) q₀ q₀ := hker
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      (prod.lift (HomogeneousCosetRelation.source i)
        (HomogeneousCosetRelation.target i)).left := by
    rw [pair_eq_inclusion i, Over.comp_left]
    let : _root_.AlgebraicGeometry.IsClosedImmersion
        (HomogeneousCosetRelation.inclusion i).left :=
      HomogeneousCosetRelation.inclusion_isClosedImmersion i hc
    have : IsIso (pairIso (G := G)).hom.left :=
      (Over.forget S).map_isIso (pairIso (G := G)).hom
    infer_instance
  have hopen : _root_.AlgebraicGeometry.IsOpenImmersion
      (prod.lift (HomogeneousCosetRelation.source i)
        (HomogeneousCosetRelation.target i)).left := by
    rw [pair_eq_inclusion i, Over.comp_left]
    let : _root_.AlgebraicGeometry.IsOpenImmersion
        (HomogeneousCosetRelation.inclusion i).left :=
      MorphismProperty.of_isPullback
        ((HomogeneousCosetRelation.inclusion_isPullback i).map (Over.forget S)) hi
    have : IsIso (pairIso (G := G)).hom.left :=
      (Over.forget S).map_isIso (pairIso (G := G)).hom
    infer_instance
  have hsep : IsSeparated X :=
    relative_diagonal_of_smooth_presentation
      (@_root_.AlgebraicGeometry.IsClosedImmersion) q₀ hqsm hqsurj
      (HomogeneousCosetRelation.source i) (HomogeneousCosetRelation.target i) hrel hclosed
  have hdopen : IsOpenImmersion (diag X.presheaf) :=
    relative_diagonal_of_smooth_presentation
      (@_root_.AlgebraicGeometry.IsOpenImmersion) q₀ hqsm hqsurj
      (HomogeneousCosetRelation.source i) (HomogeneousCosetRelation.target i) hrel hopen
  have hatlas : HasAtlasProperty (@Etale.{u}) X :=
    etale_structural_atlas_of_smooth_presentation q₀ hqsm hqsurj hdopen
  obtain ⟨Q, ⟨e⟩⟩ := hScheme S X hsep hatlas
  let q : G.X ⟶ Q := Y.preimage (q₀ ≫ e.inv)
  have hq : Y.map q ≫ e.hom = q₀ := by
    dsimp [q]
    rw [Functor.map_preimage]
    simp
  have hsq : IsPullback (𝟙 (Y.obj G.X)) (Y.map q) q₀ e.hom :=
    IsPullback.of_horiz_isIso ⟨by simpa using hq.symm⟩
  let : Smooth q.left := hqsm.projection e.hom (𝟙 _) q hsq
  let : Surjective q.left := hqsurj.projection e.hom (𝟙 _) q hsq
  let rep : X.presheaf.RepresentableBy Q :=
    (Functor.RepresentableBy.equivUliftYonedaIso.{u + 1} X.presheaf Q).symm e
  let : _root_.AlgebraicGeometry.IsSeparated Q.hom :=
    isSeparated_of_representableBy rep hsep
  have hfp : LocallyOfFinitePresentation Q.hom := by
    have : LocallyOfFinitePresentation (q.left ≫ Q.hom) := by
      rw [Over.w q]
      infer_instance
    exact Langlands.AlgebraicGeometry.locallyOfFinitePresentation_of_surjective_flat_comp
      q.left Q.hom
  let : LocallyOfFinitePresentation Q.hom := hfp
  have hqc : QuasiCompact Q.hom := by
    constructor
    intro W hWo hWc
    have hcompact : IsCompact ((q.left ≫ Q.hom) ⁻¹' W) := by
      rw [Over.w q]
      exact QuasiCompact.isCompact_preimage W hWo hWc
    have himage := hcompact.image q.left.continuous
    change IsCompact (q.left '' (q.left ⁻¹' (Q.hom ⁻¹' W))) at himage
    rwa [Set.image_preimage_eq _ q.left.surjective] at himage
  let : QuasiCompact Q.hom := hqc
  have hqcomp : QuasiCompact (q.left ≫ Q.hom) := by
    rw [Over.w q]
    infer_instance
  let : QuasiCompact (q.left ≫ Q.hom) := hqcomp
  have hpair : IsPullback (Y.map (HomogeneousCosetRelation.source i))
      (Y.map (HomogeneousCosetRelation.target i)) (Y.map q) (Y.map q) := by
    apply IsKernelPair.cancel_right_of_mono (f₂ := e.hom)
    rwa [hq]
  have hpair' : IsPullback (HomogeneousCosetRelation.source i)
      (HomogeneousCosetRelation.target i) q q :=
    IsPullback.of_map_of_faithful Y hpair
  exact ⟨⟨Q, q, inferInstance, inferInstance, hqc, inferInstance, inferInstance,
    QuasiCompact.of_comp q.left Q.hom,
    HomogeneousCosetRelation.fibers_of_isPullback i q hpair'⟩⟩

end ClopenQuotient

/-- The unchanged clopen relative identity-component quotient statement
reduces to general separated etale algebraic-space schemehood. -/
theorem clopenQuotient_of_separatedEtaleScheme
    (hScheme : SeparatedEtaleSchemeStatement.{u}) :
    ClopenQuotientStatement.{u} := by
  intro S G _ _ _ H i hi hc
  let : _root_.AlgebraicGeometry.IsOpenImmersion i.hom.hom.left := hi.isOpenImmersion
  let : Smooth H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  exact ClopenQuotient.nonempty_quotient_of_separatedEtaleScheme i hScheme
    hi.isOpenImmersion hc

end Langlands.GroupScheme.RelativeIdentityComponent
