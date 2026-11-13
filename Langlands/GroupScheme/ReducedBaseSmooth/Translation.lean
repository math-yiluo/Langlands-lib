import Langlands.GroupScheme.RelativeIdentityComponent.FieldProductCover
import Langlands.GroupScheme.RelativeIdentityComponent.ProductImage
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation

/-! # Smoothness spreads from the unit section by translation -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ReducedBaseSmooth

open Langlands.GroupScheme.RelativeIdentityComponent
open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

section Product

variable {S : Scheme.{u}} (H : GroupScheme S) {P : Over S} (i : P ⟶ H.X)

/-- The product of two test points is a left shear followed by the second projection. -/
theorem tensorHom_comp_mul_eq :
    (i ⊗ₘ i) ≫ μ[H.X] =
      (𝟙 P ⊗ₘ i) ≫ (DominantHomFlat.shearLeft i).hom ≫ snd P H.X := by
  rw [DominantHomFlat.shearLeft_hom_snd, MonObj.comp_mul]
  simp only [tensorHom_fst_assoc, tensorHom_snd, Category.id_comp, Hom.mul_def]
  rfl

/-- If the test scheme is smooth over the base and maps by an open immersion, the product
map is smooth. -/
theorem smooth_tensorHom_comp_mul [Smooth P.hom] [IsOpenImmersion i.left] :
    Smooth ((i ⊗ₘ i) ≫ μ[H.X]).left := by
  rw [tensorHom_comp_mul_eq, Over.comp_left, Over.comp_left, Over.snd_left]
  have : IsOpenImmersion (𝟙 P ⊗ₘ i).left := by
    rw [Over.tensorHom_left]
    exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      (Over.w _).symm (Over.w _).symm
  have : IsIso (DominantHomFlat.shearLeft i).hom.left :=
    (Over.forget S).map_isIso (DominantHomFlat.shearLeft i).hom
  infer_instance

end Product

section Surjective

variable {S : Scheme.{u}} (H : GroupScheme S) {P : Over S} (i : P ⟶ H.X)
  [IsOpenImmersion i.left]

/-- If an open subscheme contains the unit section and every residue fibre is smooth and
connected, products of two of its points exhaust the group. -/
theorem range_tensorHom_comp_mul_eq_univ
    (hsm : ∀ s : S, Smooth (H.X.hom.fiberToSpecResidueField s))
    (hconn : ∀ s : S, ConnectedSpace (H.X.hom.fiber s))
    (he : Set.range η[H.X].left ⊆ Set.range i.left) :
    Set.range ((i ⊗ₘ i) ≫ μ[H.X]).left = Set.univ := by
  refine Set.eq_univ_of_forall fun h => ?_
  let s := H.X.hom h
  let K := S.residueField s
  let b : Spec (CommRingCat.of K) ⟶ S := S.fromSpecResidueField s
  let F := Over.pullback b
  let H' := (GroupScheme.baseChange b).obj H
  let i' := F.map i
  have : Smooth H'.X.hom := hsm s
  have : ConnectedSpace H'.X.left := hconn s
  have : IsOpenImmersion i'.left :=
    MorphismProperty.of_isPullback (overPullback_isPullback b i).flip
      (inferInstance : IsOpenImmersion i.left)
  let e : 𝟙_ (Over S) ⟶ P := liftOver i η[H.X] he
  have hei : e ≫ i = η[H.X] := liftOver_fac _ _ _
  let eP' : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ F.obj P :=
    Functor.LaxMonoidal.ε F ≫ F.map e
  have hei' : eP' ≫ i' = η[H'.X] := by
    change (Functor.LaxMonoidal.ε F ≫ F.map e) ≫ F.map i = _
    rw [Category.assoc, ← F.map_comp, hei]
    rfl
  have heunit' : IdentityComponent.identityPoint H' ∈ Set.range i'.left := by
    refine ⟨eP'.left (IsLocalRing.closedPoint K), ?_⟩
    exact congrArg (fun f => f.left (IsLocalRing.closedPoint K)) hei'
  have hcover := identitySet_subset_range_fieldOpenProduct H' i' heunit'
  have hall : IdentityComponent.identitySet H' = Set.univ :=
    PreconnectedSpace.connectedComponent_eq_univ _
  have hmem : H.X.hom.asFiber h ∈ Set.range (baseChangedProduct H b i).left :=
    hcover (hall ▸ Set.mem_univ (H.X.hom.asFiber h))
  rw [range_baseChangedProduct] at hmem
  have hpt : pullback.fst H.X.hom b (H.X.hom.asFiber h) = h := H.X.hom.fiberι_asFiber h
  exact hpt ▸ hmem

end Surjective

section Descent

/-- Smoothness descends along a smooth surjection onto a locally Noetherian scheme. -/
theorem smooth_of_smooth_comp_of_surjective {X Y Z : Scheme.{u}} (p : X ⟶ Y) (g : Y ⟶ Z)
    [Smooth p] [Surjective p] [Smooth (p ≫ g)] [LocallyOfFinitePresentation g]
    [IsLocallyNoetherian Y] : Smooth g := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := p.surjective y
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let V : Y.Opens := ⟨p '' W, p.isOpenMap _ W.2⟩
  have hWV : W ≤ p ⁻¹ᵁ V := fun w hw => ⟨w, hw, rfl⟩
  let q := p.resLE V W hWV
  have : IsAffine W := hW
  have : Smooth q := IsZariskiLocalAtSource.resLE hWV inferInstance
  have : Surjective q := by
    constructor
    rintro ⟨_, w, hw, rfl⟩
    refine ⟨⟨w, hw⟩, V.ι.isOpenEmbedding.injective ?_⟩
    change (q ≫ V.ι) ⟨w, hw⟩ = _
    rw [Scheme.Hom.resLE_comp_ι]
    rfl
  have : QuasiCompact q := quasiCompact_of_compactSpace q
  have : Smooth (q ≫ V.ι ≫ g) := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
    infer_instance
  have : Smooth (V.ι ≫ g) :=
    Smooth.of_comp_of_smooth_of_surjective_of_locallyOfFinitePresentation q (V.ι ≫ g)
  have hV : V.ι ⁻¹ᵁ g.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq]
    exact (V.ι ≫ g).smoothLocus_eq_top
  have hxV : (⟨p x, x, hxW, rfl⟩ : V) ∈ V.ι ⁻¹ᵁ g.smoothLocus := hV ▸ trivial
  exact hxV

end Descent

section Main

variable {S : Scheme.{u}} (H : GroupScheme S) [IsLocallyNoetherian S]
  [LocallyOfFiniteType H.X.hom]

/-- The smooth locus of the structure morphism, as a scheme over the base. -/
abbrev smoothLocusOver : Over S := Over.mk (H.X.hom.smoothLocus.ι ≫ H.X.hom)

/-- The inclusion of the smooth locus. -/
abbrev smoothLocusInclusion : smoothLocusOver H ⟶ H.X :=
  Over.homMk H.X.hom.smoothLocus.ι

instance : IsOpenImmersion (smoothLocusInclusion H).left :=
  inferInstanceAs (IsOpenImmersion H.X.hom.smoothLocus.ι)

instance : Smooth (smoothLocusOver H).hom := by
  change Smooth (H.X.hom.smoothLocus.ι ≫ H.X.hom)
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
  exact Scheme.Opens.ι_preimage_self _

/-- If every residue fibre is smooth and connected and the unit section lies in the smooth
locus, then the group scheme is smooth. -/
theorem smooth_of_range_unit_subset_smoothLocus
    (hsm : ∀ s : S, Smooth (H.X.hom.fiberToSpecResidueField s))
    (hconn : ∀ s : S, ConnectedSpace (H.X.hom.fiber s))
    (he : Set.range η[H.X].left ⊆ H.X.hom.smoothLocus) :
    Smooth H.X.hom := by
  let i := smoothLocusInclusion H
  let P := smoothLocusOver H
  have : IsLocallyNoetherian H.X.left := LocallyOfFiniteType.isLocallyNoetherian H.X.hom
  have : Smooth ((i ⊗ₘ i) ≫ μ[H.X]).left := smooth_tensorHom_comp_mul H i
  have : Surjective ((i ⊗ₘ i) ≫ μ[H.X]).left := by
    rw [surjective_iff, ← Set.range_eq_univ]
    apply range_tensorHom_comp_mul_eq_univ H i hsm hconn
    change Set.range η[H.X].left ⊆ Set.range H.X.hom.smoothLocus.ι
    rw [Scheme.Opens.range_ι]
    exact he
  have : Smooth (((i ⊗ₘ i) ≫ μ[H.X]).left ≫ H.X.hom) := by
    rw [Over.w ((i ⊗ₘ i) ≫ μ[H.X]), Over.tensorObj_hom]
    infer_instance
  exact smooth_of_smooth_comp_of_surjective ((i ⊗ₘ i) ≫ μ[H.X]).left H.X.hom

end Main

end Langlands.GroupScheme.ReducedBaseSmooth
