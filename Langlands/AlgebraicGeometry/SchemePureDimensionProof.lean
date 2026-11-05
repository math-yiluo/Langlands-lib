import Langlands.AlgebraicGeometry.SchemePureDimensionStatement
import Langlands.AlgebraicGeometry.SchemeComponentDimension
import Langlands.AlgebraicGeometry.AffineSchemePureDimensionProof
import Langlands.AlgebraicGeometry.SchemeFiberBaseChange

/-! # Pure-dimension locality and arbitrary locally finite-type base change -/

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

/-- Restrict a pure-dimensional scheme to an actual open, using the dimension
comparison on the ambient components. -/
theorem HasPureDimension.open_of_componentOpenDimensionInvariant
    {X : Scheme.{u}} {d : ℕ} (h : HasPureDimension X d)
    (hcomp : ComponentOpenDimensionInvariant X) (U : X.Opens) :
    HasPureDimension U.toScheme d := by
  intro Z hZ
  change Z ∈ irreducibleComponents (U : Set X) at hZ
  let T : Set X := closure ((Subtype.val : U → X) '' Z)
  have hT : T ∈ irreducibleComponents X :=
    closure_image_mem_irreducibleComponents_open U Z hZ
  let V := openInSubspace T U
  let e : V ≃ₜ Z := (subtypePreimageCommHomeomorph T (U : Set X)).trans
    (Homeomorph.setCongr (preimage_closure_image_irreducibleComponent_open U Z hZ))
  have hV : (V : Set T).Nonempty := by
    obtain ⟨x, hx⟩ := hZ.1.nonempty
    let y := e.symm ⟨x, hx⟩
    exact ⟨y.1, y.2⟩
  exact (e.isHomeomorph.topologicalKrullDim_eq _).symm.trans
    ((hcomp T hT V hV).trans (h T hT))

/-- Pure dimension is local on open covers whenever every ambient component
has dimension invariant on its nonempty opens. -/
theorem hasPureDimension_iff_openCover_of_componentOpenDimensionInvariant
    {X : Scheme.{u}} (hcomp : ComponentOpenDimensionInvariant X)
    {ι : Type v} (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i) (d : ℕ) :
    HasPureDimension X d ↔ ∀ i, HasPureDimension (U i).toScheme d := by
  constructor
  · intro h i
    exact h.open_of_componentOpenDimensionInvariant hcomp (U i)
  · intro h Z hZ
    obtain ⟨x, hxZ⟩ := hZ.1.nonempty
    obtain ⟨i, hxi⟩ := hcover x
    let V := openInSubspace Z (U i)
    have hV : (V : Set Z).Nonempty := ⟨⟨x, hxZ⟩, hxi⟩
    have hmeet : (Z ∩ range (Subtype.val : U i → X)).Nonempty :=
      ⟨x, hxZ, ⟨⟨x, hxi⟩, rfl⟩⟩
    have hpre := preimage_mem_irreducibleComponents hZ (U i).isOpenEmbedding' hmeet
    exact (hcomp Z hZ V hV).symm.trans
      (((subtypePreimageCommHomeomorph Z (U i : Set X)).isHomeomorph.topologicalKrullDim_eq _).trans
        (h i _ hpre))

/-- No affine, compactness, or separation hypothesis is needed. -/
theorem hasPureDimension_iff_openCover_locallyOfFiniteType
    (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    {ι : Type v} (U : ι → X.Opens) (hcover : ∀ x : X, ∃ i, x ∈ U i) (d : ℕ) :
    HasPureDimension X d ↔ ∀ i, HasPureDimension (U i).toScheme d :=
  hasPureDimension_iff_openCover_of_componentOpenDimensionInvariant
    (componentOpenDimensionInvariant_locallyOfFiniteType k X f) U hcover d

/-- Affine opens and their actual inverse images reduce arbitrary locally
finite-type schemes to the affine field-extension comparison. -/
theorem hasPureDimension_fieldExtension_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] (d : ℕ) :
    HasPureDimension X d ↔
      HasPureDimension (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) d := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pr := pullback.fst f g
  have hcover : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 := by
    intro x
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨⟨U, hU⟩, hxU⟩
  have hX := hasPureDimension_iff_openCover_locallyOfFiniteType k X f
    (fun U : X.affineOpens => U.1) hcover d
  have hP := hasPureDimension_iff_openCover_locallyOfFiniteType K (pullback f g)
    (pullback.snd f g) (fun U : X.affineOpens => pr ⁻¹ᵁ U.1)
    (fun x => hcover (pr x)) d
  refine hX.trans ((forall_congr' (fun U => ?_)).trans hP.symm)
  let e : (pr ⁻¹ᵁ U.1).toScheme ≅ pullback (U.1.ι ≫ f) g :=
    ((isPullback_morphismRestrict pr U.1).paste_vert
      (IsPullback.of_hasPullback f g)).isoPullback
  exact (hasPureDimension_affine_fieldExtension_iff k K U.1.toScheme (U.1.ι ≫ f) d).trans
    (hasPureDimension_iff_of_iso e).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Actual residue-field scalar extension compares the fibres of any
cartesian base change of a locally finite-type morphism. -/
theorem hasPureDimension_locallyFiniteType_fiberBaseChange_iff
    {P X Y Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} [LocallyOfFiniteType f]
    (h : IsPullback a b f g) (y : Y) (d : ℕ) :
    HasPureDimension (b.fiber y) d ↔ HasPureDimension (f.fiber (g y)) d := by
  let : Algebra (Z.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (g y)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  exact (hasPureDimension_fiberBaseChange_iff h y d).trans
    (hasPureDimension_fieldExtension_iff (Z.residueField (g y))
      (Y.residueField y) (f.fiber (g y)) (f.fiberToSpecResidueField (g y)) d).symm

/-- The exact grouped target for arbitrary locally finite-type schemes. -/
theorem schemePureDimensionComparisons :
    SchemePureDimensionComparisons.{u,v} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k _ X f _ ι U hcover d
    exact hasPureDimension_iff_openCover_locallyOfFiniteType k X f U hcover d
  · intro k K _ _ _ X f _ d
    exact hasPureDimension_fieldExtension_iff k K X f d
  · intro P X Y Z a b f g _ h y d
    exact hasPureDimension_locallyFiniteType_fiberBaseChange_iff h y d
  · intro P X Y Z a b f g _ h d
    have preserve : HasPureDimensionFibers d f → HasPureDimensionFibers d b :=
      fun hf y => (hasPureDimension_locallyFiniteType_fiberBaseChange_iff h y d).mpr (hf (g y))
    refine ⟨preserve, fun hg => ⟨?_, preserve⟩⟩
    intro hb z
    obtain ⟨y, rfl⟩ := hg.surj z
    exact (hasPureDimension_locallyFiniteType_fiberBaseChange_iff h y d).mp (hb y)

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
