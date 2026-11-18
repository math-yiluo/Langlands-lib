import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent
import Langlands.AlgebraicGeometry.FiberMapEqualityDescent
import Langlands.AlgebraicGeometry.Picard.NoetherianAmpleFibreCover
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback

/-! # Affine residue fibres and finitely generated coefficient models -/

noncomputable section

universe u

open Set Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.SchemeFiberGeometry

variable {X Y : Scheme.{u}}

/-- The locus where the actual residue-field fibre is affine. -/
def affineFiberLocus (f : X ⟶ Y) : Set Y :=
  {y | IsAffineHom (f.fiberToSpecResidueField y)}

/-- Affineness at a point over a changed base is equivalent to affineness at
its image, by faithfully flat descent over the actual residue-field map. -/
theorem affineFiberLocus_baseChange {P Z : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) :
    affineFiberLocus b = g ⁻¹' affineFiberLocus f := by
  ext y
  change IsAffineHom (b.fiberToSpecResidueField y) ↔
    IsAffineHom (f.fiberToSpecResidueField (g y))
  let k := g.residueFieldMap y
  let : Algebra (Z.residueField (g y)) (Y.residueField y) := k.hom.toAlgebra
  have hk : Flat (Spec.map k) := by
    apply Flat.SpecMap_iff.mpr
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  constructor
  · intro hy
    exact MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (fiberBaseChangeSquare h y).flip
      ⟨⟨surjective_spec_residueFieldMap g y, hk⟩, inferInstance⟩ hy
  · exact MorphismProperty.of_isPullback (fiberBaseChangeSquare h y)

/-- Each point of the affine-fibre locus over a noetherian affine base has
a constructible neighbourhood contained in that locus. -/
theorem exists_isConstructible_subset_affineFiberLocus
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (y : Spec (CommRingCat.of R)) (hy : y ∈ affineFiberLocus f) :
    ∃ s : Set (Spec (CommRingCat.of R)), IsConstructible s ∧
      y ∈ s ∧ s ⊆ affineFiberLocus f := by
  let K := (Spec (CommRingCat.of R)).residueField y
  let p := (Spec (CommRingCat.of R)).fromSpecResidueField y
  let : Algebra R K := (Spec.preimage p).hom.toAlgebra
  have hp : Spec.map (CommRingCat.ofHom (algebraMap R K)) = p := Spec.map_preimage p
  have hK : IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
    rw [hp]
    exact @isAffine_of_isAffineHom _ _ (f.fiberToSpecResidueField y) hy inferInstance
  obtain ⟨B, hB, _, hAff⟩ :=
    exists_fg_subalgebra_isAffine_pullback_of_isAffine_pullback f (∅ : Finset K)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let q := Spec.map (CommRingCat.ofHom (algebraMap B K))
  have hq : q ≫ g = p := by
    dsimp only [q, g]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq, hp]
  have hfin : Algebra.FiniteType R B := (Subalgebra.fg_iff_finiteType B).mp hB
  have hfp : LocallyOfFinitePresentation g := (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.FinitePresentation.of_finiteType.mp (RingHom.finiteType_algebraMap.mpr hfin))
  refine ⟨range g, ?_, ?_, ?_⟩
  · rw [← image_univ]
    exact g.isConstructible_image .univ
  · exact ⟨q (IsLocalRing.closedPoint K),
      (Scheme.Hom.comp_apply q g _).symm.trans (by rw [hq]; exact Scheme.fromSpecResidueField_apply _ _)⟩
  · rintro _ ⟨t, rfl⟩
    have ht : t ∈ affineFiberLocus (pullback.snd f g) := by
      change IsAffineHom (pullback.snd (pullback.snd f g)
        ((Spec (CommRingCat.of B)).fromSpecResidueField t))
      let : IsAffine (pullback f g) := hAff
      let : IsAffineHom (pullback.snd f g) := inferInstance
      infer_instance
    rw [affineFiberLocus_baseChange (IsPullback.of_hasPullback f g)] at ht
    exact ht

/-- If the pullback over a ring extension has affine residue fibres, a finitely
generated intermediate algebra has affine residue fibres as well. -/
theorem exists_fg_subalgebra_affineFiberLocus_eq_univ
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (h : affineFiberLocus
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))) = univ)
    (t : Finset A) :
    ∃ B : Subalgebra R A, B.FG ∧ (↑t : Set A) ⊆ B ∧
      affineFiberLocus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R B)))) =
        univ := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap R A))
  have hg : g ⁻¹' affineFiberLocus f = univ :=
    (affineFiberLocus_baseChange (IsPullback.of_hasPullback f g)).symm.trans h
  have hx (x : Spec (CommRingCat.of A)) : g x ∈ affineFiberLocus f := by
    change x ∈ g ⁻¹' affineFiberLocus f
    rw [hg]
    exact mem_univ x
  choose C hC hxC hsub using fun x => exists_isConstructible_subset_affineFiberLocus f (g x) (hx x)
  obtain ⟨s, hs⟩ := Picard.exists_finset_cover_of_isConstructible
    (fun x => g ⁻¹' C x) (fun x => g.isConstructible_preimage (hC x))
    (fun x => ⟨x, hxC x⟩)
  let U := ⋃ x ∈ (↑s : Set (Spec (CommRingCat.of A))), C x
  have hU : IsConstructible U := IsConstructible.biUnion s.finite_toSet fun x _ => hC x
  have hUsub : U ⊆ affineFiberLocus f := iUnion₂_subset fun x _ => hsub x
  have hUg : g ⁻¹' U = univ := eq_univ_of_forall fun x => by
    obtain ⟨z, hz, hxz⟩ := hs x
    exact mem_iUnion₂.mpr ⟨z, hz, hxz⟩
  obtain ⟨B, hB, htB, hBU⟩ :=
    FiberMapEqualityDescent.exists_fg_subalgebra_preimage_eq_univ U hU hUg t
  refine ⟨B, hB, htB, ?_⟩
  rw [affineFiberLocus_baseChange (IsPullback.of_hasPullback _ _)]
  apply eq_univ_of_forall
  intro x
  apply hUsub
  change x ∈ PrimeSpectrum.comap (algebraMap R B) ⁻¹' U
  rw [hBU]
  exact mem_univ x

end Langlands.AlgebraicGeometry.SchemeFiberGeometry
