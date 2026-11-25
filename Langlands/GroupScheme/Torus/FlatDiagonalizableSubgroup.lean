import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeFinite
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Flat closed subgroups of diagonalizable groups over integral domains -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Diagonalizable

/-- Group-like spanning detects every group-like element over a domain when the
coalgebra is torsion-free. -/
theorem groupLike_mem_of_span_eq_top_of_torsionFree
    {R : Type u} [CommRing R] [IsDomain R] {C : Type v} [AddCommGroup C]
    [Module R C] [Coalgebra R C] [Module.IsTorsionFree R C]
    {T : Set C} (hT : T ⊆ {c : C | IsGroupLikeElem R c})
    (hspan : Submodule.span R T = ⊤) {g : C} (hg : IsGroupLikeElem R g) : g ∈ T := by
  by_contra h
  have hli : LinearIndepOn R id (insert g T) :=
    linearIndepOn_isGroupLikeElem.mono (Set.insert_subset hg hT)
  exact hli.notMem_span_of_insert h (by simp [hspan])

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    {H : GroupScheme (Spec R)} [IsAffine H.X.left]

/-- The actual affine Hopf coordinates of a map to a diagonalizable group. -/
def subgroupCoordinateMap (i : H ⟶ (groupScheme R Λ).toGrp) :
    hopfAlgebra R Λ ⟶ AffineCoordinates.hopfAlgebra H :=
  (hopfSpec.fullyFaithful.preimage
    ((AffineCoordinates.hopfSpecIso H).hom ≫ i ≫ (hopfSpecIso R Λ).inv)).unop

/-- A closed inclusion makes its actual coordinate map surjective. -/
theorem subgroupCoordinateMap_surjective (i : H ⟶ (groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) : Function.Surjective (subgroupCoordinateMap i).hom := by
  apply surjective_of_isClosedSubgroup_hopfSpec
  have hφ : (hopfSpec R).map (subgroupCoordinateMap i).op =
      (AffineCoordinates.hopfSpecIso H).hom ≫ i ≫ (hopfSpecIso R Λ).inv :=
    hopfSpec.fullyFaithful.map_preimage _
  rw [hφ]
  exact IsClosedSubgroup.iso_comp (AffineCoordinates.hopfSpecIso H)
    (hi.comp_iso (hopfSpecIso R Λ).symm)

/-- Monomials in the ambient group algebra restrict to actual coordinate
characters of the subgroup. -/
def subgroupCharacterMap (i : H ⟶ (groupScheme R Λ).toGrp) :
    Λ →+ Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)) :=
  AddMonoidHom.mk' (fun l => Additive.ofMul
    ⟨(subgroupCoordinateMap i).hom (AddMonoidAlgebra.single l 1),
      (AddMonoidAlgebra.isGroupLikeElem_single_one (R := R) l).map
        (subgroupCoordinateMap i).hom⟩) (by
    intro a b
    apply Additive.toMul.injective
    apply GroupLike.val_injective
    simp only [toMul_ofMul, toMul_add, GroupLike.val_mul, ← map_mul,
      AddMonoidAlgebra.single_mul_single, one_mul])

/-- The coordinate algebra of an actual closed subgroup is spanned by its
restricted monomial characters, over any coefficient ring. -/
theorem span_subgroupCoordinateMap_groupLike (i : H ⟶ (groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) :
    Submodule.span R ((subgroupCoordinateMap i).hom ''
      {a : AddMonoidAlgebra R Λ | IsGroupLikeElem R a}) = ⊤ := by
  have hm := Submodule.map_span (subgroupCoordinateMap i).hom.toLinearMap
    {a : AddMonoidAlgebra R Λ | IsGroupLikeElem R a}
  rw [AddMonoidAlgebra.span_isGroupLikeElem, Submodule.map_top,
    LinearMap.range_eq_top.2 (subgroupCoordinateMap_surjective i hi)] at hm
  exact hm.symm

/-- In particular, all coordinate group-like elements span. -/
theorem span_groupLike_of_closedSubgroup (i : H ⟶ (groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) :
    Submodule.span R {a : AffineCoordinates.hopfAlgebra H | IsGroupLikeElem R a} = ⊤ := by
  apply top_unique
  rw [← span_subgroupCoordinateMap_groupLike i hi]
  apply Submodule.span_mono
  rintro _ ⟨a, ha, rfl⟩
  exact ha.map (subgroupCoordinateMap i).hom

/-- Flatness of the actual group gives flatness of its affine Hopf coordinates. -/
theorem flat_hopfAlgebra [Flat H.X.hom] :
    Module.Flat R (AffineCoordinates.hopfAlgebra H) := by
  have h : Flat ((AffineCoordinates.hopfSpecIso H).hom.hom.hom.left ≫ H.X.hom) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  rw [Over.w] at h
  change Flat (Spec.map (CommRingCat.ofHom
    (algebraMap R (AffineCoordinates.hopfAlgebra H)))) at h
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp h)

section Domain

variable [IsDomain R] [Flat H.X.hom]

/-- Over a domain, every character of a flat closed subgroup is a restriction
of a character of the given diagonalizable group. -/
theorem subgroupCharacterMap_surjective (i : H ⟶ (groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) : Function.Surjective (subgroupCharacterMap i) := by
  let : Module.Flat R (AffineCoordinates.hopfAlgebra H) := flat_hopfAlgebra
  intro g
  have hT : (subgroupCoordinateMap i).hom ''
      {a : AddMonoidAlgebra R Λ | IsGroupLikeElem R a} ⊆
      {a : AffineCoordinates.hopfAlgebra H | IsGroupLikeElem R a} := by
    rintro _ ⟨a, ha, rfl⟩
    exact ha.map (subgroupCoordinateMap i).hom
  obtain ⟨a, ha, hga⟩ := groupLike_mem_of_span_eq_top_of_torsionFree hT
    (span_subgroupCoordinateMap_groupLike i hi) (Additive.toMul g).isGroupLikeElem_val
  obtain ⟨l, rfl⟩ := AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one.1 ha
  exact ⟨l, Additive.toMul.injective (GroupLike.val_injective hga)⟩

/-- A flat closed subgroup over a domain is the diagonalizable group on its
full coordinate character group, with all torsion retained. -/
def flatClosedSubgroupIso (i : H ⟶ (groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) :
    H ≅ (groupScheme R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))).toGrp := by
  let : Module.Flat R (AffineCoordinates.hopfAlgebra H) := flat_hopfAlgebra
  let e : AffineCoordinates.hopfAlgebra H ≃ₐc[R]
      AddMonoidAlgebra R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H))) :=
    (Langlands.MonoidAlgebra.bialgEquivOfSpanGroupLike
      (span_groupLike_of_closedSubgroup i hi)).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv R R (GroupLike R (AffineCoordinates.hopfAlgebra H)))
  exact (AffineCoordinates.isoOfBialgEquiv H
    (hopfAlgebra R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))) e).symm ≪≫
      hopfSpecIso R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))

/-- Finite generation descends to the full subgroup character group. -/
theorem subgroup_characters_fg [AddGroup.FG Λ]
    (i : H ⟶ (groupScheme R Λ).toGrp) (hi : IsClosedSubgroup i) :
    AddGroup.FG (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H))) :=
  AddGroup.fg_of_surjective (subgroupCharacterMap_surjective i hi)

/-- The preceding actual presentation supplies relative diagonalizability. -/
theorem isDiagonalizable_of_flat_closedSubgroup [AddGroup.FG Λ]
    (i : H ⟶ (groupScheme R Λ).toGrp) (hi : IsClosedSubgroup i) :
    RelativeMultiplicativeType.IsDiagonalizable H := by
  have hfg := subgroup_characters_fg i hi
  refine ⟨Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)), inferInstance, hfg, ?_⟩
  exact ⟨flatClosedSubgroupIso i hi ≪≫
    (baseChangeIso (Gm.toSpecZ (Spec R))
      (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))).symm⟩

/-- Local quasi-finiteness forces finiteness of a flat closed subgroup of a
finite-type diagonalizable group over a domain. -/
theorem isFinite_of_flat_closedSubgroup [AddGroup.FG Λ]
    (i : H ⟶ (groupScheme R Λ).toGrp) (hi : IsClosedSubgroup i)
    [LocallyQuasiFinite H.X.hom] : IsFinite H.X.hom :=
  (isDiagonalizable_of_flat_closedSubgroup i hi).isFinite

end Domain

end Langlands.GroupScheme.Diagonalizable
