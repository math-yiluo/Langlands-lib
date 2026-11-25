import Langlands.GroupScheme.Torus.FlatDiagonalizableSubgroup
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Finite flat local closed subgroups of diagonalizable groups -/

noncomputable section

universe u v

open CategoryTheory Opposite AlgebraicGeometry Module
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Diagonalizable

section Coalgebra

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {C : Type v} [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Over a local ring, every group-like element is a member of any finite
basis consisting of group-like elements. -/
theorem groupLike_mem_basis {ι : Type v} [Fintype ι] (b : Basis ι R C)
    (hb : ∀ i, IsGroupLikeElem R (b i)) {g : C} (hg : IsGroupLikeElem R g) :
    ∃ i, g = b i := by
  classical
  have hs : ∑ i, b.repr g i = 1 := by
    have h := congrArg (Coalgebra.counit (R := R)) (b.sum_repr g)
    simpa only [map_sum, map_smul, (hb _).counit_eq_one, smul_eq_mul,
      mul_one, hg.counit_eq_one] using h
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum (hs ▸ isUnit_one)
  have hc (j k : ι) : (b.tensorProduct b).repr (Coalgebra.comul g) (j, k) =
      if j = k then b.repr g j else 0 := by
    let d : C →ₗ[R] R := ((b.tensorProduct b).coord (j, k)).comp Coalgebra.comul
    have hd : d = if j = k then b.coord j else 0 := by
      apply b.ext
      intro l
      by_cases hjk : j = k
      · subst k
        by_cases hlj : l = j
        · subst l
          simp [d, hb, Basis.coord_apply]
        · simp [d, hb, Basis.coord_apply, Ne.symm hlj]
      · by_cases hlj : l = j
        · subst l
          simp [d, hb, Basis.coord_apply, hjk, Ne.symm hjk]
        · by_cases hlk : l = k
          · subst l
            simp [d, hb, Basis.coord_apply, Ne.symm hlj]
          · simp [d, hb, Basis.coord_apply, Ne.symm hlj, Ne.symm hlk, hjk]
    change d g = _
    rw [hd]
    split_ifs <;> rfl
  have hmul (j : ι) : b.repr g i * b.repr g j = if j = i then b.repr g j else 0 := by
    have h := hc j i
    rwa [hg.comul_eq_tmul_self, Basis.tensorProduct_repr_tmul_apply, smul_eq_mul] at h
  have hii : b.repr g i = 1 := by
    apply hi.mul_left_cancel
    simpa using hmul i
  refine ⟨i, b.repr.injective ?_⟩
  ext j
  by_cases hji : j = i
  · subst j
    simp [hii]
  · have hj := hmul j
    simpa [hji, hii, Basis.repr_self, Finsupp.single_apply, Ne.symm hji] using hj

/-- A finite flat coalgebra over a local ring spanned by group-like elements
has a finite basis consisting of group-like elements. -/
theorem exists_groupLike_basis [Module.Finite R C] [Module.Flat R C]
    (hspan : Submodule.span R {g : C | IsGroupLikeElem R g} = ⊤) :
    ∃ (ι : Type v) (_ : Fintype ι) (b : Basis ι R C), ∀ i, IsGroupLikeElem R (b i) := by
  let : Module.Free R C := Module.free_of_flat_of_isLocalRing
  let : Module.FinitePresentation R C := Module.finitePresentation_of_projective R C
  let v : GroupLike R C → C := GroupLike.val
  have hv : Submodule.span R (Set.range v) = ⊤ := by
    convert hspan using 2
    ext x
    exact ⟨fun ⟨g, hg⟩ => hg ▸ g.isGroupLikeElem_val,
      fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  obtain ⟨ι, a, b, hb⟩ := Module.exists_basis_of_span_of_flat v hv
  let : Finite ι := Module.Finite.finite_basis b
  refine ⟨ι, Fintype.ofFinite ι, b, ?_⟩
  intro i
  rw [hb]
  exact (a i).isGroupLikeElem_val

/-- The complete group-like family of a finite flat coalgebra spanned by
that family is linearly independent over a local ring. -/
theorem linearIndependent_groupLike_of_finite_flat [Module.Finite R C] [Module.Flat R C]
    (hspan : Submodule.span R {g : C | IsGroupLikeElem R g} = ⊤) :
    LinearIndependent R (GroupLike.val (R := R) (A := C)) := by
  obtain ⟨ι, inst, b, hb⟩ := exists_groupLike_basis hspan
  let f : ι → GroupLike R C := fun i => ⟨b i, hb i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact b.injective (congrArg GroupLike.val h)
    · intro g
      obtain ⟨i, hi⟩ := groupLike_mem_basis b hb g.isGroupLikeElem_val
      exact ⟨i, GroupLike.val_injective hi.symm⟩
  let e := Equiv.ofBijective f hf
  exact (linearIndependent_equiv' e (by rfl)).mp b.linearIndependent

/-- There are finitely many group-like elements in a finite flat coalgebra
over a local ring when they span the module. -/
theorem finite_groupLike_of_finite_flat [Module.Finite R C] [Module.Flat R C]
    (hspan : Submodule.span R {g : C | IsGroupLikeElem R g} = ⊤) :
    Finite (GroupLike R C) := by
  obtain ⟨ι, inst, b, hb⟩ := exists_groupLike_basis hspan
  let f : ι → GroupLike R C := fun i => ⟨b i, hb i⟩
  apply Finite.of_surjective f
  intro g
  obtain ⟨i, hi⟩ := groupLike_mem_basis b hb g.isGroupLikeElem_val
  exact ⟨i, GroupLike.val_injective hi.symm⟩

end Coalgebra

section Bialgebra

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {A : Type v} [Ring A] [Bialgebra R A] [Module.Finite R A] [Module.Flat R A]

/-- Reconstruction of a finite flat bialgebra over a local ring from all its
group-like elements. -/
def finiteFlatLocalBialgEquiv
    (hspan : Submodule.span R {a : A | IsGroupLikeElem R a} = ⊤) :
    MonoidAlgebra R (GroupLike R A) ≃ₐc[R] A := by
  refine BialgEquiv.ofBijective MonoidAlgebra.liftGroupLikeBialgHom ⟨?_, ?_⟩
  · intro x y hxy
    apply MonoidAlgebra.coeff_injective
    apply linearIndependent_groupLike_of_finite_flat hspan
    exact (Langlands.MonoidAlgebra.liftGroupLikeBialgHom_eq_linearCombination x).symm.trans
      (hxy.trans (Langlands.MonoidAlgebra.liftGroupLikeBialgHom_eq_linearCombination y))
  · exact Langlands.MonoidAlgebra.liftGroupLikeBialgHom_surjective hspan

end Bialgebra

section GroupScheme

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    {H : GroupScheme (Spec R)} [IsAffine H.X.left]

/-- Finiteness of the actual group gives finite generation of its affine
Hopf coordinates as a module. -/
theorem finite_hopfAlgebra [IsFinite H.X.hom] :
    Module.Finite R (AffineCoordinates.hopfAlgebra H) := by
  have h : IsFinite ((AffineCoordinates.hopfSpecIso H).hom.hom.hom.left ≫ H.X.hom) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
    infer_instance
  rw [Over.w] at h
  change IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R (AffineCoordinates.hopfAlgebra H)))) at h
  exact RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff
    (CommRingCat.ofHom (algebraMap R (AffineCoordinates.hopfAlgebra H)))).mp h)

variable [IsLocalRing R] [IsFinite H.X.hom] [Flat H.X.hom]

/-- A finite flat closed subgroup of a diagonalizable group over a local ring
is diagonalizable on its full finite coordinate character group. -/
def finiteFlatLocalClosedSubgroupIso (i : H ⟶ (groupScheme R Λ).toGrp)
    (hi : IsClosedSubgroup i) :
    H ≅ (groupScheme R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))).toGrp := by
  let : Module.Finite R (AffineCoordinates.hopfAlgebra H) := finite_hopfAlgebra
  let : Module.Flat R (AffineCoordinates.hopfAlgebra H) := flat_hopfAlgebra
  let e : AffineCoordinates.hopfAlgebra H ≃ₐc[R]
      AddMonoidAlgebra R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H))) :=
    (finiteFlatLocalBialgEquiv (span_groupLike_of_closedSubgroup i hi)).symm.trans
      (MonoidAlgebra.toAdditiveBialgEquiv R R (GroupLike R (AffineCoordinates.hopfAlgebra H)))
  exact (AffineCoordinates.isoOfBialgEquiv H
    (hopfAlgebra R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))) e).symm ≪≫
      hopfSpecIso R (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))

/-- The full character group in the finite flat local presentation is finite. -/
theorem finite_characters_of_finite_flat_closedSubgroup
    (i : H ⟶ (groupScheme R Λ).toGrp) (hi : IsClosedSubgroup i) :
    Finite (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H))) := by
  let : Module.Finite R (AffineCoordinates.hopfAlgebra H) := finite_hopfAlgebra
  let : Module.Flat R (AffineCoordinates.hopfAlgebra H) := flat_hopfAlgebra
  let : Finite (GroupLike R (AffineCoordinates.hopfAlgebra H)) :=
    finite_groupLike_of_finite_flat (span_groupLike_of_closedSubgroup i hi)
  infer_instance

/-- Every finite flat affine closed subgroup of a diagonalizable group over
a local ring is relatively diagonalizable, without finite-type assumptions
on the ambient character group. -/
theorem isDiagonalizable_of_finite_flat_closedSubgroup
    (i : H ⟶ (groupScheme R Λ).toGrp) (hi : IsClosedSubgroup i) :
    RelativeMultiplicativeType.IsDiagonalizable H := by
  let : Finite (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H))) :=
    finite_characters_of_finite_flat_closedSubgroup i hi
  refine ⟨Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)), inferInstance,
    inferInstance, ?_⟩
  exact ⟨finiteFlatLocalClosedSubgroupIso i hi ≪≫
    (baseChangeIso (Gm.toSpecZ (Spec R))
      (Additive (GroupLike R (AffineCoordinates.hopfAlgebra H)))).symm⟩

end GroupScheme

end Langlands.GroupScheme.Diagonalizable
