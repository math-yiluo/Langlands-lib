import Langlands.GroupScheme.Unipotent.SplitTorusHom
import Langlands.GroupScheme.SubgroupIntersection
import Mathlib.RingTheory.Coalgebra.GroupLike

/-! # Closed subgroups of split tori meet unipotent subgroups trivially -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct Coalgebra
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Unipotent

open AffineLinearEmbedding Chevalley

section Coalgebra

variable {K : Type*} [Field K]

/-- A nonzero element `c` of a coalgebra over a field with `Δ c = c ⊗ c` is group-like. -/
theorem isGroupLikeElem_of_comul_eq {A : Type*} [AddCommGroup A] [Module K A] [Coalgebra K A]
    {c : A} (hc : comul (R := K) c = c ⊗ₜ[K] c) (h0 : c ≠ 0) : IsGroupLikeElem K c := by
  refine ⟨?_, hc⟩
  have h := Coalgebra.rTensor_counit_comul (R := K) c
  rw [hc, LinearMap.rTensor_tmul] at h
  have h2 := congrArg (TensorProduct.lid K A) h
  rw [TensorProduct.lid_tmul, TensorProduct.lid_tmul, one_smul] at h2
  have h3 : (counit (R := K) c - 1) • c = 0 := by rw [sub_smul, h2, one_smul, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 h0

/-- The image of a surjective coalgebra map out of a coalgebra with a basis of elements
`b i` satisfying `Δ (b i) = b i ⊗ b i` is spanned by its group-like elements. -/
theorem span_groupLike_of_surjective {A C : Type*} [AddCommGroup A] [Module K A]
    [Coalgebra K A] [AddCommGroup C] [Module K C] [Coalgebra K C] (r : A →ₗc[K] C)
    (hr : Function.Surjective r) {κ : Type*} (b : Module.Basis κ K A)
    (hb : ∀ i, comul (R := K) (b i) = b i ⊗ₜ[K] b i) :
    ⊤ ≤ Submodule.span K (Set.range (GroupLike.val (R := K) (A := C))) := by
  rintro c -
  obtain ⟨a, rfl⟩ := hr c
  have ha : a ∈ Submodule.span K (Set.range b) := b.mem_span a
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      by_cases h0 : r (b i) = 0
      · rw [h0]
        exact Submodule.zero_mem _
      · apply Submodule.subset_span
        have hcomul : comul (R := K) (r (b i)) = r (b i) ⊗ₜ[K] r (b i) := by
          rw [← CoalgHomClass.map_comp_comul_apply, hb i]
          simp
        exact ⟨⟨r (b i), isGroupLikeElem_of_comul_eq hcomul h0⟩, rfl⟩
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  | smul t x _ hx =>
      rw [map_smul]
      exact Submodule.smul_mem _ t hx

/-- Over a field, a coalgebra spanned by its group-like elements has a basis of group-like
elements. -/
def groupLikeBasis {C : Type*} [AddCommGroup C] [Module K C] [Coalgebra K C]
    (hspan : ⊤ ≤ Submodule.span K (Set.range (GroupLike.val (R := K) (A := C)))) :
    Module.Basis (GroupLike K C) K C :=
  Module.Basis.mk linearIndep_groupLikeVal hspan

theorem groupLikeBasis_comul {C : Type*} [AddCommGroup C] [Module K C] [Coalgebra K C]
    (hspan : ⊤ ≤ Submodule.span K (Set.range (GroupLike.val (R := K) (A := C))))
    (g : GroupLike K C) :
    comul (R := K) (groupLikeBasis hspan g) =
      groupLikeBasis hspan g ⊗ₜ[K] groupLikeBasis hspan g := by
  rw [groupLikeBasis, Module.Basis.mk_apply]
  exact g.isGroupLikeElem_val.comul_eq_tmul_self

end Coalgebra

variable {k : Type u} [Field k]
  {F H : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B C : CommAlgCat.{u} (CommRingCat.of k)}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (d : (H ⋙ forget GrpCat).CorepresentableBy C)

/-- A homomorphism from a corepresented group whose coordinate bialgebra has a basis of
group-like elements to a corepresented group whose coordinate bialgebra satisfies
`OneMemStable` sends every algebra point to the identity. -/
theorem pointsTrans_eq_one_of_groupLike_basis (hB : letI := bialgebra e; OneMemStable k B)
    {κ : Type*} (g : Module.Basis κ k C)
    (hg : letI := bialgebra d; ∀ i, comul (R := k) (g i) = g i ⊗ₜ[k] g i)
    (φ : Corepresented.groupScheme H d ⟶ Corepresented.groupScheme F e)
    (A : CommAlgCat.{u} (CommRingCat.of k)) (x : H.obj A) :
    (Corepresented.pointsTrans d e φ).app A x = 1 := by
  let α := Corepresented.pointsTrans d e φ
  let := bialgebra e
  let := bialgebra d
  have hr : coordinateRestriction e d α =
      (Algebra.ofId k C).comp (AffineLinearEmbedding.counit e) := by
    apply AlgHom.ext
    intro f
    exact bialgHom_eq_algebraMap_counit hB (coordinateRestrictionBialgHom e d α) g hg f
  have h := pt_comp_coordinateRestriction e d α (A := A) (d.homEquiv.symm x).hom
  rw [pt_homEquiv_symm, hr, ← AlgHom.comp_assoc, pt_comp_counit] at h
  exact h.symm

/-- A homomorphism from a corepresented group whose coordinate bialgebra has a basis of
group-like elements to a corepresented group whose coordinate bialgebra satisfies
`OneMemStable` is trivial. -/
theorem hom_eq_zero_of_groupLike_basis (hB : letI := bialgebra e; OneMemStable k B)
    {κ : Type*} (g : Module.Basis κ k C)
    (hg : letI := bialgebra d; ∀ i, comul (R := k) (g i) = g i ⊗ₜ[k] g i)
    (φ : Corepresented.groupScheme H d ⟶ Corepresented.groupScheme F e) :
    φ = 0 := by
  apply Corepresented.hom_ext_affinePoints
  intro S f
  have h1 := Corepresented.pointsTrans_app d e φ (Corepresented.affinePointsEquiv _ _ S f)
  rw [MulEquiv.symm_apply_apply] at h1
  rw [← h1, pointsTrans_eq_one_of_groupLike_basis e d hB g hg φ]
  change 1 = Corepresented.affinePointsEquiv F e S (f ≫ (1 : _ ⟶ _))
  rw [MonObj.comp_one, map_one]

end Langlands.GroupScheme.Unipotent

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- Every homomorphism from a closed subgroup of a split torus to an affine unipotent group
scheme over a field is trivial. -/
theorem IsSplitTorus.hom_eq_zero_of_isClosedSubgroup
    {S Z U : GroupScheme (Spec (CommRingCat.of k))} [IsAffine Z.X.left] [IsAffine U.X.left]
    (hS : IsSplitTorus S) {incl : Z ⟶ S} (hincl : IsClosedSubgroup incl) (hU : IsUnipotent U)
    (ψ : Z ⟶ U) : ψ = 0 := by
  classical
  obtain ⟨I, hI, ⟨eS⟩⟩ := hS
  have := Fintype.ofFinite I
  let eD : (Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp ≅ S :=
    Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ)) ≪≫ eS.symm
  let eZ := AffineCoordinates.groupSchemeIso Z
  let eU := AffineCoordinates.groupSchemeIso U
  let dZ := AffineCoordinates.corepresentation Z
  let dD := Diagonalizable.grpCorepresentation (CommRingCat.of k) (I → ℤ)
  let incl' : Corepresented.groupScheme (AffineCoordinates.functor Z) dZ ⟶
      Corepresented.groupScheme (Diagonalizable.functor (CommRingCat.of k) (I → ℤ)) dD :=
    eZ.hom ≫ incl ≫ eD.inv
  let α := Corepresented.pointsTrans dZ dD incl'
  have hc : IsClosedSubgroup (Corepresented.groupSchemeMap dZ dD α) := by
    rw [Corepresented.groupSchemeMap_pointsTrans]
    have h1 : IsClosedImmersion incl.hom.hom.left := hincl
    have h2 : IsClosedImmersion eZ.hom.hom.hom.left := IsClosedSubgroup.of_iso eZ
    have h3 : IsClosedImmersion eD.inv.hom.hom.left := IsClosedSubgroup.of_iso eD.symm
    change IsClosedImmersion (eZ.hom.hom.hom.left ≫ incl.hom.hom.left ≫ eD.inv.hom.hom.left)
    infer_instance
  have hsurj := Chevalley.coordinateRestriction_surjective dD dZ α hc
  let := AffineLinearEmbedding.bialgebra dZ
  let := AffineLinearEmbedding.bialgebra dD
  let rc : Diagonalizable.algebra (CommRingCat.of k) (I → ℤ) →ₗc[k] AffineCoordinates.algebra Z :=
    Chevalley.coordinateRestrictionBialgHom dD dZ α
  have hsurj' : Function.Surjective rc := fun c => hsurj c
  have hspan := Unipotent.span_groupLike_of_surjective rc hsurj'
    (AddMonoidAlgebra.basis (I → ℤ) k) (Unipotent.diagonalizable_comul_basis (I → ℤ))
  have hU' : IsUnipotent (Corepresented.groupScheme (AffineCoordinates.functor U)
      (AffineCoordinates.corepresentation U)) := IsUnipotent.of_iso eU hU
  have h0 := Unipotent.hom_eq_zero_of_groupLike_basis (AffineCoordinates.corepresentation U) dZ
    (Unipotent.oneMemStable_of_isUnipotent _ hU') (Unipotent.groupLikeBasis hspan)
    (Unipotent.groupLikeBasis_comul hspan) (eZ.hom ≫ ψ ≫ eU.inv)
  calc ψ = eZ.inv ≫ (eZ.hom ≫ ψ ≫ eU.inv) ≫ eU.hom := by simp
    _ = 0 := by erw [h0, Limits.zero_comp, Limits.comp_zero]

/-- Over a field, a split torus and a unipotent closed subgroup of a common group meet
trivially on every test scheme: if a point of the torus and a point of the unipotent group
have the same image, the torus point is the identity. -/
theorem IsSplitTorus.eq_one_of_comp_eq_comp
    {S U P : GroupScheme (Spec (CommRingCat.of k))} [IsAffine S.X.left] [IsAffine U.X.left]
    (hS : IsSplitTorus S) (hU : IsUnipotent U) {s : S ⟶ P} {j : U ⟶ P} [Mono s.hom.hom]
    (hj : IsClosedSubgroup j) {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ S.X)
    (n : T ⟶ U.X) (h : a ≫ s.hom.hom = n ≫ j.hom.hom) : a = 1 := by
  have hincl := isClosedSubgroup_subgroupIntersectionFst s hj
  have : IsClosedImmersion (subgroupIntersectionFst s j).hom.hom.left := hincl
  have : IsAffine (subgroupIntersection s j).X.left :=
    isAffine_of_isAffineHom (subgroupIntersectionFst s j).hom.hom.left
  have h0 := IsSplitTorus.hom_eq_zero_of_isClosedSubgroup hS hincl hU (subgroupIntersectionSnd s j)
  let hpb := subgroupIntersection_isPullback s j
  have h0' : (subgroupIntersectionSnd s j).hom.hom =
      (1 : (subgroupIntersection s j).X ⟶ U.X) := by
    rw [h0]
    rfl
  have hn : n = 1 :=
    calc n = hpb.lift a n h ≫ (subgroupIntersectionSnd s j).hom.hom := (hpb.lift_snd a n h).symm
      _ = hpb.lift a n h ≫ 1 := congrArg _ h0'
      _ = 1 := MonObj.comp_one _
  have h1 : a ≫ s.hom.hom = 1 ≫ s.hom.hom := by
    rw [h, hn, MonObj.one_comp, MonObj.one_comp]
  exact (cancel_mono _).mp h1

end Langlands.GroupScheme
