import Langlands.GroupScheme.SplitComponent.LatticeImage

/-! # The image lattice of a homomorphism from a lattice torus

Over a field, the classifying map `ψ : B' → k[Λ]` of a natural homomorphism `α` from a lattice
torus has range spanned by the characters `[m]` it contains, and these `m` form a subgroup
`M ⊆ Λ`. Hence `α` factors through the lattice torus of `M`, by a homomorphism whose classifying
map `B' → k[M]` is surjective; centrality passes to this factor.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.SplitComponent

open Corepresented.LinearEmbedding

section Subgroup

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
  {F' : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B' : CommAlgCat.{u} R}
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

/-- `[a + b] = [a] * [b]` in the group algebra. -/
theorem single_one_mul_single_one (a b : Λ) :
    (AddMonoidAlgebra.single (a + b) (1 : R) : AddMonoidAlgebra R Λ) =
      AddMonoidAlgebra.single a 1 * AddMonoidAlgebra.single b 1 := by
  rw [AddMonoidAlgebra.single_mul_single, mul_one]

/-- The lattice `M ⊆ Λ` of characters `[m]` lying in the range of the classifying map. -/
def imageSubgroup (α : latticeFunctor R Λ ⟶ F') : AddSubgroup Λ where
  carrier := {m | AddMonoidAlgebra.single m (1 : R) ∈
    (classify (latticeCorep R Λ) d α).hom.range}
  zero_mem' := by
    rw [Set.mem_ofPred_eq, ← AddMonoidAlgebra.one_def]
    exact Subalgebra.one_mem _
  add_mem' := by
    intro a b ha hb
    rw [Set.mem_ofPred_eq] at ha hb ⊢
    rw [single_one_mul_single_one]
    exact Subalgebra.mul_mem _ ha hb
  neg_mem' := by
    intro a ha
    obtain ⟨h, hh⟩ := (AlgHom.mem_range _).mp ha
    refine (AlgHom.mem_range _).mpr ⟨(antipode d).hom h, ?_⟩
    have := congrArg (fun q : B' ⟶ latticeAlgebra R Λ => q.hom h)
      (classify_antipode (latticeCorep R Λ) d α)
    simp only [CommAlgCat.hom_comp, AlgHom.coe_comp, Function.comp_apply] at this
    rw [← this, hh, antipode_latticeCorep_single]

theorem mem_imageSubgroup {α : latticeFunctor R Λ ⟶ F'} {m : Λ} :
    m ∈ imageSubgroup d α ↔
      AddMonoidAlgebra.single m (1 : R) ∈ (classify (latticeCorep R Λ) d α).hom.range :=
  Iff.rfl

omit [AddCommGroup Λ] in
/-- A subalgebra containing `[m]` for every `m` in the support of `x` contains `x`. -/
theorem mem_subalgebra_of_support [AddMonoid Λ] {S : Subalgebra R (AddMonoidAlgebra R Λ)}
    {x : AddMonoidAlgebra R Λ} (h : ∀ m ∈ x.coeff.support, AddMonoidAlgebra.single m 1 ∈ S) :
    x ∈ S := by
  rw [← AddMonoidAlgebra.sum_coeff_single x]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [show (AddMonoidAlgebra.single m (x.coeff m) : AddMonoidAlgebra R Λ) =
      x.coeff m • AddMonoidAlgebra.single m 1 by rw [AddMonoidAlgebra.smul_single', mul_one]]
  exact Subalgebra.smul_mem _ (h m hm) _

/-- The algebra map classifying restriction along a lattice homomorphism is `mapDomain`. -/
theorem classify_latticeMap_hom {Λ' : Type u} [AddCommGroup Λ'] (l : Λ →+ Λ') :
    (classify (latticeCorep R Λ') (latticeCorep R Λ) (latticeMap l)).hom =
      AddMonoidAlgebra.mapDomainAlgHom R R l :=
  latticeAlgHom_ext fun m => by
    rw [classify_latticeMap_single, AddMonoidAlgebra.mapDomainAlgHom_apply,
      AddMonoidAlgebra.mapDomain_single]

theorem classify_latticeMap_injective {Λ' : Type u} [AddCommGroup Λ'] {l : Λ →+ Λ'}
    (hl : Function.Injective l) :
    Function.Injective (classify (latticeCorep R Λ') (latticeCorep R Λ) (latticeMap l)).hom := by
  rw [classify_latticeMap_hom]
  exact AddMonoidAlgebra.mapDomain_injective hl

/-- The inclusion `R[M] → R[Λ]` of a sublattice. -/
abbrev incl (M : AddSubgroup Λ) : latticeAlgebra R M ⟶ latticeAlgebra R Λ :=
  classify (latticeCorep R Λ) (latticeCorep R M) (latticeMap M.subtype)

theorem incl_injective (M : AddSubgroup Λ) : Function.Injective (incl (R := R) M).hom :=
  classify_latticeMap_injective Subtype.val_injective

theorem incl_single (M : AddSubgroup Λ) (m : M) :
    (incl (R := R) M).hom (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single (m : Λ) 1 :=
  classify_latticeMap_single M.subtype m

end Subgroup

section Field

variable {k : Type u} [Field k] {Λ : Type u} [AddCommGroup Λ]
  {F' : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}} {B' : CommAlgCat.{u} (CommRingCat.of k)}
  (d : (F' ⋙ forget GrpCat).CorepresentableBy B')

theorem mem_imageSubgroup_of_coeff_ne_zero (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F')
    {x : AddMonoidAlgebra k Λ}
    (hx : x ∈ (classify (latticeCorep (CommRingCat.of k) Λ) d α).hom.range) {m : Λ}
    (hm : x.coeff m ≠ 0) : m ∈ imageSubgroup d α := by
  obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).mp hx
  have key := coeff_smul_single_eq d α h m
  rw [mem_imageSubgroup]
  have hs : (AddMonoidAlgebra.single m (1 : k) : AddMonoidAlgebra k Λ) =
      (((classify (latticeCorep (CommRingCat.of k) Λ) d α).hom h).coeff m)⁻¹ •
        (((classify (latticeCorep (CommRingCat.of k) Λ) d α).hom h).coeff m •
          AddMonoidAlgebra.single m 1) := by
    rw [smul_smul, inv_mul_cancel₀ hm, one_smul]
  rw [hs, key]
  exact Subalgebra.smul_mem _ (AlgHom.mem_range_self _ _) _

theorem mem_range_iff (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F')
    (x : AddMonoidAlgebra k Λ) :
    x ∈ (classify (latticeCorep (CommRingCat.of k) Λ) d α).hom.range ↔
      ∀ m ∈ x.coeff.support, m ∈ imageSubgroup d α := by
  constructor
  · intro hx m hm
    exact mem_imageSubgroup_of_coeff_ne_zero d α hx (Finsupp.mem_support_iff.mp hm)
  · intro h
    exact mem_subalgebra_of_support fun m hm => h m hm

theorem range_incl (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    (incl (R := CommRingCat.of k) (imageSubgroup d α)).hom.range =
      (classify (latticeCorep (CommRingCat.of k) Λ) d α).hom.range := by
  classical
  ext x
  rw [mem_range_iff d α]
  constructor
  · intro hx m hm
    obtain ⟨y, rfl⟩ := (AlgHom.mem_range _).mp hx
    rw [DFunLike.congr_fun (classify_latticeMap_hom (imageSubgroup d α).subtype) y,
      AddMonoidAlgebra.mapDomainAlgHom_apply] at hm
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hm)
    exact n.2
  · intro h
    refine mem_subalgebra_of_support fun m hm => ?_
    rw [← incl_single (imageSubgroup d α) ⟨m, h m hm⟩]
    exact AlgHom.mem_range_self _ _

/-- An injective algebra map undoes the inverse of its corestriction to its range. -/
theorem ofInjective_symm_apply' {A C : Type u} [CommRing A] [CommRing C] [Algebra k A]
    [Algebra k C] (f : A →ₐ[k] C) (hf : Function.Injective f) (y : f.range) :
    f ((AlgEquiv.ofInjective f hf).symm y) = y := by
  rw [← AlgEquiv.ofInjective_apply f hf, AlgEquiv.apply_symm_apply]

/-- The classifying map of `α`, with values in the algebra `k[M]` of the image lattice. -/
def imageClassify (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    B' ⟶ latticeAlgebra (CommRingCat.of k) (imageSubgroup d α) :=
  CommAlgCat.ofHom ((AlgEquiv.ofInjective (incl (R := CommRingCat.of k) (imageSubgroup d α)).hom
    (incl_injective _)).symm.toAlgHom.comp
    ((classify (latticeCorep (CommRingCat.of k) Λ) d α).hom.codRestrict _ fun h => by
      rw [range_incl]
      exact AlgHom.mem_range_self _ h))

theorem imageClassify_comp_incl (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    imageClassify d α ≫ incl (imageSubgroup d α) = classify (latticeCorep _ Λ) d α := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro h
  exact ofInjective_symm_apply' (incl (R := CommRingCat.of k) (imageSubgroup d α)).hom
    (incl_injective _) _

theorem imageClassify_surjective (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    Function.Surjective (imageClassify d α).hom := by
  intro y
  have hy : (incl (R := CommRingCat.of k) (imageSubgroup d α)).hom y ∈
      (classify (latticeCorep (CommRingCat.of k) Λ) d α).hom.range := by
    rw [← range_incl]
    exact AlgHom.mem_range_self _ y
  obtain ⟨h, hh⟩ := (AlgHom.mem_range _).mp hy
  refine ⟨h, incl_injective _ ?_⟩
  rw [← hh]
  exact congrArg (fun q : B' ⟶ latticeAlgebra (CommRingCat.of k) Λ => q.hom h)
    (imageClassify_comp_incl d α)

theorem pair_incl_injective (M : AddSubgroup Λ) :
    Function.Injective (pair (incl (R := CommRingCat.of k) M ≫ inl _)
      (incl (R := CommRingCat.of k) M ≫ inr _)).hom := by
  have h : ∀ z, (pair (incl (R := CommRingCat.of k) M ≫ inl _)
      (incl (R := CommRingCat.of k) M ≫ inr _)).hom z =
        TensorProduct.map (incl (R := CommRingCat.of k) M).hom.toLinearMap
          (incl (R := CommRingCat.of k) M).hom.toLinearMap z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b => simp [pair, inl, inr, Algebra.TensorProduct.tmul_mul_tmul]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  intro x y hxy
  rw [h, h] at hxy
  exact TensorProduct.map_injective_of_flat_flat _ _ (incl_injective M) (incl_injective M) hxy

theorem lift2_incl_injective (M : AddSubgroup Λ) :
    Function.Injective (lift2 (incl (R := CommRingCat.of k) M ≫ jl _ B') (jr _ B')).hom := by
  have h : ∀ z, (lift2 (incl (R := CommRingCat.of k) M ≫ jl _ B') (jr _ B')).hom z =
      LinearMap.rTensor B' (incl (R := CommRingCat.of k) M).hom.toLinearMap z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      rw [lift2_tmul]
      simp [jl, jr]
    | add z w hz hw => rw [map_add, map_add, hz, hw]
  intro x y hxy
  rw [h, h] at hxy
  exact Module.Flat.rTensor_preserves_injective_linearMap _ (incl_injective M) hxy

theorem imageClassify_comul (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    imageClassify d α ≫ comul (latticeCorep _ (imageSubgroup d α)) =
      comul d ≫ pair (imageClassify d α ≫ inl _) (imageClassify d α ≫ inr _) := by
  apply cancel_injective (pair_incl_injective (imageSubgroup d α))
  rw [Category.assoc, ← classify_comul (latticeCorep _ Λ) (latticeCorep _ (imageSubgroup d α))
      (latticeMap (imageSubgroup d α).subtype), ← Category.assoc, imageClassify_comp_incl,
    classify_comul, Category.assoc, pair_comp, Category.assoc, Category.assoc, inl_pair,
    inr_pair, ← Category.assoc, ← Category.assoc, imageClassify_comp_incl]

/-- The homomorphism from the lattice torus of the image lattice through which `α` factors. -/
def imageHom (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    latticeFunctor (CommRingCat.of k) (imageSubgroup d α) ⟶ F' :=
  ofClassify (latticeCorep _ _) d (imageClassify d α) (imageClassify_comul d α)

theorem classify_imageHom (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    classify (latticeCorep _ _) d (imageHom d α) = imageClassify d α :=
  classify_ofClassify _ _ _ _

theorem latticeMap_comp_imageHom (α : latticeFunctor (CommRingCat.of k) Λ ⟶ F') :
    latticeMap (imageSubgroup d α).subtype ≫ imageHom d α = α := by
  apply nat_ext (latticeCorep _ Λ) d
  rw [classify_comp (latticeCorep _ Λ) (latticeCorep _ (imageSubgroup d α)), classify_imageHom]
  exact imageClassify_comp_incl d α

theorem IsCentralNat.imageHom {α : latticeFunctor (CommRingCat.of k) Λ ⟶ F'}
    (hα : IsCentralNat α) : IsCentralNat (imageHom d α) := by
  rw [isCentralNat_iff (latticeCorep _ _) d, classify_imageHom]
  rw [isCentralNat_iff (latticeCorep _ Λ) d] at hα
  unfold CentralIdentity at hα ⊢
  apply cancel_injective (lift2_incl_injective (B' := B') (imageSubgroup d α))
  rw [Category.assoc, Category.assoc, pair_comp, pair_comp, Category.assoc, jl_lift2, jr_lift2,
    ← Category.assoc, imageClassify_comp_incl]
  exact hα

end Field

end Langlands.GroupScheme.SplitComponent
