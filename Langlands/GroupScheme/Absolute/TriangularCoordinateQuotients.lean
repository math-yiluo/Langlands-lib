import Langlands.GroupScheme.Absolute.TriangularCoordinateSeries
import Langlands.GroupScheme.AffineNormalSubgroupQuotientStatement
import Langlands.GroupScheme.SubgroupFunctor.FppfImagePullback
import Langlands.GroupScheme.SubgroupFunctor.QuotientEmbedding
import Langlands.GroupScheme.DominantHomFlat

/-! # Actual quotient comparisons for the finite triangular coordinate series -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TriangularLayer

variable {k : Type u} [Field k]
  {H : GroupScheme (Spec (CommRingCat.of k))}

/-- An actual affine quotient of finite type by a specified full subgroup
functor. Existence is supplied separately. -/
structure QuotientTerm (F : SubgroupFunctor H) where
  quotient : GroupScheme (Spec (CommRingCat.of k))
  hom : H ⟶ quotient
  locallyOfFiniteType : LocallyOfFiniteType quotient.X.hom
  isAffineHom : IsAffineHom quotient.X.hom
  isFppfQuotient : RelativeRoot.IsFppfQuotient F hom

namespace QuotientTerm

variable {F E : SubgroupFunctor H} (A : QuotientTerm F)

instance : LocallyOfFiniteType A.quotient.X.hom := A.locallyOfFiniteType
instance : IsAffineHom A.quotient.X.hom := A.isAffineHom
instance : Flat A.hom.hom.hom.left := A.isFppfQuotient.1
instance : Surjective A.hom.hom.hom.left := A.isFppfQuotient.2.1
instance : LocallyOfFinitePresentation A.hom.hom.hom.left := A.isFppfQuotient.2.2.1

instance [IsAffineHom H.X.hom] : QuasiCompact A.hom.hom.hom.left := by
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : IsAffine A.quotient.X.left := isAffine_of_isAffineHom A.quotient.X.hom
  infer_instance

variable (B : QuotientTerm E) (hEF : E ≤ F)

include hEF in
/-- The smaller kernel is killed by the quotient with the larger kernel. -/
theorem kernel_comp_eq_zero : kernelι B.hom ≫ A.hom = 0 := by
  apply Grp.hom_ext
  change (kernelι B.hom).hom.hom ≫ A.hom.hom.hom = 1
  apply (mem_range_kernelι_iff A.hom _).mp
  apply A.isFppfQuotient.2.2.2.ge (kernel B.hom).X
  apply hEF (kernel B.hom).X
  apply B.isFppfQuotient.2.2.2.le (kernel B.hom).X
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

variable [IsAffineHom H.X.hom]

/-- The actual comparison from the quotient by the smaller kernel to the
quotient by the larger kernel, constructed by fpqc homomorphism descent. -/
def comparison : B.quotient ⟶ A.quotient :=
  FpqcHomDescent.hom B.hom A.hom (kernel_comp_eq_zero A B hEF)

theorem comparison_fac : B.hom ≫ comparison A B hEF = A.hom :=
  FpqcHomDescent.fac B.hom A.hom (kernel_comp_eq_zero A B hEF)

/-- The full inverse image of the comparison kernel is exactly the original
larger kernel on every test scheme. -/
theorem comparison_comap_kernel :
    (SubgroupFunctor.range (kernelι (comparison A B hEF))).comap B.hom = F := by
  ext T x
  change (x ≫ B.hom.hom.hom) ∈
    (SubgroupFunctor.range (kernelι (comparison A B hEF))).carrier T ↔ x ∈ F.carrier T
  rw [mem_range_kernelι_iff]
  have hs : B.hom.hom.hom ≫ (comparison A B hEF).hom.hom = A.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) (comparison_fac A B hEF)
  constructor
  · intro hx
    apply A.isFppfQuotient.2.2.2.le T
    apply (mem_range_kernelι_iff A.hom x).mpr
    rwa [Category.assoc, hs] at hx
  · intro hx
    have hx' := (mem_range_kernelι_iff A.hom x).mp
      (A.isFppfQuotient.2.2.2.ge T hx)
    rwa [Category.assoc, hs]

/-- The comparison is flat and surjective: these properties descend from
its factorization of the two given fppf quotient morphisms. -/
theorem comparison_flat_surjective :
    Flat (comparison A B hEF).hom.hom.left ∧
      Surjective (comparison A B hEF).hom.hom.left := by
  have hs : B.hom.hom.hom.left ≫ (comparison A B hEF).hom.hom.left =
      A.hom.hom.hom.left :=
    congrArg (fun f => f.hom.hom.left) (comparison_fac A B hEF)
  have hflat : Flat (comparison A B hEF).hom.hom.left := by
    apply Flat.of_stalkMap
    intro x
    obtain ⟨z, hz⟩ := B.hom.hom.hom.left.surjective x
    rw [← hz]
    exact DominantHomFlat.flat_stalkMap_of_comm
      (comparison A B hEF).hom.hom.left A.hom.hom.hom.left
      (𝟙 A.quotient.X.left) B.hom.hom.hom.left
      (by simpa only [Category.comp_id] using hs.symm) z
      (Flat.stalkMap A.hom.hom.hom.left z)
  have hsurj : Surjective (comparison A B hEF).hom.hom.left := by
    have : Surjective (B.hom.hom.hom.left ≫ (comparison A B hEF).hom.hom.left) :=
      hs.symm ▸ inferInstance
    exact Surjective.of_comp B.hom.hom.hom.left (comparison A B hEF).hom.hom.left
  exact ⟨hflat, hsurj⟩

/-- Each actual comparison is an fppf quotient by its full actual kernel. -/
theorem comparison_isFppfQuotient :
    RelativeRoot.IsFppfQuotient
      (SubgroupFunctor.range (kernelι (comparison A B hEF))) (comparison A B hEF) := by
  have : LocallyOfFiniteType
      ((comparison A B hEF).hom.hom.left ≫ A.quotient.X.hom) := by
    rw [Over.w]
    infer_instance
  have : LocallyOfFiniteType (comparison A B hEF).hom.hom.left :=
    locallyOfFiniteType_of_comp _ A.quotient.X.hom
  have : IsLocallyNoetherian A.quotient.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian A.quotient.X.hom
  obtain ⟨hf, hs⟩ := comparison_flat_surjective A B hEF
  exact ⟨hf, hs, inferInstance, rfl⟩

variable {K : GroupScheme (Spec (CommRingCat.of k))} {i : K ⟶ H}
  (hi : F.IsRepresentedBy i)

/-- Restrict the original smaller-kernel quotient to the actual larger
subgroup, with codomain the full comparison kernel. -/
def kernelRestriction : K ⟶ kernel (comparison A B hEF) :=
  hi.restrictionHom ⟨inferInstance, rfl⟩ B.hom
    (comparison_comap_kernel A B hEF).ge

theorem kernelRestriction_comp :
    kernelRestriction A B hEF hi ≫ kernelι (comparison A B hEF) = i ≫ B.hom :=
  hi.restrictionHom_comp ⟨inferInstance, rfl⟩ B.hom
    (comparison_comap_kernel A B hEF).ge

/-- This restriction is the actual base change of the original quotient. -/
theorem kernelRestriction_isPullback :
    IsPullback i.hom.hom (kernelRestriction A B hEF hi).hom.hom
      B.hom.hom.hom (kernelι (comparison A B hEF)).hom.hom :=
  hi.isPullback_of_comap_eq ⟨inferInstance, rfl⟩ B.hom
    (kernelRestriction A B hEF hi) (kernelRestriction_comp A B hEF hi).symm
    (comparison_comap_kernel A B hEF)

/-- The entire kernel of the restricted map is the inverse image of the
original smaller subgroup on every test scheme. -/
theorem range_kernel_kernelRestriction :
    SubgroupFunctor.range (kernelι (kernelRestriction A B hEF hi)) = E.comap i := by
  ext T x
  rw [mem_range_kernelι_iff]
  change x ≫ (kernelRestriction A B hEF hi).hom.hom = 1 ↔
    (x ≫ i.hom.hom) ∈ E.carrier T
  have hmem : (x ≫ i.hom.hom) ∈ E.carrier T ↔
      (x ≫ i.hom.hom) ≫ B.hom.hom.hom = 1 :=
    ⟨fun hx => (mem_range_kernelι_iff B.hom _).mp
      (B.isFppfQuotient.2.2.2.ge T hx),
     fun hx => B.isFppfQuotient.2.2.2.le T
      ((mem_range_kernelι_iff B.hom _).mpr hx)⟩
  rw [hmem]
  have hs : (kernelRestriction A B hEF hi).hom.hom ≫
      (kernelι (comparison A B hEF)).hom.hom = i.hom.hom ≫ B.hom.hom.hom :=
    congrArg (fun f => f.hom.hom) (kernelRestriction_comp A B hEF hi)
  constructor
  · intro hx
    calc
      _ = (x ≫ (kernelRestriction A B hEF hi).hom.hom) ≫
          (kernelι (comparison A B hEF)).hom.hom := by
        rw [Category.assoc, ← hs, ← Category.assoc]
      _ = 1 := by rw [hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono (kernelι (comparison A B hEF)).hom.hom).mp
    rw [MonObj.one_comp, Category.assoc, hs, ← Category.assoc, hx]

/-- The actual larger subgroup maps fppf onto the full comparison kernel,
and its full kernel is the original smaller subgroup pulled back to it. -/
theorem kernelRestriction_isFppfQuotient :
    RelativeRoot.IsFppfQuotient (E.comap i) (kernelRestriction A B hEF hi) := by
  have hpb := (kernelRestriction_isPullback A B hEF hi).map
    (Over.forget (Spec (CommRingCat.of k)))
  have hf : Flat (kernelRestriction A B hEF hi).hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Flat B.hom.hom.hom.left)
  have hs : Surjective (kernelRestriction A B hEF hi).hom.hom.left :=
    MorphismProperty.of_isPullback hpb (inferInstance : Surjective B.hom.hom.hom.left)
  have hp : LocallyOfFinitePresentation
      (kernelRestriction A B hEF hi).hom.hom.left :=
    MorphismProperty.of_isPullback hpb
      (inferInstance : LocallyOfFinitePresentation B.hom.hom.hom.left)
  exact ⟨hf, hs, hp, range_kernel_kernelRestriction A B hEF hi⟩

end QuotientTerm

variable [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom] {N : ℕ}

/-- Generic quotient existence, kept explicit, supplies actual affine
quotients for all terms of the triangular coordinate series. -/
def seriesQuotient (hquot : AffineNormalSubgroupQuotientStatement.{u})
    (j : H ⟶ GeneralLinear.blockParabolicScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ))) (t : ℕ) :
    QuotientTerm (SubgroupFunctor.range (seriesHom
      (j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) _) t)) :=
  Classical.choice (by
    obtain ⟨Q, q, hft, haff, hq⟩ := hquot k H _ _
      (isClosedSubgroup_filtrationHom _ _ _) (isNormal_seriesHom j t)
    exact ⟨⟨Q, q, hft, haff, hq⟩⟩)

end Langlands.GroupScheme.TriangularLayer
