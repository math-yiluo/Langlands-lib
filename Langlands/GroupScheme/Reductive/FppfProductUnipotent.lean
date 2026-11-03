import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.MatrixRepresentation.CommonFixedVector
import Langlands.GroupScheme.Reductive.FppfProductFixedVectors

/-! # Unipotence of represented fppf products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme

namespace SubgroupFunctor

variable {S : Scheme.{u}} {G H J P : GroupScheme S}

/-- Normality of an image is reflected by a monic ambient inclusion. -/
theorem isNormal_range_of_mono_comp (q : H ⟶ P) (p : P ⟶ G)
    [Mono p.hom.hom] (hN : (range (q ≫ p)).IsNormal) :
    (range q).IsNormal := by
  intro T g x _ hx
  obtain ⟨y, rfl⟩ := mem_range.mp hx
  have hy : y ≫ (q ≫ p).hom.hom ∈ (range (q ≫ p)).carrier T :=
    mem_range.mpr ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := mem_range.mp
    (hN T (g ≫ p.hom.hom) (y ≫ (q ≫ p).hom.hom) (Subgroup.mem_top _) hy)
  apply mem_range.mpr
  refine ⟨z, ?_⟩
  apply (cancel_mono p.hom.hom).1
  simpa only [Grp.comp_hom_hom, Category.assoc, MonObj.mul_comp,
    GrpObj.inv_comp] using hz

namespace IsFppfProduct

variable {F N : SubgroupFunctor G} {p : P ⟶ G} {i : H ⟶ G} {j : J ⟶ G}

/-- The actual homomorphism from the left represented factor into the product. -/
def leftFactor (hp : IsFppfProduct F N p) (hH : F.IsRepresentedBy i) : H ⟶ P := by
  let : Mono i.hom.hom := hH.1
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  exact factorOfRangeLE (hH.2 ▸ hp.left_le)

/-- The actual homomorphism from the right represented factor into the product. -/
def rightFactor (hp : IsFppfProduct F N p) (hJ : N.IsRepresentedBy j) : J ⟶ P := by
  let : Mono j.hom.hom := hJ.1
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  exact factorOfRangeLE (hJ.2 ▸ hp.right_le)

theorem leftFactor_comp (hp : IsFppfProduct F N p) (hH : F.IsRepresentedBy i) :
    hp.leftFactor hH ≫ p = i := by
  let : Mono i.hom.hom := hH.1
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  exact factorOfRangeLE_comp (hH.2 ▸ hp.left_le)

theorem rightFactor_comp (hp : IsFppfProduct F N p) (hJ : N.IsRepresentedBy j) :
    hp.rightFactor hJ ≫ p = j := by
  let : Mono j.hom.hom := hJ.1
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  exact factorOfRangeLE_comp (hJ.2 ▸ hp.right_le)

/-- Product multiplication is the ordered product of the lifted factor points. -/
theorem productMul_eq_lifted_mul (hp : IsFppfProduct F N p)
    (hH : F.IsRepresentedBy i) (hJ : N.IsRepresentedBy j) :
    hp.productMul hH hJ =
      (fst H.X J.X ≫ (hp.leftFactor hH).hom.hom) *
        (snd H.X J.X ≫ (hp.rightFactor hJ).hom.hom) := by
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  apply (cancel_mono p.hom.hom).1
  rw [hp.productMul_comp hH hJ, MonObj.mul_comp]
  simp only [Category.assoc, ← Grp.comp_hom_hom, leftFactor_comp, rightFactor_comp]

end IsFppfProduct

end SubgroupFunctor

namespace MatrixRepresentation

variable {R : CommRingCat.{u}} {G H J P : GroupScheme (Spec R)}
variable {n : Type} [Fintype n] [DecidableEq n]

/-- All-test fixedness descends from the lifted factors to their product. -/
theorem isFixedVector_of_fppfProduct (ρ : MatrixRepresentation P n)
    {F N : SubgroupFunctor G} {p : P ⟶ G} {i : H ⟶ G} {j : J ⟶ G}
    (hp : SubgroupFunctor.IsFppfProduct F N p)
    (hH : F.IsRepresentedBy i) (hJ : N.IsRepresentedBy j)
    (v : n → R)
    (hfixH : (ρ.restrict (hp.leftFactor hH)).IsFixedVector v)
    (hfixJ : (ρ.restrict (hp.rightFactor hJ)).IsFixedVector v) :
    ρ.IsFixedVector v := by
  let m := hp.productMul hH hJ
  let : Epi m.left := hp.epi_productMul hH hJ
  apply (ρ.isFixedVector_iff_epi_point m v).2
  change (ρ.pointMatrix _ (hp.productMul hH hJ) :
    Matrix n n Γ((H.X ⊗ J.X).left, ⊤)) *ᵥ _ = _
  rw [hp.productMul_eq_lifted_mul hH hJ, map_mul,
    Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  rw [← pointMatrix_restrict ρ (hp.rightFactor hJ),
    hfixJ (H.X ⊗ J.X) (snd H.X J.X)]
  exact hfixH (H.X ⊗ J.X) (fst H.X J.X)

end MatrixRepresentation

variable {k : Type u} [Field k]
variable {G H J P : GroupScheme (Spec (CommRingCat.of k))}

/-- A supplied represented fppf product of affine unipotent factors is unipotent
when the first factor has normal image in the ambient group scheme. -/
theorem isUnipotent_fppfProduct (i : H ⟶ G) (j : J ⟶ G) (p : P ⟶ G)
    (hi : IsClosedSubgroup i) (hj : IsClosedSubgroup j)
    (hp : SubgroupFunctor.IsFppfProduct (SubgroupFunctor.range i)
      (SubgroupFunctor.range j) p)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (hAffH : IsAffine H.X.left) (hAffJ : IsAffine J.X.left)
    (hH : IsUnipotent H) (hJ : IsUnipotent J) :
    IsUnipotent P := by
  let : IsClosedImmersion i.hom.hom.left := hi
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono p.hom.hom := Over.mono_of_mono_left _
  let hrepH : (SubgroupFunctor.range i).IsRepresentedBy i := ⟨inferInstance, rfl⟩
  let hrepJ : (SubgroupFunctor.range j).IsRepresentedBy j := ⟨inferInstance, rfl⟩
  have hnormal : (SubgroupFunctor.range (hp.leftFactor hrepH)).IsNormal := by
    apply SubgroupFunctor.isNormal_range_of_mono_comp _ p
    rwa [hp.leftFactor_comp hrepH]
  intro n _ _ _ ρ
  obtain ⟨v, hv, hvH, hvJ⟩ := ρ.exists_common_fixedVector
    (hp.leftFactor hrepH) (hp.rightFactor hrepJ) hnormal hAffH hAffJ hH hJ
  exact ⟨v, hv, ρ.isFixedVector_of_fppfProduct hp hrepH hrepJ v hvH hvJ⟩

end Langlands.GroupScheme
