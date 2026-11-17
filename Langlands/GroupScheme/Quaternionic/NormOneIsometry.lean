import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.CentralIsogeny.Basic

/-! # The actual reduced-norm-one subgroup of an isometry group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The kernel of the actual reduced norm restricted to the actual isometry group.
This definition makes no smoothness or connectedness assertion. -/
def normOneIsometryGroup (q : σ.QuadraticForms n) :
    GroupScheme (Spec (CommRingCat.of K)) :=
  kernel (σ.isometryGroupι q ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D))

/-- The inclusion of the reduced-norm-one subgroup in the isometry group. -/
def normOneIsometryGroupι (q : σ.QuadraticForms n) :
    σ.normOneIsometryGroup q ⟶ σ.isometryGroup q :=
  kernelι _

/-- The composite inclusion in the actual matrix-algebra unit group. -/
def normOneIsometryAmbientι (q : σ.QuadraticForms n) :
    σ.normOneIsometryGroup q ⟶ CentralSimpleUnits.groupScheme K (Matrix n n D) :=
  σ.normOneIsometryGroupι q ≫ σ.isometryGroupι q

instance mono_isometryGroupι (q : σ.QuadraticForms n) :
    Mono (σ.isometryGroupι q).hom.hom := by
  have : IsClosedImmersion (σ.isometryGroupι q).hom.hom.left :=
    σ.isClosedSubgroup_isometryGroupι q
  exact Over.mono_of_mono_left _

instance mono_normOneIsometryAmbientι (q : σ.QuadraticForms n) :
    Mono (σ.normOneIsometryAmbientι q).hom.hom := by
  have : Mono (σ.normOneIsometryGroupι q).hom.hom := kernelι_mono _
  rw [normOneIsometryAmbientι, Grp.comp_hom_hom]
  infer_instance

theorem isClosedSubgroup_normOneIsometryGroupι (q : σ.QuadraticForms n) :
    IsClosedSubgroup (σ.normOneIsometryGroupι q) := by
  have : IsSeparated (Gm (Spec (CommRingCat.of K))).X.hom := by
    have : IsSeparated Gm.overSpecZ.{u}.hom := by
      change IsSeparated (Spec.map _)
      infer_instance
    change IsSeparated (Limits.pullback.snd _ (Gm.toSpecZ _))
    infer_instance
  exact kernelι_isClosedImmersion _

theorem isClosedSubgroup_normOneIsometryAmbientι (q : σ.QuadraticForms n) :
    IsClosedSubgroup (σ.normOneIsometryAmbientι q) :=
  (σ.isClosedSubgroup_normOneIsometryGroupι q).comp
    (σ.isClosedSubgroup_isometryGroupι q)

/-- On every test scheme, membership is exactly the reduced-norm-one equation. -/
theorem mem_range_normOneIsometryGroupι_iff (q : σ.QuadraticForms n)
    {T : Over (Spec (CommRingCat.of K))} (y : T ⟶ (σ.isometryGroup q).X) :
    y ∈ (SubgroupFunctor.range (σ.normOneIsometryGroupι q)).carrier T ↔
      y ≫ (σ.isometryGroupι q).hom.hom ≫
        (CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
  have h := mem_range_kernelι_iff
    (σ.isometryGroupι q ≫ CentralSimpleUnits.reducedNormHom K (Matrix n n D)) y
  rw [Grp.comp_hom_hom] at h
  exact h

/-- The full range is the intersection of the isometry subgroup and the actual
reduced-norm-one subgroup, on every test scheme. -/
theorem mem_range_normOneIsometryAmbientι_iff (q : σ.QuadraticForms n)
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (CentralSimpleUnits.groupScheme K (Matrix n n D)).X) :
    x ∈ (SubgroupFunctor.range (σ.normOneIsometryAmbientι q)).carrier T ↔
      x ∈ (SubgroupFunctor.range (σ.isometryGroupι q)).carrier T ∧
        x ≫ (CentralSimpleUnits.reducedNormHom K (Matrix n n D)).hom.hom = 1 := by
  rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range, normOneIsometryAmbientι,
    Grp.comp_hom_hom]
  constructor
  · rintro ⟨y, rfl⟩
    have hk := (σ.mem_range_normOneIsometryGroupι_iff q
      (y ≫ (σ.normOneIsometryGroupι q).hom.hom)).1
        (SubgroupFunctor.mem_range.2 ⟨y, rfl⟩)
    exact ⟨⟨y ≫ (σ.normOneIsometryGroupι q).hom.hom, Category.assoc _ _ _⟩,
      by simpa only [Category.assoc] using hk⟩
  · rintro ⟨⟨y, rfl⟩, hN⟩
    have hk := (σ.mem_range_normOneIsometryGroupι_iff q y).2 (by
      rw [← Category.assoc]
      exact hN)
    obtain ⟨z, rfl⟩ := SubgroupFunctor.mem_range.1 hk
    exact ⟨z, (Category.assoc _ _ _).symm⟩

/-- The range criterion in tensor coordinates, for any representative of the
quadratic form and any test scheme, including nonreduced tests. -/
theorem mem_range_normOneIsometryAmbientι_iff_equations (q : σ.QuadraticForms n)
    (Q : Matrix n n D) (hQ : (Submodule.Quotient.mk Q : σ.QuadraticForms n) = q)
    {T : Over (Spec (CommRingCat.of K))}
    (x : T ⟶ (CentralSimpleUnits.groupScheme K (Matrix n n D)).X) :
    x ∈ (SubgroupFunctor.range (σ.normOneIsometryAmbientι q)).carrier T ↔
      IsometryCut.defect (σ.matrix n) Q
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T x :
            ((algΓ (CommRingCat.of K)).obj T).unop ⊗[K] Matrix n n D) ∈
        (σ.quadraticKernel n).baseChange ((algΓ (CommRingCat.of K)).obj T).unop ∧
      Langlands.CentralSimple.reducedNormUnits K (Matrix n n D)
          ((algΓ (CommRingCat.of K)).obj T).unop
          (FiniteAlgebraUnits.pointsEquiv (Module.finBasis K (Matrix n n D)) T x) = 1 := by
  rw [mem_range_normOneIsometryAmbientι_iff, mem_range_isometryGroupι_iff σ q Q hQ]
  refine and_congr_right fun _ => ?_
  rw [← (Gm.pointsEquiv (Spec (CommRingCat.of K)) T).injective.eq_iff,
    CentralSimpleUnits.reducedNormHom_points, _root_.map_one]
  rfl

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
