import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.AbelianScheme.Kernel

/-! # Retracts of tori and kernels of homomorphisms with a section -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Retract

variable {k : Type u} [Field k]
    {T H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

/-- An affine group-scheme retract of a split torus is a split torus. -/
theorem IsSplitTorus.of_retract (hT : IsSplitTorus T) (r : T ⟶ H) (s : H ⟶ T)
    (hs : s ≫ r = 𝟙 H) : IsSplitTorus H := by
  obtain ⟨D, p, i, hi, hp, _⟩ := hT.exists_factor_isSplitSubtorus' r
  let : IsClosedImmersion i.hom.hom.left := hi.2
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono i := (Grp.forget _).mono_of_mono_map (f := i) ‹Mono i.hom.hom›
  have hsplit : (s ≫ p) ≫ i = 𝟙 H := by rw [Category.assoc, hp, hs]
  let : IsSplitEpi i := ⟨⟨s ≫ p, hsplit⟩⟩
  let : IsIso i := isIso_of_mono_of_isSplitEpi i
  exact IsSplitTorus.of_iso (asIso i).symm hi.1

/-- An affine group-scheme retract of a torus is a torus. The same retraction
after a splitting extension reduces this to the split case. -/
theorem IsTorus.of_retract (hT : IsTorus T) (r : T ⟶ H) (s : H ⟶ T)
    (hs : s ≫ r = 𝟙 H) : IsTorus H := by
  obtain ⟨K, hK, aK, hsplit⟩ := hT
  let := hK
  let := aK
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let : IsAffineHom ((GroupScheme.baseChange b).obj H).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b)
    infer_instance
  refine ⟨K, hK, aK, hsplit.of_retract
    ((GroupScheme.baseChange b).map r) ((GroupScheme.baseChange b).map s) ?_⟩
  rw [← Functor.map_comp, hs]
  exact (GroupScheme.baseChange b).map_id H

end Retract

namespace Torus

section SectionKernel

variable {B : Scheme.{u}} {T : CommGroupScheme B} {D : GroupScheme B}
    (q : T.toGrp ⟶ D) (s : D ⟶ T.toGrp) (hs : s ≫ q = 𝟙 D)

include hs in
private theorem section_points (V : Over B) (d : V ⟶ D.X) :
    (d ≫ s.hom.hom) ≫ q.hom.hom = d := by
  change d ≫ (s ≫ q).hom.hom = d
  rw [hs]
  exact Category.comp_id d

/-- Remove the section component of a point in the commutative source and
regard the result as an actual kernel point. -/
def sectionKernelRetractionPoints (V : Over B) :
    (V ⟶ T.X) →* (V ⟶ (kernel q).X) :=
  (kernelPointsEquiv q V).symm.toMonoidHom.comp
    { toFun := fun x => ⟨x * (x ≫ q.hom.hom ≫ s.hom.hom)⁻¹, by
        change (x * (x ≫ q.hom.hom ≫ s.hom.hom)⁻¹) ≫ q.hom.hom = 1
        rw [MonObj.mul_comp, GrpObj.inv_comp]
        rw [show (x ≫ q.hom.hom ≫ s.hom.hom) ≫ q.hom.hom = x ≫ q.hom.hom by
          simpa only [Category.assoc] using section_points q s hs V (x ≫ q.hom.hom)]
        exact mul_inv_cancel _⟩
      map_one' := by
        apply Subtype.ext
        simp only [MonObj.one_comp, inv_one, one_mul]
        rfl
      map_mul' := by
        intro x y
        apply Subtype.ext
        simp only [MonObj.mul_comp, mul_inv_rev]
        change (x * y) *
            ((y ≫ q.hom.hom ≫ s.hom.hom)⁻¹ *
              (x ≫ q.hom.hom ≫ s.hom.hom)⁻¹) =
          (x * (x ≫ q.hom.hom ≫ s.hom.hom)⁻¹) *
            (y * (y ≫ q.hom.hom ≫ s.hom.hom)⁻¹)
        ac_rfl }

@[simp] theorem sectionKernelRetractionPoints_comp (V : Over B) (x : V ⟶ T.X) :
    sectionKernelRetractionPoints q s hs V x ≫ (kernelι q).hom.hom =
      x * (x ≫ q.hom.hom ≫ s.hom.hom)⁻¹ := by
  change ((kernelPointsEquiv q V)
    ((kernelPointsEquiv q V).symm _)).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem sectionKernelRetractionPoints_naturality {V W : Over B} (f : W ⟶ V)
    (x : V ⟶ T.X) :
    sectionKernelRetractionPoints q s hs W (f ≫ x) =
      f ≫ sectionKernelRetractionPoints q s hs V x := by
  apply (cancel_mono (kernelι q).hom.hom).mp
  rw [sectionKernelRetractionPoints_comp,
    Category.assoc f (sectionKernelRetractionPoints q s hs V x) (kernelι q).hom.hom,
    sectionKernelRetractionPoints_comp, MonObj.comp_mul, GrpObj.comp_inv]
  simp only [Category.assoc]

/-- The actual retraction of the kernel inclusion supplied by a section of
a homomorphism from a commutative group scheme. -/
def sectionKernelRetraction : T.toGrp ⟶ kernel q :=
  homOfPoints (sectionKernelRetractionPoints q s hs)
    (sectionKernelRetractionPoints_naturality q s hs)

@[simp] theorem sectionKernelRetraction_points (V : Over B) (x : V ⟶ T.X) :
    (x ≫ (sectionKernelRetraction q s hs).hom.hom) ≫ (kernelι q).hom.hom =
      x * (x ≫ q.hom.hom ≫ s.hom.hom)⁻¹ := by
  rw [sectionKernelRetraction, comp_homOfPoints]
  exact sectionKernelRetractionPoints_comp q s hs V x

/-- The constructed map is a retraction of the original kernel inclusion,
as an equality of actual group-scheme morphisms. -/
theorem kernelι_sectionKernelRetraction :
    kernelι q ≫ sectionKernelRetraction q s hs = 𝟙 (kernel q) := by
  apply hom_ext_points
  intro V x
  apply (cancel_mono (kernelι q).hom.hom).mp
  change ((x ≫ (kernelι q).hom.hom) ≫
    (sectionKernelRetraction q s hs).hom.hom) ≫ (kernelι q).hom.hom =
      (x ≫ (𝟙 (kernel q) : kernel q ⟶ kernel q).hom.hom) ≫ (kernelι q).hom.hom
  rw [sectionKernelRetraction_points]
  have hx := (kernelPointsEquiv q V x).property
  change (x ≫ (kernelι q).hom.hom) ≫ q.hom.hom = 1 at hx
  rw [← Category.assoc (x ≫ (kernelι q).hom.hom), hx,
    MonObj.one_comp, inv_one, mul_one, Grp.id_hom_hom, Category.comp_id]

end SectionKernel

section Field

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {D : GroupScheme (Spec (CommRingCat.of k))}
    (q : T.toGrp ⟶ D) (s : D ⟶ T.toGrp) (hs : s ≫ q = 𝟙 D)
    [IsAffineHom (kernel q).X.hom]

include s hs in
/-- An affine actual kernel of a sectioned homomorphism from a split torus
is a split torus. -/
theorem isSplitTorus_kernel_of_section (hT : IsSplitTorus T.toGrp) :
    IsSplitTorus (kernel q) :=
  hT.of_retract (sectionKernelRetraction q s hs) (kernelι q)
    (kernelι_sectionKernelRetraction q s hs)

include s hs in
/-- An affine actual kernel of a sectioned homomorphism from a torus
is a torus, over the original field. -/
theorem isTorus_kernel_of_section (hT : IsTorus T.toGrp) :
    IsTorus (kernel q) :=
  hT.of_retract (sectionKernelRetraction q s hs) (kernelι q)
    (kernelι_sectionKernelRetraction q s hs)

end Field

end Torus

end Langlands.GroupScheme
