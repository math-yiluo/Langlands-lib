import Langlands.GroupScheme.Lie.SmoothScalarExtension
import Langlands.GroupScheme.Lie.LinearBaseChangeNaturality
import Langlands.GroupScheme.Lie.SmoothDifferential
import Langlands.GroupScheme.Torus.LocalSpecialization
import Mathlib.RingTheory.LocalRing.Module

/-! # Surjective differentials detected on the special fibre of a local base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Lie

/-- Surjectivity of the specified actual differential over the coefficient algebra. -/
def HasSurjectiveDifferential
    {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A] : Prop :=
  Function.Surjective (targetMapLinear f A)

/-- Surjectivity of a map to a finite module over a local ring is detected
by tensoring with its residue field. -/
theorem surjective_of_lTensor_residueField_surjective
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] (f : M →ₗ[R] N)
    (hf : Function.Surjective (f.lTensor (IsLocalRing.ResidueField R))) :
    Function.Surjective f := by
  let k := IsLocalRing.ResidueField R
  have hm : Function.Surjective (TensorProduct.mk R k M 1) :=
    TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
  have hh : Function.Surjective
      ((TensorProduct.mk R k N 1).comp f) := by
    have h := hf.comp hm
    convert h using 1
    funext x
    rfl
  apply LinearMap.range_eq_top.mp
  apply IsLocalRing.map_tensorProduct_mk_eq_top.mp
  rw [← LinearMap.range_comp]
  exact LinearMap.range_eq_top.mpr hh

section ScalarExtension

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [Smooth G.X.hom] [Smooth H.X.hom]
  (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A]

/-- Actual smooth Lie scalar extension intertwines the specified differential. -/
theorem targetMapLinear_smoothKernelScalarExtension
    (x : A ⊗[R] Additive (lieKernel G R)) :
    targetMapLinear f A (smoothKernelScalarExtension G A x) =
      smoothKernelScalarExtension H A ((targetMapLinear f R).baseChange A x) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    simp only [smoothKernelScalarExtension_tmul, LinearMap.baseChange_tmul,
      map_smul, lieKernelTargetLinear_map]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Surjectivity of the base differential extends to every coefficient algebra
for smooth affine source and target over any commutative ring. -/
theorem targetMapLinear_surjective_of_base
    (hf : Function.Surjective (targetMapLinear f R)) :
    Function.Surjective (targetMapLinear f A) := by
  intro y
  obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective A hf
    ((smoothKernelScalarExtension H A).symm y)
  refine ⟨smoothKernelScalarExtension G A x, ?_⟩
  change (targetMapLinear f R).baseChange A x = _ at hx
  rw [targetMapLinear_smoothKernelScalarExtension, hx,
    LinearEquiv.apply_symm_apply]

end ScalarExtension

/-- An isomorphism on the special fibre of a homomorphism of smooth affine
groups over a local ring forces its actual differential to be surjective
on every coefficient algebra. -/
theorem hasSurjectiveDifferential_of_specialFibreIso
    {R : Type u} [CommRing R] [IsLocalRing R]
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [Smooth G.X.hom] [Smooth H.X.hom]
    (f : G ⟶ H) (hf : TorusLocalSpecialization.IsSpecialFibreIsomorphism f)
    (A : Type u) [CommRing A] [Algebra R A] :
    HasSurjectiveDifferential f A := by
  let k := IsLocalRing.ResidueField R
  let b := algebraBaseMap R k
  let Gk := (GroupScheme.baseChange b).obj G
  let Hk := (GroupScheme.baseChange b).obj H
  have : IsAffineHom Gk.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b))
  have : IsAffineHom Hk.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b))
  have : IsIso ((GroupScheme.baseChange b).map f) := hf
  have hfs : Smooth ((GroupScheme.baseChange b).map f).hom.hom.left := by
    have : IsIso ((GroupScheme.baseChange b).map f).hom.hom :=
      (Grp.forget (Over (Spec (CommRingCat.of k)))).map_isIso
        ((GroupScheme.baseChange b).map f)
    have : IsIso ((GroupScheme.baseChange b).map f).hom.hom.left :=
      (Over.forget (Spec (CommRingCat.of k))).map_isIso
        ((GroupScheme.baseChange b).map f).hom.hom
    infer_instance
  have hfk : Function.Surjective
      (targetMapLinear ((GroupScheme.baseChange b).map f) k) :=
    targetMapLinear_surjective_of_smooth _ k hfs
  have hforig : Function.Surjective (targetMapLinear f k) := by
    intro y
    obtain ⟨x, hx⟩ := hfk ((kernelBaseChangeLinearEquiv R k H k).symm y)
    refine ⟨kernelBaseChangeLinearEquiv R k G k x, ?_⟩
    rw [← kernelBaseChangeLinearEquiv_target R k k, hx,
      LinearEquiv.apply_symm_apply]
  have hft : Function.Surjective ((targetMapLinear f R).baseChange k) := by
    intro y
    obtain ⟨x, hx⟩ := hforig (smoothKernelScalarExtension H k y)
    refine ⟨(smoothKernelScalarExtension G k).symm x, ?_⟩
    apply (smoothKernelScalarExtension H k).injective
    rw [← targetMapLinear_smoothKernelScalarExtension,
      LinearEquiv.apply_symm_apply, hx]
  have : Module.Finite R (Additive (lieKernel H R)) :=
    finite_lieKernel_of_smooth H
  have hfr : Function.Surjective (targetMapLinear f R) :=
    surjective_of_lTensor_residueField_surjective _ hft
  exact targetMapLinear_surjective_of_base f A hfr

end Langlands.GroupScheme.Lie
