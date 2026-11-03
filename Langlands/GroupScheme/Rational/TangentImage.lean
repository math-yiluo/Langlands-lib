import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.ActionWeightComparisonProof
import Langlands.GroupScheme.Rational.SplitTorusFiniteRank
import Langlands.GroupScheme.Lie.ActionWeights

/-! # Intrinsic tangent submodules and exact Lie images of subgroup functors -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section TargetMaps

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    (j : H ⟶ G) (A : Type u) [CommRing A] [Algebra R A]

/-- Postcomposition commutes with the actual epsilon scaling. -/
theorem lieKernelTarget_scale (c : A) (x : lieKernel H A) :
    Lie.targetMap j A (lieKernelScale H c x) =
      lieKernelScale G c (Lie.targetMap j A x) := by
  apply Subtype.ext
  exact Category.assoc _ _ _

variable [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

@[simp] theorem lieKernelTargetLinear_val (x : Additive (lieKernel H A)) :
    (Lie.targetMapLinear j A x).toMul.val = x.toMul.val ≫ j.hom.hom := rfl

end TargetMaps

namespace RelativeRoot

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The actual tangent image of an all-test subgroup, with scalar closure supplied
by its restriction law for epsilon-scaling maps. -/
def tangentSubmodule (F : SubgroupFunctor G) :
    Submodule k (Additive (lieKernel G k)) where
  carrier := {X | X.toMul.val ∈ F.carrier
    ((algSpec (CommRingCat.of k)).obj
      (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k))))}
  zero_mem' := (F.carrier _).one_mem
  add_mem' hX hY := (F.carrier _).mul_mem hX hY
  smul_mem' c _X hX := F.comp_mem
    ((algSpec (CommRingCat.of k)).map
      (CommAlgCat.ofHom (GeneralLinear.DualNumber.epsilonScaleAlg c)).op) hX

@[simp] theorem mem_tangentSubmodule (F : SubgroupFunctor G)
    (X : Additive (lieKernel G k)) :
    X ∈ tangentSubmodule F ↔ X.toMul.val ∈ F.carrier
      ((algSpec (CommRingCat.of k)).obj
        (op (CommAlgCat.of (CommRingCat.of k) (DualNumber k)))) := Iff.rfl

/-- Inclusions on every test induce inclusions of actual tangent submodules. -/
theorem tangentSubmodule_mono {F F' : SubgroupFunctor G} (h : F ≤ F') :
    tangentSubmodule F ≤ tangentSubmodule F' :=
  fun _ hX => h _ hX

@[simp] theorem tangentSubmodule_inf (F F' : SubgroupFunctor G) :
    tangentSubmodule (F ⊓ F') = tangentSubmodule F ⊓ tangentSubmodule F' := rfl

@[simp] theorem tangentSubmodule_top :
    tangentSubmodule (⊤ : SubgroupFunctor G) = ⊤ := rfl

@[simp] theorem tangentSubmodule_bot :
    tangentSubmodule (⊥ : SubgroupFunctor G) = ⊥ := by
  ext X
  change X.toMul.val = 1 ↔ X = 0
  constructor
  · intro h
    apply Additive.toMul.injective
    exact Subtype.ext h
  · rintro rfl
    rfl

/-- The published exact Lie-image predicate is equality with the intrinsic tangent submodule. -/
theorem hasLieImage_iff_tangentSubmodule_eq (F : SubgroupFunctor G)
    (W : Submodule k (Additive (lieKernel G k))) :
    HasLieImage F W ↔ tangentSubmodule F = W := by
  constructor
  · intro h
    exact Submodule.ext h
  · rintro rfl X
    rfl

/-- Every all-test subgroup has its intrinsic tangent submodule as exact Lie image. -/
theorem hasLieImage_tangentSubmodule (F : SubgroupFunctor G) :
    HasLieImage F (tangentSubmodule F) := fun _ => Iff.rfl

/-- Exact Lie images are unique, without any representability hypothesis. -/
theorem HasLieImage.unique {F : SubgroupFunctor G}
    {W W' : Submodule k (Additive (lieKernel G k))}
    (h : HasLieImage F W) (h' : HasLieImage F W') : W = W' :=
  (hasLieImage_iff_tangentSubmodule_eq F W).mp h |>.symm.trans
    ((hasLieImage_iff_tangentSubmodule_eq F W').mp h')

/-- An inclusion of subgroup functors gives the corresponding inclusion of their exact Lie images. -/
theorem HasLieImage.mono {F F' : SubgroupFunctor G}
    {W W' : Submodule k (Additive (lieKernel G k))}
    (h : HasLieImage F W) (h' : HasLieImage F' W') (hFF' : F ≤ F') : W ≤ W' := by
  rw [← (hasLieImage_iff_tangentSubmodule_eq F W).mp h,
    ← (hasLieImage_iff_tangentSubmodule_eq F' W').mp h']
  exact tangentSubmodule_mono hFF'

section Represented

variable {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]
    (j : H ⟶ G) [Mono j.hom.hom]

/-- For a monomorphic representative, the intrinsic tangent submodule is the
range of the actual differential. Monicity forces any lift of an identity-kernel
point to belong to the identity kernel itself. -/
theorem tangentSubmodule_range :
    tangentSubmodule (SubgroupFunctor.range j) = LinearMap.range (Lie.targetMapLinear j k) := by
  ext X
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : Lie.reduction H y = 1 := by
      apply (cancel_mono j.hom.hom).mp
      calc
        Lie.reduction H y ≫ j.hom.hom = Lie.reduction G (y ≫ j.hom.hom) :=
          Category.assoc _ _ _
        _ = Lie.reduction G X.toMul.val := congrArg (Lie.reduction G) hy
        _ = 1 := X.toMul.property
        _ = 1 ≫ j.hom.hom := (MonObj.one_comp j.hom.hom).symm
    refine ⟨Additive.ofMul ⟨y, hy0⟩, ?_⟩
    apply Additive.toMul.injective
    exact Subtype.ext hy
  · rintro ⟨Y, rfl⟩
    exact ⟨Y.toMul.val, rfl⟩

/-- A monomorphic representative has precisely its differential range as Lie image. -/
theorem hasLieImage_range :
    HasLieImage (SubgroupFunctor.range j) (LinearMap.range (Lie.targetMapLinear j k)) :=
  (hasLieImage_iff_tangentSubmodule_eq _ _).mpr (tangentSubmodule_range j)

omit [Mono j.hom.hom] in
theorem hasLieImage_of_isRepresentedBy {F : SubgroupFunctor G}
    (hj : F.IsRepresentedBy j) :
    HasLieImage F (LinearMap.range (Lie.targetMapLinear j k)) := by
  have : Mono j.hom.hom := hj.1
  rw [← hj.2]
  exact hasLieImage_range j

end Represented

section Weights

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    (b : AutomorphicAction S.toGrp G)

/-- The intrinsic eigenvector span is the existing differential weight space. -/
theorem actionWeightSpace_eq_lieWeightSpace (χ : characterLattice S) :
    actionWeightSpace b χ = b.lieWeightSpace (𝟙 S.toGrp) χ := by
  ext X
  rw [mem_actionWeightSpace_iff]
  constructor
  · intro h A _ _ s
    apply Additive.toMul.injective
    apply Subtype.ext
    simpa only [AutomorphicAction.differential_val, lieKernel_smul_toMul,
      lieKernelMapLinear_toMul, Grp.id_hom_hom, Category.comp_id] using h A s
  · intro h A _ _ s
    have h' := congrArg (fun z : Additive (lieKernel G A) => z.toMul.val) (h A s)
    simpa only [AutomorphicAction.differential_val, lieKernel_smul_toMul,
      lieKernelMapLinear_toMul, Grp.id_hom_hom, Category.comp_id] using h'

/-- Stability on all tests implies stability of the intrinsic tangent submodule
under the differential of every ground-field torus point. -/
theorem differential_mem_tangentSubmodule {F : SubgroupFunctor G}
    (hF : b.IsStable F) (s : Lie.AffinePoints S.toGrp k)
    {X : Additive (lieKernel G k)} (hX : X ∈ tangentSubmodule F) :
    b.differential s X ∈ tangentSubmodule F :=
  hF _ (Lie.constant S.toGrp s) X.toMul.val hX

/-- A character occurs precisely when its weight space meets the intrinsic
tangent submodule in a nonzero vector. -/
theorem mem_actionWeightSupport_iff (F : SubgroupFunctor G) (χ : characterLattice S) :
    χ ∈ actionWeightSupport b F ↔
      actionWeightSpace b χ ⊓ tangentSubmodule F ≠ ⊥ := by
  rw [Submodule.ne_bot_iff]
  constructor
  · rintro ⟨X, hX, hχ, hF⟩
    exact ⟨X, ⟨hχ, hF⟩, hX⟩
  · rintro ⟨X, ⟨hχ, hF⟩, hX⟩
    exact ⟨X, hX, hχ, hF⟩

/-- Specifying the exact Lie image determines the entire intrinsic weight support. -/
theorem HasLieImage.actionWeightSupport_eq {F : SubgroupFunctor G}
    {W : Submodule k (Additive (lieKernel G k))} (hF : HasLieImage F W) :
    actionWeightSupport b F = {χ | actionWeightSpace b χ ⊓ W ≠ ⊥} := by
  ext χ
  rw [mem_actionWeightSupport_iff, (hasLieImage_iff_tangentSubmodule_eq F W).mp hF]
  rfl

end Weights

end RelativeRoot
end Langlands.GroupScheme
