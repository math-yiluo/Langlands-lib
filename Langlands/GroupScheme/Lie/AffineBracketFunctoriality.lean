import Langlands.GroupScheme.Lie.AffineBracket
import Langlands.GroupScheme.AffineHopfMorphism
import Langlands.GroupScheme.AffineCoordinateEvaluation
import Langlands.GroupScheme.Lie.KernelTargetMaps
import Langlands.GroupScheme.Lie.GroupAlgebraCoefficientMaps

/-! # Functoriality of the affine tangent Lie bracket -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite WithConv

namespace Langlands.GroupScheme.Lie

open AffineCoordinates AffineHopfMorphism

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

private local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

set_option backward.isDefEq.respectTransparency false in
private theorem algSpec_map_pullback (f : G ⟶ H) :
    (algSpec R).map (CommAlgCat.ofHom (pullback f).hom.toAlgHom).op =
      (coordinateSchemeIso G).hom ≫ f.hom.hom ≫ (coordinateSchemeIso H).inv := by
  have h := congrArg (fun z => z.hom.hom) (AffineHopfMorphism.pullback_map f)
  change (algSpec R).map (CommAlgCat.ofHom (pullback f).hom.toAlgHom).op =
    (hopfSpecIso G).hom.hom.hom ≫ f.hom.hom ≫ (hopfSpecIso H).inv.hom.hom at h
  rw [hopfSpecIso_hom_hom_hom, hopfSpecIso_inv_hom_hom] at h
  exact h

variable {A : Type u} [CommRing A] [Algebra R A]

private abbrev hopfPoint (x : AffinePoints G A) : hopfAlgebra G →ₐ[R] A :=
  ((pointEquiv G (CommAlgCat.of R A)).symm x).hom

private theorem pointEquiv_hopfPoint (x : AffinePoints G A) :
    pointEquiv G (CommAlgCat.of R A) (CommAlgCat.ofHom (hopfPoint x)) = x :=
  Equiv.apply_symm_apply _ _

set_option backward.isDefEq.respectTransparency false in
private theorem hopfPoint_target (f : G ⟶ H) (x : AffinePoints G A) :
    hopfPoint (G := H) (x ≫ f.hom.hom) = (hopfPoint x).comp (pullback f).hom.toAlgHom := by
  have h : CommAlgCat.ofHom (hopfPoint (G := H) (x ≫ f.hom.hom)) =
      (CommAlgCat.ofHom (pullback f).hom.toAlgHom) ≫ CommAlgCat.ofHom (hopfPoint x) := by
    apply (pointEquiv H (CommAlgCat.of R A)).injective
    rw [pointEquiv_hopfPoint, pointEquiv_comp]
    change x ≫ f.hom.hom = (algSpec R).map (CommAlgCat.ofHom (hopfPoint x)).op ≫
      ((algSpec R).map (CommAlgCat.ofHom (pullback f).hom.toAlgHom).op ≫
        (coordinateSchemeIso H).hom)
    rw [algSpec_map_pullback]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change x ≫ f.hom.hom = (pointEquiv G (CommAlgCat.of R A)
      (CommAlgCat.ofHom (hopfPoint x))) ≫ f.hom.hom
    rw [pointEquiv_hopfPoint]
  exact congrArg CommAlgCat.Hom.hom h

/-- The Hopf-coordinate counit derivation is the infinitesimal coefficient
of the algebra homomorphism classifying the actual dual-number point. -/
theorem kernelCounitDerivationLinearEquiv_eq_snd
    (x : Additive (lieKernel G A)) (b : hopfAlgebra G) :
    (kernelCounitDerivationLinearEquiv G x).val b =
      (((pointEquiv G (CommAlgCat.of R (DualNumber A))).symm x.toMul.val).hom b).snd := by
  change (kernelCounitDerivationLinearEquiv G x).val b = (hopfPoint x.toMul.val b).snd
  have h : CommAlgCat.ofHom (hopfPoint x.toMul.val) = CommAlgCat.ofHom
      ((pointCoordinates G x.toMul.val).comp (lieCoordinateAlgEquiv G).toAlgHom) := by
    apply (pointEquiv G (CommAlgCat.of R (DualNumber A))).injective
    exact (pointEquiv_hopfPoint (A := DualNumber A) x.toMul.val).trans
      (((pointEquiv_comp_lieCoordinateAlgEquiv G (C := CommAlgCat.of R (DualNumber A))
        (pointCoordinates G x.toMul.val)).trans
          ((pointCoordinates G).symm_apply_apply x.toMul.val)).symm)
  rw [kernelCounitDerivationLinearEquiv_apply]
  change (pointCoordinates G x.toMul.val (lieCoordinateAlgEquiv G b)).snd = _
  exact (congrArg (fun φ => (φ.hom b).snd) h).symm

private theorem kernelCounitDerivation_target (f : G ⟶ H) (x : Additive (lieKernel G A)) :
    (kernelCounitDerivationLinearEquiv H (targetMapLinear f A x)).val.ofConv =
      (kernelCounitDerivationLinearEquiv G x).val.ofConv.comp (pullback f).hom.toCoalgHom.toLinearMap := by
  apply LinearMap.ext
  intro b
  change (kernelCounitDerivationLinearEquiv H (targetMapLinear f A x)).val b =
    (kernelCounitDerivationLinearEquiv G x).val ((pullback f).hom b)
  rw [kernelCounitDerivationLinearEquiv_eq_snd, kernelCounitDerivationLinearEquiv_eq_snd]
  change (hopfPoint (G := H) (x.toMul.val ≫ f.hom.hom) b).snd = _
  rw [hopfPoint_target]
  rfl

/-- Postcomposition by a group-scheme homomorphism preserves the tangent Lie bracket. -/
theorem targetMapLinear_lie (f : G ⟶ H) (x y : Additive (lieKernel G A)) :
    targetMapLinear f A ⁅x, y⁆ = ⁅targetMapLinear f A x, targetMapLinear f A y⁆ := by
  apply (kernelCounitDerivationLinearEquiv H).injective
  apply Subtype.ext
  apply ofConv_injective
  have h (z : Additive (lieKernel G A)) :
      (kernelCounitDerivationLinearEquiv H (targetMapLinear f A z)).val =
        toConv ((kernelCounitDerivationLinearEquiv G z).val.ofConv.comp
          (pullback f).hom.toCoalgHom.toLinearMap) :=
    congrArg toConv (kernelCounitDerivation_target f z)
  rw [kernelCounitDerivation_target]
  simp only [kernelCounitDerivationLinearEquiv_lie, h, ofConv_sub,
    LinearMap.sub_comp, LinearMap.convMul_comp_coalgHom_distrib]

/-- The Lie algebra homomorphism with the existing linear differential as its underlying map. -/
def targetMapLieHom (f : G ⟶ H) (A : Type u) [CommRing A] [Algebra R A] :
    Additive (lieKernel G A) →ₗ⁅A⁆ Additive (lieKernel H A) :=
  { targetMapLinear f A with map_lie' := fun {x y} => targetMapLinear_lie f x y }

@[simp] theorem targetMapLieHom_toLinearMap (f : G ⟶ H) :
    (targetMapLieHom f A).toLinearMap = targetMapLinear f A := rfl

@[simp] theorem targetMapLieHom_id :
    targetMapLieHom (𝟙 G) A = LieHom.id := by
  apply LieHom.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  change x.toMul.val ≫ 𝟙 G.X = x.toMul.val
  exact Category.comp_id _

variable {K : GroupScheme (Spec R)} in
/-- The Lie differential preserves composition with the underlying point maps unchanged. -/
theorem targetMapLieHom_comp [IsAffineHom K.X.hom] (f : G ⟶ H) (g : H ⟶ K) :
    targetMapLieHom (f ≫ g) A = (targetMapLieHom g A).comp (targetMapLieHom f A) := by
  apply LieHom.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  change x.toMul.val ≫ (f.hom.hom ≫ g.hom.hom) =
    (x.toMul.val ≫ f.hom.hom) ≫ g.hom.hom
  exact (Category.assoc _ _ _).symm

variable {B : Type u} [CommRing B] [Algebra R B]

private theorem kernelCounitDerivation_coefficient (f : A →ₐ[R] B) (x : Additive (lieKernel G A)) :
    (kernelCounitDerivationLinearEquiv G (lieKernelMapLinear G f x)).val.ofConv =
      f.toLinearMap.comp (kernelCounitDerivationLinearEquiv G x).val.ofConv := by
  ext b
  change (kernelCounitDerivationLinearEquiv G (lieKernelMapLinear G f x)).val b =
    f ((kernelCounitDerivationLinearEquiv G x).val b)
  rw [kernelCounitDerivationLinearEquiv_apply, kernelCounitDerivationLinearEquiv_apply,
    kernelDerivationLinearEquiv_map]

/-- The same bracket is preserved by semilinear change of the test algebra. -/
theorem lieKernelMapLinear_lie (f : A →ₐ[R] B) (x y : Additive (lieKernel G A)) :
    lieKernelMapLinear G f ⁅x, y⁆ = ⁅lieKernelMapLinear G f x, lieKernelMapLinear G f y⁆ := by
  apply (kernelCounitDerivationLinearEquiv G).injective
  apply Subtype.ext
  apply ofConv_injective
  have h (z : Additive (lieKernel G A)) :
      (kernelCounitDerivationLinearEquiv G (lieKernelMapLinear G f z)).val =
        toConv (f.toLinearMap.comp (kernelCounitDerivationLinearEquiv G z).val.ofConv) :=
    congrArg toConv (kernelCounitDerivation_coefficient f z)
  rw [kernelCounitDerivation_coefficient]
  simp only [kernelCounitDerivationLinearEquiv_lie, h, ofConv_sub,
    LinearMap.comp_sub, LinearMap.algHom_comp_convMul_distrib]

/-- The Lie differential commutes with coefficient change on actual tangent vectors. -/
theorem targetMapLieHom_map (f : G ⟶ H) (a : A →ₐ[R] B) (x : Additive (lieKernel G A)) :
    targetMapLieHom f B (lieKernelMapLinear G a x) =
      lieKernelMapLinear H a (targetMapLieHom f A x) :=
  lieKernelTargetLinear_map f a x

end Langlands.GroupScheme.Lie
