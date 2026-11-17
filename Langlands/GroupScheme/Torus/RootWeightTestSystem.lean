import Langlands.AlgebraicGeometry.Modules.AffineTestRealization
import Langlands.GroupScheme.Torus.RelativeAdjointWeightBaseChange
import Langlands.GroupScheme.Reductive.AffinePinnedWeightTransport
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange

/-! # The actual exponent-weight modules as an affine test system

For a smooth affine group scheme `G` over an arbitrary scheme `S`, a coordinate torus
`t : splitTorus S I ⟶ G` and an exponent `m : I → ℤ`, the actual exponent-weight modules of the
pullbacks of `(G, t)` to all affine tests `a : Spec R ⟶ S`, together with the actual
exponent-weight base-change equivalences normalized by `baseChangeCompIso`, form an
`AffineTestSystem S`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.splitTorus

open Langlands.AlgebraicGeometry.Modules

/-- Affineness of the structure morphism is preserved by base change. -/
local instance testAffine {X Y : Scheme.{u}} (H : GroupScheme X) [IsAffineHom H.X.hom]
    (a : Y ⟶ X) : IsAffineHom ((baseChange a).obj H).X.hom :=
  MorphismProperty.pullback_snd H.X.hom a inferInstance

/-- Smoothness of the structure morphism is preserved by base change. -/
local instance testSmooth {X Y : Scheme.{u}} (H : GroupScheme X) [Smooth H.X.hom]
    (a : Y ⟶ X) : Smooth ((baseChange a).obj H).X.hom :=
  inferInstanceAs (Smooth (pullback.snd H.X.hom a))

variable {S : Scheme.{u}} (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme S) [IsAffineHom G.X.hom] [Smooth G.X.hom]
  (t : splitTorus S I ⟶ G) (m : I → ℤ)

/-- The normalized coordinate torus of the pullback of `(G, t)` along an affine test. -/
abbrev testTorus {R : CommRingCat.{u}} (a : Spec R ⟶ S) :
    splitTorus (Spec R) I ⟶ (baseChange a).obj G :=
  (baseChangeIso a I).inv ≫ (baseChange a).map t

/-- The actual exponent-weight module of the pullback of `(G, t)` along an affine test. -/
abbrev testWeightSpace {R : CommRingCat.{u}} (a : Spec R ⟶ S) :
    Submodule R (Additive (lieKernel ((baseChange a).obj G) R)) :=
  exponentWeightSpace I ((baseChange a).obj G) (testTorus I G t a) m

omit [DecidableEq I] [IsAffineHom G.X.hom] [Smooth G.X.hom] in
lemma baseChangeHom_comp_inv {R A : CommRingCat.{u}} [Algebra R A] (a : Spec R ⟶ S) :
    baseChangeHom (r := R) (K := A) ((baseChange a).obj G) I (testTorus I G t a) ≫
        (baseChangeCompIso a (Spec.map (CommRingCat.ofHom (algebraMap R A))) G).symm.hom =
      (Iso.refl _).hom ≫ testTorus I G t (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a) := by
  rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
  change ((baseChangeIso (Spec.map (CommRingCat.ofHom (algebraMap R A))) I).inv ≫
    (baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map (testTorus I G t a)) ≫ _ = _
  rw [baseChangeTorusHom_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Coefficient extension of the weight module along an algebra `R → A`, landing on the
composite test `Spec A ⟶ Spec R ⟶ S`: the actual exponent-weight base-change equivalence followed
by the transport along `baseChangeCompIso`. -/
def weightExtComp {R A : CommRingCat.{u}} [Algebra R A] (a : Spec R ⟶ S) :
    A ⊗[R] testWeightSpace I G t m a ≃ₗ[A]
      testWeightSpace I G t m (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a) :=
  (exponentWeightBaseChangeEquiv (r := R) (K := A) ((baseChange a).obj G) I
      (testTorus I G t a) m).trans
    (exponentWeightSpaceTransportEquiv
      (baseChangeCompIso a (Spec.map (CommRingCat.ofHom (algebraMap R A))) G).symm
      (Iso.refl _) (baseChangeHom_comp_inv I G t a) m m (fun _ _ _ x => by simp))

/-- Coefficient extension of the weight module along an algebra `R → A`, for any test `b`
equal to `Spec A ⟶ Spec R ⟶ S`. -/
def weightExt {R A : CommRingCat.{u}} [Algebra R A] {a : Spec R ⟶ S} {b : Spec A ⟶ S}
    (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) :
    A ⊗[R] testWeightSpace I G t m a ≃ₗ[A] testWeightSpace I G t m b := by
  subst h
  exact weightExtComp I G t m a

set_option synthInstance.maxHeartbeats 100000 in
/-- The value of the coefficient extension of a vector `x`, projected to the original group,
is the projection of the coefficient extension `lieKernelMap` of `x` over the original test. -/
theorem weightExt_point {R A : CommRingCat.{u}} [Algebra R A] {a : Spec R ⟶ S}
    {b : Spec A ⟶ S} (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b)
    (x : testWeightSpace I G t m a) :
    (((weightExt I G t m h (1 ⊗ₜ x) : testWeightSpace I G t m b) :
        Additive (lieKernel ((baseChange b).obj G) A))).toMul.val.left ≫
        pullback.fst G.X.hom b =
      (lieKernelMap ((baseChange a).obj G) (Algebra.ofId R A)
        (x : Additive (lieKernel ((baseChange a).obj G) R)).toMul).val.left ≫
        pullback.fst G.X.hom a := by
  subst h
  have : IsAffineHom ((baseChange (algebraBaseMap R A)).obj ((baseChange a).obj G)).X.hom :=
    testAffine _ _
  have hz : Lie.kernelBaseChangeLinearEquiv R A ((baseChange a).obj G) A
      (Lie.smoothSchemeScalarExtension (K := A) ((baseChange a).obj G)
        (1 ⊗ₜ (x : Additive (lieKernel ((baseChange a).obj G) R)))) =
      lieKernelMapLinear ((baseChange a).obj G) (Algebra.ofId R A) x := by
    rw [Lie.smoothSchemeScalarExtension_tmul, one_smul, LinearEquiv.apply_symm_apply]
  have hz' := congrArg (fun y => (Additive.toMul y).val.left) hz
  simp only [Lie.kernelBaseChangeLinearEquiv, lieKernelMapLinear_toMul] at hz'
  change (Lie.affineBaseChangeEquiv R A ((baseChange a).obj G) (DualNumber A) _).left = _ at hz'
  rw [Lie.affineBaseChangeEquiv_left] at hz'
  rw [← hz']
  change ((Lie.smoothSchemeScalarExtension (K := A) ((baseChange a).obj G)
      (1 ⊗ₜ (x : Additive (lieKernel ((baseChange a).obj G) R)))).toMul.val ≫
      (baseChangeCompIso a (Spec.map (CommRingCat.ofHom (algebraMap R A))) G).inv.hom.hom).left ≫
      pullback.fst G.X.hom (Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a) = _
  rw [Over.comp_left, Category.assoc, GroupScheme.baseChangeCompIso_inv_fst, Category.assoc]
  rfl

omit [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- A dual-number kernel vector of a pullback of `G` is determined by its projection to `G`. -/
theorem lieKernel_ext_of_fst {R : CommRingCat.{u}} (a : Spec R ⟶ S) {B : Type u} [CommRing B]
    [Algebra R B] {y y' : lieKernel ((baseChange a).obj G) B}
    (h : y.val.left ≫ pullback.fst G.X.hom a = y'.val.left ≫ pullback.fst G.X.hom a) :
    y = y' := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w y.val).trans (Over.w y'.val).symm

/-- Coefficient change of dual-number kernel vectors precomposes with the spectrum map. -/
theorem lieKernelMap_val_left {R : CommRingCat.{u}} (H : GroupScheme (Spec R)) {A B : Type u}
    [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (y : lieKernel H A) :
    (lieKernelMap H f y).val.left =
      Spec.map (CommRingCat.ofHom (GeneralLinear.DualNumber.coefficientAlgMap f).toRingHom) ≫
        y.val.left :=
  rfl

/-- The coefficient-extension identifications of the weight modules are compatible with towers
of algebras. -/
theorem weightExt_comp {R A B : CommRingCat.{u}} [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] {a : Spec R ⟶ S} {b : Spec A ⟶ S} {c : Spec B ⟶ S}
    (hab : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b)
    (hbc : Spec.map (CommRingCat.ofHom (algebraMap A B)) ≫ b = c)
    (hac : Spec.map (CommRingCat.ofHom (algebraMap R B)) ≫ a = c)
    (x : testWeightSpace I G t m a) :
    weightExt I G t m hac (1 ⊗ₜ x) =
      weightExt I G t m hbc (1 ⊗ₜ weightExt I G t m hab (1 ⊗ₜ x)) := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply lieKernel_ext_of_fst G c
  rw [weightExt_point, weightExt_point, lieKernelMap_val_left _ (Algebra.ofId A B),
    Category.assoc, weightExt_point]
  have key : lieKernelMap ((baseChange a).obj G) (Algebra.ofId R B)
      (x : Additive (lieKernel ((baseChange a).obj G) R)).toMul =
      lieKernelMap ((baseChange a).obj G) ((Algebra.ofId A B).restrictScalars R)
        (lieKernelMap ((baseChange a).obj G) (Algebra.ofId R A)
          (x : Additive (lieKernel ((baseChange a).obj G) R)).toMul) :=
    congrArg Additive.toMul (Lie.smooth_lieKernelMapLinear_base ((baseChange a).obj G)
      ((Algebra.ofId A B).restrictScalars R)
      (x : Additive (lieKernel ((baseChange a).obj G) R))).symm
  rw [key, lieKernelMap_val_left, Category.assoc]
  rfl

/-- **The actual exponent-weight modules as an affine test system.** On a test
`a : Spec R ⟶ S` the module is the actual exponent-weight space of the normalized pullback
`((baseChange a).obj G, (baseChangeIso a I).inv ≫ (baseChange a).map t)`; coefficient extension
is the actual exponent-weight base-change equivalence normalized by `baseChangeCompIso`. -/
def weightTestSystem : AffineTestSystem S where
  obj a := ModuleCat.of _ (testWeightSpace I G t m a)
  ext h := weightExt I G t m h
  ext_comp hab hbc hac x := weightExt_comp I G t m hab hbc hac x

lemma weightTestSystem_obj {R : CommRingCat.{u}} (a : Spec R ⟶ S) :
    (weightTestSystem I G t m).obj a = ModuleCat.of R (testWeightSpace I G t m a) :=
  rfl

lemma weightTestSystem_ext {R A : CommRingCat.{u}} [Algebra R A] {a : Spec R ⟶ S}
    {b : Spec A ⟶ S} (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b)
    (z : A ⊗[R] testWeightSpace I G t m a) :
    (weightTestSystem I G t m).ext h z = weightExt I G t m h z :=
  rfl

end Langlands.GroupScheme.splitTorus
