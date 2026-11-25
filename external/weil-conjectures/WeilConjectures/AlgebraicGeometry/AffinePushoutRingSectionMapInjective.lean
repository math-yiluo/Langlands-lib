/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMap
import WeilConjectures.AlgebraicGeometry.PushoutRegularModuleComparison
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.QuasicoherentPushforwardQcqs
import WeilConjectures.AlgebraicGeometry.AffinePushoutRingSectionMapTmul
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
variable {U X : Scheme.{u}} (f : U ⟶ X)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical affine tensor section map has zero kernel.
Source: Stacks Project, Morphisms, Tag 01SB, affine reduction; Schemes, Tags 01IA and 01HV.
(blueprint: stage3-affine-pushout-ring-section-map-injective).

Proof: Put D = Γ(X,V), W = f⁻¹V and C = Γ(U,W). W is affine. The regular
module of A = f_*O_U, restricted along O_X → A, is f_*O_U as an O_X-module.
It is quasi-coherent: O_U is quasi-coherent and f is affine, hence qcqs.
Specialize affine_module_tensor_baseChange to the regular A-module. The inverse
image of a regular algebra module is the regular module of the inverse-image
algebra: the inverse-image unit respects addition and multiplication, and these
operations determine their extensions uniquely. Extension of that module along
`t` is the regular B-module; the inverse maps before sheafification are
z ⊗ a ↦ z*t(a) and z ↦ z ⊗ 1, and they remain inverse after sheafification.
Thus the cancellation comparison identifies the underlying O_U-module of B
with tensor pullback of f_*O_U. The affine pullback sections comparison gives a
bijective D-linear map C ⊗[D] C → B(W), after swapping its tensor factors.
Its unit formula sends 1 ⊗ d to t(η(d)); O_U-linearity sends c ⊗ d to
b(c)*t(η(d)). This is exactly affinePushoutSectionMap_tmul. Additive tensor
induction identifies the linear map with the constructed ring map on all
inputs. Its injectivity gives the claim. No surjectivity of the constructed
ring map is asserted here. If C is the zero ring, the tensor is zero and the
same argument applies; no nonzero or nonempty assumption is used. -/
theorem affinePushoutSectionMap_injective [IsAffineHom f]
    (B : U.toTopCat.Sheaf CommRingCat.{u}) (b : U.sheaf ⟶ B)
    (t : TopCat.Sheaf.inverseImageRing f.base
      ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf) ⟶ B)
    (hpushout : IsPushout (tensorPullbackRingMap f)
      ((TopCat.Sheaf.inverseImageConstruction f.base CommRingCat.{u}).map
        (show X.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf from ⟨f.c⟩)) b t)
    (V : X.Opens) (hV : IsAffineOpen V) :
    letI : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
    Function.Injective (affinePushoutSectionMap f B b t hpushout V).hom := by
  classical
  dsimp only
  let : Algebra Γ(X, V) Γ(U, f ⁻¹ᵁ V) := (f.app V).hom.toAlgebra
  let G := (pushforward f).obj (SheafOfModules.unit U.ringCatSheaf)
  have : QuasiSeparated f := by
    have := IsSeparated.of_isAffineHom f
    infer_instance
  have : (SheafOfModules.unit U.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit.{u, u, u}
  have hG : G.IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_quasiSeparated f _
  obtain ⟨e, he⟩ := exists_pushout_regularModule_comparison f B b t hpushout
  have hs := exists_tensorPullback_affine_sections f
    ⟨V, hV⟩ ⟨f ⁻¹ᵁ V, hV.preimage f⟩ le_rfl
  dsimp only at hs
  rw [Scheme.Hom.appLE_eq_app] at hs
  obtain ⟨c, hc, _, hct, _⟩ := hs
  let q := affinePushoutSectionMap f B b t hpushout V
  have hformula (x y : Γ(U, f ⁻¹ᵁ V)) :
      e.hom.val.app (op (f ⁻¹ᵁ V)) (c G hG (y ⊗ₜ[Γ(X, V)] x)) =
        q.hom (x ⊗ₜ[Γ(X, V)] y) := by
    rw [hct]
    simp only [homOfLE_refl, op_id]
    rw [((tensorPullback f).obj G).presheaf.map_id]
    change e.hom.val.app (op (f ⁻¹ᵁ V))
      (x • (show Γ((tensorPullback f).obj G, f ⁻¹ᵁ V) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app G).val.app
          (op V) y)) = _
    rw [(e.hom.val.app (op (f ⁻¹ᵁ V))).hom.map_smul]
    rw [he]
    exact (affinePushoutSectionMap_tmul f B b t hpushout V x y).symm
  have hcomparison (z : Γ(U, f ⁻¹ᵁ V) ⊗[Γ(X, V)] Γ(U, f ⁻¹ᵁ V)) :
      e.hom.val.app (op (f ⁻¹ᵁ V))
        (c G hG (TensorProduct.comm Γ(X, V) Γ(U, f ⁻¹ᵁ V) Γ(U, f ⁻¹ᵁ V) z)) =
          q.hom z := by
    induction z using TensorProduct.inductionOn with
    | tmul x y => simpa only [TensorProduct.comm_tmul] using hformula x y
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have : IsIso (e.hom.val.app (op (f ⁻¹ᵁ V))) :=
    (SheafOfModules.evaluation U.ringCatSheaf (op (f ⁻¹ᵁ V))).map_isIso e.hom
  intro z z' hzz
  apply (TensorProduct.comm Γ(X, V) Γ(U, f ⁻¹ᵁ V) Γ(U, f ⁻¹ᵁ V)).injective
  apply (hc G hG).1
  apply (ConcreteCategory.bijective_of_isIso (e.hom.val.app (op (f ⁻¹ᵁ V)))).1
  exact (hcomparison z).trans (hzz.trans (hcomparison z').symm)
end
end AlgebraicGeometry.Scheme.Modules
