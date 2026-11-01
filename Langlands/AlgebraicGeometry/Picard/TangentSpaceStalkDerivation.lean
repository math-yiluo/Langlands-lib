import Langlands.AlgebraicGeometry.SectionTangentDerivations
import Langlands.AlgebraicGeometry.Picard.StalkTangent
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Derivation.Basic

/-! # The tangent module at a rational point as derivations of the stalk -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.CommutativeAlgebra.PointDerivation Langlands.Scheme.SectionPoint

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The algebra map of `stalkAlgebraOver` is the germ of the pulled-back global section. -/
lemma stalkAlgebraOver_algebraMap (p : X ⟶ Spec (CommRingCat.of K)) (z : X) (c : K) :
    letI := stalkAlgebraOver p z
    algebraMap K (X.presheaf.stalk z) c =
      X.presheaf.germ ⊤ z trivial (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) := by
  have h : Spec.preimage (X.fromSpecStalk z ≫ p) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ z trivial := by
    rw [← cancel_mono (Scheme.ΓSpecIso (X.presheaf.stalk z)).inv, Scheme.ΓSpecIso_inv_naturality,
      Spec.map_preimage, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
    simp
  exact ConcreteCategory.congr_hom h c

variable {k : Type u} [Field k] (Y : Over (Spec (CommRingCat.of k)))
  (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y)

/-- A section of `Y → Spec k` is a rational point. -/
lemma isRationalPoint_left : IsRationalPoint Y.hom e.left := Over.w e

/-- The closed point of `Spec k`, viewed in the source of the section. -/
abbrev basePoint : (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left := IsLocalRing.closedPoint k

/-- The isomorphism from the stalk of `Spec k` at its closed point to `k`. -/
abbrev closedStalkEquiv :
    (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.presheaf.stalk (basePoint (k := k)) ≃+* k :=
  (stalkClosedPointIso (CommRingCat.of k)).commRingCatIsoToRingEquiv

/-- Evaluation of the stalk at the rational point, with values in `k`. -/
abbrev pointEval : Y.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k)) →+* k :=
  (closedStalkEquiv (k := k) : _ →+* k).comp (e.left.stalkMap basePoint).hom

lemma closedStalkEquiv_germ (c : k) :
    closedStalkEquiv (k := k) ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.presheaf.germ ⊤
      basePoint trivial ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)) = c := by
  have h := ConcreteCategory.congr_hom (germ_stalkClosedPointIso_hom (CommRingCat.of k))
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
  exact h.trans (by simp)

lemma pointEval_baseMap (c : Γ(Spec (CommRingCat.of k), ⊤)) :
    pointEval Y e (baseMap Y.hom e.left basePoint c) = (Scheme.ΓSpecIso (CommRingCat.of k)).hom c := by
  change closedStalkEquiv (k := k) (e.left.stalkMap basePoint (baseMap Y.hom e.left basePoint c)) = _
  rw [stalkMap_baseMap]
  exact ConcreteCategory.congr_hom (germ_stalkClosedPointIso_hom (CommRingCat.of k)) c

/-- Point derivations with values in `k` are the `k`-derivations of the stalk, for the base
algebra `stalkAlgebraOver` and the module structure given by the rational augmentation. -/
def derivationsLinearEquiv :
    letI := stalkAlgebraOver Y.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation Y.hom e.left (isRationalPoint_left Y e)).toRingHom.toAlgebra
    derivations (baseMap Y.hom e.left basePoint) (pointEval Y e) ≃ₗ[k]
      Derivation k (Y.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) k := by
  letI := stalkAlgebraOver Y.hom (e.left (IsLocalRing.closedPoint k))
  letI := (rationalStalkAugmentation Y.hom e.left (isRationalPoint_left Y e)).toRingHom.toAlgebra
  have hsmul : ∀ (a : Y.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) (m : k),
      a • m = pointEval Y e a * m := by
    intro a m
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, rationalStalkAugmentation_toRingHom]
    rfl
  have halg : ∀ c : k, algebraMap k (Y.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) c =
      baseMap Y.hom e.left basePoint ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) :=
    fun c => stalkAlgebraOver_algebraMap Y.hom _ c
  exact
  { toFun := fun δ => Derivation.mk'
      { toFun := (δ : _ →+ k)
        map_add' := map_add _
        map_smul' := fun c r => by
          change (δ : _ →+ k) (c • r) = c • (δ : _ →+ k) r
          rw [Algebra.smul_def c r, derivations_mul, halg c, derivations_base, pointEval_baseMap,
            smul_eq_mul]
          simp }
      (fun a b => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, hsmul]
        exact derivations_mul δ a b)
    invFun := fun D => ⟨(D : _ →ₗ[k] k).toAddMonoidHom,
      fun a b => by
        simp only [LinearMap.toAddMonoidHom_coe, Derivation.coeFn_coe]
        rw [Derivation.leibniz, hsmul, hsmul],
      fun c => by
        simp only [LinearMap.toAddMonoidHom_coe, Derivation.coeFn_coe]
        have : baseMap Y.hom e.left basePoint c = algebraMap k _
            ((Scheme.ΓSpecIso (CommRingCat.of k)).hom c) := by
          rw [halg]
          simp
        rw [this, Derivation.map_algebraMap]⟩
    left_inv := fun δ => rfl
    right_inv := fun D => Derivation.ext fun _ => rfl
    map_add' := fun δ δ' => Derivation.ext fun _ => rfl
    map_smul' := fun c δ => Derivation.ext fun _ => rfl }

/-- The tangent module at a rational point is `k`-linearly the space of `k`-valued point
derivations of the stalk. -/
def tangentDerivationsLinearEquiv :
    Langlands.Scheme.tangentSpaceAtPoint Y e ≃ₗ[k]
      derivations (baseMap Y.hom e.left basePoint) (pointEval Y e) := by
  haveI : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact
  { (tangentDerivationEquiv Y e basePoint).trans
      (derivationsCongr (closedStalkEquiv (k := k))).toEquiv with
    map_add' := fun t t' =>
      (congrArg (derivationsCongr (closedStalkEquiv (k := k)))
        (tangentDerivationEquiv_add Y e basePoint t t')).trans (map_add _ _ _)
    map_smul' := fun c t => by
      change derivationsCongr closedStalkEquiv (tangentDerivationEquiv Y e basePoint
          ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c •
            (show Γ(Langlands.Scheme.tangentAtSection Y e, ⊤) from t))) =
        c • derivationsCongr closedStalkEquiv (tangentDerivationEquiv Y e basePoint t)
      rw [tangentDerivationEquiv_smul, derivationsCongr_smul, closedStalkEquiv_germ] }

/-- The published tangent module at a rational point is `k`-linearly equivalent to the
`k`-derivations of the actual stalk, with Worker 509's `stalkAlgebraOver` base algebra and the
coefficient action through `rationalStalkAugmentation`. -/
def tangentSpaceAtPointDerivationEquiv :
    letI := stalkAlgebraOver Y.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation Y.hom e.left (isRationalPoint_left Y e)).toRingHom.toAlgebra
    Langlands.Scheme.tangentSpaceAtPoint Y e ≃ₗ[k]
      Derivation k (Y.left.presheaf.stalk (e.left (IsLocalRing.closedPoint k))) k :=
  (tangentDerivationsLinearEquiv Y e).trans (derivationsLinearEquiv Y e)

/-- Evaluation formula: on the germ of a section `a` over `U`, the derivation attached to `t` is
the image in `k` of the germ at the closed point of `tangentEval Y e t U a`. -/
lemma tangentSpaceAtPointDerivationEquiv_germ (t : Langlands.Scheme.tangentSpaceAtPoint Y e)
    (U : Y.left.Opens) (hx : e.left (IsLocalRing.closedPoint k) ∈ U) (a : Γ(Y.left, U)) :
    letI := stalkAlgebraOver Y.hom (e.left (IsLocalRing.closedPoint k))
    letI := (rationalStalkAugmentation Y.hom e.left (isRationalPoint_left Y e)).toRingHom.toAlgebra
    tangentSpaceAtPointDerivationEquiv Y e t (Y.left.presheaf.germ U _ hx a) =
      closedStalkEquiv (k := k) ((Over.mk (𝟙 (Spec (CommRingCat.of k)))).left.presheaf.germ
        (e.left ⁻¹ᵁ U) basePoint (e.left.mem_preimage.2 hx)
        (sectionEquiv e.left U (tangentEval Y e t U a))) := by
  have : Subsingleton (Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact congrArg (closedStalkEquiv (k := k)) (tangentDerivationEquiv_germ Y e basePoint t U hx a)

end Langlands.AlgebraicGeometry.Picard
