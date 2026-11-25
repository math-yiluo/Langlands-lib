/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-! # Constant multiplication on twisted sections

Source: Stacks Project, Lemma 01YS, proof of (5); homogeneous fraction construction
of the twisting sheaf, Tag 01M6.
(blueprint: lem-sc-p1-twisted-sections-constant-action).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

private theorem constant_value (k : Type u) [Field k] (c : k)
    (x : Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    ((ρ c).1 ⟨x, trivial⟩).val =
      (Localization.mk (MvPolynomial.C c) 1 :
        Localization.AtPrime x.asHomogeneousIdeal.toIdeal) := by
  change ((((Scheme.ΓSpecIso _).inv ≫
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop).hom
    ((MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k) c)).1 ⟨x, trivial⟩).val = _
  simp only [Proj.toSpecZero, Scheme.Hom.comp_appTop, Proj.basicOpenToSpec,
    Category.assoc, ← Scheme.ΓSpecIso_inv_naturality_assoc,
    Scheme.Opens.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
  simp only [Scheme.isoOfEq_inv]
  simp only [Scheme.Hom.appTop, Scheme.homOfLE_app, Scheme.Opens.topIso_inv]
  have ht (X : Scheme.{u}) : X.topIso.inv.appTop = (⊤ : X.Opens).topIso.hom := by
    apply (cancel_mono (⊤ : X.Opens).topIso.inv).mp
    change X.topIso.inv.appTop ≫ X.topIso.hom.appTop = _
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp only [Scheme.Hom.id_appTop, Iso.hom_inv_id]
  rw [← Scheme.Hom.appTop, ht]
  simp only [Scheme.Opens.topIso_hom, ← Functor.map_comp, ← CategoryTheory.op_comp]
  change (HomogeneousLocalization.mapId
    (MvPolynomial.homogeneousSubmodule (Fin 2) k)
    (Submonoid.powers_le.mpr (show x ∈ Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) 1 by
      simp only [Proj.basicOpen_one, TopologicalSpace.Opens.mem_top]))
    (HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.homogeneousSubmodule (Fin 2) k) (Submonoid.powers 1)
      ((MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k) c))).val = _
  rfl

private theorem twist_cast_val (k : Type u) [Field k] {i j : ℤ} (h : i = j)
    (U : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Opens)
    (s : Γ(Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) i, U)) (x : U) :
    ((Scheme.Modules.Hom.app (eqToHom
      (congrArg (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) h)) U s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = s.1 x := by
  subst j
  rfl

namespace Scheme.Modules

private theorem tensor_hom_ext {X : Scheme.{u}} {M N P : X.Modules}
    (f g : M ⊗ N ⟶ P)
    (h : ∀ (U : X.Opens) (s : Γ(M, U)) (t : Γ(N, U)),
      f.app U (tmulSection s t) = g.app U (tmulSection s t)) : f = g := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (M.val ⊗ N.val) P).injective
  ext U t : 3
  induction t using TensorProduct.inductionOn with
  | tmul s t => exact h U.unop s t
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

private theorem tensor_smul {X : Scheme.{u}} (M N : X.Modules) (r : Γ(X, ⊤)) :
    M ◁ N.smulHom r = (M ⊗ N).smulHom r := by
  apply tensor_hom_ext
  intro U s t
  rw [whiskerLeft_app_tmulSection, smulHom_app_apply, tmulSection_smul,
    smulHom_app_apply]

end Scheme.Modules

/-- Constant homogeneous multiplication agrees with the canonical base-field action.
Source: Stacks Project, Lemma 01YS, proof of (5), and Tag 01M6.
(blueprint: lem-sc-p1-twisted-sections-constant-action).

Proof: on D₊(Xᵢ) and each of its subopens the structure-map image of c is the degree-zero
fraction C(c)/1. The definition of twistMul multiplies a degree-n fraction a/b by
C(c)/1. This is therefore multiplication by the restriction of the global function
ρ(c), on every section of O(n). Equality on the two basic opens, which cover Proj,
gives equality of these sheaf morphisms after transporting n+0 to n. Tensoring this
morphism with the identity of G acts by the same scalar: on pure tensors,
x tensor (ρ(c) y) = ρ(c) (x tensor y). Additivity gives the equality on the presheaf
tensor product, and sheafification preserves it. Evaluating on global sections gives
the displayed formula. Proof irrelevance makes it independent of the equality p and
of ha. No coherence or positivity assumption is required; c=0 and c=1 give zero and
the identity, and the argument also applies to the zero sheaf and negative twists. -/
theorem serreTwistedSectionsConstantAction
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (n : ℤ) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    letI := Module.compHom
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
    ∀ (c : k)
      (ha : MvPolynomial.C c ∈ MvPolynomial.homogeneousSubmodule (Fin 2) k 0)
      (s : Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤))
      (p : G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)
        (n + (0 : ℕ)) = G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n),
      Scheme.Modules.Hom.app ((G ◁ Proj.twistMul n ha) ≫ eqToHom p) ⊤ s =
        c • s := by
  dsimp only
  intro c ha s p
  let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
    (Scheme.ΓSpecIso _).inv.hom).comp
      (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
  change Scheme.Modules.Hom.app ((G ◁ Proj.twistMul n ha) ≫ eqToHom p) ⊤ s = ρ c • s
  let h : n + ((0 : ℕ) : ℤ) = n := by omega
  let e := eqToHom (congrArg
    (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k)) h)
  have hm : Proj.twistMul n ha ≫ e = Scheme.Modules.smulHom
      (Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n) (ρ c) := by
    ext U t : 3
    refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
    change ((Scheme.Modules.Hom.app e U
      (Scheme.Modules.Hom.app (Proj.twistMul n ha) U t)).1 x :
        Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) = _
    rw [twist_cast_val k h]
    change (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (MvPolynomial.C c) 1 =
        ((ρ c).1 ⟨x.1, trivial⟩).val *
          (t.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    rw [constant_value k c x.1]
    exact mul_comm _ _
  have he : G ◁ e = eqToHom p := whiskerLeft_eqToHom G _
  rw [← he, ← whiskerLeft_comp, hm, Scheme.Modules.tensor_smul, Scheme.Modules.smulHom_app_apply]
  simp

end AlgebraicGeometry
