/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.GaloisPointGeometricComparison
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.FieldTheory.GaloisUnitsCohomology
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.EtaleUnitsStalkEvaluationOverfield

/-!
# The stalk of the multiplicative group at the Galois point

The stalk of the étale sheaf `𝔾ₘ` on `Spec K` at the Galois point
`AlgebraicGeometry.Scheme.galoisPoint K Ks`, for `Ks` the separable closure of `K`, is the
group of units of `Ks`: a germ of a unit is sent to its value at the geometric point. This
identification is equivariant for the natural actions of `Gal(Ks/K)`.

Source: Stacks Project, Example 03QV (2), and Tag 03QU.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (K : Type u) [Field K]

/-- The stalk of `𝔾ₘ` at the Galois point `galoisPoint K (SeparableClosure K)` is the additive
group of units of the separable closure: the germ of a unit `z` on an étale neighbourhood
`(X, x)` is sent to the value of `z` at the geometric point `x`
(`AlgebraicGeometry.Scheme.gmSheafFiberGaloisPointAddEquiv_toPresheafFiber`). It intertwines
the Galois actions (`AlgebraicGeometry.Scheme.gmSheafFiberGaloisPointAddEquiv_presheafFiberAct`).

It is obtained from evaluation at the geometric point `Spec (AlgebraicClosure K) ⟶ Spec K`
(`AlgebraicGeometry.Scheme.exists_etaleUnits_stalk_evaluation_overfield`), which is unique as
the separable closure embeds into the algebraic closure, transported along
`AlgebraicGeometry.Scheme.galoisPointSheafFiberIso`.

Source: Stacks Project, Example 03QV (2), and Tag 03QU. -/
noncomputable def gmSheafFiberGaloisPointAddEquiv :
    ((galoisPoint K (SeparableClosure K)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        (Spec (.of K)).gmSheaf ≃+ Additive (SeparableClosure K)ˣ :=
  ((galoisPointSheafFiberIso K (SeparableClosure K) (AlgebraicClosure K)).app
      (Spec (.of K)).gmSheaf).addCommGroupIsoToAddEquiv.trans
    (exists_etaleUnits_stalk_evaluation_overfield K (AlgebraicClosure K)).choose

/-- The stalk of `𝔾ₘ` at the Galois point sends the germ of a unit to its value at the
geometric point. -/
lemma gmSheafFiberGaloisPointAddEquiv_toPresheafFiber (X : (Spec (.of K)).Etale)
    (x : (galoisPoint K (SeparableClosure K)).fiber.obj X)
    (z : (Spec (.of K)).gmSheaf.obj.obj (op X)) :
    ((Additive.toMul (gmSheafFiberGaloisPointAddEquiv K
        ((galoisPoint K (SeparableClosure K)).toPresheafFiber X x (Spec (.of K)).gmSheaf.obj z)) :
        (SeparableClosure K)ˣ) : SeparableClosure K) =
      (ΓSpecIso (.of (SeparableClosure K))).hom
        (x.down.left.appTop ((Additive.toMul z.down : Γ(X.left, ⊤)ˣ) : Γ(X.left, ⊤))) := by
  apply (algebraMap (SeparableClosure K) (AlgebraicClosure K)).injective
  have h := (exists_etaleUnits_stalk_evaluation_overfield K (AlgebraicClosure K)).choose_spec X
    (specAlgebraMapOverHom K (SeparableClosure K) (AlgebraicClosure K) ≫ x.down) z
  have h' := galoisPointSheafFiberIso_hom_app_toPresheafFiber_apply K (SeparableClosure K)
    (AlgebraicClosure K) (Spec (.of K)).gmSheaf X x z
  rw [gmSheafFiberGaloisPointAddEquiv, AddEquiv.trans_apply]
  erw [h', h]
  change (ΓSpecIso _).hom ((specAlgebraMap (SeparableClosure K) (AlgebraicClosure K) ≫
    x.down.left).appTop _) = _
  rw [Hom.comp_appTop]
  exact ConcreteCategory.congr_hom (ΓSpecIso_naturality
    (CommRingCat.ofHom (algebraMap (SeparableClosure K) (AlgebraicClosure K)))) _

/-- The identification of the stalk of `𝔾ₘ` at the Galois point with the units of the
separable closure is `Gal(Ks/K)`-equivariant. -/
lemma gmSheafFiberGaloisPointAddEquiv_presheafFiberAct (σ : Gal(SeparableClosure K/K))
    (v : ((galoisPoint K (SeparableClosure K)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      (Spec (.of K)).gmSheaf) :
    gmSheafFiberGaloisPointAddEquiv K ((galoisPoint K (SeparableClosure K)).presheafFiberAct
        (galoisPointAct K (SeparableClosure K)) (Spec (.of K)).gmSheaf.obj σ v) =
      (Field.galoisUnitsTopRep K).ρ σ (gmSheafFiberGaloisPointAddEquiv K v) := by
  obtain ⟨X, x, z, rfl⟩ :=
    (galoisPoint K (SeparableClosure K)).toPresheafFiber_jointly_surjective v
  erw [GrothendieckTopology.Point.toPresheafFiber_presheafFiberAct_apply]
  apply Additive.toMul.injective
  apply Units.ext
  rw [gmSheafFiberGaloisPointAddEquiv_toPresheafFiber]
  change _ = σ ((Additive.toMul (gmSheafFiberGaloisPointAddEquiv K
    ((galoisPoint K (SeparableClosure K)).toPresheafFiber X x (Spec (.of K)).gmSheaf.obj z)) :
      (SeparableClosure K)ˣ) : SeparableClosure K)
  rw [gmSheafFiberGaloisPointAddEquiv_toPresheafFiber, galoisPointAct_app_down,
    Over.comp_left, galoisOverHom_left, Hom.comp_appTop]
  exact ConcreteCategory.congr_hom
    (ΓSpecIso_naturality (CommRingCat.ofHom (σ : SeparableClosure K →+* SeparableClosure K))) _

end AlgebraicGeometry.Scheme
