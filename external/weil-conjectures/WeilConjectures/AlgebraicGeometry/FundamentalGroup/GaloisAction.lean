/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Conj
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Functoriality

/-!
# The Galois group of a point acting on the étale fundamental group

Let `y : Spec K ⟶ Y` be a morphism from the spectrum of a ring `K` and `Ω` a separably closed
field with a `K`-algebra structure, so that `ȳ : Spec Ω ⟶ Spec K ⟶ Y` is a geometric point.
Every `K`-automorphism `σ` of `Ω` acts on the fibre functor at `ȳ` by precomposition with
`Spec σ` (`AlgebraicGeometry.Scheme.FiniteEtale.galoisToAut`). Transporting along a path
`τ` from `ȳ` to a geometric point `s`, this gives a homomorphism `Gal(Ω / K) →* π₁(Y, s)`
(`AlgebraicGeometry.Scheme.FiniteEtale.galoisToFundamentalGroup`), characterised by
`ρ(σ) • τ y = τ (Spec σ ≫ y)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {Y : Scheme.{u}} {K Ω : Type u} [CommRing K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω]
  (y : Spec (.of K) ⟶ Y)

variable (Ω) in
/-- The geometric point `Spec Ω ⟶ Spec K ⟶ Y` over a point `y : Spec K ⟶ Y`. -/
noncomputable abbrev pointOfAlgebra : Spec (.of Ω) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ y

omit [IsSepClosed Ω] in
lemma specMapIso_hom_comp_pointOfAlgebra (σ : Ω ≃ₐ[K] Ω) :
    (specMapIso σ.toRingEquiv).hom ≫ pointOfAlgebra Ω y = pointOfAlgebra Ω y := by
  rw [← Category.assoc]
  congr 1
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact σ.commutes a

/-- The Galois group `Gal(Ω / K)` acts on the fibre functor at the geometric point
`Spec Ω ⟶ Spec K ⟶ Y`: an automorphism `σ` acts by precomposition with `Spec σ`. -/
noncomputable def galoisToAut : (Ω ≃ₐ[K] Ω) →* Aut (fiber (pointOfAlgebra Ω y)) where
  toFun σ := .of <| fiberPrecompIso _ (specMapIso σ.toRingEquiv)
    (specMapIso_hom_comp_pointOfAlgebra y σ)
  map_one' := by
    ext P t
    refine fiber_ext _ ?_
    change Spec.map _ ≫ t.left = t.left
    have : (1 : Ω ≃ₐ[K] Ω).toRingEquiv.toCommRingCatIso.op.hom.unop = 𝟙 _ := rfl
    rw [this, Spec.map_id, Category.id_comp]
  map_mul' σ τ := by
    ext P t
    refine fiber_ext _ ?_
    change Spec.map _ ≫ t.left = Spec.map _ ≫ Spec.map _ ≫ t.left
    rw [← Category.assoc, ← Spec.map_comp]
    rfl

lemma galoisToAut_hom_app_left (σ : Ω ≃ₐ[K] Ω) (P : Y.FiniteEtale)
    (t : (fiber (pointOfAlgebra Ω y)).obj P) :
    ((galoisToAut y σ).asIso.hom.app P t).left =
      Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ t.left :=
  rfl

variable [ConnectedSpace Y] {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] {s : Spec (.of Ω') ⟶ Y}
  (τ : fiber (pointOfAlgebra Ω y) ≅ fiber s)
  (G : Type u) [Group G] [∀ P, MulAction G ((fiber s).obj P)] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [IsFundamentalGroup (fiber s) G]

/-- The Galois group `Gal(Ω / K)` of a point `y : Spec K ⟶ Y` maps to the fundamental group
`π₁(Y, s)`, transporting its action on the fibre functor at `Spec Ω ⟶ Spec K ⟶ Y` along a path
`τ`. -/
noncomputable def galoisToFundamentalGroup : (Ω ≃ₐ[K] Ω) →* G :=
  (toAutMulEquiv (fiber s) G).symm.toMonoidHom.comp
    ((Iso.conjAut τ).toMonoidHom.comp (galoisToAut y))

/-- The image of `σ` in `π₁(Y, s)` acts on the fibre at `s` as `Spec σ` does on the fibre at
`Spec Ω`, transported along `τ`. -/
lemma galoisToFundamentalGroup_smul (σ : Ω ≃ₐ[K] Ω) (P : Y.FiniteEtale)
    (t : (fiber (pointOfAlgebra Ω y)).obj P) :
    galoisToFundamentalGroup y τ G σ • τ.hom.app P t =
      τ.hom.app P ((galoisToAut y σ).asIso.hom.app P t) := by
  rw [← toAut_hom_app_apply (F := fiber s) (G := G)]
  change ((toAutMulEquiv (fiber s) G) ((toAutMulEquiv (fiber s) G).symm
    (Iso.conjAut τ (galoisToAut y σ)))).asIso.hom.app P _ = _
  rw [MulEquiv.apply_symm_apply, Iso.conjAut_hom]
  change (τ.hom.app P) ((galoisToAut y σ).asIso.hom.app P ((τ.inv.app P) (τ.hom.app P t))) = _
  rw [← ConcreteCategory.comp_apply (τ.hom.app P) (τ.inv.app P), τ.hom_inv_id_app]
  rfl

end AlgebraicGeometry.Scheme.FiniteEtale
