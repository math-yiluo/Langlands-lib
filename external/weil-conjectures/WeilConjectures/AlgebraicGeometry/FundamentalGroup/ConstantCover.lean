/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.WeilGroup

/-!
# Geometric fibres of constant covers

Let `p : X₀ ⟶ Spec k₀` be a scheme over a field `k₀`, `s : Spec Ω ⟶ X₀` a geometric point, and
`κ : k₀ →+* Ω` the ring homomorphism with `Spec κ = s ≫ p`. The geometric fibre at `s` of the
constant cover `X₀ ×_{k₀} Spec A` of a finite étale `k₀`-algebra `A` is the set of ring
homomorphisms `A →+* Ω` restricting to `κ` on `k₀`
(`AlgebraicGeometry.Scheme.FiniteEtale.fiberConstantCoverEquiv`), naturally in `A`: a
`k₀`-algebra map `f : A → B` induces the morphism of constant covers
`AlgebraicGeometry.Scheme.FiniteEtale.constantCoverHom f : X₀ ×_{k₀} Spec B ⟶ X₀ ×_{k₀} Spec A`,
which acts on geometric fibres by precomposition with `f`.

## Main definitions

- `AlgebraicGeometry.Scheme.FiniteEtale.constantCoverHom`
- `AlgebraicGeometry.Scheme.FiniteEtale.baseRingHom`
- `AlgebraicGeometry.Scheme.FiniteEtale.fiberConstantCoverEquiv`
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {k₀ : Type u} [Field k₀] {X₀ : Scheme.{u}} (p : X₀ ⟶ Spec (.of k₀))

lemma FiniteEtaleAlgebra.specMap_comp_specHom' {A B : FiniteEtaleAlgebra k₀}
    (f : A.1 →ₐ[k₀] B.1) :
    Spec.map (CommRingCat.ofHom (f : A.1 →+* B.1)) ≫ A.specHom = B.specHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact f.commutes x

/-- The morphism `1 ×_{k₀} Spec f : X₀ ×_{k₀} Spec B ⟶ X₀ ×_{k₀} Spec A` of constant covers
induced by a `k₀`-algebra map `f : A → B`. -/
noncomputable def constantCoverHom {A B : FiniteEtaleAlgebra k₀} (f : A.1 →ₐ[k₀] B.1) :
    constantCover p B ⟶ constantCover p A :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk
    (pullback.map p B.specHom p A.specHom (𝟙 X₀) (Spec.map (CommRingCat.ofHom (f : A.1 →+* B.1)))
      (𝟙 _) (by simp) (by simp [FiniteEtaleAlgebra.specMap_comp_specHom']))
    (by simp))

@[simp]
lemma constantCoverHom_hom_left {A B : FiniteEtaleAlgebra k₀} (f : A.1 →ₐ[k₀] B.1) :
    (constantCoverHom p f).hom.left =
      pullback.map p B.specHom p A.specHom (𝟙 X₀)
        (Spec.map (CommRingCat.ofHom (f : A.1 →+* B.1))) (𝟙 _) (by simp)
        (by simp [FiniteEtaleAlgebra.specMap_comp_specHom']) :=
  rfl

lemma constantCoverMap_eq_constantCoverHom (A : FiniteEtaleAlgebra k₀) (φ : A.1 →ₐ[k₀] A.1) :
    constantCoverMap p A φ = constantCoverHom p φ :=
  rfl

lemma constantCoverHom_comp {A B C : FiniteEtaleAlgebra k₀} (f : A.1 →ₐ[k₀] B.1)
    (g : B.1 →ₐ[k₀] C.1) :
    constantCoverHom p (g.comp f) = constantCoverHom p g ≫ constantCoverHom p f := by
  apply hom_ext
  change _ = (constantCoverHom p g).hom.left ≫ (constantCoverHom p f).hom.left
  apply pullback.hom_ext
  · simp
  · simp only [constantCoverHom_hom_left, Category.assoc, pullback.lift_snd,
      pullback.lift_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

variable {Ω : Type u} [Field Ω] (s : Spec (.of Ω) ⟶ X₀)

/-- The ring homomorphism `κ : k₀ →+* Ω` through which the geometric point `s` lies over
`Spec k₀`: `Spec κ = s ≫ p`. -/
noncomputable def baseRingHom : k₀ →+* Ω :=
  (Spec.preimage (s ≫ p)).hom

lemma spec_map_baseRingHom :
    Spec.map (CommRingCat.ofHom (baseRingHom p s)) = s ≫ p :=
  Spec.map_preimage _

variable [IsSepClosed Ω]

/-- The point of the geometric fibre at `s` of a finite étale `X₀`-scheme `P` given by a
morphism `t : Spec Ω ⟶ P` over `s`. -/
noncomputable def fiberMk (P : X₀.FiniteEtale) (t : Spec (.of Ω) ⟶ P.obj.left)
    (ht : t ≫ P.obj.hom = s) : (fiber s).obj P :=
  Over.homMk t ht

@[simp]
lemma fiberMk_left (P : X₀.FiniteEtale) (t : Spec (.of Ω) ⟶ P.obj.left)
    (ht : t ≫ P.obj.hom = s) : (fiberMk s P t ht).left = t :=
  rfl

/-- The geometric fibre at `s` of the constant cover `X₀ ×_{k₀} Spec A` is the set of ring
homomorphisms `A →+* Ω` restricting to `κ` on `k₀`: a point of the fibre is a pair of `s` and a
morphism `Spec Ω ⟶ Spec A` over `Spec k₀`. -/
noncomputable def fiberConstantCoverEquiv (A : FiniteEtaleAlgebra k₀) :
    (fiber s).obj (constantCover p A) ≃
      {φ : A.1 →+* Ω // φ.comp (algebraMap k₀ A.1) = baseRingHom p s} where
  toFun y := ⟨(Spec.preimage (y.left ≫ pullback.snd p A.specHom)).hom, by
    have : CommRingCat.ofHom (algebraMap k₀ A.1) ≫
        Spec.preimage (y.left ≫ pullback.snd p A.specHom) = Spec.preimage (s ≫ p) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
        ← pullback.condition, ← Category.assoc]
      congr 1
      exact fiber_left_comp s y
    exact congrArg CommRingCat.Hom.hom this⟩
  invFun φ := fiberMk s (constantCover p A)
    (pullback.lift s (Spec.map (CommRingCat.ofHom φ.1)) (by
      rw [← spec_map_baseRingHom]
      conv_lhs => rw [← φ.2]
      rw [CommRingCat.ofHom_comp, Spec.map_comp]))
    (pullback.lift_fst _ _ _)
  left_inv y := by
    apply fiber_ext
    change pullback.lift _ _ _ = y.left
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact (fiber_left_comp s y).symm
    · rw [pullback.lift_snd]
      exact Spec.map_preimage _
  right_inv φ := by
    apply Subtype.ext
    dsimp only
    rw [fiberMk_left, pullback.lift_snd, Spec.preimage_map]
    rfl

lemma fiberConstantCoverEquiv_apply (A : FiniteEtaleAlgebra k₀)
    (y : (fiber s).obj (constantCover p A)) :
    (fiberConstantCoverEquiv p s A y).1 =
      (Spec.preimage (y.left ≫ pullback.snd p A.specHom)).hom := by
  rfl

/-- The morphism of constant covers induced by `f : A → B` acts on geometric fibres by
precomposition with `f`. -/
lemma fiberConstantCoverEquiv_fiber_map {A B : FiniteEtaleAlgebra k₀} (f : A.1 →ₐ[k₀] B.1)
    (y : (fiber s).obj (constantCover p B)) :
    (fiberConstantCoverEquiv p s A ((fiber s).map (constantCoverHom p f) y)).1 =
      (fiberConstantCoverEquiv p s B y).1.comp (f : A.1 →+* B.1) := by
  rw [fiberConstantCoverEquiv_apply, fiberConstantCoverEquiv_apply, fiber_map_left]
  change _ = (CommRingCat.ofHom (f : A.1 →+* B.1) ≫
    Spec.preimage (y.left ≫ pullback.snd p B.specHom)).hom
  congr 1
  apply Spec.map_injective
  rw [Spec.map_preimage, Spec.map_comp, Spec.map_preimage, constantCoverHom_hom_left,
    Category.assoc, pullback.lift_snd, Category.assoc]

end AlgebraicGeometry.Scheme.FiniteEtale
