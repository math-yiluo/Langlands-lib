import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Faithfully flat descent for coalgebras and for groupoid-like ring data

For a ring map `φ : A₀ →+* B₀`, coalgebras for the comonad `N ↦ B₀ ⊗[A₀] N` on `B₀`-modules are
descent data for modules relative to `φ` (Stacks Project Section 35.3, Tag 023F). This module
defines their coinvariants and the descent map `B₀ ⊗[A₀] coinvariants X ⟶ X`, and proves that the
descent map is an isomorphism when `φ` is faithfully flat (effective descent, Tag 023N), using
Mathlib's comonadicity of extension of scalars along faithfully flat ring maps. It then applies
this to ring data shaped like an affine étale equivalence relation with a cartesian map to one
with an affine quotient.
-/

open CategoryTheory ModuleCat TensorProduct

universe u

set_option linter.style.haveILetI false

noncomputable section

namespace Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent

section General

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

set_option backward.isDefEq.respectTransparency false in
/-- The transpose of a coalgebra map out of `comparison B` equalizes the coalgebra pair. -/
lemma homEquiv_comp_eq {B : C} {X : adj.toComonad.Coalgebra}
    (f : (Comonad.comparison adj).obj B ⟶ X) :
    adj.homEquiv _ _ f.f ≫ R.map X.a = adj.homEquiv _ _ f.f ≫ adj.unit.app (R.obj X.A) := by
  have h : L.map (adj.unit.app B) ≫ L.map (R.map f.f) = f.f ≫ X.a := f.h
  rw [Adjunction.homEquiv_unit, Category.assoc, Category.assoc, ← R.map_comp, ← h, R.map_comp,
    Adjunction.unit_naturality_assoc, Adjunction.unit_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- A map into an equalizing object transposes to a coalgebra map out of `comparison B`. -/
lemma comparison_a_comp_eq {B E : C} {X : adj.toComonad.Coalgebra} (g : B ⟶ E)
    (ι : E ⟶ R.obj X.A) (hι : ι ≫ R.map X.a = ι ≫ adj.unit.app (R.obj X.A)) :
    ((Comonad.comparison adj).obj B).a ≫ adj.toComonad.map ((adj.homEquiv _ _).symm (g ≫ ι)) =
      (adj.homEquiv _ _).symm (g ≫ ι) ≫ X.a := by
  have hk : adj.unit.app B ≫ R.map ((adj.homEquiv _ _).symm (g ≫ ι)) = g ≫ ι := by
    exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  show L.map (adj.unit.app B) ≫ L.map (R.map ((adj.homEquiv _ _).symm (g ≫ ι))) =
    (adj.homEquiv _ _).symm (g ≫ ι) ≫ X.a
  rw [← L.map_comp, hk, Adjunction.homEquiv_counit, Category.assoc, ← adj.counit_naturality,
    ← L.map_comp_assoc, Category.assoc, hι, ← Category.assoc,
    L.map_comp (g ≫ ι) (adj.unit.app (R.obj X.A)), Category.assoc]
  erw [adj.left_triangle_components (R.obj X.A), Category.comp_id]

end General

section Coalgebra

variable {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀] (φ : A₀ →+* B₀)

/-- The comonad `N ↦ B₀ ⊗[A₀] N` on `B₀`-modules. -/
abbrev descentComonad : Comonad (ModuleCat.{u} B₀) := (extendRestrictScalarsAdj.{u} φ).toComonad

/-- The coinvariants of a coalgebra `X`: the `A₀`-submodule of elements `n` with
`X.a n = 1 ⊗ n`. -/
def coinvariants (X : (descentComonad φ).Coalgebra) : Submodule A₀ ((restrictScalars φ).obj X.A) :=
  LinearMap.eqLocus ((restrictScalars φ).map X.a).hom
    ((extendRestrictScalarsAdj.{u} φ).unit.app ((restrictScalars φ).obj X.A)).hom

/-- The inclusion of the coinvariants. -/
abbrev coinvariantsι (X : (descentComonad φ).Coalgebra) :
    ModuleCat.of A₀ (coinvariants φ X) ⟶ (restrictScalars φ).obj X.A :=
  ModuleCat.ofHom (Y := ↑((restrictScalars φ).obj X.A)) (coinvariants φ X).subtype

/-- The coinvariants equalize the coaction and the unit `n ↦ 1 ⊗ n`. -/
lemma coinvariantsι_comp (X : (descentComonad φ).Coalgebra) :
    coinvariantsι φ X ≫ (restrictScalars φ).map X.a =
      coinvariantsι φ X ≫
        (extendRestrictScalarsAdj.{u} φ).unit.app ((restrictScalars φ).obj X.A) := by
  ext ⟨n, hn⟩
  exact hn

/-- The descent map `B₀ ⊗[A₀] coinvariants X ⟶ X`, `b ⊗ n ↦ b • n`. -/
def descentMap (X : (descentComonad φ).Coalgebra) :
    (extendScalars φ).obj (ModuleCat.of A₀ (coinvariants φ X)) ⟶ X.A :=
  ((extendRestrictScalarsAdj.{u} φ).homEquiv _ _).symm (coinvariantsι φ X)

set_option backward.isDefEq.respectTransparency false in
/-- Coalgebra maps out of `comparison B` correspond to linear maps into the coinvariants. -/
def coinvariantsHomEquiv (B : ModuleCat.{u} A₀) (X : (descentComonad φ).Coalgebra) :
    ((Comonad.comparison (extendRestrictScalarsAdj.{u} φ)).obj B ⟶ X) ≃
      (B ⟶ ModuleCat.of A₀ (coinvariants φ X)) where
  toFun f := ModuleCat.ofHom
    (((extendRestrictScalarsAdj.{u} φ).homEquiv _ _ f.f).hom.codRestrict _ (fun b =>
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
        (homEquiv_comp_eq (extendRestrictScalarsAdj.{u} φ) f)) b))
  invFun g :=
    { f := ((extendRestrictScalarsAdj.{u} φ).homEquiv _ _).symm (g ≫ coinvariantsι φ X)
      h := comparison_a_comp_eq (extendRestrictScalarsAdj.{u} φ) g (coinvariantsι φ X)
        (coinvariantsι_comp φ X) }
  left_inv f := by
    ext1
    apply (Equiv.symm_apply_eq _).2
    rfl
  right_inv g := by
    ext b
    show ((extendRestrictScalarsAdj.{u} φ).homEquiv _ _
      (((extendRestrictScalarsAdj.{u} φ).homEquiv _ _).symm (g ≫ coinvariantsι φ X))).hom b = _
    rw [Equiv.apply_symm_apply]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The coinvariants functor, right adjoint to the comparison functor. -/
def coinvariantsFunctor : (descentComonad φ).Coalgebra ⥤ ModuleCat.{u} A₀ :=
  Adjunction.rightAdjointOfEquiv (F := Comonad.comparison (extendRestrictScalarsAdj.{u} φ))
    (G_obj := fun X => ModuleCat.of A₀ (coinvariants φ X)) (coinvariantsHomEquiv φ) (by
      intro B B' X g h
      ext b
      show ((extendRestrictScalarsAdj.{u} φ).homEquiv _ _
        ((extendScalars φ).map g ≫ h.f)).hom b =
          ((extendRestrictScalarsAdj.{u} φ).homEquiv _ _ h.f).hom (g.hom b)
      rw [Adjunction.homEquiv_naturality_left]
      rfl)

/-- The comparison functor is left adjoint to the coinvariants functor. -/
def coinvariantsAdjunction :
    Comonad.comparison (extendRestrictScalarsAdj.{u} φ) ⊣ coinvariantsFunctor φ :=
  Adjunction.adjunctionOfEquivRight _ _

set_option backward.isDefEq.respectTransparency false in
/-- The counit of the coinvariants adjunction is the descent map. -/
lemma coinvariantsAdjunction_counit_f (X : (descentComonad φ).Coalgebra) :
    ((coinvariantsAdjunction φ).counit.app X).f = descentMap φ X := by
  simp only [coinvariantsAdjunction, Adjunction.adjunctionOfEquivRight_counit_app]
  show ((extendRestrictScalarsAdj.{u} φ).homEquiv _ _).symm (𝟙 _ ≫ coinvariantsι φ X) = _
  rw [Category.id_comp]
  rfl

/-- **Faithfully flat descent for coalgebras.** If `φ` is faithfully flat, the descent map
`B₀ ⊗[A₀] coinvariants X ⟶ X` of every coalgebra `X` is an isomorphism. -/
theorem isIso_descentMap (hφ : φ.FaithfullyFlat) (X : (descentComonad φ).Coalgebra) :
    IsIso (descentMap φ X) := by
  have : (Comonad.comparison (extendRestrictScalarsAdj.{u} φ)).IsEquivalence :=
    (comonadicExtendScalars hφ).eqv
  have h := (coinvariantsAdjunction φ).isIso_counit_app_of_iso
    ((Comonad.comparison (extendRestrictScalarsAdj.{u} φ)).objObjPreimageIso X).symm
  have h2 : IsIso ((Comonad.forget _).map ((coinvariantsAdjunction φ).counit.app X)) :=
    Functor.map_isIso _ _
  rw [Comonad.forget_map, coinvariantsAdjunction_counit_f] at h2
  exact h2

/-- The descent map of a coalgebra along a faithfully flat ring map is bijective. -/
theorem bijective_descentMap (hφ : φ.FaithfullyFlat) (X : (descentComonad φ).Coalgebra) :
    Function.Bijective (descentMap φ X).hom := by
  have := isIso_descentMap φ hφ X
  exact (ConcreteCategory.bijective_of_isIso (descentMap φ X))

end Coalgebra

section GroupoidDescent

variable {A₀ B₀ B C C₂ : Type u} [CommRing A₀] [CommRing B₀] [CommRing B] [CommRing C]
  [CommRing C₂]

set_option backward.isDefEq.respectTransparency false in
/-- **Faithfully flat descent for an étale-groupoid-like ring structure.** Let `φ : A₀ → B₀` be
faithfully flat and `F : B₀ → B` a ring map. Suppose `C` is the pushout `B₀ ⊗[A₀] B` along the
maps `τ ∘ F` and `σ`, `C₂` is the pushout `C ⊗[σ, B, τ] C` with coprojections `ι₁`, `ι₂`, and
`d : C → B`, `c : C → C₂` are ring maps with `d ∘ τ = d ∘ σ = id`, `c ∘ τ = ι₁ ∘ τ` and
`c ∘ σ = ι₂ ∘ σ` (a unit and a composition). Then `B` is the base change along `φ` of the
equalizer `A = {b | τ b = σ b}`: the square `A₀ → B₀, A₀ → A, B₀ → B, A → B` is a pushout. -/
theorem isPushout_eqLocus_of_groupoid (φ : A₀ →+* B₀) (hφ : φ.FaithfullyFlat) (F : B₀ →+* B)
    (τ σ : B →+* C) (d : C →+* B) (ι₁ ι₂ c : C →+* C₂)
    (hP : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom (F.comp φ))
      (CommRingCat.ofHom (τ.comp F)) (CommRingCat.ofHom σ))
    (hP₂ : IsPushout (CommRingCat.ofHom σ) (CommRingCat.ofHom τ) (CommRingCat.ofHom ι₁)
      (CommRingCat.ofHom ι₂))
    (hdτ : d.comp τ = RingHom.id B) (hdσ : d.comp σ = RingHom.id B)
    (hcτ : c.comp τ = ι₁.comp τ) (hcσ : c.comp σ = ι₂.comp σ)
    (hmem : ∀ a : A₀, F (φ a) ∈ τ.eqLocus σ) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ((F.comp φ).codRestrict _ hmem))
      (CommRingCat.ofHom F) (CommRingCat.ofHom (τ.eqLocus σ).subtype) := by
  have hw : (τ.comp F).comp φ = (σ.comp F).comp φ := by
    have := congrArg CommRingCat.Hom.hom hP.w
    simpa using this
  have hw₂ : ι₁.comp σ = ι₂.comp τ := by
    have := congrArg CommRingCat.Hom.hom hP₂.w
    simpa using this
  letI : Algebra A₀ B₀ := φ.toAlgebra
  letI : Algebra B₀ B := F.toAlgebra
  letI : Algebra A₀ B := (F.comp φ).toAlgebra
  haveI : IsScalarTower A₀ B₀ B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra B₀ C := (τ.comp F).toAlgebra
  letI : Algebra B C := σ.toAlgebra
  letI : Algebra A₀ C := ((τ.comp F).comp φ).toAlgebra
  haveI : IsScalarTower A₀ B₀ C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A₀ B C := IsScalarTower.of_algebraMap_eq (fun a => congrArg (· a) hw)
  haveI : Algebra.IsPushout A₀ B₀ B C := CommRingCat.isPushout_iff_isPushout.mp hP
  let e : B₀ ⊗[A₀] B ≃ₐ[B₀] C := Algebra.IsPushout.equiv A₀ B₀ B C
  have he : ∀ (b₀ : B₀) (b : B), e (b₀ ⊗ₜ b) = τ (F b₀) * σ b := fun b₀ b =>
    Algebra.IsPushout.equiv_tmul _ _ _ _ b₀ b
  let τ' : B →ₐ[B₀] C := { τ with commutes' := fun _ => rfl }
  let a : B →ₐ[B₀] B₀ ⊗[A₀] B := e.symm.toAlgHom.comp τ'
  have hea : ∀ b, e (a b) = τ b := fun b => e.apply_symm_apply (τ b)
  -- the multiplication map and the diagonal
  have hμ : ∀ x : B₀ ⊗[A₀] B,
      ((extendRestrictScalarsAdj.{u} φ).counit.app (ModuleCat.of B₀ B)).hom x = d (e x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b₀ b =>
      rw [he, map_mul, ← RingHom.comp_apply d τ, ← RingHom.comp_apply d σ, hdτ, hdσ]
      change b₀ • b = F b₀ * b
      exact Algebra.smul_def b₀ b
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  -- the second pushout `C₂ = B₀ ⊗[A₀] C`
  have hP₃ : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom ((τ.comp F).comp φ))
      (CommRingCat.ofHom (ι₁.comp (τ.comp F))) (CommRingCat.ofHom ι₂) := by
    have := (hP.flip.paste_horiz hP₂.flip).flip
    exact this
  letI : Algebra B₀ C₂ := (ι₁.comp (τ.comp F)).toAlgebra
  letI : Algebra C C₂ := ι₂.toAlgebra
  letI : Algebra A₀ C₂ := ((ι₁.comp (τ.comp F)).comp φ).toAlgebra
  haveI : IsScalarTower A₀ B₀ C₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A₀ C C₂ := IsScalarTower.of_algebraMap_eq (fun a => by
    change ι₁ (τ (F (φ a))) = ι₂ (τ (F (φ a)))
    rw [← RingHom.comp_apply ι₂ τ, ← hw₂, RingHom.comp_apply]
    exact congrArg ι₁ (congrArg (· a) hw))
  haveI : Algebra.IsPushout A₀ B₀ C C₂ := CommRingCat.isPushout_iff_isPushout.mp hP₃
  let e₂ : B₀ ⊗[A₀] C ≃ₐ[B₀] C₂ := Algebra.IsPushout.equiv A₀ B₀ C C₂
  have he₂ : ∀ (b₀ : B₀) (x : C), e₂ (b₀ ⊗ₜ x) = ι₁ (τ (F b₀)) * ι₂ x := fun b₀ x =>
    Algebra.IsPushout.equiv_tmul _ _ _ _ b₀ x
  let Ψ : B₀ ⊗[A₀] (B₀ ⊗[A₀] B) ≃ₐ[A₀] C₂ :=
    (Algebra.TensorProduct.congr AlgEquiv.refl (e.restrictScalars A₀)).trans (e₂.restrictScalars A₀)
  have hΨ : ∀ (b₀ : B₀) (y : B₀ ⊗[A₀] B), Ψ (b₀ ⊗ₜ y) = ι₁ (τ (F b₀)) * ι₂ (e y) := fun b₀ y =>
    he₂ b₀ (e y)
  have hδ : ∀ x : B₀ ⊗[A₀] B,
      Ψ (((descentComonad φ).δ.app (ModuleCat.of B₀ B)).hom x) = c (e x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b₀ n =>
      change Ψ (b₀ ⊗ₜ ((1 : B₀) ⊗ₜ n)) = c (e (b₀ ⊗ₜ n))
      rw [hΨ, he, he, map_one, map_one, one_mul, map_mul, ← RingHom.comp_apply c τ,
        ← RingHom.comp_apply c σ, hcτ, hcσ, RingHom.comp_apply, RingHom.comp_apply]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have hGa : ∀ x : B₀ ⊗[A₀] B,
      Ψ (((descentComonad φ).map (ModuleCat.ofHom (a.toLinearMap : B →ₗ[B₀] B₀ ⊗[A₀] B))).hom x) =
        ι₁ (e x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b₀ n =>
      change Ψ (b₀ ⊗ₜ (a n)) = ι₁ (e (b₀ ⊗ₜ n))
      rw [hΨ, hea, he, map_mul, ← RingHom.comp_apply ι₂ τ, ← hw₂, RingHom.comp_apply]
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  let X : (descentComonad φ).Coalgebra :=
    { A := ModuleCat.of B₀ B
      a := ModuleCat.ofHom (a.toLinearMap : B →ₗ[B₀] B₀ ⊗[A₀] B)
      counit := by
        ext b
        change ((extendRestrictScalarsAdj.{u} φ).counit.app (ModuleCat.of B₀ B)).hom (a b) = b
        rw [hμ, hea, ← RingHom.comp_apply d τ, hdτ, RingHom.id_apply]
      coassoc := by
        ext b
        apply Ψ.injective
        change Ψ (((descentComonad φ).δ.app (ModuleCat.of B₀ B)).hom (a b)) =
          Ψ (((descentComonad φ).map (ModuleCat.ofHom (a.toLinearMap : B →ₗ[B₀] B₀ ⊗[A₀] B))).hom
            (a b))
        rw [hδ, hGa, hea, ← RingHom.comp_apply c τ, hcτ, RingHom.comp_apply] }
  -- the coinvariants are the equalizer of `τ` and `σ`
  have hcoinv : ∀ n : B, n ∈ coinvariants φ X ↔ τ n = σ n := by
    intro n
    change a n = (1 : B₀) ⊗ₜ n ↔ _
    rw [← e.injective.eq_iff, hea, he, map_one, map_one, one_mul]
  set A : Subring B := τ.eqLocus σ with hA
  letI : Algebra A₀ A := ((F.comp φ).codRestrict _ hmem).toAlgebra
  letI : Algebra A B := A.subtype.toAlgebra
  haveI : IsScalarTower A₀ A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ψ : A ≃ₗ[A₀] coinvariants φ X :=
    { toFun := fun x => ⟨x.1, (hcoinv x.1).2 x.2⟩
      invFun := fun y => ⟨y.1, (hcoinv y.1).1 y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let D := LinearEquiv.ofBijective (descentMap φ X).hom (bijective_descentMap φ hφ X)
  let E : B₀ ⊗[A₀] A ≃ₗ[B₀] B :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B₀ B₀) ψ).trans D
  have hE : ∀ x : A, E ((1 : B₀) ⊗ₜ x) = algebraMap A B x := by
    intro x
    change (1 : B₀) • (x.1 : B) = x.1
    exact one_smul _ _
  haveI : Algebra.IsPushout A₀ B₀ A B := ⟨IsBaseChange.of_equiv E hE⟩
  exact CommRingCat.isPushout_of_isPushout A₀ B₀ A B

end GroupoidDescent

end Langlands.AlgebraicGeometry.FaithfullyFlatCoalgebraDescent

end
