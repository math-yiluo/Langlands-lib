/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Counting geometric points of étale fibres

* `Algebra.natCard_algHom_eq_finrank_of_etale`: an étale algebra `A` over a separably closed
  field `K` has exactly `finrank K A` points with values in `K`.
* `AlgebraicGeometry.Scheme.Hom.natCard_geometricFiber_Spec_map_eq_finrank`: for a finite free
  ring map `R ⟶ S` and a geometric point `ζ : R ⟶ Ω` over which `Spec S ⟶ Spec R` is étale (the
  base change to `Spec Ω` is étale), the geometric fibre has `finrank R S` points.
* `AlgebraicGeometry.Scheme.Hom.geometricFiberPullbackEquiv`: the geometric fibre of a fibre
  product over the base is the product of the geometric fibres.
* `AlgebraicGeometry.etale_comp_ι_of_isPullback`, `AlgebraicGeometry.etale_pullback_snd_of_range`:
  étaleness over an open subset is stable under base change.

These are used for the punctured diagonal of blueprint `lemma-tangent-cones-on-cover` (ii).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped TensorProduct

/-- **Points of an étale algebra over a separably closed field.** An étale algebra `A` over a
separably closed field `K` has exactly `finrank K A` algebra homomorphisms to `K`: it is a finite
product of copies of `K`. -/
theorem Algebra.natCard_algHom_eq_finrank_of_etale (K A : Type*) [Field K] [IsSepClosed K]
    [CommRing A] [Algebra K A] [Algebra.Etale K A] :
    Nat.card (A →ₐ[K] K) = Module.finrank K A := by
  classical
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  have : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  have : Finite (PrimeSpectrum A) := by
    have : IsArtinianRing A := isArtinian_of_tower K inferInstance
    infer_instance
  let := Fintype.ofFinite (PrimeSpectrum A)
  refine le_antisymm (card_algHom_le_finrank K A K) ?_
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective
    (fun p ↦ (Pi.evalAlgHom K (fun _ ↦ K) p).comp e.toAlgHom) fun p q h ↦ ?_
  by_contra hpq
  have := congrArg (fun φ : A →ₐ[K] K ↦ φ (e.symm (Pi.single p 1))) h
  simp only [AlgHom.coe_comp, Function.comp_apply, Pi.evalAlgHom_apply] at this
  rw [AlgEquiv.coe_toAlgHom, e.apply_symm_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hpq)] at this
  exact one_ne_zero this

namespace AlgebraicGeometry

open Scheme

namespace Scheme.Hom

/-- The geometric fibre of `Spec S ⟶ Spec R` over the geometric point given by `ζ : R ⟶ Ω` is the
set of ring homomorphisms `S ⟶ Ω` extending `ζ`. -/
noncomputable def geometricFiberSpecEquiv {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {Ω : Type u} [Field Ω] (ζ : R →+* Ω) :
    (Spec.map (CommRingCat.ofHom (algebraMap R S))).GeometricFiber
      (Spec.map (CommRingCat.ofHom ζ)) ≃ RingHom.PointsOver ζ S where
  toFun x := ⟨(Spec.preimage x.1).hom, by
    have h : CommRingCat.ofHom (algebraMap R S) ≫ Spec.preimage x.1 = CommRingCat.ofHom ζ :=
      Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage, x.2])
    exact congrArg CommRingCat.Hom.hom h⟩
  invFun χ := ⟨Spec.map (CommRingCat.ofHom χ.1), by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact RingHom.congr_fun χ.2 a⟩
  left_inv x := Subtype.ext (by simp)
  right_inv χ := by
    refine Subtype.ext ?_
    simp

/-- **The geometric fibre of a finite étale morphism of affine schemes.** Let `R ⟶ S` be finite
free and `ζ : R ⟶ Ω` a geometric point with `Ω` separably closed over which `Spec S ⟶ Spec R` is
étale (the base change to `Spec Ω` is étale). Then the geometric fibre over `ζ` has
`finrank R S` points. -/
theorem natCard_geometricFiber_Spec_map_eq_finrank {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Module.Free R S] [Module.Finite R S] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ζ : R →+* Ω) (h : Etale (pullback.fst (Spec.map (CommRingCat.ofHom ζ))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))) :
    Nat.card ((Spec.map (CommRingCat.ofHom (algebraMap R S))).GeometricFiber
      (Spec.map (CommRingCat.ofHom ζ))) = Module.finrank R S := by
  let : Algebra R Ω := ζ.toAlgebra
  have := ζ.domain_nontrivial
  have hfst := pullbackSpecIso_hom_fst R Ω S
  have : Etale (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[R] S))) := by
    have : Etale ((pullbackSpecIso R Ω S).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : Ω →+* Ω ⊗[R] S))) := by
      rw [hfst]
      exact h
    rwa [MorphismProperty.cancel_left_of_respectsIso (P := @Etale)] at this
  have : Algebra.Etale Ω (Ω ⊗[R] S) := by
    rw [← RingHom.etale_algebraMap]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  rw [← Module.finrank_baseChange (R := Ω),
    ← Algebra.natCard_algHom_eq_finrank_of_etale Ω (Ω ⊗[R] S)]
  refine Nat.card_congr ((geometricFiberSpecEquiv ζ).trans
    ((RingHom.PointsOver.tensorEquiv (φ' := RingHom.id Ω) (A' := Ω) rfl).symm.trans ?_))
  exact
    { toFun t := { t.1 with commutes' := RingHom.congr_fun t.2 }
      invFun t := ⟨t.toRingHom, RingHom.ext t.commutes⟩
      left_inv t := rfl
      right_inv t := rfl }

/-- **The geometric fibre of a fibre product over the base** is the product of the geometric
fibres. -/
noncomputable def geometricFiberPullbackEquiv {X₁ X₂ T : Scheme.{u}} (f₁ : X₁ ⟶ T) (f₂ : X₂ ⟶ T)
    {Ω : Type u} [Field Ω] (z : Spec (.of Ω) ⟶ T) :
    (pullback.fst f₁ f₂ ≫ f₁).GeometricFiber z ≃ f₁.GeometricFiber z × f₂.GeometricFiber z where
  toFun x := (⟨x.1 ≫ pullback.fst f₁ f₂, by rw [Category.assoc]; exact x.2⟩,
    ⟨x.1 ≫ pullback.snd f₁ f₂, by rw [Category.assoc, ← pullback.condition]; exact x.2⟩)
  invFun y := ⟨pullback.lift y.1.1 y.2.1 (by rw [y.1.2, y.2.2]), by
    rw [pullback.lift_fst_assoc]
    exact y.1.2⟩
  left_inv x := Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _))
  right_inv y := Prod.ext (Subtype.ext (pullback.lift_fst _ _ _))
    (Subtype.ext (pullback.lift_snd _ _ _))

/-- Precomposing with an isomorphism does not change the geometric fibre. -/
noncomputable def geometricFiberCompIsoEquiv {X X' Y : Scheme.{u}} (α : X ⟶ X') [IsIso α]
    (f : X' ⟶ Y) {Ω : Type u} [Field Ω] (z : Spec (.of Ω) ⟶ Y) :
    (α ≫ f).GeometricFiber z ≃ f.GeometricFiber z where
  toFun x := ⟨x.1 ≫ α, by rw [Category.assoc, x.2]⟩
  invFun y := ⟨y.1 ≫ inv α, by rw [Category.assoc, IsIso.inv_hom_id_assoc, y.2]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)

end Scheme.Hom

/-- **Étaleness over an open subset is stable under base change.** In a pullback square
`P ⟶ X`, `P ⟶ Y'` of `f : X ⟶ Y` along `g : Y' ⟶ Y`, if `f` is étale on the open `V ⊆ X`, then
`P ⟶ Y'` is étale on the preimage of `V`. -/
theorem etale_comp_ι_of_isPullback {P X Y Y' : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback fst snd f g) (V : X.Opens) [Etale (V.ι ≫ f)] :
    Etale ((fst ⁻¹ᵁ V).ι ≫ snd) := by
  exact MorphismProperty.of_isPullback ((isPullback_morphismRestrict fst V).paste_vert h) ‹_›

/-- If `f` is étale over the open `U` of the target, then the base change of `f` along a morphism
landing in `U` is étale. -/
theorem etale_pullback_snd_of_range {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [Etale ((f ⁻¹ᵁ U).ι ≫ f)] (g : Y' ⟶ Y) (hg : Set.range g.base ⊆ U) :
    Etale (pullback.snd f g) := by
  have : Etale (f ∣_ U) := by
    have : Etale ((f ∣_ U) ≫ U.ι) := by rwa [morphismRestrict_ι]
    exact Etale.of_comp _ U.ι
  let g' := IsOpenImmersion.lift U.ι g (by rwa [Opens.range_ι])
  have hg' : g' ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
  have h : IsPullback (pullback.fst (f ∣_ U) g' ≫ (f ⁻¹ᵁ U).ι) (pullback.snd (f ∣_ U) g') f g := by
    rw [← hg']
    exact (IsPullback.of_hasPullback (f ∣_ U) g').paste_horiz
      (isPullback_morphismRestrict f U).flip
  have : Etale (pullback.snd (f ∣_ U) g') :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (f ∣_ U) g') ‹_›
  rw [← (Iso.inv_comp_eq _).mpr h.isoPullback_hom_snd.symm]
  infer_instance

/-- Étaleness on an open subset passes to smaller open subsets. -/
theorem etale_comp_ι_of_le {X Y : Scheme.{u}} (f : X ⟶ Y) {V V' : X.Opens} (h : V' ≤ V)
    [Etale (V.ι ≫ f)] : Etale (V'.ι ≫ f) := by
  rw [← X.homOfLE_ι h, Category.assoc]
  infer_instance

/-- If `g` is étale on the open `W` and maps `W` into an open `V` on which `f` is étale, then
`g ≫ f` is étale on `W`. -/
theorem etale_comp_ι_comp_of_range {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (W : X.Opens)
    (V : Y.Opens) [Etale (W.ι ≫ g)] [Etale (V.ι ≫ f)] (h : Set.range (W.ι ≫ g).base ⊆ V) :
    Etale (W.ι ≫ g ≫ f) := by
  let l := IsOpenImmersion.lift V.ι (W.ι ≫ g) (by rwa [Opens.range_ι])
  have hl : l ≫ V.ι = W.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have : Etale (l ≫ V.ι) := by
    rw [hl]
    infer_instance
  have : Etale l := Etale.of_comp l V.ι
  rw [← Category.assoc, ← hl, Category.assoc]
  infer_instance

end AlgebraicGeometry
