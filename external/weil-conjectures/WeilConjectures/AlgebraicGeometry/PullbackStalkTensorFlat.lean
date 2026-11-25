/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Flatness of the fibre-product stalk over the tensor product of stalks

Source: Stacks Project, Examples, Tag 0FLS; Schemes, Tag 01I4; Algebra, Tag 00HT.
(blueprint: lem-pc-pullback-stalk-tensor-flat).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry

private theorem spec_stalkCongr_fromSpecStalk {S : Scheme.{u}} {s t : S} (h : s = t) :
    Spec.map (S.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ S.fromSpecStalk s =
      S.fromSpecStalk t := by
  subst t
  simp

private theorem preimmersion_pullback_map
    {A B R X T S : Scheme.{u}} (a : A ⟶ R) (b : B ⟶ R)
    (f : X ⟶ S) (g : T ⟶ S) (iA : A ⟶ X) (iB : B ⟶ T) (iR : R ⟶ S)
    [IsPreimmersion iA] [IsPreimmersion iB] [Mono iR]
    (ha : a ≫ iR = iA ≫ f) (hb : b ≫ iR = iB ≫ g) :
    IsPreimmersion (pullback.map a b f g iA iB iR ha hb) := by
  rw [pullback_map_eq_pullbackFstFstIso_inv]
  infer_instance

/-- The canonical tensor-product map to a fibre-product stalk is flat.
Source: Stacks Project, Examples, Tag 0FLS, the paragraph on the canonical stalk map.
(blueprint: lem-pc-pullback-stalk-tensor-flat).

Proof: Choose affine neighbourhoods Spec R₀ of the common image and Spec A₀, Spec B₀
of the two projected points lying over it. Their fibre product is Spec(A₀ ⊗[R₀] B₀).
Its local ring C at x' is the localization at the prime of x'. The rings R, A and B
are the corresponding localizations of R₀, A₀ and B₀. Consequently A ⊗[R] B is
obtained by inverting the elements of A₀ and B₀ outside the two projected primes in
A₀ ⊗[R₀] B₀. All these elements are units in C, so C is a further localization of
A ⊗[R] B. The four equations identify this map with the stipulated algebra map.
Localization is flat. No flatness hypothesis on either scheme morphism is used. -/
theorem pullback_stalk_tensor_flat
    {S T X : Scheme.{u}} (g : T ⟶ S) (f : X ⟶ S)
    (x' : ↥(pullback f g))
    [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk ((pullback.fst f g)
      x'))] [Algebra (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x'))] [Algebra ((X.presheaf.stalk ((pullback.fst f g) x'))
      ⊗[(S.presheaf.stalk (f ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g)
      x'))) ((pullback f g).presheaf.stalk x')]
    (hRA : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (X.presheaf.stalk
      ((pullback.fst f g) x')) = (f.stalkMap ((pullback.fst f g) x')).hom)
    (hRB : algebraMap (S.presheaf.stalk (f ((pullback.fst f g) x'))) (T.presheaf.stalk
      ((pullback.snd f g) x')) =
      (g.stalkMap ((pullback.snd f g) x')).hom.comp (S.presheaf.stalkCongr (Inseparable.of_eq
        (congrArg (fun φ : pullback f g ⟶ S => φ x') pullback.condition))).hom.hom)
    (hAC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp (algebraMap (X.presheaf.stalk ((pullback.fst f g) x'))
      ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f ((pullback.fst f g)
      x')))] (T.presheaf.stalk ((pullback.snd f g) x')))) =
      ((pullback.fst f g).stalkMap x').hom)
    (hBC : (algebraMap ((X.presheaf.stalk ((pullback.fst f g) x')) ⊗[(S.presheaf.stalk (f
      ((pullback.fst f g) x')))] (T.presheaf.stalk ((pullback.snd f g) x'))) ((pullback f
      g).presheaf.stalk x')).comp
      Algebra.TensorProduct.includeRight.toRingHom =
        ((pullback.snd f g).stalkMap x').hom)
    : Module.Flat
      ((X.presheaf.stalk ((pullback.fst f g) x'))
        ⊗[S.presheaf.stalk (f ((pullback.fst f g) x'))]
        (T.presheaf.stalk ((pullback.snd f g) x')))
      ((pullback f g).presheaf.stalk x') := by
  let R := S.presheaf.stalk (f ((pullback.fst f g) x'))
  let A := X.presheaf.stalk ((pullback.fst f g) x')
  let B := T.presheaf.stalk ((pullback.snd f g) x')
  let C := (pullback f g).presheaf.stalk x'
  let a := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R B))
  let iA := X.fromSpecStalk ((pullback.fst f g) x')
  let iB := T.fromSpecStalk ((pullback.snd f g) x')
  let iR := S.fromSpecStalk (f ((pullback.fst f g) x'))
  have ha : a ≫ iR = iA ≫ f := by
    dsimp [a, iR, iA]
    rw [hRA]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hb : b ≫ iR = iB ≫ g := by
    dsimp [b, iR, iB]
    rw [hRB]
    change Spec.map ((S.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun φ : pullback f g ⟶ S ↦ φ x') pullback.condition))).hom ≫
        g.stalkMap ((pullback.snd f g) x')) ≫ _ = _
    rw [Spec.map_comp, Category.assoc]
    have hp : f ((pullback.fst f g) x') = g ((pullback.snd f g) x') :=
      congrArg (fun φ : pullback f g ⟶ S ↦ φ x') pullback.condition
    change Spec.map (g.stalkMap ((pullback.snd f g) x')) ≫
      Spec.map (S.presheaf.stalkCongr (Inseparable.of_eq hp)).hom ≫
        S.fromSpecStalk (f ((pullback.fst f g) x')) = _
    rw [spec_stalkCongr_fromSpecStalk hp]
    exact Scheme.SpecMap_stalkMap_fromSpecStalk g
  let m := pullback.map a b f g iA iB iR ha hb
  have hm : IsPreimmersion m := preimmersion_pullback_map a b f g iA iB iR ha hb
  let h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R A B)
  let k : Spec (.of (A ⊗[R] B)) ⟶ pullback f g := h.isoPullback.hom ≫ m
  have hk : IsPreimmersion k := by
    dsimp [k]
    infer_instance
  let j := Spec.map (CommRingCat.ofHom (algebraMap (A ⊗[R] B) C))
  have hj : j ≫ k = (pullback f g).fromSpecStalk x' := by
    apply pullback.hom_ext
    · dsimp [k, m, pullback.map]
      simp only [Category.assoc, pullback.lift_fst]
      rw [h.isoPullback_hom_fst_assoc, ← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((algebraMap (A ⊗[R] B) C).comp
        (algebraMap A (A ⊗[R] B)))) ≫ iA = _
      rw [hAC]
      exact Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.fst f g)
    · dsimp [k, m, pullback.map]
      simp only [Category.assoc, pullback.lift_snd]
      rw [h.isoPullback_hom_snd_assoc, ← Category.assoc, ← Spec.map_comp]
      change Spec.map (CommRingCat.ofHom ((algebraMap (A ⊗[R] B) C).comp
        Algebra.TensorProduct.includeRight.toRingHom)) ≫ iB = _
      rw [hBC]
      exact Scheme.SpecMap_stalkMap_fromSpecStalk (pullback.snd f g)
  have hflat : Flat (j ≫ k) := by
    rw [hj]
    exact Scheme.flat_fromSpecStalk (pullback f g) x'
  have hjflat : Flat j :=
    MorphismProperty.of_postcomp (W := @Flat)
      (W' := MorphismProperty.monomorphisms Scheme) j k (inferInstance : Mono k) hflat
  exact RingHom.flat_algebraMap_iff.mp (Flat.SpecMap_iff.mp hjflat)

end AlgebraicGeometry
