/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalFunctorial
public import Mathlib.RingTheory.Ideal.CotangentBaseChange
import WeilConjectures.AlgebraicGeometry.ClosedImmersionConormalAffineSourceCoordinates
import WeilConjectures.AlgebraicGeometry.AffineConormalSections
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine

/-! # Affine comparison for the canonical conormal base-change map

Source: Stacks Project, Morphisms, Lemma 0473, affine reduction, and
Schemes, Lemma 01JU (1)
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def cotangentEquiv {R P B : Type*}
    [CommRing R] [CommRing P] [CommRing B] [Algebra R P] [Algebra R B]
    (I : Ideal P) (J : Ideal B) (e : P ≃ₐ[R] B) (h : I.map e.toRingHom = J) :
    I.Cotangent ≃ₗ[R] J.Cotangent := by
  have hf : I ≤ J.comap e.toAlgHom := by
    intro x hx
    change e x ∈ J
    rw [← h]
    exact Ideal.mem_map_of_mem _ hx
  have hg : J ≤ I.comap e.symm.toAlgHom := by
    intro y hy
    change e.symm y ∈ I
    rw [← h] at hy
    change y ∈ I.map (e.toRingEquiv : P →+* B) at hy
    rw [Ideal.map_comap_of_equiv e.toRingEquiv] at hy
    exact hy
  exact
    { toLinearMap := Ideal.mapCotangent I J e.toAlgHom hf
      invFun := Ideal.mapCotangent J I e.symm.toAlgHom hg
      left_inv := by
        intro x
        obtain ⟨x, rfl⟩ := I.toCotangent_surjective x
        change Ideal.mapCotangent J I e.symm.toAlgHom hg
          (Ideal.mapCotangent I J e.toAlgHom hf (I.toCotangent x)) = I.toCotangent x
        simp only [Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (e.symm_apply_apply x)
      right_inv := by
        intro y
        obtain ⟨y, rfl⟩ := J.toCotangent_surjective y
        change Ideal.mapCotangent I J e.toAlgHom hf
          (Ideal.mapCotangent J I e.symm.toAlgHom hg (J.toCotangent y)) = J.toCotangent y
        simp only [Ideal.mapCotangent_toCotangent]
        congr 1
        exact Subtype.ext (e.apply_symm_apply y) }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem targetCoordinates {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    ∃ eT : Γ((tensorPullback i).obj i.ker.toModules, i ⁻¹ᵁ U.1) ≃+
        ((i'.ker.ideal U').map (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(X', U'.1) →+* Γ(X, U.1) ⊗[Γ(X', U'.1)] Γ(X', U'.1))).Cotangent,
      ∀ (b : Γ(X, U.1)) (a : i'.ker.ideal U') (s : Γ(i.ker.toModules, U.1)),
        i.ker.toModulesι.app U.1 s = g.appLE U'.1 U.1 H (a : Γ(X', U'.1)) →
        eT (i.app U.1 b •
          (show Γ((tensorPullback i).obj i.ker.toModules, i ⁻¹ᵁ U.1) from
            ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
              i.ker.toModules).app U.1 s)) =
          (i'.ker.ideal U').tensorCotangentHom Γ(X', U'.1) Γ(X, U.1)
            (b ⊗ₜ[Γ(X', U'.1)] (i'.ker.ideal U').toCotangent a) := by
  classical
  dsimp only
  let : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
  let A := Γ(X', U'.1)
  let B := Γ(X, U.1)
  let J := i'.ker.ideal U'
  let K := J.map (Algebra.TensorProduct.includeRight.toRingHom : A →+* B ⊗[A] A)
  let r : B ⊗[A] A ≃ₐ[B] B := Algebra.TensorProduct.rid A B B
  have hi : i.ker.ideal U = J.map (g.appLE U'.1 U.1 H).hom := by
    let p : IsPullback i f g i' := IsPullback.of_isLimit hc
    have hk : i.ker = i'.ker.comap g := by
      rw [← p.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
        Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    rw [hk]
    exact Scheme.IdealSheafData.ideal_comap_appLE i'.ker g U' U H
  have hr : K.map r.toRingHom = i.ker.ideal U := by
    rw [hi]
    dsimp only [K]
    rw [Ideal.map_map]
    congr 1
    ext a
    change r (1 ⊗ₜ[A] a) = _
    simp only [r, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
    rfl
  let E := cotangentEquiv K (i.ker.ideal U) r hr
  have := RingHomInvPair.of_ringEquiv (RingEquiv.refl B)
  have := RingHomInvPair.of_ringEquiv_symm (RingEquiv.refl B)
  obtain ⟨C, hC⟩ := (affine_conormal_sections i).2 U B (RingEquiv.refl B)
    (i.ker.ideal U) (by simp)
  refine ⟨C.symm.toAddEquiv.trans E.symm.toAddEquiv, ?_⟩
  intro b a s hs
  let x : K := ⟨1 ⊗ₜ[A] (a : A), Ideal.mem_map_of_mem _ a.property⟩
  let y : i.ker.ideal U := ⟨r (x : B ⊗[A] A), by
    rw [← hr]; exact Ideal.mem_map_of_mem _ x.property⟩
  have hy : (y : B) = g.appLE U'.1 U.1 H (a : A) := by
    simp only [y, x, r, Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_one]
    rfl
  have hunit : C ((i.ker.ideal U).toCotangent y) =
      ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
        i.ker.toModules).app U.1 s := hC y s (hs.trans hy.symm)
  change E.symm (C.symm (b •
    (((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
      i.ker.toModules).app U.1 s))) = _
  rw [← hunit, C.symm.map_smulₛₗ, C.symm_apply_apply]
  change E.symm (b • (i.ker.ideal U).toCotangent y) = _
  rw [E.symm.map_smul]
  have hE : E (K.toCotangent x) = (i.ker.ideal U).toCotangent y := rfl
  rw [← hE, E.symm_apply_apply, Ideal.tensorCotangentHom_tmul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On compatible affine ambient charts, the canonical conormal map is conjugate,
as a function on sections, to `Ideal.tensorCotangentHom`. No surjectivity or
injectivity is asserted here.

Source: Stacks Project, Morphisms, Lemma 0473, affine reduction; Schemes,
Lemma 01JU (1), the ideal of a base-changed closed immersion.
(blueprint: lem-weil-pbc-closed-immersion-conormal-affine-base-change-comparison).

Proof: Write A = Γ(X', U') and B = Γ(X, U), and let J be the ideal of i' on U'.
The inverse image of U' under i' is Spec(A/J), by the affine closed-immersion
criterion. Restrict the cartesian square to U and U', using open-preimage
pullbacks and cartesian-square pasting. The quotient base-change calculation
identifies i⁻¹(U) with Spec(B/JB), and its immersion ideal with JB.
The affine conormal sections equivalence identifies the conormal on i'⁻¹(U')
with J/J². The affine pullback sections equivalence identifies the source on
i⁻¹(U) with (B/JB) ⊗[A/J] (J/J²). Since J annihilates J/J², the quotient
scalar tensor equivalence identifies this with B ⊗[A] (J/J²).
The multiplication equivalence B ⊗[A] A ≃ B carries the extended ideal
J.map(includeRight) to JB, and induces an equivalence on the cotangent
quotients. Compose its inverse with the target affine conormal sections
equivalence to obtain the second displayed equivalence.
The canonical-map equation in closedImmersion_conormal_functorial sends the
class of a ∈ J, multiplied by b ∈ B, to the class of b times the image of a.
This agrees with tensorCotangentHom_tmul. These classes generate the source
by the affine pullback sections equivalence; tensor induction proves the
commutation equation for every section. -/
theorem closedImmersion_conormal_affine_base_change_comparison
    {X Z X' Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
    [IsClosedImmersion i] [IsClosedImmersion i']
    (g : X ⟶ X') (f : Z ⟶ Z') (h : i ≫ g = f ≫ i')
    (hc : IsLimit (PullbackCone.mk i f h))
    (c : (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules) ⟶
      (tensorPullback i).obj i.ker.toModules)
    (hcanonical : c = Classical.choose ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2))
    (U : X.affineOpens) (U' : X'.affineOpens) (H : U.1 ≤ g ⁻¹ᵁ U'.1) :
    letI : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
    ∃ (eS : Γ((tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules),
          i ⁻¹ᵁ U.1) ≃
        Γ(X, U.1) ⊗[Γ(X', U'.1)] (i'.ker.ideal U').Cotangent)
      (eT : Γ((tensorPullback i).obj i.ker.toModules, i ⁻¹ᵁ U.1) ≃
        ((i'.ker.ideal U').map (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(X', U'.1) →+* Γ(X, U.1) ⊗[Γ(X', U'.1)] Γ(X', U'.1))).Cotangent),
      ∀ s, eT (c.app (i ⁻¹ᵁ U.1) s) =
        (i'.ker.ideal U').tensorCotangentHom Γ(X', U'.1) Γ(X, U.1) (eS s) := by
  classical
  dsimp only
  let : Algebra Γ(X', U'.1) Γ(X, U.1) := (g.appLE U'.1 U.1 H).hom.toAlgebra
  obtain ⟨eS, hS⟩ :=
    closedImmersion_conormal_affine_source_coordinates i i' g f h hc U U' H
  obtain ⟨eT, hT⟩ := targetCoordinates i i' g f h hc U U' H
  let S := (tensorPullback f).obj ((tensorPullback i').obj i'.ker.toModules)
  let T := (tensorPullback i).obj i.ker.toModules
  let q := pushforwardComp f i' ≪≫ pushforwardCongr h.symm
  let j := ((Classical.choose (exists_tensorPullbackAdjunction i')).unit.app
      i'.ker.toModules) ≫
    (pushforward i').map
      (((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app
        ((tensorPullback i').obj i'.ker.toModules)))
  have hmap :
      j ≫ q.hom.app S ≫ (pushforward (i ≫ g)).map c =
        j ≫ (pushforward i').map ((pushforward f).map c) ≫ q.hom.app T := by
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun k ↦ j ≫ k) (q.hom.naturality c).symm
  have hclasses (s' : Γ(i'.ker.toModules, U'.1)) :
      ∃ s : Γ(i.ker.toModules, U.1),
        i.ker.toModulesι.app U.1 s = g.appLE U'.1 U.1 H
          (i'.ker.toModulesι.app U'.1 s') ∧
        c.app (i ⁻¹ᵁ U.1)
          (S.val.map (homOfLE (i.preimage_mono H)).op
            ((j ≫ q.hom.app S).app U'.1 s')) =
          ((Classical.choose (exists_tensorPullbackAdjunction i)).unit.app
            i.ker.toModules).app U.1 s := by
    have hfun := (Classical.choose_spec ((Classical.choose_spec
      (closedImmersion_conormal_functorial i i' g f h).2).2)).1.2
    rw [← hcanonical] at hfun
    obtain ⟨s, hs, he⟩ := hfun U U' H s'
    refine ⟨s, hs, ?_⟩
    have hn := c.val.naturality (homOfLE (i.preimage_mono H)).op
    have hn' := congrArg (fun k ↦ k ((j ≫ q.hom.app S).app U'.1 s')) hn
    have hv := congrArg (fun k ↦ k.app U'.1 s') hmap
    have hv' : c.app ((i ≫ g) ⁻¹ᵁ U'.1) ((j ≫ q.hom.app S).app U'.1 s') =
        (j ≫ (pushforward i').map ((pushforward f).map c) ≫
          q.hom.app T).app U'.1 s' := hv
    rw [← he]
    calc
      c.app (i ⁻¹ᵁ U.1)
          (S.val.map (homOfLE (i.preimage_mono H)).op
            ((j ≫ q.hom.app S).app U'.1 s')) =
          T.val.map (homOfLE (i.preimage_mono H)).op
            (c.app ((i ≫ g) ⁻¹ᵁ U'.1) ((j ≫ q.hom.app S).app U'.1 s')) := hn'
      _ = _ := by
        rw [hv']
        simp only [j, q, T, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
          Category.assoc]
  refine ⟨eS.toEquiv, eT.toEquiv, ?_⟩
  intro s
  have ht (t : Γ(X, U.1) ⊗[Γ(X', U'.1)] (i'.ker.ideal U').Cotangent) :
      eT (c.app (i ⁻¹ᵁ U.1) (eS.symm t)) =
        (i'.ker.ideal U').tensorCotangentHom Γ(X', U'.1) Γ(X, U.1) t := by
    induction t using TensorProduct.inductionOn with
    | tmul b a =>
      obtain ⟨a, rfl⟩ := (i'.ker.ideal U').toCotangent_surjective a
      have ha : (a : Γ(X', U'.1)) ∈ Set.range (i'.ker.toModulesι.app U'.1) := by
        rw [i'.ker.range_toModulesι_app U']
        exact a.property
      obtain ⟨s', hs'⟩ := ha
      obtain ⟨s, hs, he⟩ := hclasses s'
      rw [hS b a s' hs']
      rw [Hom.app_smul]
      have he' := he
      simp only [S, j, q, Iso.trans_hom, NatTrans.comp_app, Category.assoc] at he'
      rw [he']
      apply hT b a s
      simpa only [hs'] using hs
    | add t t' ht ht' => simp only [map_add, ht, ht']
  change eT (c.app (i ⁻¹ᵁ U.1) s) =
    (i'.ker.ideal U').tensorCotangentHom Γ(X', U'.1) Γ(X, U.1) (eS s)
  simpa only [AddEquiv.symm_apply_apply] using ht (eS s)

end AlgebraicGeometry.Scheme.Modules
