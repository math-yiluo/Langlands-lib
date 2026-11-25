/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.AlgebraicGeometry.AffineSpace.PolynomialFamilyRealization
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Polynomial deformation of an affine-space automorphism to a linear map

The family below involves only schemes and polynomial coordinates. It contains no
cohomology, trace, coefficient ring, or choice of orientation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

private lemma towerIso_over (S : Scheme.{u}) (d : ℕ) :
    (affineTraceAffineSpaceIso S d).hom ≫ AffineSpace (ULift.{u} (Fin d)) S ↘ S =
      affineTraceProjection S d := AffineSpace.homOfVector_over _ _

private lemma towerIso_inv_over (S : Scheme.{u}) (d : ℕ) :
    (affineTraceAffineSpaceIso S d).inv ≫ affineTraceProjection S d =
      AffineSpace (ULift.{u} (Fin d)) S ↘ S := by
  rw [← towerIso_over, Iso.inv_hom_id_assoc]

private lemma towerIso_coordinate (S : Scheme.{u}) (d : ℕ) (i : Fin d) :
    (affineTraceAffineSpaceIso S d).hom.appTop (AffineSpace.coord S (ULift.up i)) =
      affineTraceCoordinate S d i := AffineSpace.homOfVector_appTop_coord _ _ _

private lemma towerMap_coordinate {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ)
    (j : Fin d) :
    (affineTraceMap f d).appTop (affineTraceCoordinate S d j) =
      affineTraceCoordinate S' d j := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · simpa only [affineTraceCoordinate, Fin.lastCases_last, affineTraceMap] using!
        (AffineSpace.map_appTop_coord (affineTraceMap f d) PUnit.unit)
    · simp only [affineTraceCoordinate, Fin.lastCases_castSucc]
      change (affineTraceMap f (d + 1)).appTop
        ((AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘
          affineTraceTower S d).appTop (affineTraceCoordinate S d i)) = _
      erw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
      change ((AffineSpace.map PUnit.{u + 1} (affineTraceMap f d)) ≫
        AffineSpace PUnit.{u + 1} (affineTraceTower S d) ↘ affineTraceTower S d).appTop _ = _
      rw [AffineSpace.map_over, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ih]

private lemma towerIso_naturality {S' S : Scheme.{u}} (f : S' ⟶ S) (d : ℕ) :
    affineTraceMap f d ≫ (affineTraceAffineSpaceIso S d).hom =
      (affineTraceAffineSpaceIso S' d).hom ≫ AffineSpace.map (ULift.{u} (Fin d)) f := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, towerIso_over, (affineTraceMap_isPullback f d).w,
      Category.assoc, AffineSpace.map_over, ← Category.assoc, towerIso_over]
  · rintro ⟨i⟩
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      towerIso_coordinate, AffineSpace.map_appTop_coord, towerMap_coordinate]

private lemma towerLinear_compat (S : Scheme.{u}) (d : ℕ)
    (g : Matrix.GeneralLinearGroup (ULift.{u} (Fin d)) Γ(S, ⊤)) :
    affineTraceLinearMap S d
        (Units.map (Matrix.reindexRingEquiv Γ(S, ⊤) Equiv.ulift).toMonoidHom g) ≫
      (affineTraceAffineSpaceIso S d).hom =
    (affineTraceAffineSpaceIso S d).hom ≫
      AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
        (fun i ↦ ∑ j : ULift.{u} (Fin d),
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S).appTop (g i j) *
            AffineSpace.coord S j) := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, towerIso_over, affineTraceLinearMap_over, Category.assoc,
      AffineSpace.homOfVector_over, towerIso_over]
  · rintro ⟨i⟩
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, towerIso_coordinate,
      affineTraceLinearMap_coordinate, AffineSpace.homOfVector_appTop_coord,
      map_sum, map_mul]
    have h (r : Γ(S, ⊤)) : (affineTraceAffineSpaceIso S d).hom.appTop
        ((AffineSpace (ULift.{u} (Fin d)) S ↘ S).appTop r) =
          (affineTraceProjection S d).appTop r := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, towerIso_over]
    simp only [h]
    exact (Fintype.sum_equiv Equiv.ulift _ _ (fun ⟨j⟩ ↦ by
      rw [towerIso_coordinate]
      rfl)).symm

/-- Any polynomial automorphism is joined to its linear part by an affine-line family
of polynomial automorphisms. The endpoints and the projection are the actual tower maps.

Source: Furter--Poloni, "On the maximality of the triangular subgroup", Lemma 3.1,
proof, pp. 5--6 (translation followed by rescaling);
https://www.math.u-bordeaux.fr/~jpfurter/onTheMaximalityOfTheTriangularSubgroup.pdf .
For the same rescaling over arbitrary algebraically closed fields, see Blanc,
"Conjugacy classes of special automorphisms of the affine spaces", introduction,
pp. 939--940, https://msp.org/ant/2016/10-5/ant-v10-n5-p01-p.pdf .
The combined family and the characteristic-independent coordinate verification below
are written by agent M2 for the geometric presentation calculation in blueprint
sec-smooth-purity/sk-prop-an/cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-affine-space-polynomial-deformation).

Proof: in polynomial coordinates write F for e and b=F(0). Over k[t] set
H(t,x)=(F(tx)-b)/t+t*b. This is polynomial: every monomial of F-b has positive
x-degree, so its substituted monomial is divisible by t. Its inverse is
J(t,y)=F^{-1}(t*y+(1-t^2)*b)/t. The numerator vanishes at t=0 because F^{-1}(b)=0,
so J is polynomial as well. After inverting t the two substitution composites are
identity. The polynomial ring over the field injects into its localization at t;
therefore both composites are already identity over k[t]. At t=1, H is F. At t=0,
H is the degree-one part of F-b, i.e. its Jacobian at zero. Specializing J at zero
provides its inverse linear map (the derivative of F^{-1} at b). Their matrices
are inverse, giving g in GL_d(k). Transport these polynomial maps through the
coordinate-tower affine-space isomorphisms. The coordinate equations give both
endpoint squares and the equation over the parameter line. For d=0 the tower is
the base and use the identity family and the unique empty invertible matrix.
Algebraic closure is unnecessary; the argument works in every characteristic.
-/
theorem affineSpace_polynomial_deformation
    (k : Type u) [Field k] (d : ℕ)
    (e : affineTraceTower (Spec (.of k)) d ≅ affineTraceTower (Spec (.of k)) d)
    (he : e.hom ≫ affineTraceProjection (Spec (.of k)) d =
      affineTraceProjection (Spec (.of k)) d) :
    ∃ (g : Matrix.GeneralLinearGroup (Fin d) Γ(Spec (.of k), ⊤))
      (E : affineTraceTower (AffineSpace PUnit.{u + 1} (Spec (.of k))) d ≅
        affineTraceTower (AffineSpace PUnit.{u + 1} (Spec (.of k))) d),
      E.hom ≫ affineTraceProjection (AffineSpace PUnit.{u + 1} (Spec (.of k))) d =
        affineTraceProjection (AffineSpace PUnit.{u + 1} (Spec (.of k))) d ∧
      affineTraceMap (AffineSpace.zeroSection PUnit.{u + 1} (Spec (.of k))) d ≫ E.hom =
        affineTraceLinearMap (Spec (.of k)) d g ≫
          affineTraceMap (AffineSpace.zeroSection PUnit.{u + 1} (Spec (.of k))) d ∧
      affineTraceMap (AffineSpace.oneSection PUnit.{u + 1} (Spec (.of k))) d ≫ E.hom =
        e.hom ≫ affineTraceMap
          (AffineSpace.oneSection PUnit.{u + 1} (Spec (.of k))) d := by
  classical
  let S : Scheme.{u} := Spec (.of k)
  let σ := ULift.{u} (Fin d)
  let a := affineTraceAffineSpaceIso S d
  let T := AffineSpace PUnit.{u + 1} S
  let b := affineTraceAffineSpaceIso T d
  let e' := a.symm ≪≫ e ≪≫ a
  have he' : e'.hom ≫ AffineSpace σ S ↘ S = AffineSpace σ S ↘ S := by
    dsimp only [e', Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, towerIso_over, he, towerIso_inv_over]
  have : IsAffine S := inferInstanceAs (IsAffine (Spec (.of k)))
  obtain ⟨g, E, hE, h0, h1⟩ := AffineSpace.polynomial_deformation σ S e' he'
  let g' : Matrix.GeneralLinearGroup (Fin d) Γ(S, ⊤) :=
    Units.map (Matrix.reindexRingEquiv Γ(S, ⊤) Equiv.ulift).toMonoidHom g
  refine ⟨g', b ≪≫ E ≪≫ b.symm, ?_, ?_, ?_⟩
  · dsimp only [Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Category.assoc, towerIso_inv_over, hE, towerIso_over]
  · apply (cancel_mono b.hom).mp
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, towerIso_naturality, Category.assoc, h0,
      ← Category.assoc, ← towerLinear_compat]
    rw [Category.assoc, ← towerIso_naturality]
  · apply (cancel_mono b.hom).mp
    dsimp only [Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, towerIso_naturality, Category.assoc, h1]
    dsimp only [e', Iso.trans_hom, Iso.symm_hom]
    dsimp only [a, S]
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [Category.assoc, ← towerIso_naturality]

end AlgebraicGeometry
