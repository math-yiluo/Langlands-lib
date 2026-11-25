/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSpecQuotientSolutions
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.EtaleUpperStarRepresentableFiniteLocallyConstant
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearFreeKernelCoordinates
import WeilConjectures.RingTheory.FrobeniusPolynomialEtale

/-!
# Frobenius-linear fixed points in an affine free frame

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb.
(blueprint: lem-fd-frobenius-linear-free-kernel-stratification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Fixed points in an affine finite free frame admit a finite constructible stratification.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb,
polynomial fixed-point representation and application of Tag 03S0.
(blueprint: lem-fd-frobenius-linear-free-kernel-stratification).

Proof: the supplied frame and its dual give coordinates on every étale test object.
Naturality of the tensor/abstract pullback comparison makes these coordinates commute
with all restrictions. Let a_ij be the coordinates of F on the frame. Semilinearity
makes the fixed-point equations x_i - sum_j a_ij x_j^p = 0. The global-sections/affine-spectrum
adjunction and the quotient universal property
identify maps from a test object to the affine solution scheme over the base with
solution vectors, naturally in the test object. Evaluation of the categorical abelian kernel gives
the fixed-point subgroup,
so this natural bijection identifies the underlying lifted kernel with the solution
representable. The proved Frobenius polynomial Jacobian theorem, with b=0, makes the
solution scheme étale over the affine base. It is affine and of finite presentation,
so both schemes are qcqs. The étale stratified-finiteness theorem supplies a finite
constructible immersed partition on which the solution scheme is finite étale.
Representables commute with inverse image. Finite étale representables are finite
locally constant, and forgetting abelian groups commutes with inverse image. Transport
these properties across the kernel comparison to obtain each asserted stratum.
Rank zero is the identity solution scheme; the empty affine base is vacuous.
-/
theorem frobenius_linear_free_kernel_stratification
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [IsAffine S] [CharP Γ(S, ⊤) p]
    (E : S.Modules) [E.IsQuasicoherent]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e))
    (n : ℕ) (α : E ≅
      SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) :
    ∃ T : Stratification S, ∀ k : Fin T.n,
      IsFiniteLocallyConstantSheafOfTypes
        ((sheafCompose (T.domain k).smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (T.immersion k)).obj
            ((sheafCompose S.smallEtaleTopology
              AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (kernel (F - 𝟙 _))))) := by
  classical
  obtain ⟨a, c, hc⟩ := exists_frobenius_linear_free_kernel_coordinates p S E F hF n α
  let f : Fin n → MvPolynomial (Fin n) Γ(S, ⊤) :=
    fun i ↦ MvPolynomial.X i - ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j ^ p
  have hA : Algebra.Etale Γ(S, ⊤)
      (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span (Set.range f)) := by
    have hf : f = fun i ↦ MvPolynomial.C 0 + MvPolynomial.X i -
        ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j ^ p := by
      funext i
      rw [map_zero, zero_add]
    rw [hf]
    exact Algebra.frobenius_polynomial_etale Γ(S, ⊤) p n a 0
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤)
      (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span (Set.range f))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr hA
  have : Etale (specQuotientStructureMap f) := by
    unfold specQuotientStructureMap
    infer_instance
  let P : S.Etale := Etale.mk (specQuotientStructureMap f)
  let K := kernel (F - 𝟙 _)
  let eqv (U : S.Etale) : K.obj.obj (op U) ≃ (U ⟶ P) :=
    (c U).trans ((Equiv.subtypeEquivRight fun x ↦ by simp [f, sub_eq_zero]).trans
      (etaleHomSpecQuotientEquiv f U).symm)
  have heqv (U W : S.Etale) (g : W ⟶ U) (s : K.obj.obj (op U)) :
      eqv W (K.obj.map g.op s) = g ≫ eqv U s := by
    apply (etaleHomSpecQuotientEquiv f W).injective
    ext i
    rw [etaleHomSpecQuotientEquiv_comp]
    simp only [eqv, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hc U W g s i
  let e : (sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
      ((sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj K) ≅
      S.smallEtaleTopology.uliftYoneda.{u + 1}.obj P :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
      (fun U ↦ (Equiv.ulift.trans ((eqv U.unop).trans Equiv.ulift.symm)).toIso) (by
        intro U W g
        ext s
        exact congrArg ULift.up (heqv U.unop W.unop g.unop s.down)))
  obtain ⟨T, -, hT⟩ := exists_etale_stratified_finite (specQuotientStructureMap f)
  refine ⟨T, fun k ↦ ?_⟩
  have : IsFinite (pullback.snd P.hom (T.immersion k)) := (hT k).1
  exact isFiniteLocallyConstant_forget_upperStar_of_iso_uliftYoneda (T.immersion k) _ P e

end AlgebraicGeometry.Scheme
