/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearVectorBundleAffineCoordinates
import WeilConjectures.RingTheory.FrobeniusPolynomialEtale
import WeilConjectures.RingTheory.FrobeniusPolynomialSurjective

/-!
# Local surjectivity of a Frobenius-linear difference

Source: Stacks Project, `more-etale.tex`, Tag 0GKU, lines 4213--4270
(blueprint: lem-fd-frobenius-linear-vector-bundle-locally-surjective).

This is the local lifting step of the Frobenius-linear vector-bundle theorem. Its
proof is the local Artin--Schreier lifting argument on finite locally free charts,
expressed by the covering image sieves on the small étale site.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry
namespace Scheme
open Modules

attribute [local irreducible] Modules.tensorPullback Modules.tensorPullbackObj
attribute [local instance 2000]
  Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf

private theorem eval_sub_id {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    (G : Sheaf J AddCommGrpCat.{u}) (f : G ⟶ G) (U : Cᵒᵖ) (m : G.obj.obj U) :
    (f - 𝟙 G).hom.app U m = f.hom.app U m - m := rfl

private theorem exists_affine_polynomial_cover
    (p : ℕ) [Fact p.Prime] (V : Scheme.{u}) [IsAffine V] [CharP Γ(V, ⊤) p]
    (n : ℕ) (a : Fin n → Fin n → Γ(V, ⊤)) (bv : Fin n → Γ(V, ⊤)) (v : V) :
    ∃ (W : V.Etale) (w : W.left) (z : Fin n → Γ(W.left, ⊤)),
      W.hom w = v ∧
      let c : Γ(V, ⊤) →+* Γ(W.left, ⊤) := W.hom.appTop.hom
      ∀ i, c (bv i) + z i - ∑ k, c (a i k) * (z k) ^ p = 0 := by
  classical
  let R := Γ(V, ⊤)
  let r : Fin n → MvPolynomial (Fin n) R := fun i ↦
    MvPolynomial.C (bv i) + MvPolynomial.X i -
      ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j ^ p
  let I := Ideal.span (Set.range r)
  let Q := MvPolynomial (Fin n) R ⧸ I
  let φ : R ⟶ CommRingCat.of Q :=
    CommRingCat.ofHom (algebraMap R Q)
  let j₀ : Spec (.of Q) ⟶ Spec R := Spec.map φ
  have hj₀ : Etale j₀ := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact (RingHom.etale_algebraMap).mpr (Algebra.frobenius_polynomial_etale R p n a bv)
  let : Etale j₀ := hj₀
  let j : Spec (.of Q) ⟶ V := j₀ ≫ V.isoSpec.inv
  have : Surjective j₀ := ⟨Algebra.frobenius_polynomial_surjective R p n a bv⟩
  have : Etale j := inferInstance
  have : Surjective j := inferInstance
  obtain ⟨w, hw⟩ := j.surjective v
  let W : V.Etale := Scheme.Etale.mk j
  let q : Q →+* Γ(W.left, ⊤) := (Scheme.ΓSpecIso (.of Q)).inv.hom
  let z : Fin n → Γ(W.left, ⊤) := fun i ↦ q (Ideal.Quotient.mk I (MvPolynomial.X i))
  have heq : V.isoSpec.inv.appTop = (Scheme.ΓSpecIso R).inv := by
    apply (cancel_mono V.isoSpec.hom.appTop).mp
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
    simp only [Scheme.Hom.id_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    change 𝟙 R = (Scheme.ΓSpecIso R).inv ≫ (Scheme.ΓSpecIso R).hom
    exact (Scheme.ΓSpecIso R).inv_hom_id.symm
  have hjapp : W.hom.appTop = φ ≫ (Scheme.ΓSpecIso (.of Q)).inv := by
    change (j₀ ≫ V.isoSpec.inv).appTop = _
    rw [Scheme.Hom.comp_appTop, heq]
    exact (Scheme.ΓSpecIso_inv_naturality φ).symm
  let c : R →+* Γ(W.left, ⊤) := W.hom.appTop.hom
  have hC (r : R) : q (Ideal.Quotient.mk I (MvPolynomial.C r)) = c r := by
    change q (Ideal.Quotient.mk I (MvPolynomial.C r)) = W.hom.appTop r
    rw [hjapp]
    rfl
  refine ⟨W, w, z, hw, ?_⟩
  change ∀ i, c (bv i) + z i - ∑ k, c (a i k) * (z k) ^ p = 0
  intro i
  have hz :
      c (bv i) + z i -
        ∑ k, c (a i k) * (z k) ^ p = 0 := by
    have hr : Ideal.Quotient.mk I (r i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
    have hq := congrArg q hr
    simp only [r, map_sub, map_add, map_sum, map_mul, map_pow, map_zero] at hq
    change q (Ideal.Quotient.mk I (MvPolynomial.C (bv i))) + z i -
      ∑ k, q (Ideal.Quotient.mk I (MvPolynomial.C (a i k))) * (z k) ^ p = 0 at hq
    rw [hC (bv i)] at hq
    have hsum :
        (∑ k, q (Ideal.Quotient.mk I (MvPolynomial.C (a i k))) * (z k) ^ p) =
        ∑ k, c (a i k) * (z k) ^ p := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun c ↦ c * (z k) ^ p) (hC (a i k))
    rw [hsum] at hq
    exact hq
  exact hz

-- Checking the scalar-action coercions needs a larger kernel budget.
private theorem exists_frobenius_linear_local_lift
    (p : ℕ) [Fact p.Prime]
    (S : Scheme.{u}) [S.Over (Spec (.of (ULift.{u} (ZMod p))))]
    (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteLocallyFree]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e)) (U : S.Etale)
    (b : Γ((Modules.tensorPullback U.hom).obj E, ⊤)) (x : U.left) :
    ∃ (W : S.Etale) (f : W ⟶ U) (w : W.left)
      (t : Γ((Modules.tensorPullback W.hom).obj E, ⊤)),
      f.left w = x ∧ (F - 𝟙 _).hom.app (op W) t =
        (Modules.etaleTensorSectionsSheaf E).obj.map f.op b := by
  classical
  obtain ⟨V, g, v, hv, hV, hc, n, e, a, henat, heF⟩ :=
    exists_frobenius_linear_vector_bundle_affine_coordinates p S E F hF U x
  let : IsAffine V.left := hV
  let : CharP Γ(V.left, ⊤) p := hc
  let bV := (Modules.etaleTensorSectionsSheaf E).obj.map g.op b
  let bv := e V (𝟙 V) bV
  obtain ⟨W', w, z, hw, hz⟩ := exists_affine_polynomial_cover p V.left n a bv v
  let W : S.Etale := Scheme.Etale.mk (W'.hom ≫ V.hom)
  let h : W ⟶ V := MorphismProperty.Over.homMk W'.hom rfl
  let t := (e W h).symm z
  have ht : (F - 𝟙 _).hom.app (op W) t =
      (Modules.etaleTensorSectionsSheaf E).obj.map h.op bV := by
    apply (e W h).injective
    let FW : Γ((tensorPullback W.hom).obj E, ⊤) →+
        Γ((tensorPullback W.hom).obj E, ⊤) := (F.hom.app (op W)).hom
    have hdiff : (F - 𝟙 _).hom.app (op W) t = FW t - t :=
      eval_sub_id S.smallEtaleTopology _ F (op W) t
    rw [hdiff]
    change e W h (FW t - t) = _
    funext i
    simp only [map_sub, Pi.sub_apply]
    change e W h (F.hom.app (op W) t) i - e W h t i = _
    rw [heF W h t i, show e W h t = z from (e W h).apply_symm_apply z,
      henat W h bV i]
    exact sub_eq_iff_eq_add.mpr (sub_eq_zero.mp (hz i)).symm
  refine ⟨W, h ≫ g, w, t, ?_, ?_⟩
  · change g.left (W'.hom w) = x
    rw [hw, hv]
  · simpa only [op_comp, Functor.map_comp, AddCommGrpCat.comp_apply, bV] using ht

private theorem locally_surjective_of_pointwise_lifts
    (S : Scheme.{u}) (G H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (f : G ⟶ H)
    (hf : ∀ (U : S.Etale) (b : H.obj.obj (op U)) (x : U.left),
      ∃ (W : S.Etale) (g : W ⟶ U) (w : W.left) (t : G.obj.obj (op W)),
        g.left w = x ∧ f.hom.app (op W) t = H.obj.map g.op b) :
    Sheaf.IsLocallySurjective f := by
  classical
  constructor
  intro U b
  choose W g w t hw ht using hf U b
  have hcover : Sieve.ofArrows W g ∈ S.smallEtaleTopology U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨x, ⟨w x, hw x⟩⟩
  apply S.smallEtaleTopology.superset_covering _ hcover
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  exact ⟨t x, ht x⟩

/-- The map `F - 1` admits local lifts on the small étale site.

Source: Stacks Project, `more-etale.tex`, Tag 0GKU, lemma-frobenius-linear-on-vb,
proof steps 1--4 and the local-lifting assertion of step 5
(blueprint: lem-fd-frobenius-linear-vector-bundle-locally-surjective).

Proof: trivialize the finite locally free module on affine opens.  The equations
`F(x)-x=b` are represented by the polynomial schemes whose Jacobian is the identity.
Lang--Steinberg gives a geometric point above every point of the base, so these
étale covers are surjective.  They therefore provide local lifts of every section,
so the image sieve of every section is covering. This is local surjectivity of
`F - 1`. The argument includes rank zero and empty
objects, since the empty Jacobian and the zero sheaf satisfy the same statements.
-/
theorem frobenius_linear_vector_bundle_locally_surjective
    (p : ℕ) [Fact p.Prime]
    (S : Scheme.{u}) [S.Over (Spec (.of (ULift.{u} (ZMod p))))]
    (E : S.Modules) [E.IsQuasicoherent] [E.IsFiniteLocallyFree]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e)) :
    Sheaf.IsLocallySurjective (F - 𝟙 _) := by
  apply locally_surjective_of_pointwise_lifts S _ _ (F - 𝟙 _)
  intro U b x
  exact exists_frobenius_linear_local_lift p S E F hF U b x

end Scheme
end AlgebraicGeometry
