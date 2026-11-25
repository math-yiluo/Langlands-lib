/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Points of the spectrum of a polynomial quotient over an affine base

Let `S` be an affine scheme with global sections `R` and let `A = R[X_i] / (f_k)`.
For an étale `S`-scheme `U`, morphisms of étale `S`-schemes from `U` to `Spec A`
correspond to solutions `x : ι → Γ(U, ⊤)` of the equations `f_k(x) = 0`, where the
coefficients are mapped into `Γ(U, ⊤)` by the structure morphism. The bijection is
natural in `U`.

Source: Stacks Project, Tag 0GKU, proof of lemma-frobenius-linear-on-vb
(the global-sections/affine-spectrum adjunction and the quotient universal property).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} [IsAffine S] {ι κ : Type} (f : κ → MvPolynomial ι Γ(S, ⊤))

/-- Morphisms of étale `S`-schemes `U ⟶ V` are morphisms of the underlying schemes over `S`. -/
@[simps]
noncomputable def etaleHomEquivSubtype (U V : S.Etale) :
    (U ⟶ V) ≃ {t : U.left ⟶ V.left // t ≫ V.hom = U.hom} where
  toFun g := ⟨g.left, MorphismProperty.Over.w g⟩
  invFun t := MorphismProperty.Over.homMk t.1 t.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The `Γ`-`Spec` adjunction: morphisms `X ⟶ Spec B` are ring maps `B ⟶ Γ(X, ⊤)`. -/
@[simps]
noncomputable def homSpecEquivAppTop (X : Scheme.{u}) (B : CommRingCat.{u}) :
    (X ⟶ Spec B) ≃ (B ⟶ Γ(X, ⊤)) where
  toFun t := (Scheme.ΓSpecIso B).inv ≫ t.appTop
  invFun φ := X.toSpecΓ ≫ Spec.map φ
  left_inv t := ext_of_isAffine (by
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality,
      Iso.hom_inv_id_assoc])
  right_inv φ := by simp

/-- A morphism `t : X ⟶ Spec A` lies over `S` (via `Spec A ⟶ Spec Γ(S, ⊤) ≅ S` and a given
`c : X ⟶ S`) iff the corresponding ring map is compatible with `Γ(c)`. -/
lemma comp_spec_map_isoSpec_inv_eq_iff {X : Scheme.{u}} {A : CommRingCat.{u}}
    (t : X ⟶ Spec A) (α : Γ(S, ⊤) ⟶ A) (c : X ⟶ S) :
    t ≫ Spec.map α ≫ S.isoSpec.inv = c ↔ α ≫ homSpecEquivAppTop X A t = c.appTop := by
  rw [← Category.assoc, Iso.comp_inv_eq,
    ← (homSpecEquivAppTop X Γ(S, ⊤)).apply_eq_iff_eq (x := t ≫ Spec.map α),
    homSpecEquivAppTop_apply, homSpecEquivAppTop_apply, homSpecEquivAppTop_apply,
    Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
    Iso.inv_hom_id_assoc]

/-- A ring map out of a quotient of a polynomial ring is evaluation at the images of the
variables, with coefficients mapped along the induced map on coefficients. -/
lemma hom_comp_mk_eq_eval₂Hom {R : CommRingCat.{u}} {I : Ideal (MvPolynomial ι R)}
    {T : CommRingCat.{u}} (φ : CommRingCat.of (MvPolynomial ι R ⧸ I) ⟶ T) :
    φ.hom.comp (Ideal.Quotient.mk I) = MvPolynomial.eval₂Hom
      (CommRingCat.ofHom (algebraMap R _) ≫ φ).hom
      (fun i ↦ φ (Ideal.Quotient.mk I (MvPolynomial.X i))) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · rw [RingHom.comp_apply, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
    simp
  · simp

/-- Ring maps out of `Γ(S, ⊤)[X_i] / (f_k)` extending a given `c : Γ(S, ⊤) ⟶ T` are the
solutions in `T` of the equations `f_k = 0`. -/
noncomputable def mvPolynomialQuotientHomEquiv (T : CommRingCat.{u}) (c : Γ(S, ⊤) ⟶ T) :
    {φ : CommRingCat.of (MvPolynomial ι Γ(S, ⊤) ⧸ Ideal.span (Set.range f)) ⟶ T //
        CommRingCat.ofHom (algebraMap Γ(S, ⊤) _) ≫ φ = c} ≃
      {x : ι → T // ∀ k, MvPolynomial.eval₂ c.hom x (f k) = 0} where
  toFun φ := ⟨fun i ↦ φ.1 (Ideal.Quotient.mk _ (MvPolynomial.X i)), fun k ↦ by
    obtain ⟨φ, rfl⟩ := φ
    rw [← MvPolynomial.coe_eval₂Hom, ← hom_comp_mk_eq_eval₂Hom, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self k)), map_zero]⟩
  invFun x := ⟨CommRingCat.ofHom (Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom c.hom x.1)
    fun a ha ↦ RingHom.mem_ker.1 ((Ideal.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact x.2 k)) ha)), by
    ext r
    exact MvPolynomial.eval₂_C _ _ _⟩
  left_inv φ := by
    obtain ⟨φ, rfl⟩ := φ
    refine Subtype.ext (CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext ?_))
    rw [hom_comp_mk_eq_eval₂Hom φ]
    exact Ideal.Quotient.lift_comp_mk _ _ _
  right_inv x := by
    refine Subtype.ext (funext fun i ↦ ?_)
    simp

/-- The structure morphism `Spec (Γ(S, ⊤)[X_i] / (f_k)) ⟶ S` of an affine scheme `S`. -/
noncomputable def specQuotientStructureMap :
    Spec (.of (MvPolynomial ι Γ(S, ⊤) ⧸ Ideal.span (Set.range f))) ⟶ S :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) _)) ≫ S.isoSpec.inv

/-- Morphisms of étale `S`-schemes from `U` to `Spec (Γ(S, ⊤)[X_i] / (f_k))` are the
solutions in `Γ(U, ⊤)` of the equations `f_k = 0`, with coefficients mapped along the
structure morphism of `U`. -/
noncomputable def etaleHomSpecQuotientEquiv [Etale (specQuotientStructureMap f)]
    (U : S.Etale) :
    (U ⟶ Etale.mk (specQuotientStructureMap f)) ≃
      {x : ι → Γ(U.left, ⊤) // ∀ k, MvPolynomial.eval₂ U.hom.appTop.hom x (f k) = 0} :=
  ((etaleHomEquivSubtype U _).trans ((homSpecEquivAppTop U.left _).subtypeEquiv fun t ↦
    comp_spec_map_isoSpec_inv_eq_iff (S := S) t _ U.hom)).trans
      (mvPolynomialQuotientHomEquiv f _ U.hom.appTop)

/-- The coordinates of the solution attached to `t` are the global sections `t^*(X_i)`. -/
lemma etaleHomSpecQuotientEquiv_apply_coe [Etale (specQuotientStructureMap f)] (U : S.Etale)
    (t : U ⟶ Etale.mk (specQuotientStructureMap f)) (i : ι) :
    (etaleHomSpecQuotientEquiv f U t).1 i = t.left.appTop ((Scheme.ΓSpecIso _).inv
      (Ideal.Quotient.mk (Ideal.span (Set.range f)) (MvPolynomial.X i))) :=
  rfl

/-- The solution attached to a composite `g ≫ t` is the restriction along `g` of the
solution attached to `t`. -/
theorem etaleHomSpecQuotientEquiv_comp [Etale (specQuotientStructureMap f)]
    {U W : S.Etale} (g : W ⟶ U) (t : U ⟶ Etale.mk (specQuotientStructureMap f)) (i : ι) :
    (etaleHomSpecQuotientEquiv f W (g ≫ t)).1 i =
      g.left.appTop ((etaleHomSpecQuotientEquiv f U t).1 i) := by
  rw [etaleHomSpecQuotientEquiv_apply_coe, etaleHomSpecQuotientEquiv_apply_coe]
  rfl

end AlgebraicGeometry.Scheme
