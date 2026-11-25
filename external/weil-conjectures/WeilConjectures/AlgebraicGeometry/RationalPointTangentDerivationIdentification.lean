/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeTangentSpace
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.AlgebraicGeometry.RationalTangentCoefficientLinearMap
import WeilConjectures.AlgebraicGeometry.RationalCotangentFunctionalRealization

/-!
# Rational tangent vectors and cotangent functionals

Source: Stacks Project, Tags 0B2D and 0B2E, with base `Spec k`
(blueprint: lem-sc-rational-point-tangent-derivation-identification).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- At a rational point, extraction of the epsilon coefficient of the stalk homomorphism
identifies tangent vectors with the dual of the cotangent space. The map `r` is the structural
map from `k` to the residue field; its bijectivity expresses rationality. Scalar structures
are restricted along `r`. The displayed dual-number formula uses residue-field coordinates,
so that the coefficient `D a : k` appears as `r (D a)`.
Source: Stacks Project, Tags 0B2D and 0B2E
(blueprint: lem-sc-rational-point-tangent-derivation-identification).

Proof:
1. The closed-point condition implies that the stalk homomorphism reduces to the residue
   map, using the Spec-local-ring correspondence to reconstruct the spectrum morphism and
   cancel the monomorphism from the local spectrum to `X`
   (lem-weil-pbc-morphism-from-spec-local-ring).
   Unique dual-number coordinates give `D`; additivity and multiplication give additivity
   and the residue-valued Leibniz identity. The base-morphism condition makes `D` vanish on k.
2. The Leibniz identity makes `D` vanish on products of maximal-ideal elements, hence on
   their square ideal. It descends to the quotient, additively and k-linearly.
3. A functional on the cotangent space recovers `D a` by applying it to the class of
   `a` minus its structural-field residue. Expanding products proves the Leibniz identity,
   giving a local k-algebra map into dual numbers. The Spec-local-ring correspondence
   recovers a unique tangent vector. Scaling epsilon scales coefficients, and the pushout
   addition of def-sc-scheme-tangent-space adds them. Thus this bijection is k-linear. -/
theorem exists_rationalPoint_tangent_cotangent_linearEquiv
    (k : Type u) [Field k] (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (x : X) :
    let R := X.presheaf.stalk x
    let K := X.residueField x
    let r : k →+* K :=
      (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
    Function.Bijective r →
    letI : Module k (schemeTangentSpace k X p x) :=
      Module.compHom (schemeTangentSpace k X p x) r
    letI : Module K (IsLocalRing.CotangentSpace R) :=
      inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
    letI : Module k (IsLocalRing.CotangentSpace R) :=
      Module.compHom (IsLocalRing.CotangentSpace R) r
    ∃ e : schemeTangentSpace k X p x ≃ₗ[k] (IsLocalRing.CotangentSpace R →ₗ[k] k),
      ∀ θ : schemeTangentSpace k X p x,
        ∃ hx : θ.val (IsLocalRing.closedPoint (DualNumber K)) = x,
          let sharp : R →+* DualNumber K :=
            (eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
              Scheme.stalkClosedPointTo θ.val).hom
          ∃! D : R → k,
            (∀ a : R, sharp a =
              TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r (D a))) ∧
            (∀ a : IsLocalRing.maximalIdeal R,
              e θ ((IsLocalRing.maximalIdeal R).toCotangent a) = D a) := by
  dsimp only
  intro hr
  let R := X.presheaf.stalk x
  let K := X.residueField x
  let s : k →+* R := (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x).hom
  let r : k →+* K :=
    (StructureSheaf.toStalk k (p x) ≫ p.stalkMap x ≫ X.residue x).hom
  let : Module k (schemeTangentSpace k X p x) :=
    Module.compHom (schemeTangentSpace k X p x) r
  let : Module K (IsLocalRing.CotangentSpace R) :=
    inferInstanceAs (Module (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))
  let : Module k (IsLocalRing.CotangentSpace R) :=
    Module.compHom (IsLocalRing.CotangentSpace R) r
  obtain ⟨L, hL⟩ := exists_rationalTangent_coefficient_linearMap k X p x hr
  have hinj : Function.Injective L := by
    intro θ η hθη
    obtain ⟨hx, D, hD, hDm, hDk⟩ := hL θ
    obtain ⟨hy, E, hE, hEm, hEk⟩ := hL η
    have hcoeff (a : R) : D a = E a := by
      obtain ⟨c, hc⟩ := hr.2 ((X.residue x).hom a)
      have hb : a - s c ∈ IsLocalRing.maximalIdeal R := by
        apply (IsLocalRing.residue_eq_zero_iff _).mp
        change (X.residue x).hom (a - s c) = 0
        rw [map_sub]
        change (X.residue x).hom a - r c = 0
        rw [hc, sub_self]
      have hm := congrArg (fun ℓ ↦ ℓ ((IsLocalRing.maximalIdeal R).toCotangent
        ⟨a - s c, hb⟩)) hθη
      rw [hDm, hEm] at hm
      have hd : D (s c) = 0 := hDk c
      have he : E (s c) = 0 := hEk c
      simpa only [map_sub, hd, he, sub_zero] using hm
    have hsharp :
        eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
            Scheme.stalkClosedPointTo θ.val =
          eqToHom (congrArg (fun y : X ↦ X.presheaf.stalk y) hy.symm) ≫
            Scheme.stalkClosedPointTo η.val := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (hD a).trans ((congrArg
        (fun d ↦ TrivSqZeroExt.inl ((X.residue x).hom a) + TrivSqZeroExt.inr (r d))
        (hcoeff a)).trans (hE a).symm)
    apply Subtype.ext
    have hθ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk θ.val
    have hη := Scheme.Spec_stalkClosedPointTo_fromSpecStalk η.val
    have hθ' : Spec.map (eqToHom
        (congrArg (fun y : X ↦ X.presheaf.stalk y) hx.symm) ≫
        Scheme.stalkClosedPointTo θ.val) ≫ X.fromSpecStalk x = θ.val := by
      have H (y : X) (h : θ.val (IsLocalRing.closedPoint (DualNumber K)) = y) :
          Spec.map (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) h.symm) ≫
            Scheme.stalkClosedPointTo θ.val) ≫ X.fromSpecStalk y = θ.val := by
        subst y
        simpa using hθ
      exact H x hx
    have hη' : Spec.map (eqToHom
        (congrArg (fun y : X ↦ X.presheaf.stalk y) hy.symm) ≫
        Scheme.stalkClosedPointTo η.val) ≫ X.fromSpecStalk x = η.val := by
      have H (y : X) (h : η.val (IsLocalRing.closedPoint (DualNumber K)) = y) :
          Spec.map (eqToHom (congrArg (fun z : X ↦ X.presheaf.stalk z) h.symm) ≫
            Scheme.stalkClosedPointTo η.val) ≫ X.fromSpecStalk y = η.val := by
        subst y
        simpa using hη
      exact H x hy
    rw [← hθ', ← hη', hsharp]
  have hsurj : Function.Surjective L := by
    intro ℓ
    obtain ⟨θ, hx, D, hD, hDm⟩ := exists_rationalCotangent_tangent_realization k X p x hr ℓ
    obtain ⟨hy, E, hE, hEm, _⟩ := hL θ
    have hcoeff (a : R) : E a = D a := by
      apply hr.1
      have h := congrArg TrivSqZeroExt.snd ((hE a).symm.trans (hD a))
      simpa using h
    refine ⟨θ, ?_⟩
    ext v
    obtain ⟨a, rfl⟩ := (IsLocalRing.maximalIdeal R).toCotangent_surjective v
    exact (hEm a).trans ((hcoeff a).trans (hDm a).symm)
  let e := LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  refine ⟨e, ?_⟩
  intro θ
  obtain ⟨hx, D, hD, hDm, _⟩ := hL θ
  refine ⟨hx, D, ⟨hD, hDm⟩, ?_⟩
  intro E hE
  funext a
  apply hr.1
  have h := congrArg TrivSqZeroExt.snd ((hE.1 a).symm.trans (hD a))
  simpa using h

end AlgebraicGeometry
