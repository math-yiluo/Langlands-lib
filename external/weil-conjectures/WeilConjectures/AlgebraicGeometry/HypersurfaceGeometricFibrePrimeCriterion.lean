/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # A prime-ideal criterion for geometric integrality of a hypersurface fibre

Source: Stacks Project, Tags 01JQ and 05DY.
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
namespace AlgebraicGeometry

private noncomputable def tensorPolynomialQuotientEquiv
    {A K : Type u} [CommRing A] [CommRing K] [Algebra A K]
    (n : ℕ) (P : MvPolynomial (Fin n) A) :
    K ⊗[A] (MvPolynomial (Fin n) A ⧸ Ideal.span {P}) ≃+*
      (MvPolynomial (Fin n) K ⧸ Ideal.span {MvPolynomial.map (algebraMap A K) P}) := by
  let e := (MvPolynomial.algebraTensorAlgEquiv (σ := Fin n) A K).toRingEquiv
  refine (Algebra.TensorProduct.tensorQuotientEquiv (R := A) A (MvPolynomial (Fin n) A) K
    (Ideal.span {P})).toRingEquiv.trans (Ideal.quotientEquiv _ _ e ?_)
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_span, Set.image_singleton]
  simp [e, Algebra.TensorProduct.includeRight_apply]

private theorem residue_toSpecΓ (S : Scheme.{u}) (s : S) :
    S.fromSpecResidueField s ≫ S.toSpecΓ = Spec.map (S.Γevaluation s) := by
  simp only [Scheme.fromSpecResidueField, Category.assoc,
    Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

private theorem hypersurface_pullback_integral_iff
    {S : Scheme.{u}} [IsAffine S]
    (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)) (s : S)
    (K : Type u) [Field K] (φ : S.residueField s →+* K) :
    let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
    let g : H ⟶ S := Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
    IsIntegral (pullback g (Spec.map (CommRingCat.ofHom φ) ≫
      S.fromSpecResidueField s)) ↔
      (Ideal.span {MvPolynomial.map (φ.comp (S.Γevaluation s).hom) P}).IsPrime := by
  dsimp only
  let A := Γ(S, ⊤)
  let B := MvPolynomial (Fin n) A ⧸ Ideal.span {P}
  let ρ := φ.comp (S.Γevaluation s).hom
  let : Algebra A K := ρ.toAlgebra
  let c : A →+* B := (Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C
  let g := Spec.map (CommRingCat.ofHom c) ≫ S.isoSpec.inv
  let y := Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s
  have hy : y ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom ρ) := by
    change y ≫ S.toSpecΓ = _
    simp only [y, Category.assoc, residue_toSpecΓ, ← Spec.map_comp]
    rfl
  have h : IsPullback (pullback.fst g y) (pullback.snd g y)
      (Spec.map (CommRingCat.ofHom c)) (Spec.map (CommRingCat.ofHom ρ)) :=
    (IsPullback.of_hasPullback g y).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) S.isoSpec
      (by simp) (by simp) (by simp [g]) hy
  let e := h.isoPullback ≪≫ pullbackSpecIso A B K
  let er := (Algebra.TensorProduct.comm A B K).toRingEquiv.trans
    (tensorPolynomialQuotientEquiv n P)
  have he : IsIntegral (pullback g y) ↔
      IsIntegral (Spec (.of (MvPolynomial (Fin n) K ⧸ Ideal.span {MvPolynomial.map ρ P}))) := by
    let e' := e ≪≫ Scheme.Spec.mapIso er.toCommRingCatIso.symm.op
    exact ⟨fun h ↦ by
      exact @IsIntegral.of_isIso _ _ h e'.hom inferInstance, fun h ↦ by
      exact @IsIntegral.of_isIso _ _ h e'.inv inferInstance⟩
  rw [he, affine_isIntegral_iff, Ideal.Quotient.isDomain_iff_prime]

/-- A hypersurface fibre is geometrically integral precisely when its defining
principal ideal stays prime under every field extension of the residue field.

Source: Stacks Project, Tag 01JQ (affine fibre products), Tag 05DY (geometric
integrality is geometric reducedness and geometric irreducibility).
Proof: For a ring map phi from kappa(s) to a field K, paste the pullback defining
H_s with Spec K -> Spec kappa(s). The canonical affine identification of S with
Spec Gamma(S, top) identifies this iterated pullback with
Spec(K tensor_A (A[t_1,...,t_n]/(P))), where A acts on K by phi composed with
evaluation at s. Tensoring a polynomial ring with K gives K[t_1,...,t_n], and
right exactness of tensor identifies the quotient with K[t_1,...,t_n]/(P_K).
These identifications respect the maps to Spec K. An affine scheme is integral
exactly when its ring is a domain, and this quotient is a domain exactly when
(P_K) is prime, including properness. Conversely every morphism Spec K to
Spec kappa(s) comes from such a ring map by full faithfulness of Spec. Thus the
universal quantifier over phi is exactly geometric integrality. A scheme is
integral iff it is reduced and irreducible; distribute the quantifier over this
conjunction to obtain the displayed equivalence. If P = 0 the quotient is the
polynomial ring, so the criterion still holds. If P is a nonzero constant after
a specialization both sides fail, since the quotient is zero and the spectrum
is empty. No integrality or finiteness assumption on S is used.
(blueprint: lem-sbc-hypersurface-geometric-fibre-prime-criterion) -/
theorem hypersurface_geometric_fibre_prime_criterion
    {S : Scheme.{u}} [IsAffine S]
    (n : ℕ) (P : MvPolynomial (Fin n) Γ(S, ⊤)) (s : S) :
    let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
    let g : H ⟶ S := Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
    (GeometricallyIrreducible (g.fiberToSpecResidueField s) ∧
      GeometricallyReduced (g.fiberToSpecResidueField s)) ↔
      ∀ (K : Type u) [Field K] (φ : S.residueField s →+* K),
        (Ideal.span {MvPolynomial.map (φ.comp (S.Γevaluation s).hom) P}).IsPrime := by
  dsimp only
  let H := Spec (.of (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span {P}))
  let g : H ⟶ S := Spec.map (CommRingCat.ofHom
    ((Ideal.Quotient.mk (Ideal.span {P})).comp MvPolynomial.C)) ≫ S.isoSpec.inv
  let f := g.fiberToSpecResidueField s
  have hGI : (GeometricallyIrreducible f ∧ GeometricallyReduced f) ↔
      GeometricallyIntegral f := by
    constructor
    · intro h
      have := h.1
      have := h.2
      exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
    · intro h
      have := h
      exact ⟨inferInstance, inferInstance⟩
  change (GeometricallyIrreducible f ∧ GeometricallyReduced f) ↔ _
  have : ObjectProperty.IsClosedUnderIsomorphisms (@IsIntegral : Scheme.{u} → Prop) := by
    constructor
    intro X Y e h
    exact @IsIntegral.of_isIso _ _ h e.hom inferInstance
  rw [hGI, geometricallyIntegral_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
  have hpoint (K : Type u) [Field K] (φ : S.residueField s →+* K) :
      IsIntegral (pullback f (Spec.map (CommRingCat.ofHom φ))) ↔
        (Ideal.span {MvPolynomial.map (φ.comp (S.Γevaluation s).hom) P}).IsPrime := by
    let e := pullbackLeftPullbackSndIso g (S.fromSpecResidueField s)
      (Spec.map (CommRingCat.ofHom φ))
    have hi : IsIntegral (pullback f (Spec.map (CommRingCat.ofHom φ))) ↔
        IsIntegral (pullback g (Spec.map (CommRingCat.ofHom φ) ≫
          S.fromSpecResidueField s)) := by
      exact ⟨fun h ↦ @IsIntegral.of_isIso _ _ h e.hom inferInstance,
        fun h ↦ @IsIntegral.of_isIso _ _ h e.inv inferInstance⟩
    exact hi.trans (hypersurface_pullback_integral_iff n P s K φ)
  constructor
  · intro h K _ φ
    exact (hpoint K φ).mp (h K (Spec.map (CommRingCat.ofHom φ)))
  · intro h K _ y
    obtain ⟨φ, rfl⟩ := Spec.map_surjective y
    exact (hpoint K φ.hom).mpr (h K φ.hom)

end AlgebraicGeometry
