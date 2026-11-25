/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.GabberAbsolutelyAlgebraicallyClosed

/-!
# Integral covers with trivial étale cohomology

Source: Stacks Project, Lemma 09ZD (label `lemma-integral-cover-trivial-cohomology`),
part (1), etale-cohomology.tex line 14467
(blueprint: lem-weil-pbc-integral-cover-trivial-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- An affine scheme admits an integral surjective cover whose closed subschemes have
vanishing positive-degree étale cohomology with finite constant coefficients.  The
proof follows Stacks Lemma 09ZD(1): construct the cover from the integral closure of a
polynomial presentation in an algebraic closure of its fraction field, then apply
Lemma 09ZC to closed subschemes. (blueprint: lem-weil-pbc-integral-cover-trivial-cohomology)

Proof steps: the polynomial presentation and integral-closure construction use
`def-weil-affine-spectrum`, `lem-weil-pbc-polynomial-ring-domain`,
`def-weil-algebraic-closure`, and `lem-weil-pbc-integral-closure-algebraic-extension-normal`;
integrality uses `lem-weil-pbc-spec-integral-ring-map-integral`; surjectivity uses
`pqf-lem-lying-over`; and the vanishing assertion uses
`lem-weil-pbc-gabber-absolutely-algebraically-closed`, together with the stated
closed-immersion, constant-sheaf, and étale-cohomology notions.
-/
theorem exists_integral_cover_trivial_cohomology (X : Scheme.{u}) [IsAffine X] :
    ∃ (X' : Scheme.{u}) (π : X' ⟶ X),
      IsIntegralHom π ∧ Surjective π ∧
      ∀ (Z' : Scheme.{u}) (i : Z' ⟶ X') [IsClosedImmersion i],
        ∀ (M : Type (u + 1)) [AddCommGroup M] [Finite M] (q : ℤ),
          1 ≤ q →
            IsZero ((Etale.cohomology AddCommGrpCat.{u + 1} Z' q).obj
              ((DerivedCategory.singleFunctor _ 0).obj
                ((constantSheaf Z'.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
                  (AddCommGrpCat.of M)))) := by
  let A := Γ(X, ⊤)
  let P := MvPolynomial A ℤ
  let K := FractionRing P
  let L := AlgebraicClosure K
  let R := integralClosure P L
  let φ : CommRingCat.of P ⟶ A :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (Int.castRingHom A) id)
  have hφ : Function.Surjective φ := by
    intro a
    exact ⟨MvPolynomial.X a, MvPolynomial.eval₂_X _ _ _⟩
  let j : X ⟶ Spec (CommRingCat.of P) := X.isoSpec.hom ≫ Spec.map φ
  let : IsClosedImmersion (Spec.map φ) := IsClosedImmersion.spec_of_surjective φ hφ
  let : IsClosedImmersion j := inferInstance
  let : Algebra.IsAlgebraic P L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr (inferInstance : Algebra.IsAlgebraic K L)
  have hinj : Function.Injective (algebraMap P L) :=
    (algebraMap K L).injective.comp (IsFractionRing.injective P K)
  let : IsFractionRing R L :=
    integralClosure.isFractionRing_of_algebraic (fun x hx ↦ hinj (by simpa using hx))
  let : IsIntegrallyClosed R :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn L).mpr inferInstance
  let : IsAlgClosed (FractionRing R) :=
    IsAlgClosed.of_ringEquiv L _
      (IsLocalization.algEquiv (nonZeroDivisors R) L (FractionRing R)).toRingEquiv
  let f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of P) :=
    Spec.map (CommRingCat.ofHom (algebraMap P R))
  let : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr
    (show (algebraMap P R).IsIntegral from Algebra.IsIntegral.isIntegral)
  let : Surjective f := by
    refine ⟨?_⟩
    exact (show (algebraMap P R).IsIntegral from Algebra.IsIntegral.isIntegral).comap_surjective
      (by
        intro a b hab
        apply hinj
        simpa only [IsScalarTower.algebraMap_apply P R L] using
          congrArg (algebraMap R L) hab)
  refine ⟨pullback j f, pullback.fst j f, inferInstance, inferInstance, ?_⟩
  intro Z i hi M hM hfinite q hq
  exact gabber_absolutely_algebraically_closed R inferInstance Z
    (i ≫ pullback.snd j f) M q hq

end AlgebraicGeometry
