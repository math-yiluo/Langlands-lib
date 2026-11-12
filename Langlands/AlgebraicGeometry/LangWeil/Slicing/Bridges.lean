import Langlands.AlgebraicGeometry.LangWeil.FamilyLangWeilStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement
import Langlands.AlgebraicGeometry.GeometricIrreducibilityAffine
import Langlands.AlgebraicGeometry.SchemeFiberBaseChange

/-!
# Ring-level forms of the Lang–Weil estimate and of the point-count upper bound

For an algebra `B` of finite type over a ring `R` of finite type over `ℤ`, the `κ`-points of
`Spec B` over the `κ`-point of `Spec R` given by an `R`-algebra structure on `κ` are the
`R`-algebra homomorphisms `B →ₐ[R] κ`. This module specializes `FamilyLangWeilInDimension` and
`FamilyPointUpperBoundStatement` to the morphism `Spec B ⟶ Spec R`, with the hypotheses on
geometric irreducibility and fibre dimension expressed through tensor products.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.LangWeil.Slicing

open SchemeFiberGeometry

/-- The `κ`-points of `Spec B` over the `κ`-point of `Spec R` given by the algebra structure are
the `R`-algebra homomorphisms `B →ₐ[R] κ`. -/
theorem natCard_specPoints_eq (R B κ : Type u) [CommRing R] [CommRing B] [CommRing κ]
    [Algebra R B] [Algebra R κ] :
    Nat.card {x : Spec (CommRingCat.of κ) ⟶ Spec (CommRingCat.of B) //
      x ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
        Spec.map (CommRingCat.ofHom (algebraMap R κ))} =
      Nat.card (B →ₐ[R] κ) :=
  Nat.card_congr Spec.homEquivAlgHom

/-- The spectrum of a ring of finite type over `ℤ` is locally of finite type over `ℤ`. -/
theorem locallyOfFiniteType_specULiftZ (R : Type u) [CommRing R] [Algebra.FiniteType ℤ R] :
    LocallyOfFiniteType (specULiftZIsTerminal.{u}.from (Spec (CommRingCat.of R))) := by
  have h : specULiftZIsTerminal.from (Spec (CommRingCat.of R)) =
      Spec.map (CommRingCat.ofHom ((algebraMap ℤ R).comp
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom)) :=
    specULiftZIsTerminal.hom_ext _ _
  rw [h, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
    (RingHom.FiniteType.of_surjective _ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).surjective)

/-- The spectrum of an algebra of finite type is locally of finite type over the base. -/
theorem locallyOfFiniteType_specMap (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The fibre of `Spec B ⟶ Spec R` over the image of the closed point of a `κ`-point has the
topological dimension of the residue-field fibre ring at the kernel of `R → κ`. -/
theorem topologicalKrullDim_fiber_specMap (R B κ : Type u) [CommRing R] [CommRing B] [Field κ]
    [Algebra R B] [Algebra R κ] :
    ∃ p : PrimeSpectrum R, p.asIdeal = RingHom.ker (algebraMap R κ) ∧
      topologicalKrullDim ((Spec.map (CommRingCat.ofHom (algebraMap R B))).fiber
        (Spec.map (CommRingCat.ofHom (algebraMap R κ)) (IsLocalRing.closedPoint κ))) =
        ringKrullDim (p.asIdeal.Fiber B) := by
  refine ⟨Spec.map (CommRingCat.ofHom (algebraMap R κ)) (IsLocalRing.closedPoint κ), ?_, ?_⟩
  · change Ideal.comap (algebraMap R κ) (IsLocalRing.maximalIdeal κ) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
  · rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact IsHomeomorph.topologicalKrullDim_eq _
      (specFiberTensorIso R B _).hom.homeomorph.isHomeomorph

/-- `FamilyLangWeilInDimension e` for the morphism `Spec B ⟶ Spec R`: if every field scalar
extension of `B` has prime nilradical and every residue-field fibre ring has pure dimension `e`,
then the number of `R`-algebra homomorphisms `B → κ` is `(#κ) ^ e + O((#κ) ^ (e - 1/2))`,
uniformly in the finite field `κ` and the `R`-algebra structure on it. -/
theorem langWeil_ring {e : ℕ} (hLW : FamilyLangWeilInDimension.{u} e)
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType ℤ R]
    [Algebra.FiniteType R B]
    (hgi : ∀ (K : Type u) [Field K] [Algebra R K], (nilradical (K ⊗[R] B)).IsPrime)
    (hdim : ∀ p : PrimeSpectrum R, HasPureRingDimension (p.asIdeal.Fiber B) e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R κ],
      |(Nat.card (B →ₐ[R] κ) : ℝ) - (Nat.card κ : ℝ) ^ e| ≤
        C * (Nat.card κ : ℝ) ^ ((e : ℝ) - 1 / 2) := by
  obtain ⟨C, hC, h⟩ := hLW (Spec (CommRingCat.of R)) (Spec (CommRingCat.of B))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) (locallyOfFiniteType_specULiftZ R)
    inferInstance (locallyOfFiniteType_specMap R B) inferInstance
    ((geometricallyIrreducible_specMap_iff R B).mpr hgi)
    (fun s => (hasPureDimension_specFiber_iff R B s e).mpr (hdim s))
  refine ⟨C, hC, fun κ _ _ _ => ?_⟩
  have := h κ (Spec.map (CommRingCat.ofHom (algebraMap R κ)))
  rwa [natCard_specPoints_eq] at this

/-- `FamilyPointUpperBoundStatement` for the morphism `Spec B ⟶ Spec R`: the number of
`R`-algebra homomorphisms `B → κ` is at most `C (#κ) ^ e` whenever the residue-field fibre ring
at the kernel of `R → κ` has dimension at most `e`. -/
theorem upperBound_ring (hUB : FamilyPointUpperBoundStatement.{u})
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] [Algebra.FiniteType ℤ R]
    [Algebra.FiniteType R B] :
    ∃ C : ℝ, 0 < C ∧ ∀ (κ : Type u) [Field κ] [Finite κ] [Algebra R κ] (e : ℕ),
      (∀ p : PrimeSpectrum R, p.asIdeal = RingHom.ker (algebraMap R κ) →
        ringKrullDim (p.asIdeal.Fiber B) ≤ e) →
      (Nat.card (B →ₐ[R] κ) : ℝ) ≤ C * (Nat.card κ : ℝ) ^ e := by
  obtain ⟨C, hC, h⟩ := hUB (Spec (CommRingCat.of R)) (Spec (CommRingCat.of B))
    (Spec.map (CommRingCat.ofHom (algebraMap R B))) (locallyOfFiniteType_specULiftZ R)
    inferInstance (locallyOfFiniteType_specMap R B) inferInstance
  refine ⟨C, hC, fun κ _ _ _ e he => ?_⟩
  obtain ⟨p, hp, hdim⟩ := topologicalKrullDim_fiber_specMap R B κ
  have := h κ (Spec.map (CommRingCat.ofHom (algebraMap R κ))) e (by rw [hdim]; exact he p hp)
  rwa [natCard_specPoints_eq] at this

end Langlands.AlgebraicGeometry.LangWeil.Slicing
