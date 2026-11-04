import Langlands.GroupScheme.Unipotent.PrincipalPart
import Langlands.GroupScheme.Rational.AffineLineRigidity

/-! # Affine-line constancy from an anisotropic polynomial relation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Polynomial
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.Unipotent

open RelativeRoot

variable {k : Type u} [Field k]

local notation "A" => AffineLine.scheme (Spec (CommRingCat.of k))

/-- Global functions on the affine line satisfying an anisotropic
separated-variable equation are scalar functions. -/
theorem exists_scalar_coordinates_of_anisotropic_relation {n : ℕ}
    (f : Fin n → k[X]) (hf : ∀ i, (f i).coeff 0 = 0)
    (ha : HasAnisotropicPrincipalPart f)
    (c : Fin n → Γ((A).left, ⊤))
    (hc : ∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap A) (c i) = 0) :
    ∃ b : Fin n → k, ∀ i, c i = AdditiveGroupQuotient.structureMap A (b i) := by
  classical
  let E : k[X] →+* Γ((A).left, ⊤) :=
    eval₂RingHom (AdditiveGroupQuotient.structureMap A)
      (AffineLine.coord (Spec (CommRingCat.of k)))
  have hE : Function.Bijective E :=
    AdditiveGroupQuotient.bijective_eval₂RingHom_affineLine
  choose φ hφ using fun i => hE.surjective (c i)
  have hsum : ∑ i, (f i).comp (φ i) = 0 := by
    apply hE.injective
    rw [map_sum, map_zero]
    change (∑ i, eval₂ (AdditiveGroupQuotient.structureMap A)
      (AffineLine.coord (Spec (CommRingCat.of k))) ((f i).comp (φ i))) = 0
    simpa only [eval₂_comp, show ∀ i, eval₂ (AdditiveGroupQuotient.structureMap A)
      (AffineLine.coord (Spec (CommRingCat.of k))) (φ i) = c i from hφ] using hc
  have hconstant := ha.eq_C_of_sum_comp_eq_zero hf φ hsum
  refine ⟨fun i => (φ i).coeff 0, fun i => ?_⟩
  calc
    c i = E (φ i) := (hφ i).symm
    _ = E (C ((φ i).coeff 0)) := congrArg E (congrFun hconstant i)
    _ = AdditiveGroupQuotient.structureMap A ((φ i).coeff 0) := eval₂_C _ _

section VectorCoordinates

variable {G V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (j : G.X ⟶ V.X)
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))

/-- A separated-variable polynomial equation holds on the universal point
of a scheme mapped to a vector group. -/
def HasSeparatedPolynomialRelation (f : Fin n → k[X]) : Prop :=
  (∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap G.X) ((e G.X j).toAdd i)) = 0

/-- The universal coordinate equation pulls back to every relative test. -/
theorem HasSeparatedPolynomialRelation.eval_eq_zero
    (he : IsNaturalVectorCoordinates e) {f : Fin n → k[X]}
    (h : HasSeparatedPolynomialRelation j e f)
    {T : Over (Spec (CommRingCat.of k))} (a : T ⟶ G.X) :
    (∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap T)
      ((e T (a ≫ j)).toAdd i)) = 0 := by
  classical
  have hp := congrArg a.left.appTop.hom h
  change a.left.appTop.hom
    (∑ i, (f i).eval₂ (AdditiveGroupQuotient.structureMap G.X)
      ((e G.X j).toAdd i)) = a.left.appTop.hom 0 at hp
  rw [map_sum, map_zero] at hp
  convert hp using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.hom_eval₂, AdditiveGroupQuotient.structureMap_comp]
  exact congrArg ((f i).eval₂ (AdditiveGroupQuotient.structureMap T))
    (congrFun (he G.X T a j) i)

/-- A monic map into a vector group with an anisotropic
separated-variable relation makes every actual affine-line map constant. -/
theorem hasConstantAffineLineMaps_of_anisotropic_relation [Mono j]
    (he : IsNaturalVectorCoordinates e) (f : Fin n → k[X])
    (hf : ∀ i, (f i).coeff 0 = 0) (ha : HasAnisotropicPrincipalPart f)
    (hrel : HasSeparatedPolynomialRelation j e f) :
    HasConstantAffineLineMaps G := by
  intro a
  obtain ⟨b, hb⟩ := exists_scalar_coordinates_of_anisotropic_relation f hf ha
    (fun i => (e A (a ≫ j)).toAdd i) (hrel.eval_eq_zero j e he a)
  let ρ : A ⟶ A := toUnit A ≫ AffineLine.zeroSection (Spec (CommRingCat.of k))
  refine ⟨AffineLine.zeroSection (Spec (CommRingCat.of k)) ≫ a, ?_⟩
  apply (cancel_mono j).mp
  apply (e A).injective
  apply Multiplicative.toAdd.injective
  change (e A (a ≫ j)).toAdd = (e A (ρ ≫ (a ≫ j))).toAdd
  rw [he A A ρ (a ≫ j)]
  funext i
  rw [hb i]
  change AdditiveGroupQuotient.structureMap A (b i) =
    (ρ.left.appTop.hom.comp (AdditiveGroupQuotient.structureMap A)) (b i)
  rw [AdditiveGroupQuotient.structureMap_comp]

end VectorCoordinates

end Langlands.GroupScheme.Unipotent
