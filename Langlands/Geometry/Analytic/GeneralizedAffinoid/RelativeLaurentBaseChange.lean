import Langlands.Geometry.Analytic.GeneralizedAffinoid.RelativeLaurentTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalExtension

/-! # Bounded pushouts of actual relative Laurent annuli -/

noncomputable section

universe u v

namespace Langlands.Analytic.RelativeLaurentAnnulus

open PresentedAffinoidAlgebra GeneralizedTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (t : ℝ) [Fact (0 < t)] {A B : PresentedAffinoidAlgebra K}
  (E : Type v) [NormedCommRing E] [NormedAlgebra K E]

/-- The new coordinate images of an arbitrary bounded annulus map have bounded monomials. -/
theorem hasBoundedMonomials_map_newCoordinate
    (α : BoundedAlgHom K (algebra K A t) E) :
    HasBoundedMonomials (LaurentAnnulus.radii t) E
      (fun j => α (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j)) := by
  obtain ⟨c, hc, hα⟩ := α.bounded
  refine ⟨c, hc, fun d => ?_⟩
  have hm : StrictTateAlgebra.monomialValue (Fin 2) E
      (fun j => α (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j)) d =
      α (StrictTateAlgebra.monomialValue (Fin 2) (algebra K A t)
        (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t}) d) := by
    simp only [StrictTateAlgebra.monomialValue, Finsupp.prod, map_prod, map_pow]
  rw [hm]
  exact (hα _).trans (mul_le_mul_of_nonneg_left
    (Adjoin.newCoordinate_monomial_bound_equations K A (LaurentAnnulus.radii t)
      {relation K A t} d) hc.le)

variable [IsUltrametricDist E] [CompleteSpace E]

/-- The old coefficient ideal and the inverse equation vanish at a bounded Laurent solution. -/
theorem solutionTuple_relations (β : BoundedAlgHom K B E) (b : Fin 2 → E)
    (hb : HasBoundedMonomials (LaurentAnnulus.radii t) E b) (heq : b 0 * b 1 = 1) :
    ∀ f ∈ Adjoin.relations K B (LaurentAnnulus.radii t) {relation K B t},
      evaluate (B.polyradius.append (LaurentAnnulus.radii t)) K E
        (RationalPresentation.solutionTuple K B E β b) f = 0 := by
  have hs := RationalPresentation.solutionTuple_bounded K B (LaurentAnnulus.radii t)
    E β b hb
  intro f hf
  rcases hf with ⟨g, hg, rfl⟩ | hf
  · rw [RationalPresentation.evaluate_included K B (LaurentAnnulus.radii t) E β b hs,
      (presentationMap_eq_zero_iff K B g).mpr hg]
    exact map_zero β.toAlgHom
  · rw [Set.mem_singleton_iff] at hf
    subst f
    change (evaluateHom (B.polyradius.append (LaurentAnnulus.radii t)) K E
      (RationalPresentation.solutionTuple K B E β b) hs).toAlgHom (_ * _ - 1) = 0
    rw [map_sub, map_mul, map_one]
    change evaluate (B.polyradius.append (LaurentAnnulus.radii t)) K E
      (RationalPresentation.solutionTuple K B E β b)
        (X (B.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd B.arity 0)) *
      evaluate (B.polyradius.append (LaurentAnnulus.radii t)) K E
      (RationalPresentation.solutionTuple K B E β b)
        (X (B.polyradius.append (LaurentAnnulus.radii t)) K (Fin.natAdd B.arity 1)) - 1 = 0
    rw [evaluate_X, evaluate_X]
    simpa only [RationalPresentation.solutionTuple, Fin.append_right, sub_eq_zero] using heq

/-- Evaluate the actual annulus at any bounded coefficient map and bounded inverse tuple. -/
def liftFromBase (β : BoundedAlgHom K B E) (b : Fin 2 → E)
    (hb : HasBoundedMonomials (LaurentAnnulus.radii t) E b) (heq : b 0 * b 1 = 1) :
    BoundedAlgHom K (algebra K B t) E :=
  evaluateRelations K E (B.arity + 2) (B.polyradius.append (LaurentAnnulus.radii t))
    (Adjoin.relations K B (LaurentAnnulus.radii t) {relation K B t})
    (RationalPresentation.solutionTuple K B E β b)
    (RationalPresentation.solutionTuple_bounded K B (LaurentAnnulus.radii t) E β b hb)
    (solutionTuple_relations K t E β b hb heq)

@[simp] theorem liftFromBase_baseMap (β : BoundedAlgHom K B E) (b : Fin 2 → E)
    (hb : HasBoundedMonomials (LaurentAnnulus.radii t) E b) (heq : b 0 * b 1 = 1)
    (a : B) :
    liftFromBase K t E β b hb heq (baseMap K B t a) = β a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K B a
  change evaluate (B.polyradius.append (LaurentAnnulus.radii t)) K E
    (RationalPresentation.solutionTuple K B E β b)
      (appendLeft B.polyradius (LaurentAnnulus.radii t) K f) = _
  exact RationalPresentation.evaluate_included K B (LaurentAnnulus.radii t) E β b
    (RationalPresentation.solutionTuple_bounded K B (LaurentAnnulus.radii t) E β b hb) f

theorem liftFromBase_comp_baseMap (β : BoundedAlgHom K B E) (b : Fin 2 → E)
    (hb : HasBoundedMonomials (LaurentAnnulus.radii t) E b) (heq : b 0 * b 1 = 1) :
    (liftFromBase K t E β b hb heq).comp (baseMap K B t) = β :=
  BoundedAlgHom.ext (liftFromBase_baseMap K t E β b hb heq)

@[simp] theorem liftFromBase_newCoordinate (β : BoundedAlgHom K B E) (b : Fin 2 → E)
    (hb : HasBoundedMonomials (LaurentAnnulus.radii t) E b) (heq : b 0 * b 1 = 1)
    (j : Fin 2) :
    liftFromBase K t E β b hb heq
      (Adjoin.newCoordinate K B (LaurentAnnulus.radii t) {relation K B t} j) = b j :=
  (evaluate_X (B.polyradius.append (LaurentAnnulus.radii t)) K E
    (RationalPresentation.solutionTuple K B E β b) (Fin.natAdd B.arity j)).trans
      (Fin.append_right _ _ j)

variable (φ : BoundedAlgHom K A B) (α : BoundedAlgHom K (algebra K A t) E)
  (β : BoundedAlgHom K B E)

omit [IsUltrametricDist E] [CompleteSpace E] in
/-- The actual annulus quotient supplies the inverse equation after every bounded map. -/
theorem map_coordinate_mul :
    α (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 0) *
      α (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} 1) = 1 := by
  rw [← map_mul, coordinate_mul, map_one]

/-- The bounded pushout map, formed from the coefficient leg and the source annulus variables. -/
def pushoutLift : BoundedAlgHom K (algebra K B t) E :=
  liftFromBase K t E β
    (fun j => α (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j))
    (hasBoundedMonomials_map_newCoordinate K t E α) (map_coordinate_mul K t E α)

theorem pushoutLift_comp_baseMap :
    (pushoutLift K t E α β).comp (baseMap K B t) = β :=
  liftFromBase_comp_baseMap K t E β _ _ _

@[simp] theorem pushoutLift_newCoordinate (j : Fin 2) :
    pushoutLift K t E α β
      (Adjoin.newCoordinate K B (LaurentAnnulus.radii t) {relation K B t} j) =
      α (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j) :=
  liftFromBase_newCoordinate K t E β _ _ _ j

variable [CompleteSpace K]

/-- The source annulus leg is preserved exactly when the coefficient maps agree over the base. -/
theorem pushoutLift_comp_transport
    (hcompat : α.comp (baseMap K A t) = β.comp φ) :
    (pushoutLift K t E α β).comp (transport K t φ) = α := by
  apply hom_ext K t
  · intro a
    change pushoutLift K t E α β (transport K t φ (baseMap K A t a)) = _
    rw [transport_baseMap]
    exact (congrArg (fun χ : BoundedAlgHom K B E => χ (φ a))
      (pushoutLift_comp_baseMap K t E α β)).trans
        (congrArg (fun χ : BoundedAlgHom K A E => χ a) hcompat).symm
  · intro j
    change pushoutLift K t E α β
      (transport K t φ
        (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j)) = _
    rw [transport_newCoordinate, pushoutLift_newCoordinate]

/-- Agreement on both bounded pushout legs determines the whole annulus map. -/
theorem pushout_hom_ext {F : Type v} [NormedCommRing F] [NormedAlgebra K F]
    (θ η : BoundedAlgHom K (algebra K B t) F)
    (htransport : θ.comp (transport K t φ) = η.comp (transport K t φ))
    (hbase : θ.comp (baseMap K B t) = η.comp (baseMap K B t)) : θ = η := by
  apply hom_ext K t
  · intro b
    exact congrArg (fun χ : BoundedAlgHom K B F => χ b) hbase
  · intro j
    have h := congrArg (fun χ : BoundedAlgHom K (algebra K A t) F =>
      χ (Adjoin.newCoordinate K A (LaurentAnnulus.radii t) {relation K A t} j)) htransport
    simpa only [BoundedAlgHom.comp_apply, transport_newCoordinate] using h

/-- The relative annulus square is a bounded pushout into every complete ultrametric target. -/
theorem existsUnique_pushoutLift
    (hcompat : α.comp (baseMap K A t) = β.comp φ) :
    ∃! θ : BoundedAlgHom K (algebra K B t) E,
      θ.comp (transport K t φ) = α ∧ θ.comp (baseMap K B t) = β := by
  refine ⟨pushoutLift K t E α β,
    ⟨pushoutLift_comp_transport K t E φ α β hcompat,
      pushoutLift_comp_baseMap K t E α β⟩, ?_⟩
  intro θ hθ
  apply pushout_hom_ext K t φ θ (pushoutLift K t E α β)
  · exact hθ.1.trans (pushoutLift_comp_transport K t E φ α β hcompat).symm
  · exact hθ.2.trans (pushoutLift_comp_baseMap K t E α β).symm

end Langlands.Analytic.RelativeLaurentAnnulus
