/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicQuotientCoordinateTower
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoordinateTransitionCoherence

/-! # Descending the arrows of already descended finite quotients

Source: Stacks Project, Tags 09AL, 09C6 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Once the finite quotients have specified bounded-below etale origins, their
consecutive maps descend and their scalar realizations compare with the actual tower.
This asserts neither existence of those origins nor any local marking, finite local
constancy, perfectness or geometric-stalk property. The comparisons supplied in the
hypothesis identify the actual quotients, rather than just their isomorphism classes
at geometric points. The assertion applies to every supplied family of origins and
comparison isomorphisms.

Source: Stacks Project, Tag 09C6, the arrows L_(n+1) -> L_n, using full faithfulness
in Tag 09AL and derived tensor balancing in Tag 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-coordinate-transitions).

Proof: in the fixed scalar coordinates of the actual quotients, form the consecutive
quotient maps on one flat-term K-flat representative of M. Their scalar-extension
transposes are isomorphisms by tensor balancing. The compatibility of phi with both
quotient maps and the completed scalar map identifies these with the canonical
fixed-scalar coefficient maps. Conjugate each such map by the two supplied comparison
isomorphisms. The coefficient interchange for etale/pro-etale inverse image turns it
into a map from the comparison of K_(n+1) to the comparison of the scalar restriction
of K_n. That target is bounded below, since coefficient restriction is exact. Full
faithfulness of derived comparison therefore gives its unique preimage dK_n.

For each etale source pull the square through the canonical tensor-pullback mate.
The mate's unit identity identifies the adjoint transpose of the pulled dK_n with
the pulled quotient balancing isomorphism. Exact faithful inverse image reflects
isomorphisms, so this transpose is invertible. The adjunction characterizes this as
the displayed universal structured arrow.

Pull each supplied descent comparison back to U, restrict along f, and transport
through the slice equivalence. Associated module sheafification cancels restriction
to the finite constant scalars; forgetting along the completed projection then gives
the actual completed-module quotient. The factors isomorphisms for exact derived
functors and the counit of the strict tower representative give actual. On underlying
abelian sheaves the scalar compositor is the identity. The defining lifted square
therefore becomes exactly the displayed equation with finitePerfectAdicScalarCoherence.
All choices of K-flat representatives are compared by their localization counits,
so the equation includes the strict tower representative used in RestrictedTower.
This works for unbounded M, empty charts, and zero rings; boundedness is used only
for the already supplied etale targets in the full-faithfulness step. -/
theorem finitePerfectAdic_descend_coordinate_transitions
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (K : ∀ n : ℕ, DerivedCategory (Sheaf V.left.smallEtaleTopology
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))))))
    (hKplus : ∀ n : ℕ, DerivedCategory.TStructure.t.plus (K n))
    (e : ∀ n : ℕ, ((ProEtale.comparisonUpperStar
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) V.left)
        |>.mapDerivedCategory).obj (K n) ≅ finitePerfectAdicQuotientCoordinates X d φ M V n) :
    ∃ dK : ∀ n : ℕ, K (n + 1) ⟶
        (normalizationRestrict V.left.smallEtaleTopology
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1)))).obj (K n),
    ∃ actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f n).obj
          ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
            (K n)) ≅
        (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
          (op n),
      (∀ (n : ℕ) (U : V.left.Etale), Nonempty (StructuredArrow.IsUniversal
        (StructuredArrow.mk (etaleIsomorphismNormalizationArrow V.left
          (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n) U)))) ∧
      (∀ (U : V.left.ProEt) (W : X.ProEt)
        (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
        (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map
          (localProEtaleNormalization U.hom
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n)) ≫
          (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
            ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj
              (K n)) ≫
          (actual U W f n).hom =
        (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
            (homOfLE (Nat.le_succ n)).op) := by
  obtain ⟨dJ, hJ, actualJ, hactualJ⟩ := finitePerfectAdic_quotient_coordinate_tower
    X d φ hφ hcompat M V
  exact finitePerfectAdic_coordinate_transition_coherence
    X d φ M V K hKplus e dJ hJ actualJ hactualJ

end AlgebraicGeometry.Scheme
