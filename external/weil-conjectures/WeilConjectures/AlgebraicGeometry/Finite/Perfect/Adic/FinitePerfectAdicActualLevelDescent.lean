/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicActualLevels
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicScalarCoherence
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicCoordinateTransitions
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizationCoherence

/-! # Descent of the actual quotient tower with its comparison retained

Source: Stacks Project, Tags 09AL, 09B1, 09C6 and 06YY.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- A specified etale diagram descends the actual quotient tower only when its
realization and its consecutive arrows compare with that tower. Stalkwise agreement
with the algebraic model alone does not express this requirement.
Source: Stacks Tags 09AL, 09C6 and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-descent). -/
structure FinitePerfectAdicActualLevelDescent
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (L : FinitePerfectAdicActualLevelData X d M V T) where
  actual : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f n).obj
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (L.K n)) ≅
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).obj
        (op n)
  actual_normalized : ∀ (U : V.left.ProEt) (W : X.ProEt)
    (f : W ⟶ finitePerfectAdicChartObject V U) (n : ℕ),
    (finitePerfectAdicScalarRealization X d V U W f (n + 1)).map (localProEtaleNormalization U.hom
        (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (L.dK n)) ≫
      (finitePerfectAdicScalarCoherence X d V U W f n).hom.app
        ((localProEtaleComparison U.hom (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))).obj (L.K n)) ≫
      (actual U W f n).hom =
    (actual U W f (n + 1)).hom ≫
      (finitePerfectAdicRestrictedTower X d W ((completedAdicReduction X d).obj M)).map
        (homOfLE (Nat.le_succ n)).op

/-- The actual finite quotient tower admits an etale descent with the explicit
realization comparison, compatibly with its consecutive quotient arrows.

Source: Stacks Project, Tags 09AL, 09B1, 09C6 and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-descent).

Proof: on the supplied chart identify each actual finite quotient with a complex over
fixed finite scalars via the constant-scalar equivalence. The separate markings by
T.level n show bounded finite locally constant cohomology at that level. The bounded
classical derived comparison descends this actual object to an etale complex K_n;
exact faithful inverse image reflects the bounds and finite local constancy. Its
local marking torsor has an inhabited stalk at every geometric point. This gives
boundedK, lisseK and stalk, separately for each n. Full faithfulness of that same
comparison descends the actual consecutive quotient arrows, using the coefficient
restriction compositor. Tensor balancing identifies their adjoint transposes as
isomorphisms. Etale pullback commutes with this balancing by the canonical tensor
pullback comparison, so the descended arrows satisfy universalK with its coherence.
Together these fields give L. Pullback to U followed by restriction to W transports
the descent isomorphisms to the explicit scalar realization and gives actual. The
ordinary scalar compositor is the identity on the underlying abelian sheaf, hence
is the uniquely normalized compositor already fixed in finitePerfectAdicScalarCoherence.
The equation defining each descended consecutive arrow therefore localizes to exactly
actual_normalized, including the strict tower representative comparisons. No conclusion
about an arbitrary, unrelated etale complex L is asserted. Empty charts and zero rings
are included by the same equivalences and exact functors. -/
theorem finitePerfectAdic_actual_level_descent
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (T : FinitePerfectAdicAlgebraTower d)
    (hperfect : ∀ n : ℕ, DerivedCategory.IsPerfect (T.level n))
    (hmark : FinitePerfectAdicLevelMarkings X d φ M V T) :
    ∃ L : FinitePerfectAdicActualLevelData X d M V T,
      Nonempty (FinitePerfectAdicActualLevelDescent X d M V T L) := by
  classical
  have hlevels := fun n ↦
    finitePerfectAdic_marked_origin X d φ hφ M V T hmark n (hperfect n)
  choose K hbounded hlisse e hstalk using hlevels
  have hplus (n : ℕ) : DerivedCategory.TStructure.t.plus (K n) := by
    obtain ⟨a, b, hv⟩ := hbounded n
    exact ⟨a, (DerivedCategory.isGE_iff _ a).mpr fun i hi ↦ hv i (Or.inl hi)⟩
  obtain ⟨dK, actual, huniversal, hactual⟩ :=
    finitePerfectAdic_descend_coordinate_transitions X d φ hφ hcompat M V K hplus
      (fun n ↦ (e n).some)
  let L : FinitePerfectAdicActualLevelData X d M V T :=
    { K := K
      boundedK := hbounded
      lisseK := hlisse
      stalk := hstalk
      dK := dK
      universalK := fun n ↦
        { universal := huniversal n
          coherence := etaleNormalization_coherence V.left
            (RingHom.ulift (Ideal.Quotient.factorPowSucc d.ideal (n + 1))) (dK n) } }
  exact ⟨L, ⟨{ actual := actual, actual_normalized := hactual }⟩⟩

end AlgebraicGeometry.Scheme
