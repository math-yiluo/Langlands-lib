import Langlands.AlgebraicGeometry.AlgebraicSpace.EtaleQuasiFinite
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricRank
import Langlands.AlgebraicGeometry.EtaleLocalCardinalityFinitenessStatement

/-! # Actual geometric lifts of quasi-compact etale morphisms -/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Lifts to a pullback are lifts to the original source over the composite
base point. -/
def pullbackLiftsEquiv {X Y T K : Scheme.{u}} (f : X ⟶ Y) (g : T ⟶ Y)
    (t : K ⟶ T) :
    {z : K ⟶ pullback f g // z ≫ pullback.snd f g = t} ≃
      {z : K ⟶ X // z ≫ f = t ≫ g} where
  toFun z := ⟨z.1 ≫ pullback.fst f g, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]⟩
  invFun z := ⟨pullback.lift z.1 t z.2, pullback.lift_snd _ _ _⟩
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd, z.2]
  right_inv z := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

/-- Actual field-valued lifts of a quasi-compact etale morphism form a finite
type, without assuming the original morphism finite. -/
theorem finite_lifts_of_quasiCompact_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [Etale f] {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ Y) :
    Finite {z : Spec (.of K) ⟶ X // z ≫ f = t} := by
  let : LocallyQuasiFinite (pullback.snd f t) :=
    locallyQuasiFinite_of_etale _
  let : IsFinite (pullback.snd f t) := IsFinite.of_locallyQuasiFinite _
  let := FiniteEtale.finite_sections_of_isFinite (pullback.snd f t)
  exact Finite.of_equiv _ (FiniteEtale.fibreSectionsEquiv f t)

/-- The full local-base cardinality condition occurring in the finiteness
target, factored out for transport. -/
def HasLocalConstantGeometricLiftCardinality {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
      (b : Spec (CommRingCat.of R) ⟶ Y),
    ∃ n : ℕ, ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K],
      Nat.card {z : Spec (.of K) ⟶ X //
        z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b} = n

/-- The local-base cardinality condition survives arbitrary base change. -/
theorem HasLocalConstantGeometricLiftCardinality.pullback
    {X Y T : Scheme.{u}} {f : X ⟶ Y}
    (h : HasLocalConstantGeometricLiftCardinality f) (g : T ⟶ Y) :
    HasLocalConstantGeometricLiftCardinality (pullback.snd f g) := by
  intro R _ _ b
  obtain ⟨n, hn⟩ := h R (b ≫ g)
  refine ⟨n, fun K _ _ _ ↦ ?_⟩
  rw [Nat.card_congr (pullbackLiftsEquiv f g
    (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ b))]
  simpa only [Category.assoc] using hn K

/-- A finite flat morphism of finite presentation has constant rank over a
local spectrum. -/
theorem finrank_eq_closedPoint_of_localRing {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsLocalRing R] (f : X ⟶ Spec (.of R))
    [IsFinite f] [Flat f] [LocallyOfFinitePresentation f] (p : Spec (.of R)) :
    f.finrank p = f.finrank (IsLocalRing.closedPoint R) :=
  (IsLocalRing.specializes_closedPoint p).mem_open
    (f.isLocallyConstant_finrank.isOpen_fiber (f.finrank (IsLocalRing.closedPoint R))) rfl

/-- The lift count of a finite etale morphism over a local ring is its rank at
the closed point, for every algebraically closed field test. -/
theorem natCard_lifts_eq_closedPoint_finrank {X : Scheme.{u}} {R : Type u}
    [CommRing R] [IsLocalRing R] (f : X ⟶ Spec (.of R))
    [IsFinite f] [Etale f] {K : Type u} [Field K] [IsAlgClosed K] [Algebra R K] :
    Nat.card {z : Spec (.of K) ⟶ X //
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))} =
      f.finrank (IsLocalRing.closedPoint R) := by
  rw [FiniteEtale.natCard_lifts_eq_finrank f _ (IsLocalRing.closedPoint K),
    finrank_eq_closedPoint_of_localRing f]

end Langlands.AlgebraicGeometry
