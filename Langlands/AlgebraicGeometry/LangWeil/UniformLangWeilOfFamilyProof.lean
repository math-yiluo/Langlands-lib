import Langlands.AlgebraicGeometry.LangWeil.UniformLangWeilOfFamilyStatement
import Langlands.AlgebraicGeometry.SmoothDomainStalksProof
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof
import Langlands.AlgebraicGeometry.NoetherianApproximation.ClosedFiberPolynomialCharts
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Jacobson.Ring

/-! # Conrad's Lemma 4.6 from the uniform Lang–Weil estimate in families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

/-- A smooth morphism with geometrically connected fibres is geometrically
irreducible. -/
theorem geometricallyIrreducible_of_smooth_of_geometricallyConnected
    {Y B : Scheme.{u}} (f : Y ⟶ B) (hsmooth : Smooth f) (hconn : GeometricallyConnected f) :
    GeometricallyIrreducible f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback h hsmooth
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  have : ConnectedSpace Z :=
    GeometricallyConnected.geometrically_connectedSpace y fst snd h
  have : IsIntegral Z := connectedLocallyNoetherianDomainStalksIntegral Z
    inferInstance inferInstance (smoothDomainStalks K Z snd inferInstance)
  infer_instance

/-- A field that is a finite module over the integers is finite. -/
theorem finite_of_moduleFinite_int (K : Type u) [Field K] [Module.Finite ℤ K] : Finite K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    let : Algebra (ZMod p) K := ZMod.algebra K p
    have : Module.Finite (ZMod p) K := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) K
    exact Module.finite_of_finite (ZMod p)
  · exfalso
    have : CharZero K := CharP.charP_to_charZero K
    have : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
    exact Int.not_isField (isField_of_isIntegral_of_isField
      (algebraMap ℤ K).injective_int (Field.toIsField K))

/-- The residue field of a closed point of a scheme locally of finite type over the
integers is finite. -/
theorem finite_residueField_of_isClosed {B : Scheme.{u}}
    (hBft : LocallyOfFiniteType (specULiftZIsTerminal.{u}.from B))
    (b : B) (hb : IsClosed ({b} : Set B)) : Finite (B.residueField b) := by
  have : IsClosedImmersion (B.fromSpecResidueField b) :=
    isClosed_singleton_iff_isClosedImmersion.mp hb
  have hcomp : LocallyOfFiniteType
      (B.fromSpecResidueField b ≫ specULiftZIsTerminal.{u}.from B) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.map_surjective
    (B.fromSpecResidueField b ≫ specULiftZIsTerminal.{u}.from B)
  rw [← hφ, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have hint : (algebraMap ℤ (B.residueField b)).FiniteType := by
    have := hcomp.comp (RingHom.FiniteType.of_surjective
      (ULift.ringEquiv.{0, u} (R := ℤ)).symm.toRingHom
      (ULift.ringEquiv.{0, u} (R := ℤ)).symm.surjective)
    convert this using 1
    exact Subsingleton.elim _ _
  have : Algebra.FiniteType ℤ (B.residueField b) := RingHom.finiteType_algebraMap.mp hint
  have := NoetherianApproximation.isJacobsonRing_int
  have : Module.Finite ℤ (B.residueField b) :=
    finite_of_finite_type_of_isJacobsonRing ℤ (B.residueField b)
  exact finite_of_moduleFinite_int (B.residueField b)

/-- Sections of the residue fibre `f.fiber b ⟶ Spec κ(b)` correspond to
`κ(b)`-valued points of `Y` lying over the canonical point `Spec κ(b) ⟶ B`. -/
def fiberSectionEquiv {B Y : Scheme.{u}} (f : Y ⟶ B) (b : B) :
    {s : Spec (B.residueField b) ⟶ f.fiber b //
        s ≫ f.fiberToSpecResidueField b = 𝟙 _} ≃
      {x : Spec (B.residueField b) ⟶ Y // x ≫ f = B.fromSpecResidueField b} where
  toFun s := ⟨s.1 ≫ f.fiberι b, by
    rw [Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc, s.2, Category.id_comp]⟩
  invFun x := ⟨pullback.lift x.1 (𝟙 _) (by rw [x.2, Category.id_comp]),
    pullback.lift_snd _ _ _⟩
  left_inv s := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans s.2.symm
  right_inv x := Subtype.ext (pullback.lift_fst _ _ _)

/-- The uniform Lang–Weil estimate in families implies Conrad's Lemma 4.6. -/
theorem uniformLangWeilOfFamily : UniformLangWeilOfFamilyStatement.{u} := by
  intro hfam B Y f d hBft hBqc hsmooth _ _ hft hqc hconn hdim
  have hgi : GeometricallyIrreducible f :=
    geometricallyIrreducible_of_smooth_of_geometricallyConnected f hsmooth hconn
  obtain ⟨C, hC, hbound⟩ := hfam d B Y f hBft hBqc hft hqc hgi hdim
  refine ⟨C, hC, fun b hb => ?_⟩
  have : Finite (B.residueField b) := finite_residueField_of_isClosed hBft b hb
  rw [Nat.card_congr (fiberSectionEquiv f b)]
  exact hbound (B.residueField b) (B.fromSpecResidueField b)

end Langlands.AlgebraicGeometry.LangWeil
