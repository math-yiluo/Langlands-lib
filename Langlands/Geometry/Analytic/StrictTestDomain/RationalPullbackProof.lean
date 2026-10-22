import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackStatement
import Langlands.Geometry.Analytic.StrictTestDomain.RationalRepresentationProof

/-! # Rational inverse images and bounded base change: proof -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

namespace RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P Q : PresentedStrictAffinoidAlgebra K} (d : RationalData K P)

/-- The actual fraction coordinates of the constructed rational quotient. -/
def fraction (j : Fin d.arity) : d.algebra :=
  RationalLocalization.fractionCoordinate K P d.arity d.denominator d.numerator j

theorem baseMap_denominator_mul_fraction (j : Fin d.arity) :
    d.baseMap d.denominator * d.fraction j = d.baseMap (d.numerator j) :=
  RationalLocalization.coordinate_equation K P d.arity d.denominator d.numerator j

theorem comap_baseMap_mem_locus (x : BanachSpectrum d.algebra) :
    BanachSpectrum.comap d.baseMap.toBoundedRingHom x ∈ d.locus :=
  RationalLocalization.comap_mem_locus K P d.arity d.denominator d.numerator x

/-- Bounded maps out of the rational quotient that agree on the base are equal.
The target is any normed algebra. -/
theorem hom_ext {B : Type*} [NormedCommRing B] [NormedAlgebra K B]
    (ψ ψ' : BoundedAlgHom K d.algebra B)
    (h : ψ.comp d.baseMap = ψ'.comp d.baseMap) : ψ = ψ' :=
  RationalLocalization.hom_ext_base K P d.arity d.denominator d.numerator B
    d.generatesUnitIdeal ψ ψ' h

/-- The images of the fraction coordinates under a bounded map have bounded
monomials, since the map composed with the Tate quotient map is bounded. -/
theorem hasBoundedMonomials_map_fraction {B : Type*} [NormedCommRing B]
    [NormedAlgebra K B] (a : BoundedAlgHom K d.algebra B) :
    HasBoundedMonomials (Fin d.arity) B (fun j => a (d.fraction j)) := by
  apply (hasBoundedMonomials_iff_pow_bound (Fin d.arity) B _).mpr
  intro j
  exact (hasBoundedMonomials_map_X (Fin d.algebra.arity) K B
    (a.comp (presentationMap K d.algebra))).pow_bound (Fin d.algebra.arity) B
      (Fin.natAdd P.arity j)

variable (φ : BoundedAlgHom K P Q)

/-- The pulled-back quotient represents the inverse image of the locus. -/
theorem pullback_represents :
    Represents K (d.pullback φ).baseMap
      ((BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' d.locus) := by
  rw [← d.locus_pullback φ]
  exact rationalRepresentation K Q (d.pullback φ)

/-- The composite `P → Q → C` has spectrum image in the original locus. -/
theorem hasImageIn_pullback_baseMap_comp :
    HasImageIn K ((d.pullback φ).baseMap.comp φ) d.locus := fun x =>
  (d.pullback φ).comap_baseMap_mem_locus x

/-- The comparison map from the original rational quotient to the pulled-back
one, given by the representation property tested on the pulled-back quotient. -/
def comparison : BoundedAlgHom K d.algebra (d.pullback φ).algebra :=
  ((rationalRepresentation K P d).2.2 (d.pullback φ).algebra
    ((d.pullback φ).baseMap.comp φ) (d.hasImageIn_pullback_baseMap_comp φ)).exists.choose

theorem comparison_comp_baseMap :
    (d.comparison φ).comp d.baseMap = (d.pullback φ).baseMap.comp φ :=
  ((rationalRepresentation K P d).2.2 (d.pullback φ).algebra
    ((d.pullback φ).baseMap.comp φ) (d.hasImageIn_pullback_baseMap_comp φ)).exists.choose_spec

theorem comparison_unique (i : BoundedAlgHom K d.algebra (d.pullback φ).algebra)
    (hi : i.comp d.baseMap = (d.pullback φ).baseMap.comp φ) : i = d.comparison φ :=
  d.hom_ext i (d.comparison φ) (hi.trans (d.comparison_comp_baseMap φ).symm)

/-- The comparison map sends each fraction coordinate to the corresponding
fraction coordinate, because the mapped denominator is a unit. -/
theorem comparison_fraction (j : Fin d.arity) :
    d.comparison φ (d.fraction j) = (d.pullback φ).fraction j := by
  have hbase : ∀ x : P, d.comparison φ (d.baseMap x) = (d.pullback φ).baseMap (φ x) :=
    fun x => congrArg (fun χ => χ x) (d.comparison_comp_baseMap φ)
  have hunit : IsUnit ((d.pullback φ).baseMap (φ d.denominator)) :=
    RationalLocalization.isUnit_baseMap_denominator K Q (d.pullback φ).arity
      (d.pullback φ).denominator (d.pullback φ).numerator (d.pullback φ).generatesUnitIdeal
  apply hunit.mul_left_cancel
  calc (d.pullback φ).baseMap (φ d.denominator) * d.comparison φ (d.fraction j)
      = d.comparison φ (d.baseMap d.denominator * d.fraction j) := by
        rw [← hbase]
        exact (map_mul (d.comparison φ).toAlgHom _ _).symm
    _ = (d.pullback φ).baseMap (φ (d.numerator j)) := by
        rw [d.baseMap_denominator_mul_fraction, hbase]
    _ = (d.pullback φ).baseMap (φ d.denominator) * (d.pullback φ).fraction j :=
        ((d.pullback φ).baseMap_denominator_mul_fraction j).symm

variable {B : Type*} [NormedCommRing B] [IsUltrametricDist B] [NormedAlgebra K B]
  [CompleteSpace B] (a : BoundedAlgHom K d.algebra B) (b : BoundedAlgHom K Q B)
  (hab : a.comp d.baseMap = b.comp φ)

omit [IsUltrametricDist B] [CompleteSpace B] in
include hab in
/-- Agreement over `P` transfers the fraction equations to the mapped data. -/
theorem extension_equation (j : Fin d.arity) :
    b (φ d.denominator) * a (d.fraction j) = b (φ (d.numerator j)) := by
  have hbase : ∀ x : P, b (φ x) = a (d.baseMap x) :=
    fun x => (congrArg (fun χ => χ x) hab).symm
  rw [hbase, hbase]
  change a.toAlgHom (d.baseMap d.denominator) * a.toAlgHom (d.fraction j) = _
  rw [← map_mul]
  exact congrArg a (d.baseMap_denominator_mul_fraction j)

/-- The bounded extension from the pulled-back quotient to an arbitrary
complete ultrametric normed algebra, by convergent evaluation at the images of
the original fraction coordinates. -/
def extension : BoundedAlgHom K (d.pullback φ).algebra B :=
  RationalLocalization.liftFromBase K Q (d.pullback φ).arity (d.pullback φ).denominator
    (d.pullback φ).numerator B b (fun j => a (d.fraction j))
    (d.hasBoundedMonomials_map_fraction a) (d.extension_equation φ a b hab)

theorem extension_comp_baseMap :
    (d.extension φ a b hab).comp (d.pullback φ).baseMap = b :=
  RationalLocalization.liftFromBase_comp_baseMap K Q (d.pullback φ).arity
    (d.pullback φ).denominator (d.pullback φ).numerator B b _
    (d.hasBoundedMonomials_map_fraction a) (d.extension_equation φ a b hab)

theorem extension_fraction (j : Fin d.arity) :
    d.extension φ a b hab ((d.pullback φ).fraction j) = a (d.fraction j) :=
  RationalLocalization.liftFromBase_fractionCoordinate K Q (d.pullback φ).arity
    (d.pullback φ).denominator (d.pullback φ).numerator B b _
    (d.hasBoundedMonomials_map_fraction a) (d.extension_equation φ a b hab) j

theorem extension_comp_comparison :
    (d.extension φ a b hab).comp (d.comparison φ) = a := by
  apply d.hom_ext
  apply BoundedAlgHom.ext
  intro x
  have h1 : d.comparison φ (d.baseMap x) = (d.pullback φ).baseMap (φ x) :=
    congrArg (fun χ => χ x) (d.comparison_comp_baseMap φ)
  have h2 : d.extension φ a b hab ((d.pullback φ).baseMap (φ x)) = b (φ x) :=
    congrArg (fun χ => χ (φ x)) (d.extension_comp_baseMap φ a b hab)
  have h3 : a (d.baseMap x) = b (φ x) := congrArg (fun χ => χ x) hab
  change d.extension φ a b hab (d.comparison φ (d.baseMap x)) = a (d.baseMap x)
  rw [h1, h2, h3]

omit [IsUltrametricDist B] [CompleteSpace B] in
theorem extension_unique (c c' : BoundedAlgHom K (d.pullback φ).algebra B)
    (hc : c.comp (d.pullback φ).baseMap = b) (hc' : c'.comp (d.pullback φ).baseMap = b) :
    c = c' :=
  (d.pullback φ).hom_ext c c' (hc.trans hc'.symm)

end RationalData

/-- The pulled-back rational quotient represents the inverse-image locus for
strict tests, and is the bounded pushout of the original rational quotient
along `φ` among complete ultrametric normed algebras in any universe. -/
theorem rationalPullback : RationalPullbackStatement.{u, v} := by
  intro K _ _ _ P Q d φ
  refine ⟨d.pullback_represents φ, d.comparison φ, d.comparison_comp_baseMap φ,
    fun i hi => d.comparison_unique φ i hi, ?_⟩
  intro B _ _ _ _ a b hab
  exact ⟨d.extension φ a b hab,
    ⟨d.extension_comp_comparison φ a b hab, d.extension_comp_baseMap φ a b hab⟩,
    fun c hc => d.extension_unique φ b c (d.extension φ a b hab) hc.2
      (d.extension_comp_baseMap φ a b hab)⟩

end Langlands.Analytic.StrictTestDomain
