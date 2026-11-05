import Langlands.GroupScheme.Rational.TorusVectorQuotientSection
import Langlands.GroupScheme.Rational.VectorGroupPointLine
import Langlands.GroupScheme.Nilpotent.NoTorusUnipotent
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationProof
import Langlands.GroupScheme.Rational.SplitTorusDominationReduction

/-! # Torus and additive factors in characteristic zero -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace TorusVectorExtension

/-- The original point factors through the torus and an actual additive line. -/
theorem exists_point_factors_of_vector_quotient
    {k : Type u} [Field k]
    {E Q : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom E.X.hom] [IsCommMonObj E.X] {n : ℕ}
    (Z : CommGroupScheme (Spec (CommRingCat.of k)))
    (hZ : IsTorus Z.toGrp) (hV : IsVectorGroupOfDimension Q n)
    (z : Z.toGrp ⟶ E) (hz : IsClosedSubgroup z) (hc : IsCentral z)
    (p : E ⟶ Q) (hq : IsFppfQuotient (SubgroupFunctor.range z) p)
    (x : rationalPoints E) :
    ∃ (t : rationalPoints Z.toGrp)
      (φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ E),
      x = rationalPoints.map z t *
        rationalPoints.map φ
          ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
            (Multiplicative.ofAdd (fun _ => 1))) := by
  obtain ⟨r, s, _, _, hps⟩ :=
    exists_split_of_vector_quotient hZ hV z hz hc p hq
  obtain ⟨ψ, hψ⟩ := hV.exists_pointLine (rationalPoints.map p x)
  have hline : rationalPoints.map (ψ ≫ s)
      ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
        (Multiplicative.ofAdd (fun _ => 1))) =
      (x ≫ p.hom.hom) ≫ s.hom.hom := by
    change _ ≫ (ψ.hom.hom ≫ s.hom.hom) = _
    rw [← Category.assoc]
    exact congrArg (fun y => y ≫ s.hom.hom) hψ
  have hpoint : (x ≫ p.hom.hom) ≫ s.hom.hom =
      x / ((x ≫ r.hom.hom) ≫ z.hom.hom) := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hps, Grp.Hom.hom_hom_div,
      GrpObj.comp_div, Grp.id_hom_hom, Category.comp_id]
    rfl
  refine ⟨rationalPoints.map r x, ψ ≫ s, ?_⟩
  rw [hline, hpoint]
  change x = ((x ≫ r.hom.hom) ≫ z.hom.hom) *
    (x / ((x ≫ r.hom.hom) ≫ z.hom.hom))
  rw [mul_comm, div_mul_cancel]

end TorusVectorExtension

/-- A smooth connected commutative affine group in characteristic zero has
torus and additive factors for every actual rational point, with exponent one. -/
theorem characteristicZeroPointFactors
    (k : Type u) [Field k] [CharZero k]
    (C : CommGroupScheme (Spec (CommRingCat.of k)))
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (x : rationalPoints C.toGrp) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ C.toGrp) (t : rationalPoints T.toGrp)
      (φ : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ C.toGrp),
      IsTorus T.toGrp ∧ IsClosedSubgroup i ∧
        x = rationalPoints.map i t *
          rationalPoints.map φ
            ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
              (Multiplicative.ofAdd (fun _ => 1))) := by
  have hnil : IsNilpotentGroupScheme C.toGrp := by
    unfold IsNilpotentGroupScheme
    infer_instance
  let D := hnil.centralTorusQuotient
  let : Smooth D.quotient.X.hom := D.smooth_quotient
  let : IsAffineHom D.quotient.X.hom := D.affine_quotient
  let : ConnectedSpace D.quotient.X.left := D.connected_quotient
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : IsAffine D.quotient.X.left := isAffine_of_isAffineHom D.quotient.X.hom
  have hcomm : (SubgroupFunctor.range D.inclusion).ContainsCommutators := by
    intro U a b
    have hab : a * b * a⁻¹ * b⁻¹ = 1 := by
      rw [mul_comm a b]
      group
    rw [hab]
    exact (SubgroupFunctor.range D.inclusion).carrier U |>.one_mem
  let : IsCommMonObj D.quotient.X :=
    D.fppf_quotient.isCommMonObj_of_containsCommutators hcomm
  have hU : IsUnipotent D.quotient :=
    D.nilpotent_quotient.isUnipotent_of_no_torus D.no_tori
  obtain ⟨n, hn⟩ := perfectFieldUnipotentSplit k D.quotient D.connected_quotient hU
  have hV : IsVectorGroupOfDimension D.quotient n :=
    hn.isVectorGroupOfDimension_of_commutative
  obtain ⟨t, φ, hx⟩ := TorusVectorExtension.exists_point_factors_of_vector_quotient
    D.torus D.maximal_torus.1 hV D.inclusion D.maximal_torus.2.1 D.central
      D.projection D.fppf_quotient x
  exact ⟨D.torus, D.inclusion, t, φ, D.maximal_torus.1, D.maximal_torus.2.1, hx⟩

/-- Actual torus and additive factors for a specified rational point. -/
structure CommutativePointFactorData
    {k : Type u} [Field k] (C : CommGroupScheme (Spec (CommRingCat.of k)))
    (x : rationalPoints C.toGrp) where
  torus : CommGroupScheme (Spec (CommRingCat.of k))
  inclusion : torus.toGrp ⟶ C.toGrp
  point : rationalPoints torus.toGrp
  additive : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ C.toGrp
  isTorus : IsTorus torus.toGrp
  closed : IsClosedSubgroup inclusion
  factorization : x = rationalPoints.map inclusion point *
    rationalPoints.map additive
      ((VectorGroup.coordinates (CommRingCat.of k) 1 (Over.mk (𝟙 _))).symm
        (Multiplicative.ofAdd (fun _ => 1)))

/-- Choose the actual characteristic-zero factors with their verified properties. -/
def characteristicZeroPointFactorData
    (k : Type u) [Field k] [CharZero k]
    (C : CommGroupScheme (Spec (CommRingCat.of k)))
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (x : rationalPoints C.toGrp) : CommutativePointFactorData C x :=
  Classical.choice (by
    obtain ⟨T, i, t, φ, hT, hi, hx⟩ := characteristicZeroPointFactors k C x
    exact ⟨{
      torus := T
      inclusion := i
      point := t
      additive := φ
      isTorus := hT
      closed := hi
      factorization := hx }⟩)

end Langlands.GroupScheme
