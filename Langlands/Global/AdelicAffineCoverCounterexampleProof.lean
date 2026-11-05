import Langlands.Global.AdelicAffineCoverCounterexampleStatement

/-! # Proof of the binary affine-cover counterexample -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

theorem affineLineBinaryOpen_isAffine (b : Bool) :
    IsAffineOpen (affineLineBinaryOpen R b) := by
  cases b <;> exact IsAffineOpen.Spec_basicOpen _

theorem affineLineBinaryOpen_iSup :
    (⨆ b : Bool, affineLineBinaryOpen R b) = ⊤ := by
  apply top_unique
  intro x _
  apply TopologicalSpace.Opens.mem_iSup.mpr
  by_cases hx : (MvPolynomial.X () : MvPolynomial Unit R) ∈ x.asIdeal
  · refine ⟨true, ?_⟩
    change (1 - MvPolynomial.X () : MvPolynomial Unit R) ∉ x.asIdeal
    intro h
    apply x.isPrime.ne_top
    apply (Ideal.eq_top_iff_one _).mpr
    convert x.asIdeal.add_mem hx h using 1
    ring
  · exact ⟨false, hx⟩

variable (S : Type u) [CommRing S] [Algebra R S]

theorem range_subset_affineLineComplementPuncture_iff
    (p : RingPoint R (ringTest R (MvPolynomial Unit R)) S) :
    Set.range p.left ⊆ affineLineBinaryOpen R true ↔
      IsUnit (1 - affineLinePointEquiv R S p) := by
  obtain ⟨s, rfl⟩ := (affineLinePointEquiv R S).symm.surjective p
  rw [Equiv.apply_symm_apply]
  change (Set.range (PrimeSpectrum.comap
    (MvPolynomial.aeval (R := R) (fun _ : Unit => s)).toRingHom) ⊆
      ((PrimeSpectrum.basicOpen (1 - MvPolynomial.X () : MvPolynomial Unit R)) :
        Set (PrimeSpectrum (MvPolynomial Unit R)))) ↔ IsUnit (1 - s)
  rw [Set.range_subset_iff]
  change (∀ x : PrimeSpectrum S,
    (MvPolynomial.aeval (R := R) (fun _ : Unit => s))
      (1 - MvPolynomial.X ()) ∉ x.asIdeal) ↔ IsUnit (1 - s)
  simp only [map_sub, map_one, MvPolynomial.aeval_X]
  constructor
  · intro h
    by_contra hs
    obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits hs
    exact h ⟨I, hI.isPrime⟩ hsI
  · intro hs x hx
    exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hx hs)

theorem mem_openPointMap_range_iff
    (X : Over (Spec (CommRingCat.of R))) (U : X.left.Opens)
    (p : RingPoint R X S) :
    p ∈ Set.range (openPointMap R X S U) ↔ Set.range p.left ⊆ U := by
  constructor
  · rintro ⟨q, rfl⟩
    exact (openPointEquiv R X S U q).property
  · intro h
    exact ⟨openPointLift R X S U p h, openPointMap_lift R X S U p h⟩

theorem affineLineBinaryPointUnion_eq :
    affineLineBinaryPointUnion R S =
      {p | IsUnit (affineLinePointEquiv R S p) ∨
        IsUnit (1 - affineLinePointEquiv R S p)} := by
  ext p
  simp only [affineLineBinaryPointUnion, Set.mem_iUnion, mem_openPointMap_range_iff]
  change (∃ b : Bool, Set.range p.left ⊆ affineLineBinaryOpen R b) ↔ _
  rw [Bool.exists_bool]
  exact or_congr (range_subset_affineLinePuncturedOpen_iff R S p)
    (range_subset_affineLineComplementPuncture_iff R S p)

theorem affineLineTopPointUnion_eq :
    affineLineTopPointUnion R S = Set.univ := by
  ext p
  simp only [affineLineTopPointUnion, mem_openPointMap_range_iff, Set.mem_univ,
    iff_true]
  exact Set.subset_univ _

theorem affineLineBinaryCoverDescription :
    AffineLineBinaryCoverDescriptionStatement.{u} := by
  intro R _R
  refine ⟨affineLineBinaryOpen_isAffine R, affineLineBinaryOpen_iSup R,
    isAffineOpen_top _, ?_⟩
  intro S _S _RS
  exact ⟨affineLineBinaryPointUnion_eq R S, affineLineTopPointUnion_eq R S⟩

theorem affineLineBinaryPointUnion_ssubset
    (p : RingPoint R (ringTest R (MvPolynomial Unit R)) S)
    (hp : p ∉ affineLineBinaryPointUnion R S) :
    affineLineBinaryPointUnion R S ⊂ affineLineTopPointUnion R S := by
  rw [affineLineTopPointUnion_eq]
  exact Set.ssubset_iff_exists.mpr ⟨Set.subset_univ _, p, Set.mem_univ _, hp⟩

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section NumberField

variable (K : Type u) [Field K] [NumberField K]

theorem numberFieldAffineCoverCoordinate_not_isUnit :
    ¬ IsUnit (numberFieldAffineCoverCoordinate K) := by
  intro h
  have hu := h.map (RingHom.fst (InfiniteAdeles K) (FiniteAdeles K))
  exact not_isUnit_zero hu

theorem numberFieldAffineCoverComplement_not_isUnit :
    ¬ IsUnit (1 - numberFieldAffineCoverCoordinate K) := by
  obtain ⟨I, hI0, hI⟩ :=
    Ring.exists_maximal_of_not_isField (NumberField.RingOfIntegers.not_isField K)
  let v : FinitePlace K := ⟨I, hI.isPrime, hI0⟩
  intro h
  have hu := h.map (finiteProjection K v)
  have hz : finiteProjection K v (1 - numberFieldAffineCoverCoordinate K) = 0 := by
    change (1 : FiniteCompletion K v) - 1 = 0
    exact sub_self _
  rw [hz] at hu
  exact not_isUnit_zero hu

theorem numberFieldAffineCoverPoint_not_mem :
    numberFieldAffineCoverPoint K ∉ affineLineBinaryPointUnion K (Adeles K) := by
  rw [affineLineBinaryPointUnion_eq]
  change ¬ (IsUnit (affineLinePointEquiv K (Adeles K)
      ((affineLinePointEquiv K (Adeles K)).symm (numberFieldAffineCoverCoordinate K))) ∨
    IsUnit (1 - affineLinePointEquiv K (Adeles K)
      ((affineLinePointEquiv K (Adeles K)).symm (numberFieldAffineCoverCoordinate K))))
  rw [Equiv.apply_symm_apply]
  exact not_or.mpr ⟨numberFieldAffineCoverCoordinate_not_isUnit K,
    numberFieldAffineCoverComplement_not_isUnit K⟩

theorem numberFieldAffineCoverCounterexample :
    NumberFieldAffineCoverCounterexampleStatement.{u} := by
  intro K _K _nK
  have hp := numberFieldAffineCoverPoint_not_mem K
  exact ⟨hp, affineLineBinaryPointUnion_ssubset K (Adeles K)
    (numberFieldAffineCoverPoint K) hp⟩

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]

theorem curvePlaceExtension_one_ne_reference :
    curvePlaceExtension (F := F)
      (AlgebraicCurve.RationalFunctionField.placeOfPoint k 1) ≠
        curvePlaceReference k F := by
  intro h
  have hv := congrArg
    (fun v : AlgebraicCurve.Place k F =>
      v.toValuationSubring.comap (algebraMap (RatFunc k) F)) h
  simp only [curvePlaceReference, curvePlaceExtension_comap] at hv
  have hp :
      AlgebraicCurve.RationalFunctionField.placeOfPoint k 1 =
        AlgebraicCurve.RationalFunctionField.placeOfPoint k 0 :=
    AlgebraicCurve.Place.ext hv
  exact one_ne_zero (AlgebraicCurve.RationalFunctionField.placeOfPoint_injective k hp)

theorem curvePlaceAffineCoverCoordinate_not_isUnit :
    ¬ IsUnit (curvePlaceAffineCoverCoordinate k F) := by
  classical
  intro h
  have hu := h.map (RestrictedProduct.evalRingHom
    (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
    (curvePlaceReference k F))
  have hz : (RestrictedProduct.evalRingHom
      (fun v : AlgebraicCurve.Place k F => curvePlaceCompletion v)
      (curvePlaceReference k F)) (curvePlaceAffineCoverCoordinate k F) = 0 := by
    change (if curvePlaceReference k F = curvePlaceReference k F then 0 else 1) = 0
    exact ite_eq_left rfl
  rw [hz] at hu
  exact not_isUnit_zero hu

theorem curvePlaceAffineCoverComplement_not_isUnit :
    ¬ IsUnit (1 - curvePlaceAffineCoverCoordinate k F) := by
  classical
  let v := curvePlaceExtension (F := F)
    (AlgebraicCurve.RationalFunctionField.placeOfPoint k 1)
  have hv : v ≠ curvePlaceReference k F := curvePlaceExtension_one_ne_reference k F
  intro h
  have hu := h.map (RestrictedProduct.evalRingHom
    (fun w : AlgebraicCurve.Place k F => curvePlaceCompletion w) v)
  have hz : (RestrictedProduct.evalRingHom
      (fun w : AlgebraicCurve.Place k F => curvePlaceCompletion w) v)
        (1 - curvePlaceAffineCoverCoordinate k F) = 0 := by
    change (1 : curvePlaceCompletion v) -
      (if v = curvePlaceReference k F then 0 else 1) = 0
    rw [ite_eq_right hv, sub_self]
  rw [hz] at hu
  exact not_isUnit_zero hu

variable [Finite k]

theorem curvePlaceAffineCoverPoint_not_mem :
    curvePlaceAffineCoverPoint k F ∉
      affineLineBinaryPointUnion F (CurvePlaceAdeleRing k F) := by
  rw [affineLineBinaryPointUnion_eq]
  change ¬ (IsUnit (affineLinePointEquiv F (CurvePlaceAdeleRing k F)
      ((affineLinePointEquiv F (CurvePlaceAdeleRing k F)).symm
        (curvePlaceAffineCoverCoordinate k F))) ∨
    IsUnit (1 - affineLinePointEquiv F (CurvePlaceAdeleRing k F)
      ((affineLinePointEquiv F (CurvePlaceAdeleRing k F)).symm
        (curvePlaceAffineCoverCoordinate k F))))
  rw [Equiv.apply_symm_apply]
  exact not_or.mpr ⟨curvePlaceAffineCoverCoordinate_not_isUnit k F,
    curvePlaceAffineCoverComplement_not_isUnit k F⟩

theorem curvePlaceAffineCoverCounterexample :
    CurvePlaceAffineCoverCounterexampleStatement.{u} := by
  intro k F _k _F _kF _fk _rfF _tower _ff
  have hp := curvePlaceAffineCoverPoint_not_mem k F
  exact ⟨hp, affineLineBinaryPointUnion_ssubset F (CurvePlaceAdeleRing k F)
    (curvePlaceAffineCoverPoint k F) hp⟩

end Curve

/-- The two actual affine covers have different point-image unions over full adeles. -/
theorem adelicAffineCoverCounterexample :
    AdelicAffineCoverCounterexampleStatement.{u} :=
  ⟨affineLineBinaryCoverDescription, numberFieldAffineCoverCounterexample,
    curvePlaceAffineCoverCounterexample⟩

end Langlands.Global
