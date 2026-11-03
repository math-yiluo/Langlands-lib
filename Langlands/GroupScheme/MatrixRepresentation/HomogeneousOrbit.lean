import Langlands.GroupScheme.MatrixRepresentation.SchemeAction
import Langlands.GroupScheme.SchemeActionHomogeneousConstancy

/-! # Matrix-vector orbits through homogeneous scheme quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
    {G B N : GroupScheme (Spec (CommRingCat.of k))}
    {n : Type} [Fintype n] [DecidableEq n]
    {Q : Over (Spec (CommRingCat.of k))}

/-- A fixed vector of the restricted representation gives the required actual
subgroup-fixed affine-space point. -/
theorem isFixed_constant_of_restrict (ρ : MatrixRepresentation G n)
    (i : B ⟶ G) (v : n → k) (hv : (ρ.restrict i).IsFixedVector v) :
    (ρ.schemeAction.restrict i).IsFixed (constantCoefficientPoint v) := by
  intro T b g
  apply coefficientCoordinates_injective
  rw [SchemeAction.restrict_act, coefficientCoordinates_act,
    coefficientCoordinates_constant]
  simpa only [pointMatrix_restrict] using hv T g

/-- The actual affine-space morphism descended from a subgroup-fixed vector. -/
def coefficientHomogeneousOrbitMap (ρ : MatrixRepresentation G n)
    (i : B ⟶ G) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (v : n → k) (hv : (ρ.restrict i).IsFixedVector v) :
    Q ⟶ coefficientSpace n (CommRingCat.of k) :=
  ρ.schemeAction.descendedHomogeneousOrbitMap i q hq
    (constantCoefficientPoint v) (ρ.isFixed_constant_of_restrict i v hv)

/-- Pullback to the group recovers the original coefficient-vector orbit. -/
theorem quotient_comp_coefficientHomogeneousOrbitMap (ρ : MatrixRepresentation G n)
    (i : B ⟶ G) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (v : n → k) (hv : (ρ.restrict i).IsFixedVector v) :
    q ≫ ρ.coefficientHomogeneousOrbitMap i q hq v hv =
      ρ.schemeAction.orbitMap (constantCoefficientPoint v) :=
  ρ.schemeAction.quotient_comp_descendedHomogeneousOrbitMap i q hq
    (constantCoefficientPoint v) (ρ.isFixed_constant_of_restrict i v hv)

/-- A vector fixed by a subgroup with proper homogeneous quotient is fixed by
the connected reduced ambient group. -/
theorem isFixedVector_of_proper_homogeneousQuotient
    [IsAlgClosed k] [ConnectedSpace G.X.left] [IsReduced G.X.left]
    (ρ : MatrixRepresentation G n) (i : B ⟶ G) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (v : n → k) (hv : (ρ.restrict i).IsFixedVector v) : ρ.IsFixedVector v :=
  (ρ.isFixedVector_iff_isFixed v).2
    (ρ.schemeAction.isFixed_of_proper_homogeneousQuotient i q hq
      (constantCoefficientPoint v) (ρ.isFixed_constant_of_restrict i v hv))

/-- If the vector defining an exact coordinate-line stabilizer is fixed by the
ambient representation, that stabilizer is the whole group on every test. -/
theorem range_eq_top_of_fixed_coordinateVector (ρ : MatrixRepresentation G n)
    (j : n) (iN : N ⟶ G)
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range iN).carrier T ↔
        ∃ c : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤)))
    (hv : ρ.IsFixedVector (Pi.single j 1)) :
    SubgroupFunctor.range iN = ⊤ := by
  ext T x
  constructor
  · intro _
    trivial
  intro _
  apply (hline T x).2
  refine ⟨1, ?_⟩
  have hs : (fun l => scalarMap T ((Pi.single j 1 : n → k) l)) =
      (Pi.single j 1 : n → Γ(T.left, ⊤)) := by
    funext l
    by_cases hl : l = j <;> simp [hl]
  have h := hv T x
  rw [hs] at h
  simpa only [Units.val_one, one_smul] using h

/-- Proper-quotient constancy makes an exact coordinate-line stabilizer all of
the ambient group once the quotient subgroup fixes its defining vector. -/
theorem range_eq_top_of_proper_homogeneousQuotient
    [IsAlgClosed k] [ConnectedSpace G.X.left] [IsReduced G.X.left]
    (ρ : MatrixRepresentation G n) (j : n) (iN : N ⟶ G)
    (hline : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ G.X),
      x ∈ (SubgroupFunctor.range iN).carrier T ↔
        ∃ c : Γ(T.left, ⊤)ˣ,
          (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
            (c : Γ(T.left, ⊤)) • (Pi.single j 1 : n → Γ(T.left, ⊤)))
    (i : B ⟶ G) (q : G.X ⟶ Q)
    [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsProper Q.hom]
    (hq : ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
      g ≫ q = h ≫ q → g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T)
    (hv : (ρ.restrict i).IsFixedVector (Pi.single j 1)) :
    SubgroupFunctor.range iN = ⊤ :=
  ρ.range_eq_top_of_fixed_coordinateVector j iN hline
    (ρ.isFixedVector_of_proper_homogeneousQuotient i q hq (Pi.single j 1) hv)

end Langlands.GroupScheme.MatrixRepresentation
