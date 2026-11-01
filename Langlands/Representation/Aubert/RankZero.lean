import Langlands.Representation.Aubert.InductionCommutationStatement

/-!
# The actual Aubert operators in rank zero

Evaluation and trivial coinvariant quotients identify the actual
induction-after-Jacquet objects with their inputs. Both signed sums have one
term of sign one, including the empty product Levi.
-/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Geometric Parabolic SmoothRep

universe uF uV uG uW uX

private def equivOfSubsingleton {G : Type uG} [Group G] [Subsingleton G]
    {V : Type uW} {W : Type uX}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (e : V ≃ₗ[ℂ] W) :
    ρ.Equiv σ :=
  Representation.Equiv.mk e fun g => by
    rw [Subsingleton.elim g 1, map_one, map_one]
    rfl

private def inducedCarrierEquiv {G : Type uG} [Group G] [Subsingleton G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (P : Subgroup G) (σ : Representation ℂ P V) :
    Induction.SmoothFunctions P σ ≃ₗ[ℂ] V where
  toFun f := Induction.eval P σ f 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := Induction.smoothFunctionOf P σ (fun _ => v)
    (fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl)
    ⊤ (fun _ _ => rfl)
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change Induction.eval P σ f 1 = Induction.eval P σ f g
    rw [Subsingleton.elim g 1]
  right_inv _ := rfl

private def coinvariantCarrierEquiv {G : Type uG} [Group G] [Subsingleton G]
    {V : Type uW} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) :
    Jacquet.Coinvariants ρ N ≃ₗ[ℂ] V where
  __ := Jacquet.lift ρ N LinearMap.id (fun n => by
    change LinearMap.id ∘ₗ ρ n.val = LinearMap.id
    rw [Subsingleton.elim n.val 1, map_one]
    rfl)
  invFun := Jacquet.mk ρ N
  left_inv q := by
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N q
    rfl
  right_inv _ := rfl

private def emptyBlockShape : BlockShape 0 where
  length := 0
  size := Fin.elim0
  positive := fun i => i.elim0
  sum_eq := by simp

private theorem blockShape_zero_eq (B C : BlockShape 0) : B = C := by
  have hB : B.length = 0 := Nat.eq_zero_of_le_zero B.length_le
  have hC : C.length = 0 := Nat.eq_zero_of_le_zero C.length_le
  rcases B with ⟨l, s, hp, hs⟩
  rcases C with ⟨l', s', hp', hs'⟩
  dsimp only at hB hC
  subst l
  subst l'
  have h : s = s' := funext fun i => i.elim0
  subst s'
  rfl

private abbrev emptyBlockShapeUnique : Unique (BlockShape 0) where
  default := emptyBlockShape
  uniq B := blockShape_zero_eq B emptyBlockShape

private abbrev zeroBlockIndexEmpty (B : BlockShape 0) : IsEmpty (Fin B.length) :=
  ⟨fun i => Nat.not_lt_zero i.val (lt_of_lt_of_le i.isLt B.length_le)⟩

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- In rank zero, evaluation of actual normalized induction followed by the
inverse of the trivial coinvariant quotient gives an actual representation
equivalence from induction after Jacquet restriction to the original object. -/
def inductionJacquetRankZeroEquiv (B : BlockShape 0) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier),
      ((T.normalizedParabolicInductionFunctor B).obj
        ((T.normalizedJacquetFunctor B).obj A)).representation.Equiv A.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup 0
  let : Subsingleton (GeneralLinear 0 F.Carrier) :=
    ⟨fun _ _ => Units.ext (Matrix.ext fun i _ => i.elim0)⟩
  intro A
  let eI := inducedCarrierEquiv (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B)
      ((T.normalizedJacquet B A.representation).comp (B.leviProjection F.Carrier)))
  let eJ := coinvariantCarrierEquiv
    (A.representation.comp (B.parabolic F.Carrier).subtype) (B.unipotentRadical F.Carrier)
  exact equivOfSubsingleton _ _ (eI.trans eJ)

/-- The actual refined induction-after-Jacquet object on the empty product
Levi is equivariantly linearly equivalent to its input. -/
def refinedInductionJacquetRankZeroEquiv (B : BlockShape 0) (S : BlockRefinement B) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier),
      ((T.normalizedRefinedInductionFunctor B S).obj
        ((T.normalizedRefinedJacquetFunctor B S).obj A)).representation.Equiv
          A.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.leviTopologicalGroup B
  let := zeroBlockIndexEmpty B
  let : Subsingleton (B.Levi F.Carrier) := inferInstance
  intro A
  let eI := inducedCarrierEquiv (refinedParabolic F.Carrier B S)
    (twist (T.refinedParabolicHalfModulus B S)
      ((T.normalizedRefinedJacquet B S A.representation).comp
        (refinedLeviProjection F.Carrier B S)))
  let eJ := coinvariantCarrierEquiv A.representation (refinedUnipotent F.Carrier B S)
  exact equivOfSubsingleton _ _ (eI.trans eJ)

/-- Each actual induction-after-Jacquet map is the identity in rank zero. -/
theorem inductionJacquetK0_rankZero (B : BlockShape 0) :
    letI := T.topology
    (normalizedInductionK0.{uF, uV} F T B).comp
        (normalizedJacquetK0.{uF, uV} F T B) = LinearMap.id := by
  let := T.topology
  apply FiniteLengthGrothendieckGroup.hom_ext_object
  intro A
  change normalizedInductionK0 F T B
      (normalizedJacquetK0 F T B (GeneralLinear.finiteLengthClass 0 F.Carrier A.val A.property)) =
    GeneralLinear.finiteLengthClass 0 F.Carrier A.val A.property
  have hJ := normalizedJacquetK0_hasFiniteLength F T B A.val A.property
  have hI := normalizedInductionK0_hasFiniteLength F T B _ hJ
  rw [normalizedJacquetK0_finiteLengthClass F T B A.val A.property hJ,
    normalizedInductionK0_finiteLengthClass F T B _ hJ hI]
  exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv hI A.property
    (inductionJacquetRankZeroEquiv F T B A.val)

/-- Each actual refined induction-after-Jacquet map is the identity on the
exact Grothendieck group of the empty product Levi. -/
theorem refinedInductionJacquetK0_rankZero (B : BlockShape 0) (S : BlockRefinement B) :
    letI := T.topology
    (normalizedRefinedInductionK0.{uF, uV} F T B S).comp
        (normalizedRefinedJacquetK0.{uF, uV} F T B S) = LinearMap.id := by
  let := T.topology
  apply FiniteLengthGrothendieckGroup.hom_ext_object
  intro A
  change normalizedRefinedInductionK0 F T B S
      (normalizedRefinedJacquetK0 F T B S (B.finiteLengthClass F.Carrier A.val A.property)) =
    B.finiteLengthClass F.Carrier A.val A.property
  have hJ := (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).2.1 0 B S
    A.val A.property
  have hI := (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T).1 0 B S _ hJ
  rw [normalizedRefinedJacquetK0_finiteLengthClass F T B S A.val A.property hJ,
    normalizedRefinedInductionK0_finiteLengthClass F T B S _ hJ hI]
  exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv hI A.property
    (refinedInductionJacquetRankZeroEquiv F T B S A.val)

/-- The unadjusted ambient Aubert operator is the identity in rank zero. -/
theorem alternatingOperator_rankZero :
    letI := T.topology
    alternatingOperator.{uF, uV} F T 0 = LinearMap.id := by
  let := T.topology
  let := emptyBlockShapeUnique
  let : Fintype (BlockShape 0) := Fintype.ofFinite _
  rw [alternatingOperator_eq_sum]
  simp only [inductionJacquetK0_rankZero, Nat.zero_sub, pow_zero, one_smul,
    Finset.univ_unique, Finset.sum_singleton]

/-- The unadjusted product-Levi Aubert operator is the identity in rank zero. -/
theorem alternatingOperatorOnLevi_rankZero (B : BlockShape 0) :
    letI := T.topology
    alternatingOperatorOnLevi.{uF, uV} F T B = LinearMap.id := by
  let := T.topology
  let := zeroBlockIndexEmpty B
  let : Unique (BlockRefinement B) :=
    { default := fun i => isEmptyElim i
      uniq := fun _ => Subsingleton.elim _ _ }
  let : Fintype (BlockRefinement B) := Fintype.ofFinite _
  rw [alternatingOperatorOnLevi_eq_sum]
  simp only [refinedInductionJacquetK0_rankZero, refinementSignExponent_eq,
    Nat.zero_sub, pow_zero, one_smul, Finset.univ_unique, Finset.sum_singleton]

/-- Actual normalized induction intertwines the unadjusted Aubert operators
in rank zero, with the exact short-exact-sequence relations retained. -/
theorem inductionCommutation_rankZero (B : BlockShape 0) :
    letI := T.topology
    (alternatingOperator.{uF, uV} F T 0).comp
        (normalizedInductionK0.{uF, uV} F T B) =
      (normalizedInductionK0.{uF, uV} F T B).comp
        (alternatingOperatorOnLevi.{uF, uV} F T B) := by
  let := T.topology
  rw [alternatingOperator_rankZero, alternatingOperatorOnLevi_rankZero]
  simp

end Langlands.Aubert
