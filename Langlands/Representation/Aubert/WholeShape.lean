import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Induction.SingleBlock
import Langlands.Group.GL.BlockUnipotentCoordinates
import Langlands.Representation.Geometric.BlockShapeCutCounts

/-!
# The actual induction–Jacquet identity for a one-block shape

The trivial radical and the published evaluation equivalence identify actual
normalized induction after actual Jacquet restriction with the input object.
Consequently their exact finite-length Grothendieck maps compose to the identity.
-/

noncomputable section

namespace Langlands.Aubert

open GeneralLinear Parabolic SmoothRep

universe uF uV uG

private def trivialCoinvariantEquiv {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) [Subsingleton N] :
    Jacquet.Coinvariants ρ N ≃ₗ[ℂ] V where
  __ := Jacquet.lift ρ N LinearMap.id (fun a => by
    have ha : (a : G) = 1 := congrArg Subtype.val (Subsingleton.elim a 1)
    change LinearMap.id ∘ₗ ρ a.val = LinearMap.id
    rw [ha, map_one]
    rfl)
  invFun := Jacquet.mk ρ N
  left_inv q := by
    obtain ⟨v, rfl⟩ := Jacquet.mk_surjective ρ N q
    rfl
  right_inv _ := rfl

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (hB : B.length = 1)

/-- For a single block, the actual normalized Jacquet quotient transported back
along the actual Levi equivalence is the original representation. The forward
linear map sends the class of every vector to that vector. -/
def singleBlockJacquetEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation.Equiv ((T.normalizedJacquet B ρ).comp
      (B.singleBlockLeviEquiv hB F.Carrier).symm.toMonoidHom) ρ := by
  letI := B.subsingleton_unipotentRadical F.Carrier (by omega)
  let e := trivialCoinvariantEquiv (ρ.comp (B.parabolic F.Carrier).subtype)
    (B.unipotentRadical F.Carrier)
  refine Representation.Equiv.mk e ?_
  intro g
  apply LinearMap.ext
  intro q
  obtain ⟨v, rfl⟩ := B.jacquetMk_surjective ρ q
  change e (T.normalizedJacquet B ρ
      ((B.singleBlockLeviEquiv hB F.Carrier).symm g) (B.jacquetMk ρ v)) =
    ρ g (e (B.jacquetMk ρ v))
  rw [T.normalizedJacquet_mk, T.singleBlock_leviModulus B hB]
  simp only [Units.val_one, NNReal.sqrt_one, NNReal.coe_one, Complex.ofReal_one,
    inv_one, one_smul]
  change ρ (B.leviEmbedding F.Carrier
      ((B.singleBlockLeviEquiv hB F.Carrier).symm g)) v = ρ g v
  exact congrArg (fun a => ρ a v)
    ((B.singleBlockLeviEquiv hB F.Carrier).apply_symm_apply g)

/-- The single-block Jacquet equivalence sends the actual quotient class of a
vector to that vector. -/
@[simp] theorem singleBlockJacquetEquiv_mk
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) (v : V) :
    singleBlockJacquetEquiv F T B hB ρ (B.jacquetMk ρ v) = v := rfl

/-- For a one-block shape, evaluation followed by the inverse of the trivial
coinvariant quotient identifies actual normalized induction after Jacquet
restriction with the input smooth representation. -/
def inductionJacquetSingleBlockEquiv :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ((T.normalizedParabolicInductionFunctor B).obj
        ((T.normalizedJacquetFunctor B).obj A)).representation.Equiv
          A.representation := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro A
  exact (T.singleBlockNormalizedInducedEquiv B hB
    (T.normalizedJacquet B A.representation)
    (T.isSmooth_normalizedJacquet B A.isSmooth)).trans
      (singleBlockJacquetEquiv F T B hB A.representation)

include hB in
/-- The actual normalized induction and Jacquet maps for any one-block shape
compose to the identity on the full exact finite-length smooth K0. -/
theorem inductionJacquetK0_of_length_eq_one :
    letI := T.topology
    (normalizedInductionK0.{uF, uV} F T B).comp
        (normalizedJacquetK0.{uF, uV} F T B) = LinearMap.id := by
  let := T.topology
  apply FiniteLengthGrothendieckGroup.hom_ext_object
  intro A
  change normalizedInductionK0 F T B
      (normalizedJacquetK0 F T B
        (GeneralLinear.finiteLengthClass n F.Carrier A.val A.property)) =
    GeneralLinear.finiteLengthClass n F.Carrier A.val A.property
  have hJ := normalizedJacquetK0_hasFiniteLength F T B A.val A.property
  have hI := normalizedInductionK0_hasFiniteLength F T B _ hJ
  rw [normalizedJacquetK0_finiteLengthClass F T B A.val A.property hJ,
    normalizedInductionK0_finiteLengthClass F T B _ hJ hI]
  exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv hI A.property
    (inductionJacquetSingleBlockEquiv F T B hB A.val)

/-- In positive rank the shape with no interior cuts is a one-block shape, so
its actual induction-after-Jacquet endomorphism is the identity. -/
theorem inductionJacquetK0_of_cuts_eq_empty (hn : 0 < n) (hcuts : B.cuts = ∅) :
    letI := T.topology
    (normalizedInductionK0.{uF, uV} F T B).comp
        (normalizedJacquetK0.{uF, uV} F T B) = LinearMap.id := by
  have hc := B.cuts_card
  rw [hcuts, Finset.card_empty] at hc
  have hpos := B.toComposition.length_pos_iff.mpr hn
  have hl : B.toComposition.length = B.length := by
    simp only [BlockShape.toComposition, Composition.length, List.length_ofFn]
  apply inductionJacquetK0_of_length_eq_one F T B
  omega

end Langlands.Aubert
