import Langlands.Representation.Aubert.SegmentGrothendieck
import Langlands.Representation.Classification.SegmentInitialTruncation
import Langlands.Representation.Aubert.ActualFixedFactorVector
import Langlands.Representation.CuspidalSupport.BinaryProductSupport
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.SupercuspidalEmbeddingProof
import Langlands.Representation.Classification.SegmentSocleProductCaseTwo
import Langlands.Representation.Classification.SegmentHeadSupportCons
import Langlands.Representation.Classification.SegmentProductOrderedAssembly
import Langlands.Representation.Filtration.ExactFunctorIrreducibility
import Mathlib.Algebra.MonoidAlgebra.Lift

/-!
# The cuspidal-support grading of the graded Grothendieck ring

Every irreducible representation of `GL_n(F)` has a unique supercuspidal support
`supp π`, a multiset of cuspidal data (Zelevinsky 1980, 1.10; for `n = 0` it is
empty). For an integer `s`, the map `χ_s` sending the class of an irreducible `π`
to `e^{s · supp π} [π]` extends additively to a ring homomorphism from the graded
Grothendieck ring to its group algebra over `CuspidalDatum →₀ ℤ`, because every
irreducible subquotient of a product `π × π'` of irreducibles has support
`supp π + supp π'`. For any ring endomorphism `D`, the composite
`E = μ ∘ D ∘ χ_1`, where `μ` applies `χ_{-1}` coefficientwise, is computed on
segment classes. The module also shows that the unit has infinite additive
order.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Aubert.SupportGrading

open GeneralLinear PadicField.TopologicalData VirtualRepresentation
open SmoothRep.IrreducibleGrothendieckProof SmoothRep.IrreducibleOperator

universe uF uV

variable {p : ℕ} [Fact p.Prime]

/-! ### Supercuspidal supports in every rank -/

section Support

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- A supercuspidal support of a representation of `GL_0` is empty, since
cuspidal data have positive rank. -/
theorem eq_zero_of_isSupercuspidalSupport_rankZero
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier)}
    {s : Multiset (CuspidalDatum.{max uF uV, uF} T)} (hs : T.IsSupercuspidalSupport π s) :
    s = 0 := by
  have h := hs.sum_rank
  refine Multiset.eq_zero_of_forall_notMem fun ρ hρ => ?_
  have := (Multiset.sum_eq_zero_iff.mp h) ρ.rank (Multiset.mem_map_of_mem _ hρ)
  exact ρ.rank_pos.ne' this

/-- Every irreducible representation of `GL_n(F)` has a supercuspidal support,
including `n = 0`, where the empty support works. -/
theorem exists_isSupercuspidalSupport {n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) :
    ∃ s : Multiset (CuspidalDatum.{max uF uV, uF} T), T.IsSupercuspidalSupport π s := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let ρ : Fin 0 → CuspidalDatum.{max uF uV, uF} T := Fin.elim0
    have hsum : ∑ i, (ρ i).rank = 0 := by simp
    let A : ∀ i, GeneralLinear.SupercuspidalRep.{uF, max uF uV} (F := F.Carrier)
        (n := (ρ i).rank) := fun i => i.elim0
    obtain ⟨e⟩ := Classification.SegmentProductOrderedAssembly.nonempty_iso_unit T π
      (Classification.SegmentHeadSupport.finrank_eq_one_of_isIrreducible T rfl π hπ)
    refine ⟨0, 0, ρ, by simp, hsum, A, fun i => i.elim0, hπ, ?_⟩
    exact SmoothRep.IsSubquotient.of_iso_right
      (Classification.SegmentHeadSupport.isSubquotient_refl π)
      (e ≪≫ (T.emptyProductUnitIso (T.cuspidalShape ρ hsum) fun i => (A i).obj).symm)
  · obtain ⟨k, ρ, h⟩ := glSupercuspidalEmbedding.{max uF uV, uF} p F T n hn π hπ
    exact ⟨_, k, ρ, rfl, h.isCuspidalConstituent⟩

/-- Supercuspidal supports of irreducible representations are unique in every
rank. -/
theorem isSupercuspidalSupport_unique {n : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) {s s' : Multiset (CuspidalDatum.{max uF uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) (hs' : T.IsSupercuspidalSupport π s') : s = s' := by
  let := T.topology
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [eq_zero_of_isSupercuspidalSupport_rankZero hs,
      eq_zero_of_isSupercuspidalSupport_rankZero hs']
  · exact glSupercuspidalSupportUniqueness.{max uF uV, uF} p F T n hn π hπ s s' hs hs'

/-- The chosen support `T.supercuspidalSupport π` of an irreducible `π` is a
supercuspidal support of `π`. -/
theorem isSupercuspidalSupport_supercuspidalSupport' {n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) :
    T.IsSupercuspidalSupport π
      (T.supercuspidalSupport π : Multiset (CuspidalDatum.{max uF uV, uF} T)) :=
  isSupercuspidalSupport_supercuspidalSupport (exists_isSupercuspidalSupport π hπ)

/-- Any supercuspidal support of an irreducible `π` is the chosen one. -/
theorem supercuspidalSupport_eq {n : ℕ}
    {π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) {s : Multiset (CuspidalDatum.{max uF uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) : T.supercuspidalSupport π = s :=
  (hs.eq_supercuspidalSupport fun _ _ => isSupercuspidalSupport_unique hπ).symm

/-- Isomorphic irreducible representations have the same support. -/
theorem supercuspidalSupport_eq_of_iso {n : ℕ}
    {π π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : letI := T.topology; π.IsIrreducible) (hπ' : letI := T.topology; π'.IsIrreducible)
    (e : π ≅ π') :
    (T.supercuspidalSupport π : Multiset (CuspidalDatum.{max uF uV, uF} T)) =
      T.supercuspidalSupport π' :=
  (supercuspidalSupport_eq hπ' ((isSupercuspidalSupport_supercuspidalSupport' π hπ).of_iso e)).symm

variable (F T) in
/-- The supercuspidal support of an irreducible class of `GL_n(F)`. -/
def classSupport (n : ℕ) :
    (letI := T.topology; GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier) →
      Multiset (CuspidalDatum.{max uF uV, uF} T) :=
  letI := T.topology
  Quotient.lift (fun A => T.supercuspidalSupport A.val) fun A B h => by
    obtain ⟨e⟩ := h
    exact supercuspidalSupport_eq_of_iso A.property B.property e

theorem classSupport_irreducibleIsoClass {n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) :
    letI := T.topology
    classSupport F T n (SmoothRep.irreducibleIsoClass π hπ) = T.supercuspidalSupport π :=
  rfl

variable (T) in
/-- The class of a multiset of cuspidal data in the free abelian group on them. -/
def supportDegree (s : Multiset (CuspidalDatum.{uV, uF} T)) : CuspidalDatum.{uV, uF} T →₀ ℤ :=
  (s.map fun ρ => Finsupp.single ρ 1).sum

@[simp]
theorem supportDegree_zero : supportDegree T (0 : Multiset (CuspidalDatum.{uV, uF} T)) = 0 := by
  simp [supportDegree]

@[simp]
theorem supportDegree_add (s t : Multiset (CuspidalDatum.{uV, uF} T)) :
    supportDegree T (s + t) = supportDegree T s + supportDegree T t := by
  simp [supportDegree]

@[simp]
theorem supportDegree_singleton (ρ : CuspidalDatum.{uV, uF} T) :
    supportDegree T {ρ} = Finsupp.single ρ 1 := by
  simp [supportDegree]

/-- The cuspidal content of a segment is its list of members `ν^i ρ`, `i < m`. -/
theorem cuspidalContent_eq_map_range (Δ : T.Segment.{uV, uF}) :
    Δ.cuspidalContent = (Multiset.range Δ.length).map Δ.member := by
  rw [Segment.cuspidalContent, Multiset.range, Multiset.map_coe, List.ofFn_eq_map,
    ← List.map_coe_finRange_eq_range, List.map_map]
  rfl

/-- Removing the end: `content Δ = content Δ⁻ + {end Δ}`. -/
theorem cuspidalContent_dropLastNonempty (Δ : T.Segment.{uV, uF}) (h : 1 < Δ.length) :
    Δ.cuspidalContent =
      (Δ.dropLastNonempty h).cuspidalContent + {Δ.last} := by
  obtain ⟨m, hm⟩ : ∃ m, Δ.length = m + 1 := ⟨Δ.length - 1, by omega⟩
  rw [cuspidalContent_eq_map_range, cuspidalContent_eq_map_range, hm, Multiset.range_succ,
    Multiset.map_cons, Segment.dropLastNonempty_length, hm, Nat.add_sub_cancel,
    ← Multiset.singleton_add, add_comm]
  have hl : Δ.last = Δ.member m := by simp [Segment.last, hm]
  rw [hl]
  rfl

theorem cuspidalContent_of_length_eq_one (Δ : T.Segment.{uV, uF}) (h : Δ.length = 1) :
    Δ.cuspidalContent = {Δ.last} := by
  rw [cuspidalContent_eq_map_range, h]
  simp [Segment.last, h]

/-- The supercuspidal support of the segment socle is the cuspidal content. -/
theorem supercuspidalSupport_segmentSocleObject (Δ : T.Segment.{max uF uV, uF}) :
    T.supercuspidalSupport (segmentSocleObject F T Δ) = Δ.cuspidalContent := by
  let := T.topology
  obtain ⟨_, _, h⟩ := segmentSocleObject_spec F T Δ
  exact supercuspidalSupport_eq h.1
    ((Classification.SegmentSocleProductCaseTwo.embedsCuspidal_socle Δ _
      (segmentSocleObject_spec F T Δ)).isSupercuspidalSupport h.1)

end Support

/-! ### Additive generation by irreducible classes -/

section Generation

variable {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Induction over the exact Grothendieck group of `GL_n(F)`: a property closed
under `0`, sums and negatives that holds on irreducible classes holds everywhere. -/
theorem induction_irreducible {n : ℕ}
    {P : (letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) →
      Prop}
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x))
    (hirr : letI := T.topology
      ∀ (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hπ : π.IsIrreducible),
        P (GeneralLinear.finiteLengthClass n F.Carrier π
          (SmoothRep.hasFiniteLength_of_isIrreducible hπ)))
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) :
    P x := by
  let := T.topology
  have hx : SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (factorMap x) = x :=
    LinearMap.congr_fun realize_comp_factorMap x
  rw [← hx]
  generalize factorMap x = v
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact h0
  | add v w hv hw => rw [map_add]; exact hadd _ _ hv hw
  | single c z =>
    induction c using SmoothRep.IrreducibleIsoClass.inductionOn with
    | h π hπ =>
      have h1 : P (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)
          (Finsupp.single (SmoothRep.irreducibleIsoClass π hπ) 1)) := by
        have := hirr π hπ
        change P (SmoothRep.realizeIrreducibles ℂ _ (generator _))
        rw [SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ
          (SmoothRep.hasFiniteLength_of_isIrreducible hπ)]
        exact this
      induction z using Int.induction_on with
      | zero => rw [Finsupp.single_zero, map_zero]; exact h0
      | succ k ih =>
        rw [Finsupp.single_add, map_add]
        exact hadd _ _ ih h1
      | pred k ih =>
        rw [sub_eq_add_neg, Finsupp.single_add, map_add]
        refine hadd _ _ ih ?_
        rw [Finsupp.single_neg, map_neg]
        exact hneg _ h1

end Generation

/-! ### The support twists -/

section Twist

variable (F : PadicField.{uF} p) (T : F.TopologicalData)
  (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- On rank `n`, the additive map `[π] ↦ e^{s · supp π} [π]` into the group
algebra of the graded Grothendieck ring over `CuspidalDatum →₀ ℤ`. -/
def rankSupportTwist (s : ℤ) (n : ℕ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →+
      AddMonoidAlgebra (GradedGrothendieckGroup.{uF, uV} F T)
        (CuspidalDatum.{max uF uV, uF} T →₀ ℤ) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  (Finsupp.liftAddHom fun c : GeneralLinear.IrreducibleIsoClass.{uV, uF} n F.Carrier =>
      (AddMonoidAlgebra.singleAddHom (s • supportDegree T (classSupport F T n c))).comp
        ((gradedInclusion F T n).toAddMonoidHom.comp
          ((SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)).toAddMonoidHom.comp
            (Finsupp.singleAddHom c)))).comp
    factorMap.toAddMonoidHom

theorem rankSupportTwist_apply (s : ℤ) (n : ℕ)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    rankSupportTwist F T hx hl s n x =
      (factorMap x).sum fun c z =>
        AddMonoidAlgebra.single (s • supportDegree T (classSupport F T n c))
          (gradedInclusion F T n
            (SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier) (Finsupp.single c z))) :=
  rfl

/-- If every irreducible subquotient of a finite-length `M` has support `t`, the
twist multiplies the class of `M` by `e^{s · t}`. -/
theorem rankSupportTwist_of_support (s : ℤ) {n : ℕ}
    (M : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hM : letI := T.topology; M.HasFiniteLength) (t : Multiset (CuspidalDatum.{max uF uV, uF} T))
    (ht : letI := T.topology
      ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)), D.IsIrreducible →
        SmoothRep.IsSubquotient D M → T.supercuspidalSupport D = t) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    rankSupportTwist F T hx hl s n (GeneralLinear.finiteLengthClass n F.Carrier M hM) =
      AddMonoidAlgebra.single (s • supportDegree T t)
        (gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier M hM)) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hfac : factorMap (GeneralLinear.finiteLengthClass n F.Carrier M hM) =
      compositionFactors ⟨M, hM⟩ := factorMap_ofRepresentation M hM
  have hreal : SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F.Carrier)
      (compositionFactors ⟨M, hM⟩) = GeneralLinear.finiteLengthClass n F.Carrier M hM := by
    rw [← hfac]
    exact LinearMap.congr_fun realize_comp_factorMap _
  rw [rankSupportTwist_apply, hfac]
  conv_rhs => rw [← hreal, ← Finsupp.sum_single (compositionFactors ⟨M, hM⟩)]
  have hsingle : ∀ y : GradedGrothendieckGroup.{uF, uV} F T,
      AddMonoidAlgebra.single (s • supportDegree T t) y =
      AddMonoidAlgebra.singleAddHom (s • supportDegree T t) y := fun _ => rfl
  rw [map_finsuppSum, map_finsuppSum, hsingle, map_finsuppSum]
  refine Finsupp.sum_congr fun c hc => ?_
  induction c using SmoothRep.IrreducibleIsoClass.inductionOn with
  | h D hD =>
    have hsub := (mem_support_compositionFactors_iff_isSubquotient ⟨M, hM⟩ D hD).mp hc
    rw [classSupport_irreducibleIsoClass, ht D hD hsub]
    rfl

/-- The twist of an irreducible class. -/
theorem rankSupportTwist_irreducible (s : ℤ) {n : ℕ}
    (π : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible) (hL : letI := T.topology; π.HasFiniteLength) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    rankSupportTwist F T hx hl s n (GeneralLinear.finiteLengthClass n F.Carrier π hL) =
      AddMonoidAlgebra.single (s • supportDegree T (T.supercuspidalSupport π))
        (gradedInclusion F T n (GeneralLinear.finiteLengthClass n F.Carrier π hL)) := by
  let := T.topology
  rw [rankSupportTwist_apply, GeneralLinear.finiteLengthClass, factorMap_ofRepresentation,
    compositionFactors_irreducible π hπ hL,
    generator, Finsupp.sum_single_index, classSupport_irreducibleIsoClass]
  · congr 2
    exact SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass π hπ hL
  · simp

/-- The twist of a product of two classes is the product of their twists. -/
theorem rankSupportTwist_binaryProduct (s : ℤ) (a b : ℕ)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} a F.Carrier)
    (y : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} b F.Carrier) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    rankSupportTwist F T hx hl s (a + b) (binaryProductK0 F T hx a b x y) =
      rankSupportTwist F T hx hl s a x * rankSupportTwist F T hx hl s b y := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  induction x using induction_irreducible (T := T) generalizing y with
  | h0 => simp
  | hadd x x' ih ih' => rw [LinearMap.map_add₂, map_add, ih, ih', map_add, add_mul]
  | hneg x ih => rw [LinearMap.map_neg₂, map_neg, ih, map_neg, neg_mul]
  | hirr X hX =>
    induction y using induction_irreducible (T := T) with
    | h0 => simp
    | hadd y y' ih ih' => rw [map_add, map_add, ih, ih', map_add, mul_add]
    | hneg y ih => rw [map_neg, map_neg, ih, map_neg, mul_neg]
    | hirr Y hY =>
      have hXL := SmoothRep.hasFiniteLength_of_isIrreducible hX
      have hYL := SmoothRep.hasFiniteLength_of_isIrreducible hY
      let P := (T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (X, Y)
      have hPL : P.HasFiniteLength :=
        binaryProduct_preservesFiniteLength F T a b _ _ hXL hYL
      have hP : binaryProductK0 F T hx a b (GeneralLinear.finiteLengthClass a F.Carrier X hXL)
          (GeneralLinear.finiteLengthClass b F.Carrier Y hYL) =
          GeneralLinear.finiteLengthClass (a + b) F.Carrier P hPL :=
        binaryProductK0_classes F T hx a b ⟨X, hXL⟩ ⟨Y, hYL⟩
      have hmul : gradedInclusion F T a (GeneralLinear.finiteLengthClass a F.Carrier X hXL) *
          gradedInclusion F T b (GeneralLinear.finiteLengthClass b F.Carrier Y hYL) =
          gradedInclusion F T (a + b) (GeneralLinear.finiteLengthClass (a + b) F.Carrier P hPL) := by
        change gradedMultiplication F T hx _ _ = _
        rw [gradedMultiplication_homogeneous, hP]
      have ht : ∀ (D : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (a + b) F.Carrier)),
          D.IsIrreducible → SmoothRep.IsSubquotient D P →
            T.supercuspidalSupport D = T.supercuspidalSupport X + T.supercuspidalSupport Y :=
        fun D hD hsub => supercuspidalSupport_eq hD
          (binaryProductConstituentSupport (isSupercuspidalSupport_supercuspidalSupport' X hX)
            (isSupercuspidalSupport_supercuspidalSupport' Y hY) hD hsub)
      rw [hP, rankSupportTwist_of_support F T hx hl s P hPL _ ht,
        rankSupportTwist_irreducible F T hx hl s X hX, rankSupportTwist_irreducible F T hx hl s Y hY,
        AddMonoidAlgebra.single_mul_single, hmul, supportDegree_add, smul_add]

/-- The graded support twist `χ_s`, additively. -/
def supportTwistAddHom (s : ℤ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+
      AddMonoidAlgebra (GradedGrothendieckGroup.{uF, uV} F T)
        (CuspidalDatum.{max uF uV, uF} T →₀ ℤ) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  DirectSum.toAddMonoid fun n => rankSupportTwist F T hx hl s n

theorem supportTwistAddHom_inclusion (s : ℤ) (n : ℕ)
    (x : letI := T.topology; GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    supportTwistAddHom F T hx hl s (gradedInclusion F T n x) = rankSupportTwist F T hx hl s n x := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  change DirectSum.toAddMonoid (fun k => rankSupportTwist F T hx hl s k)
    (DirectSum.of (fun k => GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} k F.Carrier) n x) = _
  exact DirectSum.toAddMonoid_of (fun k => rankSupportTwist F T hx hl s k) n x

theorem supportTwistAddHom_one (s : ℤ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    supportTwistAddHom F T hx hl s 1 = 1 := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  have hu : (T.binaryProductUnit.{uF, max uF uV}).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one _ T.finrank_binaryProductUnit
  have h0 : (T.supercuspidalSupport T.binaryProductUnit.{uF, max uF uV} :
      Multiset (CuspidalDatum.{max uF uV, uF} T)) = 0 :=
    eq_zero_of_isSupercuspidalSupport_rankZero (isSupercuspidalSupport_supercuspidalSupport' _ hu)
  change supportTwistAddHom F T hx hl s (gradedUnit F T) = 1
  rw [gradedUnit, supportTwistAddHom_inclusion, rankSupportTwist_irreducible F T hx hl s _ hu, h0,
    supportDegree_zero, smul_zero, AddMonoidAlgebra.one_def]
  rfl

theorem supportTwistAddHom_mul (s : ℤ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    ∀ x y : GradedGrothendieckGroup.{uF, uV} F T,
      supportTwistAddHom F T hx hl s (x * y) =
        supportTwistAddHom F T hx hl s x * supportTwistAddHom F T hx hl s y := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  intro x y
  induction x using DirectSum.induction_on with
  | zero => simp
  | of a x =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of b y =>
      change supportTwistAddHom F T hx hl s
          (gradedMultiplication F T hx (gradedInclusion F T a x) (gradedInclusion F T b y)) =
        supportTwistAddHom F T hx hl s (gradedInclusion F T a x) *
          supportTwistAddHom F T hx hl s (gradedInclusion F T b y)
      rw [gradedMultiplication_homogeneous, supportTwistAddHom_inclusion,
        supportTwistAddHom_inclusion, supportTwistAddHom_inclusion]
      exact rankSupportTwist_binaryProduct F T hx hl s a b x y
    | add y y' ih ih' => rw [mul_add, map_add, ih, ih', map_add, mul_add]
  | add x x' ih ih' => rw [add_mul, map_add, ih, ih', map_add, add_mul]

/-- The support twist `χ_s` as a ring homomorphism from the graded Grothendieck
ring to its group algebra over `CuspidalDatum →₀ ℤ`:
`χ_s [π] = e^{s · supp π} [π]` for every irreducible `π`. -/
def supportTwist (s : ℤ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+*
      AddMonoidAlgebra (GradedGrothendieckGroup.{uF, uV} F T)
        (CuspidalDatum.{max uF uV, uF} T →₀ ℤ) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  { supportTwistAddHom F T hx hl s with
    map_one' := supportTwistAddHom_one F T hx hl s
    map_mul' := supportTwistAddHom_mul F T hx hl s }

theorem supportTwist_apply (s : ℤ) (x : GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    supportTwist F T hx hl s x = supportTwistAddHom F T hx hl s x :=
  rfl

/-- The twist of a segment class: `χ_s ζ(Δ) = e^{s · content Δ} ζ(Δ)`. -/
theorem supportTwist_segmentSocle (s : ℤ) (Δ : T.Segment.{max uF uV, uF}) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    supportTwist F T hx hl s (gradedSegmentSocle F T Δ) =
      AddMonoidAlgebra.single (s • supportDegree T Δ.cuspidalContent)
        (gradedSegmentSocle F T Δ) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  obtain ⟨_, _, h⟩ := segmentSocleObject_spec F T Δ
  rw [supportTwist_apply, gradedSegmentSocle, supportTwistAddHom_inclusion, segmentSocleClass,
    rankSupportTwist_irreducible F T hx hl s _ h.1, supercuspidalSupport_segmentSocleObject]

end Twist

/-! ### The expansion and injectivity -/

section Expansion

variable (F : PadicField.{uF} p) (T : F.TopologicalData)
  (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- The coefficientwise inverse twist `μ`: `single g a ↦ χ_{-1}(a) e^g`. -/
def untwist :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    AddMonoidAlgebra (GradedGrothendieckGroup.{uF, uV} F T)
        (CuspidalDatum.{max uF uV, uF} T →₀ ℤ) →+*
      AddMonoidAlgebra (GradedGrothendieckGroup.{uF, uV} F T)
        (CuspidalDatum.{max uF uV, uF} T →₀ ℤ) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  AddMonoidAlgebra.liftNCRingHom (supportTwist F T hx hl (-1))
    (AddMonoidAlgebra.of _ _) fun _ _ => Commute.all _ _

/-- The expansion `E = μ ∘ D ∘ χ_1` attached to a ring endomorphism `D`. -/
def expansion
    (D : letI := T.topology; letI := gradedInductionRing F T hx hl
      GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    GradedGrothendieckGroup.{uF, uV} F T →+*
      AddMonoidAlgebra (GradedGrothendieckGroup.{uF, uV} F T)
        (CuspidalDatum.{max uF uV, uF} T →₀ ℤ) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  (untwist F T hx hl).comp ((AddMonoidAlgebra.mapRingHom _ D).comp (supportTwist F T hx hl 1))

/-- If `D ζ(Δ) = ζ(Δ) + y`, where `y` has support degree `c` and the content of
`Δ` is `c + {end Δ}`, then `E ζ(Δ) = ζ(Δ) + y e^{end Δ}`. -/
theorem expansion_segmentSocle
    (D : letI := T.topology; letI := gradedInductionRing F T hx hl
      GradedGrothendieckGroup.{uF, uV} F T →+* GradedGrothendieckGroup.{uF, uV} F T)
    (Δ : T.Segment.{max uF uV, uF}) (y : GradedGrothendieckGroup.{uF, uV} F T)
    (c : CuspidalDatum.{max uF uV, uF} T →₀ ℤ)
    (hD : letI := T.topology; letI := gradedInductionRing F T hx hl
      D (gradedSegmentSocle F T Δ) = gradedSegmentSocle F T Δ + y)
    (hy : letI := T.topology; letI := gradedInductionRing F T hx hl
      supportTwist F T hx hl (-1) y = AddMonoidAlgebra.single (-c) y)
    (hc : supportDegree T Δ.cuspidalContent = c + Finsupp.single Δ.last 1) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    expansion F T hx hl D (gradedSegmentSocle F T Δ) =
      AddMonoidAlgebra.single 0 (gradedSegmentSocle F T Δ) +
        AddMonoidAlgebra.single (Finsupp.single Δ.last 1) y := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  simp only [expansion, untwist, RingHom.comp_apply]
  rw [supportTwist_segmentSocle, one_smul, AddMonoidAlgebra.mapRingHom_single, hD,
    AddMonoidAlgebra.liftNCRingHom_single, map_add, hy, supportTwist_segmentSocle,
    AddMonoidAlgebra.of_apply, add_mul, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.single_mul_single, mul_one, mul_one, toAdd_ofAdd, hc, neg_smul, one_smul]
  congr 2 <;> abel

/-- The unit of the graded Grothendieck ring has infinite additive order. -/
theorem intCast_eq_zero (c : ℤ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    (c : GradedGrothendieckGroup.{uF, uV} F T) = 0 → c = 0 := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  intro h
  have hu : (T.binaryProductUnit.{uF, max uF uV}).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one _ T.finrank_binaryProductUnit
  let u := GeneralLinear.finiteLengthClass 0 F.Carrier (T.binaryProductUnit.{uF, max uF uV})
    (binaryProductUnit_hasFiniteLength F T)
  have h1 : gradedInclusion F T 0 (c • u) = 0 := by
    rw [map_zsmul]
    rw [← zsmul_one] at h
    exact h
  have h2 : c • u = 0 := by
    have := congrArg (DirectSum.component ℤ ℕ
      (fun k => GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} k F.Carrier) 0) h1
    rwa [gradedInclusion, DirectSum.component.lof_self, map_zero] at this
  have h3 := congrArg factorMap h2
  rw [map_zsmul, map_zero] at h3
  change c • factorMap (SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation _ _) = 0 at h3
  rw [factorMap_ofRepresentation, compositionFactors_irreducible _ hu] at h3
  have := congrArg (fun v => v (SmoothRep.irreducibleIsoClass _ hu)) h3
  simpa [generator] using this

end Expansion

end Langlands.Aubert.SupportGrading
