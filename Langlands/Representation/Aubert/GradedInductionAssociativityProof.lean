import Langlands.Representation.Aubert.GradedInductionUnitProof
import Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
import Langlands.Representation.Parabolic.OrderedProductRegroupingProof
import Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge
import Langlands.Representation.Smooth.JordanHolderGrothendieck

/-!
# Associativity of the actual graded induction multiplication

Associativity of `gradedMultiplication` for an arbitrary supplied proof of
`BinaryProductExactnessStatement`. The proof reduces to homogeneous classes of
actual finite-length objects. A rank-zero factor is reduced to the unit class
through the irreducible basis of the exact rank-zero Grothendieck group and the
unit laws of `GradedInductionUnitProof`; three positive-rank factors use the
published three-block induction-in-stages equivalence.
-/
noncomputable section

open CategoryTheory
open scoped DirectSum

namespace Langlands.Aubert

namespace GradedAssociativityProof

open GeneralLinear SmoothRep SmoothRep.FiniteLengthGrothendieckGroup

section Generic

universe uR uG uW

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- The classes of actual finite-length objects span the exact Grothendieck group. -/
theorem span_range_ofObject :
    Submodule.span ℤ (Set.range (ofObject :
      SmoothRep.FiniteLengthObject.{uR, uG, uW} R G → SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uW} R G)) =
      ⊤ := by
  set S := Submodule.span ℤ (Set.range (ofObject :
    SmoothRep.FiniteLengthObject.{uR, uG, uW} R G → SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uW} R G))
  have h : S.mkQ = 0 := hom_ext_object R G fun A => by
    rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨A, rfl⟩
  rw [eq_top_iff]
  intro x _
  have hx := LinearMap.congr_fun h x
  rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hx

/-- Induction over the exact Grothendieck group: a property closed under zero,
sums and integer multiples which holds on actual object classes holds everywhere. -/
@[elab_as_elim]
theorem induction_on {P : SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uW} R G → Prop}
    (x : SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uW} R G) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y)) (smul : ∀ (k : ℤ) x, P x → P (k • x))
    (obj : ∀ A : SmoothRep.FiniteLengthObject.{uR, uG, uW} R G, P (ofObject A)) : P x := by
  have hx : x ∈ Submodule.span ℤ (Set.range (ofObject :
      SmoothRep.FiniteLengthObject.{uR, uG, uW} R G → SmoothRep.FiniteLengthGrothendieckGroup.{uR, uG, uW} R G)) := by
    rw [span_range_ofObject]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨A, rfl⟩ := hy
    exact obj A
  | zero => exact zero
  | add y z _ _ hy hz => exact add y z hy hz
  | smul k y _ hy => exact smul k y hy

end Generic

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-! ### Graded induction -/

/-- Induction over the actual graded carrier, from homogeneous elements. -/
@[elab_as_elim]
theorem graded_induction {P : GradedGrothendieckGroup.{uF, uV} F T → Prop}
    (x : GradedGrothendieckGroup.{uF, uV} F T) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (hom : letI := T.topology
      ∀ (n : ℕ) (y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier),
        P (gradedInclusion F T n y)) : P x := by
  let := T.topology
  induction x using DirectSum.induction_on with
  | zero => exact zero
  | of n y =>
    have h := hom n y
    rwa [gradedInclusion, DirectSum.lof_eq_of] at h
  | add x y hx hy => exact add x y hx hy

/-! ### The unit class -/

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)

/-- The unit class is the class of the actual unit object. -/
theorem gradedUnit_eq :
    letI := T.topology
    gradedUnit F T = gradedInclusion F T 0
      (ofObject ⟨T.binaryProductUnit.{uF, max uF uV}, binaryProductUnit_hasFiniteLength F T⟩) :=
  rfl

/-! ### Rank zero -/


/-- Every irreducible smooth representation of `GL_0` is the actual unit line. -/
theorem nonempty_unit_equiv_of_isIrreducible :
    letI := T.topology
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 F.Carrier), π.IsIrreducible →
      Nonempty ((T.binaryProductUnit.{uF, max uF uV}).representation.Equiv
        π.representation) := by
  let := T.topology
  intro π hπ
  have : Representation.IsIrreducible π.representation := hπ
  have : Subsingleton (GeneralLinear 0 F.Carrier) := subsingleton_of_rank_eq_zero rfl
  have : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear 0 F.Carrier))
      π.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : π)
  let q : (T.binaryProductUnit.{uF, max uF uV}).representation.IntertwiningMap
      π.representation :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π v).comp
        (ULift.moduleEquiv (R := ℂ) (M := ℂ)).toLinearMap
      isIntertwining' := fun g => by
        rw [Subsingleton.elim g 1, map_one, map_one]
        rfl }
  have hq : ∀ c : ULift.{max uF uV} ℂ, q c = c.down • v := fun _ => rfl
  have hinj : Function.Injective q := by
    intro c c' hcc
    change c.down • v = c'.down • v at hcc
    exact ULift.ext _ _ (smul_left_injective ℂ hv hcc)
  have hsurj : Function.Surjective q := by
    refine (Representation.IsIrreducible.surjective_or_eq_zero q).resolve_right ?_
    intro h0
    apply hv
    have h1 := congrArg (fun f : (T.binaryProductUnit.{uF, max uF uV}).representation.IntertwiningMap
      π.representation => f (ULift.up 1)) h0
    change (1 : ℂ) • v = 0 at h1
    rwa [one_smul] at h1
  exact ⟨q.ofBijective ⟨hinj, hsurj⟩⟩


/-- Induction over exact rank-zero K0: every class is an integral multiple of the
actual unit class, because every irreducible representation of `GL_0` is the unit
line and irreducible classes form a basis. -/
@[elab_as_elim]
theorem rankZero_induction
    {P : letI := T.topology
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier → Prop}
    (x : letI := T.topology
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier)
    (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul : ∀ (k : ℤ) x, P x → P (k • x))
    (unit : letI := T.topology
      P (ofObject ⟨T.binaryProductUnit.{uF, max uF uV},
        binaryProductUnit_hasFiniteLength F T⟩)) : P x := by
  let := T.topology
  obtain ⟨v, rfl⟩ := (SmoothRep.irreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ
    (GeneralLinear 0 F.Carrier)).2 x
  induction v using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact zero
  | add v w hv hw => rw [map_add]; exact add _ _ hv hw
  | single c k =>
    have hc : Finsupp.single c k = k • VirtualRepresentation.generator c := by
      simp [VirtualRepresentation.generator]
    rw [hc, map_zsmul]
    apply smul
    induction c using SmoothRep.IrreducibleIsoClass.inductionOn with
    | h A hA =>
      rw [realizeIrreducibles_generator_irreducibleIsoClass A hA
        (hasFiniteLength_of_isIrreducible hA)]
      obtain ⟨e⟩ := nonempty_unit_equiv_of_isIrreducible F T A hA
      have hcl : ofRepresentation A (hasFiniteLength_of_isIrreducible hA) =
          ofObject ⟨T.binaryProductUnit.{uF, max uF uV},
            binaryProductUnit_hasFiniteLength F T⟩ :=
        (ofRepresentation_eq_of_equiv _ _ e).symm
      rw [hcl]
      exact unit

/-! ### Associativity with a rank-zero factor -/

/-- Associativity when the first factor is homogeneous of rank zero. -/
theorem assoc_rankZero_left :
    letI := T.topology
    ∀ (x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier)
      (y z : GradedGrothendieckGroup.{uF, uV} F T),
      gradedMultiplication F T hx (gradedMultiplication F T hx (gradedInclusion F T 0 x) y) z =
        gradedMultiplication F T hx (gradedInclusion F T 0 x)
          (gradedMultiplication F T hx y z) := by
  let := T.topology
  intro x y z
  refine rankZero_induction F T x ?_ ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x x' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  · intro k x h
    simp only [map_zsmul (gradedInclusion F T 0), LinearMap.map_smul₂, h]
  · rw [← gradedUnit_eq F T, gradedMultiplication_unit_left F T hx,
      gradedMultiplication_unit_left F T hx]

/-- Associativity when the middle factor is homogeneous of rank zero. -/
theorem assoc_rankZero_mid :
    letI := T.topology
    ∀ (x : GradedGrothendieckGroup.{uF, uV} F T)
      (y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier)
      (z : GradedGrothendieckGroup.{uF, uV} F T),
      gradedMultiplication F T hx (gradedMultiplication F T hx x (gradedInclusion F T 0 y)) z =
        gradedMultiplication F T hx x
          (gradedMultiplication F T hx (gradedInclusion F T 0 y) z) := by
  let := T.topology
  intro x y z
  refine rankZero_induction F T y ?_ ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro y y' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  · intro k y h
    simp only [map_zsmul (gradedInclusion F T 0), map_zsmul (gradedMultiplication F T hx x),
      LinearMap.map_smul₂, h]
  · rw [← gradedUnit_eq F T, gradedMultiplication_unit_left F T hx,
      gradedMultiplication_unit_right F T hx]

/-- Associativity when the last factor is homogeneous of rank zero. -/
theorem assoc_rankZero_right :
    letI := T.topology
    ∀ (x y : GradedGrothendieckGroup.{uF, uV} F T)
      (z : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 F.Carrier),
      gradedMultiplication F T hx (gradedMultiplication F T hx x y) (gradedInclusion F T 0 z) =
        gradedMultiplication F T hx x
          (gradedMultiplication F T hx y (gradedInclusion F T 0 z)) := by
  let := T.topology
  intro x y z
  refine rankZero_induction F T z ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro z z' h h'
    simp only [map_add, h, h']
  · intro k z h
    simp only [map_zsmul (gradedInclusion F T 0), map_zsmul (gradedMultiplication F T hx y),
      map_zsmul (gradedMultiplication F T hx x), map_zsmul (gradedMultiplication F T hx
        (gradedMultiplication F T hx x y)), h]
  · rw [← gradedUnit_eq F T, gradedMultiplication_unit_right F T hx,
      gradedMultiplication_unit_right F T hx]

end GradedAssociativityProof

end Langlands.Aubert

/-! ### Positive-rank associativity on actual objects -/

namespace Langlands.Aubert

namespace GradedAssociativityProof

open GeneralLinear SmoothRep SmoothRep.FiniteLengthGrothendieckGroup

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Equal smooth representations have equivalent actions. -/
def equivOfEq {n : ℕ}
    {X Y : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear n F.Carrier)}
    (h : X = Y) :
    letI := T.topology
    X.representation.Equiv Y.representation := by
  subst h
  exact Representation.Equiv.refl _

/-- For positive ranks the actual binary product is the normalized two-block
product of the literal pair family. -/
def binaryPairEquiv {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (A : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, uW} ℂ (GeneralLinear b F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor.{uF, uW} a b).obj (A, B)).representation.Equiv
      (T.normalizedProductInduced (Shahidi.twoBlocks a b ha hb)
        (Shahidi.pairFamily A.representation B.representation)) :=
  letI := T.topology
  Parabolic.equivTrans
    (equivOfEq F T
      (Classification.BinaryProductBridge.binaryNormalizedProductFunctor_obj_eq_twoBlocks
        F T ha hb A B))
    (Parabolic.equivTrans (T.normalizedProductInductionObjEquiv _ _)
      (T.normalizedProductInducedEquiv (Shahidi.twoBlocks a b ha hb) fun i =>
        match i with
        | 0 => Representation.Equiv.refl _
        | 1 => Representation.Equiv.refl _))

/-- The two bracketings of three positive-rank actual binary products are
equivalent after the entry-preserving rank cast along `Nat.add_assoc`. -/
def binaryAssocEquiv {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
    (B : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (C : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor.{uF, max uF uV} (a + b) c).obj
        ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (A, B),
          C)).representation.Equiv
      (((T.binaryNormalizedProductFunctor.{uF, max uF uV} a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor.{uF, max uF uV} b c).obj
          (B, C))).representation.comp
        (reindex (R := F.Carrier) (finCongr (Nat.add_assoc a b c))).toMonoidHom) :=
  letI := T.topology
  let eL : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} (a + b) c).obj
        ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (A, B),
          C)).representation.Equiv
      (T.normalizedProductInduced (Shahidi.twoBlocks (a + b) c (Nat.add_pos_left ha b) hc)
        (Shahidi.pairFamily
          (T.normalizedProductInduced (Shahidi.twoBlocks a b ha hb)
            (Shahidi.pairFamily A.representation B.representation))
          C.representation)) := Parabolic.equivTrans
    (binaryPairEquiv F T (Nat.add_pos_left ha b) hc
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a b).obj (A, B)) C)
    (T.normalizedProductInducedEquiv (Shahidi.twoBlocks (a + b) c (Nat.add_pos_left ha b) hc)
      fun i => match i with
        | 0 => binaryPairEquiv F T ha hb A B
        | 1 => Representation.Equiv.refl _)
  let eR : ((T.binaryNormalizedProductFunctor.{uF, max uF uV} a (b + c)).obj
        (A, (T.binaryNormalizedProductFunctor.{uF, max uF uV} b c).obj
          (B, C))).representation.Equiv
      (T.normalizedProductInduced (Shahidi.twoBlocks a (b + c) ha (Nat.add_pos_left hb c))
        (Shahidi.pairFamily A.representation
          (T.normalizedProductInduced (Shahidi.twoBlocks b c hb hc)
            (Shahidi.pairFamily B.representation C.representation)))) := Parabolic.equivTrans
    (binaryPairEquiv F T ha (Nat.add_pos_left hb c) A
      ((T.binaryNormalizedProductFunctor.{uF, max uF uV} b c).obj (B, C)))
    (T.normalizedProductInducedEquiv (Shahidi.twoBlocks a (b + c) ha (Nat.add_pos_left hb c))
      fun i => match i with
        | 0 => Representation.Equiv.refl _
        | 1 => binaryPairEquiv F T hb hc B C)
  Parabolic.equivTrans eL
    (Parabolic.equivTrans
      (Parabolic.equivSymm (Parabolic.threeBlockAssociativityEquiv.{uF, uV} T
        (Parabolic.orderedProductRegrouping.{uF, max uF uV} F T) a b c ha hb hc A B C))
      (Parabolic.equivPrecomp (Parabolic.equivSymm eR)
        (reindex (R := F.Carrier) (finCongr (Nat.add_assoc a b c))).toMonoidHom))

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)

/-- Associativity on homogeneous classes of actual objects of positive ranks. -/
theorem assoc_objects_pos {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
      (C : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)),
      gradedMultiplication F T hx
          (gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))
            (gradedInclusion F T b (ofObject B))) (gradedInclusion F T c (ofObject C)) =
        gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))
          (gradedMultiplication F T hx (gradedInclusion F T b (ofObject B))
            (gradedInclusion F T c (ofObject C))) := by
  let := T.topology
  intro A B C
  rw [gradedMultiplication_homogeneous F T hx a b, binaryProductK0_classes,
    gradedMultiplication_homogeneous F T hx b c, binaryProductK0_classes,
    ofRepresentation, ofRepresentation, gradedMultiplication_homogeneous F T hx (a + b) c,
    gradedMultiplication_homogeneous F T hx a (b + c), binaryProductK0_classes,
    binaryProductK0_classes]
  exact gradedInclusion_eq_of_rank_equiv F T (Nat.add_assoc a b c) _ _ _ _
    (binaryAssocEquiv F T ha hb hc A.val B.val C.val)

/-- Associativity on homogeneous classes of actual objects of arbitrary ranks. -/
theorem assoc_objects (a b c : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
      (C : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear c F.Carrier)),
      gradedMultiplication F T hx
          (gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))
            (gradedInclusion F T b (ofObject B))) (gradedInclusion F T c (ofObject C)) =
        gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))
          (gradedMultiplication F T hx (gradedInclusion F T b (ofObject B))
            (gradedInclusion F T c (ofObject C))) := by
  let := T.topology
  intro A B C
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact assoc_rankZero_left F T hx _ _ _
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact assoc_rankZero_mid F T hx _ _ _
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · exact assoc_rankZero_right F T hx _ _ _
  exact assoc_objects_pos F T hx ha hb hc A B C

end GradedAssociativityProof

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

open SmoothRep.FiniteLengthGrothendieckGroup

/-- Associativity of the actual all-ranks product on the full graded exact K0. -/
theorem gradedMultiplication_assoc
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    ∀ x y z, gradedMultiplication F T hx (gradedMultiplication F T hx x y) z =
      gradedMultiplication F T hx x (gradedMultiplication F T hx y z) := by
  let := T.topology
  intro x y z
  refine GradedAssociativityProof.graded_induction F T x ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x x' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  intro a x
  refine GradedAssociativityProof.induction_on x ?_ ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro x x' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  · intro k x h
    simp only [map_zsmul (gradedInclusion F T a), LinearMap.map_smul₂, h]
  intro A
  refine GradedAssociativityProof.graded_induction F T y ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro y y' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  intro b y
  refine GradedAssociativityProof.induction_on y ?_ ?_ ?_ ?_
  · simp only [map_zero, LinearMap.zero_apply]
  · intro y y' h h'
    simp only [map_add, LinearMap.add_apply, h, h']
  · intro k y h
    simp only [map_zsmul (gradedInclusion F T b),
      map_zsmul (gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))),
      LinearMap.map_smul₂, h]
  intro B
  refine GradedAssociativityProof.graded_induction F T z ?_ ?_ ?_
  · simp only [map_zero]
  · intro z z' h h'
    simp only [map_add, h, h']
  intro c z
  refine GradedAssociativityProof.induction_on z ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · intro z z' h h'
    simp only [map_add, h, h']
  · intro k z h
    simp only [map_zsmul (gradedInclusion F T c),
      map_zsmul (gradedMultiplication F T hx (gradedInclusion F T b (ofObject B))),
      map_zsmul (gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))),
      map_zsmul (gradedMultiplication F T hx (gradedMultiplication F T hx
        (gradedInclusion F T a (ofObject A)) (gradedInclusion F T b (ofObject B)))), h]
  intro C
  exact GradedAssociativityProof.assoc_objects F T hx a b c A B C


end Langlands.Aubert
