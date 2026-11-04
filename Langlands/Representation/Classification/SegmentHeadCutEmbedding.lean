import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SegmentDownCut
import Langlands.Representation.Classification.ArtinianSocleEmbedding
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Induction.BinaryProductSubquotients
import Langlands.Representation.Derivative.ProductVanishing
import Langlands.Representation.Derivative.Iteration

/-! Actual embeddings of supplied special heads at consecutive cuts. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentHeadCut

open GeneralLinear Derivative PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A local specialization of generic finite length to two positive ranks. -/
private theorem binaryFiniteLength {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (X : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (Y : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear b F.Carrier))
    (hX : letI := T.topology; X.IsIrreducible)
    (hY : letI := T.topology; Y.IsIrreducible) :
    letI := T.topology
    ((T.binaryNormalizedProductFunctor a b).obj (X,Y)).HasFiniteLength := by
  let := T.topology
  rw [T.binaryNormalizedProductFunctor_of_pos ha hb]
  change ((T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj
    ((T.binaryPairFamilyFunctor ha hb).obj (X,Y))).HasFiniteLength
  apply irreducibleProductFiniteLength F T (a+b) (by omega)
  intro i
  fin_cases i <;> assumption

/-- Equality transport retains the literal injectivity of a morphism. -/
private theorem rankCast_injective {a b : ℕ} (h : a = b)
    {X Y : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (hf : letI := T.topology; Function.Injective (SmoothRep.hom f)) :
    letI := T.topology
    Function.Injective (SmoothRep.hom ((generalLinearRankCast T h).map f)) := by
  subst h
  exact hf

/-- Equality transport retains nontriviality of the underlying carrier. -/
private theorem rankCast_nontrivial {a b : ℕ} (h : a = b)
    (X : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    [Nontrivial X] :
    letI := T.topology
    Nontrivial ((generalLinearRankCast T h).obj X) := by
  subst h
  change Nontrivial X
  infer_instance

/-- Equality transport retains finite group-algebra length. -/
private theorem rankCast_finiteLength {a b : ℕ} (h : a = b)
    (X : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear a F.Carrier))
    (hX : letI := T.topology; X.HasFiniteLength) :
    letI := T.topology
    ((generalLinearRankCast T h).obj X).HasFiniteLength := by
  subst h
  exact hX

/-- Injectivity composes at the level of actual smooth morphisms. -/
private theorem comp_injective {n : ℕ}
    {X Y Z : letI := T.topology
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear n F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (g : letI := T.topology; Y ⟶ Z)
    (hf : letI := T.topology; Function.Injective (SmoothRep.hom f))
    (hg : letI := T.topology; Function.Injective (SmoothRep.hom g)) :
    letI := T.topology
    Function.Injective (SmoothRep.hom (f ≫ g)) := by
  let := T.topology
  rw [SmoothRep.hom_comp]
  exact hg.comp hf

set_option maxHeartbeats 400000 in
/-- At every positive consecutive cut, the supplied long special head embeds
in the product of the two supplied shorter special heads, in decreasing order. -/
def headCutEmbedding
    (ρ : CuspidalDatum.{uV,uF} T)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    {π : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear ((a+b)*ρ.rank) F.Carrier)}
    {π₁ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (a*ρ.rank) F.Carrier)}
    {π₂ : letI := T.topology
      SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (b*ρ.rank) F.Carrier)}
    (hπ : T.IsSegmentHead ⟨ρ,a+b,by omega⟩ π)
    (hπ₁ : T.IsSegmentHead ⟨ρ.twist (b : ℝ),a,ha⟩ π₁)
    (hπ₂ : T.IsSegmentHead ⟨ρ,b,hb⟩ π₂)
    (A : letI := T.topology
      SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := ρ.rank))
    (hA : ρ.IsRepresentedBy A) :
    letI := T.topology
    {j : π.representation.IntertwiningMap
        ((generalLinearRankCast T (Nat.add_mul a b ρ.rank).symm).obj
          ((T.binaryNormalizedProductFunctor (a*ρ.rank) (b*ρ.rank)).obj
            (π₁,π₂))).representation //
      Function.Injective j} := by
  letI := T.topology
  let A₁ := SupercuspidalRep.twist
    (T.determinantPowerCharacter ρ.rank (b : ℝ))
    (T.isOpen_ker_determinantPowerCharacter ρ.rank (b : ℝ))
    (T.ker_determinant_le_ker_determinantPowerCharacter ρ.rank (b : ℝ)) A
  have hA₁ : (ρ.twist (b : ℝ)).IsRepresentedBy A₁ := by
    change A₁.isoClass = T.supercuspidalClassRealPowerTwist ρ.rank (b : ℝ) ρ.cls
    rw [← hA]
    rfl
  let j₁ := hπ₁.decreasingSocleEmbedding A₁ hA₁
  let j₂ := hπ₂.decreasingSocleEmbedding A hA
  let i₁ : π₁ ⟶ T.segmentInducedDown (T.segmentFactor A.obj (b : ℝ)) a ρ.rank_pos :=
    SmoothRep.ofHom j₁.1
  let i₂ : π₂ ⟶ T.segmentInducedDown A.obj b ρ.rank_pos :=
    SmoothRep.ofHom j₂.1
  let P := T.binaryNormalizedProductFunctor (a*ρ.rank) (b*ρ.rank)
  let C := generalLinearRankCast T (Nat.add_mul a b ρ.rank).symm
  let X := P.obj (π₁,π₂)
  let I : X ⟶ P.obj
      (T.segmentInducedDown (T.segmentFactor A.obj (b : ℝ)) a ρ.rank_pos,
        T.segmentInducedDown A.obj b ρ.rank_pos) := P.map (i₁,i₂)
  have hI : Function.Injective (SmoothRep.hom I) :=
    T.binaryProductMap_injective (a := a*ρ.rank) (b := b*ρ.rank)
      (X := (π₁,π₂))
      (Y := (T.segmentInducedDown (T.segmentFactor A.obj (b : ℝ)) a ρ.rank_pos,
        T.segmentInducedDown A.obj b ρ.rank_pos))
      (i₁,i₂) j₁.2 j₂.2
  have e : T.segmentInducedDown A.obj (a+b) ρ.rank_pos ≅ C.obj (P.obj
      (T.segmentInducedDown (T.segmentFactor A.obj (b : ℝ)) a ρ.rank_pos,
        T.segmentInducedDown A.obj b ρ.rank_pos)) :=
    SegmentDownCut.segmentInducedDownCutIso a b ρ.rank ha hb ρ.rank_pos T A.obj
  let i : C.obj X ⟶ T.segmentInducedDown A.obj (a+b) ρ.rank_pos :=
    C.map I ≫ e.inv
  have hCI : Function.Injective (SmoothRep.hom (C.map I)) :=
    rankCast_injective T _ I hI
  have hei : Function.Injective (SmoothRep.hom e.inv) :=
    SmoothRep.hom_hom_injective e.symm
  have hi : Function.Injective (SmoothRep.hom i) :=
    comp_injective T (n := (a+b)*ρ.rank) (X := C.obj X)
      (Y := C.obj (P.obj
        (T.segmentInducedDown (T.segmentFactor A.obj (b : ℝ)) a ρ.rank_pos,
          T.segmentInducedDown A.obj b ρ.rank_pos)))
      (Z := T.segmentInducedDown A.obj (a+b) ρ.rank_pos)
      (C.map I) e.inv hCI hei
  have h₁irr : π₁.IsIrreducible := (hπ₁.isIrreducibleSocle_down A₁ hA₁).1
  have h₂irr : π₂.IsIrreducible := (hπ₂.isIrreducibleSocle_down A hA).1
  letI : Nontrivial π₁ :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear (a*ρ.rank) F.Carrier)) π₁.representation.asModule
  letI : Nontrivial π₂ :=
    IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear (b*ρ.rank) F.Carrier)) π₂.representation.asModule
  letI : Nontrivial X := ProductVanishing.nontrivial_binary T (π₁,π₂)
  letI : Nontrivial (C.obj X) := rankCast_nontrivial T _ X
  have hX : X.HasFiniteLength :=
    binaryFiniteLength T (Nat.mul_pos ha ρ.rank_pos) (Nat.mul_pos hb ρ.rank_pos)
      π₁ π₂ h₁irr h₂irr
  have hCX : (C.obj X).HasFiniteLength := rankCast_finiteLength T _ X hX
  exact IsIrreducibleSocle.finiteLengthSubobjectEmbedding
    (ρ := (T.segmentInducedDown A.obj (a+b) ρ.rank_pos).representation)
    (π := π.representation) (σ := (C.obj X).representation)
    (hπ.isIrreducibleSocle_down A hA) hCX (SmoothRep.hom i) hi

end Langlands.Classification.SegmentHeadCut
