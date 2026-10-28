import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Classification.InverseTransposeAnalyticProof
import Langlands.Representation.Parabolic.InverseTransposeProductProof

/-!
# Reversed inverse-transpose Langlands data

Specialize the published analytic pullback and normalized-product transport
to genuine tempered Langlands data.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

/-- Rebundle two raw product actions before specializing their carriers. -/
private def productPullbackBundledEquiv
    {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
    {n : ℕ} (B C : GeneralLinear.BlockShape n)
    {V : Fin B.length → Type uV} {W : Fin C.length → Type uW}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (τ : ∀ i, Representation ℂ (GeneralLinear (C.size i) F.Carrier) (W i))
    (hσ : letI := T.topology; ∀ i, IsSmooth (σ i))
    (hτ : letI := T.topology; ∀ i, IsSmooth (τ i))
    (e : letI := T.topology
      Representation.Equiv ((T.normalizedProductInduced B σ).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
        (T.normalizedProductInduced C τ)) :
    letI := T.topology
    Representation.Equiv
      ((((T.normalizedProductInductionFunctor B).obj
        (fun i => SmoothRep.of (σ i) (hσ i))).representation).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (((T.normalizedProductInductionFunctor C).obj
        (fun i => SmoothRep.of (τ i) (hτ i))).representation) := e

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField.TopologicalData.TemperedLanglandsDatum

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n : ℕ} (d : TemperedLanglandsDatum.{uV, uF} T n)

/-- Reverse the original blocks, pull their actions back by inverse transpose,
and negate the corresponding real exponents. -/
def inverseTranspose : TemperedLanglandsDatum.{uV, uF} T n := by
  letI := T.topology
  refine
    { shape := d.shape.reverse
      blocks := fun i => SmoothRep.pullback
        (T.generalLinearInverseTranspose (d.shape.size i.rev)) (d.blocks i.rev)
      irreducible := ?_
      tempered := ?_
      exponent := fun i => -d.exponent i.rev
      strictAnti := Parabolic.reverseNegateStrictAnti _ _ d.strictAnti }
  · intro i
    exact (isIrreducible_comp_continuousMulEquiv_iff
      (d.blocks i.rev).representation
      (T.generalLinearInverseTranspose (d.shape.size i.rev))).mpr (d.irreducible i.rev)
  · intro i
    exact T.isTempered_comp_continuousMulEquiv (d.blocks i.rev).representation
      (T.generalLinearInverseTranspose (d.shape.size i.rev)) (d.tempered i.rev)

@[simp]
theorem inverseTranspose_shape : d.inverseTranspose.shape = d.shape.reverse := rfl

@[simp]
theorem inverseTranspose_blocks_representation (i : Fin d.shape.length) :
    letI := T.topology
    (d.inverseTranspose.blocks i).representation =
      (d.blocks i.rev).representation.comp
        (GeneralLinear.inverseTranspose (d.shape.size i.rev) F.Carrier).toMonoidHom := rfl

@[simp]
theorem inverseTranspose_exponent (i : Fin d.shape.length) :
    d.inverseTranspose.exponent i = -d.exponent i.rev := rfl

/-- Pullback of an original twisted block is the corresponding twisted block
of the reversed datum, through the identity on its original carrier. -/
def inverseTransposeTwistedBlockIso (i : Fin d.shape.length) :
    letI := T.topology
    SmoothRep.pullback (T.generalLinearInverseTranspose (d.shape.size i.rev))
        (T.twistedBlocks d.shape d.blocks d.exponent i.rev) ≅
      T.twistedBlocks d.inverseTranspose.shape d.inverseTranspose.blocks
        d.inverseTranspose.exponent i := by
  letI := T.topology
  apply SmoothRep.mkIso
  apply equivOfRepresentationEq
  exact Parabolic.inverseTransposeDeterminantTwist T (d.shape.size i.rev)
    (d.blocks i.rev) (d.blocks i.rev).representation (d.exponent i.rev)

/-- The actual normalized-product comparison underlying the two standard modules. -/
def inverseTransposeProductEquiv (hn : 0 < n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation.Equiv
      ((T.normalizedProductInduced d.shape
          (fun i => twist (T.determinantPowerCharacter (d.shape.size i) (d.exponent i))
            (d.blocks i).representation)).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedProductInduced d.shape.reverse (V := fun i => d.blocks i.rev)
        (fun i => twist (T.determinantPowerCharacter (d.shape.size i.rev)
            (-d.exponent i.rev))
          ((d.blocks i.rev).representation.comp
            (GeneralLinear.inverseTranspose (d.shape.size i.rev) F.Carrier).toMonoidHom))) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  have hfamily :
      (fun i : Fin d.shape.length =>
        (twist (T.determinantPowerCharacter (d.shape.size i.rev) (d.exponent i.rev))
          (d.blocks i.rev).representation).comp
          (GeneralLinear.inverseTranspose (d.shape.size i.rev) F.Carrier).toMonoidHom) =
      (fun i : Fin d.shape.length =>
        twist (T.determinantPowerCharacter (d.shape.size i.rev) (-d.exponent i.rev))
          ((d.blocks i.rev).representation.comp
            (GeneralLinear.inverseTranspose (d.shape.size i.rev) F.Carrier).toMonoidHom)) := by
    funext i
    exact Parabolic.inverseTransposeDeterminantTwist T (d.shape.size i.rev)
      (d.blocks i.rev) (d.blocks i.rev).representation (d.exponent i.rev)
  have E := Classical.choice (Parabolic.normalizedProductInverseTranspose T n hn d.shape
    (fun i => d.blocks i)
    (fun i => twist (T.determinantPowerCharacter (d.shape.size i) (d.exponent i))
            (d.blocks i).representation)
    (fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).isSmooth))
  let comparison (τ : ∀ i : Fin d.shape.reverse.length,
      Representation ℂ (GeneralLinear (d.shape.reverse.size i) F.Carrier)
        (d.blocks i.rev)) :=
    Representation.Equiv
      ((T.normalizedProductInduced d.shape
          (fun i => twist (T.determinantPowerCharacter (d.shape.size i) (d.exponent i))
            (d.blocks i).representation)).comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      (T.normalizedProductInduced d.shape.reverse τ)
  exact Eq.mp (congrArg comparison hfamily) E

/-- Compare the two genuine standard modules using their actual representations. -/
def inverseTransposeStandardModuleEquiv (hn : 0 < n) :
    letI := T.topology
    Representation.Equiv
      (d.standardModule.representation.comp
        (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom)
      d.inverseTranspose.standardModule.representation := by
  letI := T.topology
  let σ (i : Fin d.shape.length) :=
    twist (T.determinantPowerCharacter (d.shape.size i) (d.exponent i))
      (d.blocks i).representation
  let τ (i : Fin d.shape.reverse.length) :=
    twist (T.determinantPowerCharacter (d.shape.size i.rev) (-d.exponent i.rev))
      ((d.blocks i.rev).representation.comp
        (GeneralLinear.inverseTranspose (d.shape.size i.rev) F.Carrier).toMonoidHom)
  have hσ (i : Fin d.shape.length) : IsSmooth (σ i) :=
    (T.twistedBlocks d.shape d.blocks d.exponent i).isSmooth
  have hτ (i : Fin d.shape.reverse.length) : IsSmooth (τ i) :=
    (T.twistedBlocks d.inverseTranspose.shape d.inverseTranspose.blocks
      d.inverseTranspose.exponent i).isSmooth
  have E := productPullbackBundledEquiv T d.shape d.shape.reverse σ τ hσ hτ
    (d.inverseTransposeProductEquiv hn)
  have hA : (T.normalizedProductInductionFunctor d.shape).obj
      (fun i => SmoothRep.of (σ i) (hσ i)) = d.standardModule := by
    apply congrArg (T.normalizedProductInductionFunctor d.shape).obj
    rfl
  have hB : (T.normalizedProductInductionFunctor d.shape.reverse).obj
      (fun i => SmoothRep.of (τ i) (hτ i)) = d.inverseTranspose.standardModule := by
    apply congrArg (T.normalizedProductInductionFunctor d.shape.reverse).obj
    rfl
  let comparison (A B : SmoothRep.{0,uF,max uF uV} ℂ
      (GeneralLinear n F.Carrier)) :=
    Representation.Equiv (A.representation.comp
      (GeneralLinear.inverseTranspose n F.Carrier).toMonoidHom) B.representation
  exact Eq.mp (congrArg₂ comparison hA hB) E

end Langlands.PadicField.TopologicalData.TemperedLanglandsDatum
