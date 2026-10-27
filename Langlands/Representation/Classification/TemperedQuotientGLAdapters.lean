import Langlands.Representation.Classification.TemperedQuotientAux
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Classification.OppositeJacquetReciprocity
import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Induction.OppositeProductReversalProof

/-! # GL adapters for the independent tempered quotient argument -/

noncomputable section

namespace Langlands.Classification

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable (T : F.TopologicalData)
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- The actual bidual pullback map for an irreducible smooth GL representation,
using automatic admissibility to invert its canonical bidual evaluation. -/
def glSmoothDualQuotientMap (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible →
      ∀ (σ : Representation ℂ (GeneralLinear n F.Carrier) W),
        π.contragredient.representation.IntertwiningMap σ →
          (smoothContragredient σ).IntertwiningMap π.representation := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ σ a
  exact smoothDualPullbackToOriginal π.isSmooth
    ⟨smoothBidual_injective_of_compact_cofinal
        (GeneralLinear.compactOpen_cofinal F T n) π.representation π.isSmooth,
      smoothBidual_surjective_of_compact_cofinal
        (GeneralLinear.compactOpen_cofinal F T n) π.representation
        ((CuspidalSupport.cuspidalEmbedding F T n π hπ).1)⟩ a

/-- The explicitly defined GL bidual pullback is surjective when its input map
is nonzero and the auxiliary representation is smooth. -/
theorem glSmoothDualQuotientMap_surjective (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier))
      (hπ : π.IsIrreducible)
      (σ : Representation ℂ (GeneralLinear n F.Carrier) W),
      IsSmooth σ →
      ∀ a : π.contragredient.representation.IntertwiningMap σ, a ≠ 0 →
        Function.Surjective (glSmoothDualQuotientMap F T n π hπ σ a) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ σ hσ a ha
  let := hπ
  exact smoothDualPullbackToOriginal_surjective π.isSmooth hσ _
    (smoothBidual_injective_of_compact_cofinal
      (GeneralLinear.compactOpen_cofinal F T n) σ hσ) a ha

/-- Automatic admissibility removes the admissibility premise from the generic
dual-map adapter for an actual irreducible smooth GL representation. -/
theorem gl_exists_surjective_from_smoothDual (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible →
      ∀ (σ : Representation ℂ (GeneralLinear n F.Carrier) W),
        IsSmooth σ →
        ∀ a : π.contragredient.representation.IntertwiningMap σ, a ≠ 0 →
          ∃ q : (smoothContragredient σ).IntertwiningMap π.representation,
            Function.Surjective q := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ σ hσ a ha
  exact ⟨glSmoothDualQuotientMap F T n π hπ σ a,
    glSmoothDualQuotientMap_surjective F T n π hπ σ hσ a ha⟩

/-- The action used by opposite reciprocity is the actual bundled action used
in maximal-cone selection, with exactly the same inverse full modulus. -/
theorem oppositeJacquet_action_eq (n : ℕ) (B : GeneralLinear.BlockShape n)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear n F.Carrier) V) :
    OppositeSupport.jacquetAction T B ρ =
      (CuspidalJacquetMultiplicity.oppositeJacquet T B (Rep.of ρ)).ρ := rfl

/-- A nonzero opposite-Jacquet map of the smooth dual gives a quotient of the
smooth dual of opposite induction onto the original GL representation. -/
theorem gl_exists_surjective_from_oppositeInductionDual (n : ℕ)
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible →
      ∀ (σ : Representation ℂ (B.Levi F.Carrier) W)
        (A : (CuspidalJacquetMultiplicity.oppositeJacquet T B
          (Rep.of π.contragredient.representation)).ρ.IntertwiningMap σ),
        A ≠ 0 →
          ∃ q : (smoothContragredient
              (T.normalizedOppositeParabolicInduced B σ)).IntertwiningMap
                π.representation,
            Function.Surjective q := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ σ A hA
  exact gl_exists_surjective_from_smoothDual F T n π hπ
    (T.normalizedOppositeParabolicInduced B σ)
    (T.isSmooth_normalizedOppositeParabolicInduced B σ)
    (OppositeSupport.fromJacquet T B π.contragredient.representation σ
      π.contragredient.isSmooth A)
    (OppositeSupport.fromJacquet_ne_zero T B π.contragredient.representation σ
      π.contragredient.isSmooth A hA)

/-- Block reversal converts the opposite-induced embedding into an upper-product
embedding before dualizing; the quotient still targets the original input. -/
theorem gl_exists_surjective_from_reversedProductDual (n : ℕ)
    (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ (π : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      π.IsIrreducible →
      ∀ (V : Fin B.length → Type uW) [hadd : ∀ i, AddCommGroup (V i)]
        [hmod : ∀ i, Module ℂ (V i)]
        (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
        (∀ i, IsSmooth (σ i)) →
        ∀ (A : (CuspidalJacquetMultiplicity.oppositeJacquet T B
          (Rep.of π.contragredient.representation)).ρ.IntertwiningMap (B.blockTensor σ)),
          A ≠ 0 →
          letI : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) :=
            fun i => hadd i.rev
          letI : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) :=
            fun i => hmod i.rev
          ∃ q : (smoothContragredient (T.normalizedProductInduced B.reverse
              (V := fun i => V i.rev) (fun i => σ i.rev))).IntertwiningMap
                π.representation,
            Function.Surjective q := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro π hπ V hadd hmod σ hσ A hA
  let : ∀ i : Fin B.reverse.length, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin B.reverse.length, Module ℂ (V i.rev) := fun i => hmod i.rev
  obtain ⟨E, _, _⟩ := glOppositeProductReversal p F T n B V σ hσ
  let a := OppositeSupport.fromJacquet T B π.contragredient.representation
    (B.blockTensor σ) π.contragredient.isSmooth A
  have ha : a ≠ 0 := OppositeSupport.fromJacquet_ne_zero T B
    π.contragredient.representation (B.blockTensor σ) π.contragredient.isSmooth A hA
  apply gl_exists_surjective_from_smoothDual F T n π hπ
    (T.normalizedProductInduced B.reverse (V := fun i => V i.rev) (fun i => σ i.rev))
    (T.isSmooth_normalizedProductInduced B.reverse (fun i => σ i.rev))
    (E.toIntertwiningMap.comp a)
  intro hz
  apply ha
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro v
  apply E.injective
  change E (a v) = E 0
  have hv := congrArg
    (fun f : π.contragredient.representation.IntertwiningMap
      (T.normalizedProductInduced B.reverse (V := fun i => V i.rev)
        (fun i => σ i.rev)) => f v) hz
  change E (a v) = 0 at hv
  simpa only [map_zero] using hv

end Langlands.Classification
