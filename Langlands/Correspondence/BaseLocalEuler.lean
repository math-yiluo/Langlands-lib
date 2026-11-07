import Langlands.Correspondence.BlockPairEpsilon
import Langlands.Correspondence.BaseReciprocityCoherence
import Langlands.LocalFactor.WeilDeligneTransport
import Langlands.LocalField.CanonicalTransport
import Langlands.Representation.Category.UniverseLift
import Langlands.Weil.Representation.InductionContinuity
import Langlands.WeilDeligne.BlockEquivalences
import Langlands.Weil.Local.AssemblyProof
import Langlands.Correspondence.RankOneArithmeticLFactor

/-!
# Restriction of local pairs to the bottom intermediate field

The bottom intermediate field `⊥` of the common closure has the residue
cardinality of `F`, and its Weil group is the local Weil group. Restricting a
local pair to `⊥` preserves the Euler polynomial on `(ker N)^I`, at any supplied
geometric Frobenius over `⊥`. Restrictions of uncentered blocks and of twisted
zero-monodromy pairs are the corresponding pairs over `⊥`, after lifting the
carrier universe.
-/

noncomputable section

universe uK uG uH uV uW uX uY uF uP

namespace Langlands.WeilDeligneRepresentation

open scoped TensorProduct

variable {K : Type uK} {G : Type uG} {H : Type uH} [Field K] [Group G] [Group H]
  {ν : G →* Kˣ}

/-- Restriction commutes with tensor products; the underlying map is the identity. -/
def restrictTensorEquiv (φ : H →* G) (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) :
    Equiv (restrict φ (tensor A B)) (tensor (restrict φ A) (restrict φ B)) where
  representationEquiv := Representation.Equiv.mk (LinearEquiv.refl K _) (fun _ => rfl)
  comm_monodromy := rfl

/-- Restriction of an uncentered block is the block of the restriction, for the
pulled-back character; the underlying map is the identity. -/
def restrictBlockEquiv (φ : H →* G) (A : FiniteRepresentation.{uK, uG, uV} K G) (m : ℕ) :
    Equiv (restrict φ (block ν A m)) (block (ν.comp φ) (FiniteRepresentation.restrict φ A) m) where
  representationEquiv := Representation.Equiv.mk (LinearEquiv.refl K _) (fun _ => rfl)
  comm_monodromy := rfl

/-- Restriction commutes with duals; the underlying map is the identity. -/
def restrictDualEquiv (φ : H →* G) (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    Equiv (restrict φ (dual A)) (dual (restrict φ A)) where
  representationEquiv := Representation.Equiv.mk (LinearEquiv.refl K _) (fun h => by
    apply LinearMap.ext
    intro ℓ
    change (A.representation.dual (φ h)) ℓ = Representation.dual (A.representation.comp φ) h ℓ
    rw [Representation.dual_apply, Representation.dual_apply, MonoidHom.comp_apply, map_inv φ h])
  comm_monodromy := rfl

end Langlands.WeilDeligneRepresentation

namespace Langlands.Correspondence

open Weil.Local LocalFactor LocalFactor.CommonClosure LocalFactor.CommonClosureWeilDeligne
  LocalFactor.CommonClosureGamma LocalFactor.PairBlock

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The bottom intermediate field has the residue cardinality of `F`, by the
actual `ℚ_p`-algebra isomorphism `F ≃ ⊥`. -/
theorem baseResidueCardinality_eq :
    (fieldData F (baseExtension F)).residueCardinality =
      F.canonicalTopologicalData.residueCardinality := by
  let _ := ((baseExtension F).asPadicField (p := p)).algebra
  exact PadicField.CanonicalTransport.residueCardinality_eq F _
    (AlgEquiv.ofRingEquiv
      (f := (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.toRingEquiv)
      (fun x => (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.commutes
        (algebraMap (Padic p) F.Carrier x)))

theorem baseResidueCardinality_real :
    residueCardinality F (baseExtension F) = (F.canonicalTopologicalData.residueCardinality : ℝ) := by
  change ((fieldData F (baseExtension F)).residueCardinality : ℝ) = _
  rw [baseResidueCardinality_eq]

/-- The published local geometric Frobenius, as a geometric Frobenius over the
bottom intermediate field. -/
def baseGeometricFrobenius : GeometricFrobenius F (baseExtension F) :=
  ⟨baseWeilEquiv F (localGeometricFrobenius F), by
    apply Units.ext
    change (localNormCharacter F (localGeometricFrobenius F) : ℂ) =
      (((residueCardinalityUnit (fieldData F (baseExtension F)))⁻¹ : ℂˣ) : ℂ)
    rw [localNormCharacter_geometricFrobenius, Units.val_inv_eq_inv_val,
      residueCardinalityUnit_val, baseResidueCardinality_eq]⟩

/-- The Euler polynomial over the bottom field of a pair equivalent to the
restriction of a local pair `B₀` is the local Euler polynomial of `B₀`, at the
local inertia and the published geometric Frobenius. -/
theorem eulerPolynomial_base_of_equiv (B₀ : LocalWeilDeligneRepresentation.{uF, uP} F)
    (A : Pair.{uF, uV} F (baseExtension F))
    (f : WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B₀) A)
    (Φ : GeometricFrobenius F (baseExtension F)) :
    WeilDeligne.eulerPolynomial A (inertia F (baseExtension F)) Φ.val =
      WeilDeligne.eulerPolynomial B₀ (localInertia F) (localGeometricFrobenius F) := by
  rw [eulerPolynomial_eq_of_frobenius F _ A (baseGeometricFrobenius F) Φ]
  refine (WeilDeligne.eulerPolynomial_eq_of_equiv (inertia F (baseExtension F)) f _).symm.trans ?_
  exact WeilDeligne.Transport.eulerPolynomial_restrict (baseWeilEquiv F).symm.toMulEquiv B₀
    (localInertia F) (baseGeometricFrobenius F).val

/-- The dual form of `eulerPolynomial_base_of_equiv`. -/
theorem eulerPolynomial_dual_base_of_equiv (B₀ : LocalWeilDeligneRepresentation.{uF, uP} F)
    (A : Pair.{uF, uV} F (baseExtension F))
    (f : WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B₀) A)
    (Φ : GeometricFrobenius F (baseExtension F)) :
    WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A)
        (inertia F (baseExtension F)) Φ.val =
      WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual B₀) (localInertia F)
        (localGeometricFrobenius F) :=
  eulerPolynomial_base_of_equiv F (WeilDeligneRepresentation.dual B₀)
    (WeilDeligneRepresentation.dual A)
    ((WeilDeligneRepresentation.restrictDualEquiv _ B₀).trans
      (WeilDeligneRepresentation.dualEquiv f.symm)) Φ

/-- The restriction of a local Weil representation to the bottom field, with
carrier lifted to the universe of common-closure pairs. -/
def baseLift (B : LocalWeilRepresentation.{uF, uP} F) :
    FiniteRepresentation.{0, uF, max uF uP} ℂ (weilSubgroup F (baseExtension F)) :=
  FiniteRepresentation.of (universeLiftRepresentation.{uF}
    (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B).representation)

/-- The universe lift is equivalent to the restriction. -/
def baseLiftEquiv (B : LocalWeilRepresentation.{uF, uP} F) :
    FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B)
      (baseLift F B) :=
  universeLiftEquiv _

theorem baseLift_isContinuous {B : LocalWeilRepresentation.{uF, uP} F} (hB : B.IsContinuous) :
    (baseLift F B).IsContinuous :=
  (FiniteRepresentation.isContinuous_iff_of_equiv (baseLiftEquiv F B)).mp
    (FiniteRepresentation.isContinuous_restrict _ continuous_subtype_val hB)

/-- A representative of an irreducible Weil class is continuous. -/
theorem isContinuous_of_classOf_eq {n : ℕ+} {σ : IrreducibleWeilClass.{uF, uP} F n}
    {B : LocalWeilRepresentation.{uF, uP} F}
    (hB : FiniteRepresentation.classOf B = weilClassForget F σ) : B.IsContinuous := by
  obtain ⟨c, hc⟩ := σ
  induction c using Quotient.inductionOn with
  | h C =>
    obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff B C.val).mp hB
    exact (FiniteRepresentation.isContinuous_iff_of_equiv e).mpr C.property.1

/-- The restriction of an uncentered local block to the bottom field is the
block over the bottom field of the lifted restriction. -/
def restrictBlockBaseEquiv (B : LocalWeilRepresentation.{uF, uP} F) (m : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom B m))
      (WeilDeligneRepresentation.block (normCharacter F (baseExtension F)).toMonoidHom
        (baseLift F B) m) :=
  (WeilDeligneRepresentation.restrictBlockEquiv _ B m).trans
    (WeilDeligneRepresentation.Blocks.blockEquivAcross (baseLiftEquiv F B) m)

/-- The restriction of the zero-monodromy pair of `ω^k B` to the bottom field is
the twisted factor of the lifted restriction. -/
def restrictTwistedBaseEquiv (B : LocalWeilRepresentation.{uF, uP} F) (k : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom
          (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ k) B)))
      (twistedFactor F (baseExtension F) (baseLift F B) k) := by
  rw [twistedFactor_eq_zeroMonodromy]
  exact WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv _ rfl rfl
    (Representation.Equiv.mk ULift.moduleEquiv.symm (fun g => LinearMap.ext fun v => rfl))

/-- The restriction of the zero-monodromy pair of `B` is the twisted factor with
exponent zero. -/
def restrictZeroBaseEquiv (B : LocalWeilRepresentation.{uF, uP} F) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B))
      (twistedFactor F (baseExtension F) (baseLift F B) 0) := by
  let e : FiniteRepresentation.Equiv B
      (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ 0) B) :=
    ((FiniteRepresentation.twistEquivOfEq (pow_zero (localNormCharacter F).toMonoidHom) B).trans
      (FiniteRepresentation.twistOneEquiv B)).symm
  let e' : FiniteRepresentation.Equiv
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype B)
      (FiniteRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ 0) B)) :=
    FiniteRepresentation.restrictEquiv _ e
  exact (WeilDeligneRepresentation.zeroMonodromyEquivOfEquiv
    (A := WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
      (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B))
    (B := WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
      (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom
        (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ 0) B)))
    _ rfl rfl e').trans (restrictTwistedBaseEquiv F B 0)

/-- The restriction of `ω^k B ⊗ B'` with zero monodromy is the twisted factor of
the tensor of the lifted restrictions. -/
def restrictTwistedPairBaseEquiv (B B' : LocalWeilRepresentation.{uF, uP} F) (k : ℕ) :
    WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.restrict (weilSubgroup F (baseExtension F)).subtype
        (WeilDeligneRepresentation.tensor
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom
            (FiniteRepresentation.twist ((localNormCharacter F).toMonoidHom ^ k) B))
          (WeilDeligneRepresentation.zeroMonodromy (localNormCharacter F).toMonoidHom B')))
      (twistedFactor F (baseExtension F)
        (FiniteRepresentation.tensor (baseLift F B) (baseLift F B')) k) :=
  ((WeilDeligneRepresentation.restrictTensorEquiv _ _ _).trans
    (WeilDeligneRepresentation.tensorCongr (restrictTwistedBaseEquiv F B k)
      (restrictZeroBaseEquiv F B'))).trans
    (twistedPairEquiv F (baseExtension F) (baseLift F B) (baseLift F B') k 0)

end Langlands.Correspondence
