import Langlands.Galois.ClosureRestriction
import Langlands.Global.AdelicFunctoriality.Extension

/-! # Compatibility of Galois pullback with finite-place restriction -/

noncomputable section

universe uK uE uM uL uV

namespace Langlands.GaloisRepresentation

variable {K : Type uK} {E : Type uE} {M : Type uM} [Field K] [Field E] [Field M]
variable {L : Type uL} [Field L] [TopologicalSpace L]

/-- Successive pullbacks along field embeddings are equivalent to pullback along their
    composite. The comparison accounts for the chosen embeddings of algebraic closures. -/
def pullbackCompEquiv (f : K →+* E) (g : E →+* M) (A : Objects.{uK, uL, uV} K L) :
    FiniteRepresentation.Equiv (pullback g (pullback f A)).val (pullback (g.comp f) A).val := by
  letI : Algebra K E := f.toAlgebra
  letI : Algebra E M := g.toAlgebra
  letI : Algebra K M := (g.comp f).toAlgebra
  let ι := chosenClosureEmbedding f
  let κ := chosenClosureEmbedding g
  let θ : AlgebraicClosure K →ₐ[K] AlgebraicClosure M :=
    { toRingHom := κ.toRingHom.comp ι.toRingHom
      commutes' := fun x => by
        change κ (ι (algebraMap K (AlgebraicClosure K) x)) = algebraMap K (AlgebraicClosure M) x
        rw [ι.commutes]
        exact κ.commutes (f x) }
  have hRestriction :
      (restrictionAlongClosure θ).toMonoidHom =
        (Field.absoluteGaloisGroup.map f).toMonoidHom.comp
          (Field.absoluteGaloisGroup.map g).toMonoidHom := by
    apply MonoidHom.ext
    intro σ
    change restrictionAlongClosure θ σ =
      Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g σ)
    apply AlgEquiv.ext
    intro x
    apply θ.injective
    change θ (AlgEquiv.toRingEquiv (restrictionAlongClosure θ σ) x) =
      θ (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g σ)) x)
    rw [restrictionAlongClosure_commutes]
    change AlgEquiv.toRingEquiv σ (κ (ι x)) =
      κ (ι (AlgEquiv.toRingEquiv (restrictionAlongClosure ι (restrictionAlongClosure κ σ)) x))
    rw [restrictionAlongClosure_commutes ι, restrictionAlongClosure_commutes κ]
  change FiniteRepresentation.Equiv
    (FiniteRepresentation.of
      ((A.val.representation.comp (Field.absoluteGaloisGroup.map f).toMonoidHom).comp
        (Field.absoluteGaloisGroup.map g).toMonoidHom))
    (pullback (g.comp f) A).val
  rw [MonoidHom.comp_assoc, ← hRestriction, ← pullbackAlongClosure_chosen_eq (g.comp f)]
  exact pullbackAlongClosureEquiv (chosenClosureEmbedding (g.comp f)) θ A

open Langlands.Global
open Langlands.Global.AdelicFunctoriality.FiniteExtension

/-- Localizing the pullback of a global representation at a prime above `v` gives the
    pullback, along the actual completion embedding, of the local restriction at `v`. -/
def atFinitePlacePullbackEquiv [NumberField K] [NumberField E] [Algebra K E]
    (v : FinitePlace K) (w : FinitePlace E) [w.asIdeal.LiesOver v.asIdeal]
    (A : Objects.{uK, uL, uV} K L) :
    FiniteRepresentation.Equiv (atFinitePlace w (pullback (algebraMap K E) A)).val
      (pullback (completionMap v w) (atFinitePlace v A)).val := by
  have hSquare : (NumberField.FinitePlace.embedding w).comp (algebraMap K E) =
      (completionMap v w).comp (NumberField.FinitePlace.embedding v) := by
    apply RingHom.ext
    intro x
    exact (completionMap_coe v w x).symm
  let e := pullbackCompEquiv (algebraMap K E) (NumberField.FinitePlace.embedding w) A
  change FiniteRepresentation.Equiv (pullback (NumberField.FinitePlace.embedding w)
    (pullback (algebraMap K E) A)).val
    (pullback (completionMap v w) (pullback (NumberField.FinitePlace.embedding v) A)).val
  rw [hSquare] at e
  exact e.trans (pullbackCompEquiv (NumberField.FinitePlace.embedding v) (completionMap v w) A).symm

/-- Pullback of an actual global Galois representation commutes up to equivalence
    with restriction at an actual finite place above the base place. -/
def FinitePlacePullbackComparisonStatement : Prop :=
  ∀ (K : Type uK) (E : Type uE) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (L : Type uL) [Field L] [TopologicalSpace L] (v : FinitePlace K) (w : FinitePlace E)
    [w.asIdeal.LiesOver v.asIdeal] (A : Objects.{uK, uL, uV} K L),
    Nonempty (FiniteRepresentation.Equiv (atFinitePlace w (pullback (algebraMap K E) A)).val
      (pullback (completionMap v w) (atFinitePlace v A)).val)

theorem finitePlacePullbackComparison :
    FinitePlacePullbackComparisonStatement.{uK, uE, uL, uV} := by
  intro K E _ _ _ _ _ L _ _ v w _ A
  exact ⟨atFinitePlacePullbackEquiv v w A⟩

end Langlands.GaloisRepresentation
