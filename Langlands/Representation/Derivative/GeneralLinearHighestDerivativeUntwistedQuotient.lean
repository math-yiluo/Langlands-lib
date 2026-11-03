import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeConstituentQuotient
import Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistProof

/-! # Untwisted actual quotients of highest derivatives -/

noncomputable section

open CategoryTheory

namespace Langlands

universe uR uG uV uF

namespace SmoothRep

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- An inverse character twist cancels the original twist on the actual object. -/
def twistInverseCancelIso (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    (A : SmoothRep.{uR, uG, uV} R G) :
    (A.twist χ hχ).twist χ⁻¹ (isOpen_ker_inv hχ) ≅ A :=
  mkIso (equivOfRepresentationEq (twist_inv_twist χ A.representation))

/-- Move a source character twist to the inverse character on the target. -/
def untwistSourceHom (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    {A B : SmoothRep.{uR, uG, uV} R G} (f : A.twist χ hχ ⟶ B) :
    A ⟶ B.twist χ⁻¹ (isOpen_ker_inv hχ) :=
  (twistInverseCancelIso χ hχ A).inv ≫ (twistFunctor χ⁻¹ (isOpen_ker_inv hχ)).map f

/-- Untwisting the source preserves surjectivity of the actual underlying map. -/
theorem untwistSourceHom_surjective (χ : G →* Rˣ) (hχ : IsOpen (χ.ker : Set G))
    {A B : SmoothRep.{uR, uG, uV} R G} (f : A.twist χ hχ ⟶ B)
    (hf : Function.Surjective (hom f)) :
    Function.Surjective (hom (untwistSourceHom χ hχ f)) := hf

end SmoothRep

namespace InvariantBilinear

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An actual simple admissible subspace of `A`, and a quotient of `B` onto
its inverse-character-twisted smooth dual. -/
structure UntwistedConstituentDualQuotientData
    (A B : SmoothRep.{0, uG, uV} ℂ G)
    (χ : G →* ℂˣ) (hχ : IsOpen (χ.ker : Set G)) where
  constituent : Subrepresentation A.representation
  irreducible : (SmoothRep.subrepresentation A constituent).IsIrreducible
  admissible : (SmoothRep.subrepresentation A constituent).IsAdmissible
  quotient : B ⟶ (SmoothRep.subrepresentation A constituent).contragredient.twist
    χ⁻¹ (isOpen_ker_inv hχ)
  surjective : Function.Surjective (SmoothRep.hom quotient)

namespace UntwistedConstituentDualQuotientData

variable {A B : SmoothRep.{0, uG, uV} ℂ G}
  {χ : G →* ℂˣ} {hχ : IsOpen (χ.ker : Set G)}
  (w : UntwistedConstituentDualQuotientData A B χ hχ)

/-- The actual target of the retained quotient map. -/
abbrev target : SmoothRep.{0, uG, uV} ℂ G :=
  (SmoothRep.subrepresentation A w.constituent).contragredient.twist
    χ⁻¹ (isOpen_ker_inv hχ)

/-- The target is irreducible by admissible smooth duality and character twisting. -/
theorem target_irreducible (hG : CompactOpenCofinal G) : w.target.IsIrreducible :=
  (SmoothRep.isIrreducible_twist_iff _ _ _).mpr
    ((SmoothRep.isIrreducible_contragredient_iff hG _ w.admissible).mpr w.irreducible)

/-- The target remains admissible. -/
theorem target_admissible (hG : CompactOpenCofinal G) : w.target.IsAdmissible :=
  (SmoothRep.isAdmissible_twist_iff _ _ _).mpr
    ((SmoothRep.isAdmissible_contragredient_iff hG _).mpr w.admissible)

/-- The dual of the quotient target is the original constituent twisted by `χ`. -/
def targetDualIso (hG : CompactOpenCofinal G) :
    w.target.contragredient ≅
      (SmoothRep.subrepresentation A w.constituent).twist χ hχ := by
  let S := SmoothRep.subrepresentation A w.constituent
  have hχχ : χ⁻¹⁻¹ = χ := by
    ext g
    simp only [MonoidHom.inv_apply, inv_inv]
  have e : w.target.contragredient ≅ S.contragredient.contragredient.twist χ hχ := by
    simpa only [hχχ] using
      SmoothRep.contragredientTwistIso χ⁻¹ (isOpen_ker_inv hχ) S.contragredient
  exact e ≪≫ SmoothRep.twistIso χ hχ (SmoothRep.bidualIso hG S w.admissible).symm

end UntwistedConstituentDualQuotientData

end InvariantBilinear

namespace Derivative

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- Select an actual highest-derivative constituent and a quotient from the
same-order derivative of the untwisted smooth dual. -/
def chooseGeneralLinearHighestDerivativeUntwistedQuotient
    (N k : ℕ) (hk : 0 < k ∧ k ≤ N + 1) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (N + 1)
    letI := T.generalLinearTopologicalGroup (N + 1 - k)
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1) F.Carrier)),
      Nontrivial ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A) →
      ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A).HasFiniteLength →
      (∀ (j : ℕ) (hj : j ≤ N + 1), k < j →
        Subsingleton ((generalLinearDerivative T ψ (N + 1) j hj).obj A)) →
      InvariantBilinear.UntwistedConstituentDualQuotientData
        ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A)
        ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A.contragredient)
        (T.determinantPowerCharacter (N + 1 - k) 1)
        (T.isOpen_ker_determinantPowerCharacter (N + 1 - k) 1) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (N + 1)
  letI := T.generalLinearTopologicalGroup (N + 1 - k)
  intro A hA hfinite hhigh
  let B := A.contragredient.twist (T.determinantPowerCharacter (N + 1) 1)
    (T.isOpen_ker_determinantPowerCharacter (N + 1) 1)
  let w := chooseGeneralLinearHighestDerivativeConstituentQuotient T ψ N k hk A B
    (equivOfRepresentationEq rfl) hA hfinite hhigh
  let e := (DeterminantTwist.generalLinearDerivativeTwistIso T ψ 1 (N + 1) k hk.2).app
    A.contragredient
  let q : (generalLinearDerivative T ψ (N + 1) k hk.2).obj B ⟶
      (SmoothRep.subrepresentation
        ((generalLinearDerivative T ψ (N + 1) k hk.2).obj A) w.constituent).contragredient :=
    SmoothRep.ofHom w.quotient
  let f := e.inv ≫ q
  have hf : Function.Surjective (SmoothRep.hom f) :=
    w.surjective.comp (SmoothRep.equivOfIso e.symm).surjective
  exact {
    constituent := w.constituent
    irreducible := w.irreducible
    admissible := w.admissible
    quotient := SmoothRep.untwistSourceHom
      (T.determinantPowerCharacter (N + 1 - k) 1)
      (T.isOpen_ker_determinantPowerCharacter (N + 1 - k) 1) f
    surjective := SmoothRep.untwistSourceHom_surjective _ _ f hf }

end Derivative

end Langlands
