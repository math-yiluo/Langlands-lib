import Langlands.AlgebraicGeometry.Picard.RigidifiedUniversalBundle
import Langlands.AlgebraicGeometry.Picard.RigidifiedTrivialPullback

/-! # Triviality from a universal family and rigidity of parameter maps -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- The canonical trivial relative rigidified line bundle. -/
abbrev relativeTrivial (T : Over S) : relative f ε section_eq T :=
  trivial ((relativeSection f ε section_eq).app T)

lemma classesPullback_trivial {T U : Over S} (h : T ⟶ U) :
    classesPullback f ε section_eq h
        (classOf f ε section_eq (relativeTrivial f ε section_eq U)) =
      classOf f ε section_eq (relativeTrivial f ε section_eq T) :=
  Quotient.sound ⟨pullbackTrivialIso ((relativeSpace f).map h) h.left _⟩

variable {P : Over S} (L : relative f ε section_eq P)
  (hL : IsUniversal f ε section_eq L)

/-- The parameter morphism of an actual relative rigidified bundle. -/
def classifyFamily {T : Over S} (M : relative f ε section_eq T) : T ⟶ P :=
  (classifyingEquiv f ε section_eq L hL T).symm (classOf f ε section_eq M)

lemma classifyFamily_spec {T : Over S} (M : relative f ε section_eq T) :
    classifyingMap f ε section_eq L T (classifyFamily f ε section_eq L hL M) =
      classOf f ε section_eq M :=
  (classifyingEquiv f ε section_eq L hL T).apply_symm_apply _

lemma classifyFamily_pullback {T U : Over S} (h : T ⟶ U)
    (M : relative f ε section_eq U) :
    classifyFamily f ε section_eq L hL ((relativePullback f ε section_eq h).obj M) =
      h ≫ classifyFamily f ε section_eq L hL M := by
  apply (hL T).injective
  rw [classifyFamily_spec,
    classifyingMap_comp f ε section_eq RigidifiedModule.pullbackCoherence,
    classifyFamily_spec]
  rfl

/-- The section of the parameter scheme classifying the trivial family. -/
def trivialParameter : Over.mk (𝟙 S) ⟶ P :=
  classifyFamily f ε section_eq L hL
    (relativeTrivial f ε section_eq (Over.mk (𝟙 S)))

lemma classifyFamily_trivial (T : Over S) :
    classifyFamily f ε section_eq L hL (relativeTrivial f ε section_eq T) =
      Over.mkIdTerminal.from T ≫ trivialParameter f ε section_eq L hL := by
  apply (hL T).injective
  rw [classifyFamily_spec,
    classifyingMap_comp f ε section_eq RigidifiedModule.pullbackCoherence]
  change _ = classesPullback f ε section_eq (Over.mkIdTerminal.from T)
    (classifyingMap f ε section_eq L (Over.mk (𝟙 S))
      (classifyFamily f ε section_eq L hL
        (relativeTrivial f ε section_eq (Over.mk (𝟙 S)))))
  rw [classifyFamily_spec, classesPullback_trivial]

lemma classifyFamily_eq_of_iso {T : Over S} {M N : relative f ε section_eq T}
    (e : M ≅ N) :
    classifyFamily f ε section_eq L hL M =
      classifyFamily f ε section_eq L hL N := by
  exact congrArg (classifyingEquiv f ε section_eq L hL T).symm
    (Quotient.sound ⟨e⟩)

/-- Recover an actual rigidified isomorphism from equality of parameter morphisms. -/
def isoOfClassifyFamilyEq {T : Over S} (M N : relative f ε section_eq T)
    (h : classifyFamily f ε section_eq L hL M =
      classifyFamily f ε section_eq L hL N) : M ≅ N :=
  Classical.choice (Quotient.exact
    ((classifyingEquiv f ε section_eq L hL T).symm.injective h))

/-- A universal classifier turns trivial restrictions along two maps and
rigidity of the parameter morphism into an actual rigidified trivialization. -/
def trivialIsoOfTwoRestrictions {T A B : Over S} (a : A ⟶ T) (b : B ⟶ T)
    (rigidity : ∀ g : T ⟶ P,
      a ≫ g = Over.mkIdTerminal.from A ≫ trivialParameter f ε section_eq L hL →
      b ≫ g = Over.mkIdTerminal.from B ≫ trivialParameter f ε section_eq L hL →
      g = Over.mkIdTerminal.from T ≫ trivialParameter f ε section_eq L hL)
    (M : relative f ε section_eq T)
    (ha : (relativePullback f ε section_eq a).obj M ≅ relativeTrivial f ε section_eq A)
    (hb : (relativePullback f ε section_eq b).obj M ≅ relativeTrivial f ε section_eq B) :
    M ≅ relativeTrivial f ε section_eq T := by
  apply isoOfClassifyFamilyEq f ε section_eq L hL
  rw [classifyFamily_trivial]
  apply rigidity
  · rw [← classifyFamily_pullback]
    calc
      _ = classifyFamily f ε section_eq L hL (relativeTrivial f ε section_eq A) :=
        classifyFamily_eq_of_iso f ε section_eq L hL ha
      _ = _ := classifyFamily_trivial f ε section_eq L hL A
  · rw [← classifyFamily_pullback]
    calc
      _ = classifyFamily f ε section_eq L hL (relativeTrivial f ε section_eq B) :=
        classifyFamily_eq_of_iso f ε section_eq L hL hb
      _ = _ := classifyFamily_trivial f ε section_eq L hL B

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
