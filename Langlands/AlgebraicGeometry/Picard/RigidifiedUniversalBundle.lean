import Langlands.AlgebraicGeometry.Picard.RigidifiedClassPresheaf
import Mathlib.CategoryTheory.Yoneda

/-! # Universal rigidified line bundles -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.SchemeModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- The isomorphism class of an actual relative rigidified line bundle. -/
def classOf {T : Over S} (L : relative f ε section_eq T) :
    Classes f ε section_eq T :=
  Quotient.mk _ L

/-- The map on families induced by pulling back a specified rigidified line bundle. -/
def classifyingMap {P : Over S} (L : relative f ε section_eq P) (T : Over S) :
    (T ⟶ P) → Classes f ε section_eq T :=
  fun h ↦ classesPullback f ε section_eq h (classOf f ε section_eq L)

lemma classifyingMap_eq_iff {P T : Over S}
    (L : relative f ε section_eq P) (M : relative f ε section_eq T) (h : T ⟶ P) :
    classifyingMap f ε section_eq L T h = classOf f ε section_eq M ↔
      Nonempty ((relativePullback f ε section_eq h).obj L ≅ M) :=
  Quotient.eq

/-- A specified rigidified bundle is universal when its actual pullback map is bijective
on isomorphism classes for every test scheme over the base. -/
def IsUniversal {P : Over S} (L : relative f ε section_eq P) : Prop :=
  ∀ T : Over S, Function.Bijective (classifyingMap f ε section_eq L T)

lemma isUniversal_iff {P : Over S} (L : relative f ε section_eq P) :
    IsUniversal f ε section_eq L ↔
      ∀ (T : Over S) (M : relative f ε section_eq T),
        ∃! h : T ⟶ P, Nonempty ((relativePullback f ε section_eq h).obj L ≅ M) := by
  constructor
  · intro h T M
    simpa only [classifyingMap_eq_iff] using
      (h T).existsUnique (classOf f ε section_eq M)
  · intro h T
    apply (Function.bijective_iff_existsUnique _).mpr
    intro q
    refine Quotient.inductionOn q (fun M ↦ ?_)
    change ∃! a, classifyingMap f ε section_eq L T a = classOf f ε section_eq M
    simpa only [classifyingMap_eq_iff] using h T M

/-- The classification equivalence supplied by the universal property. -/
def classifyingEquiv {P : Over S} (L : relative f ε section_eq P)
    (hL : IsUniversal f ε section_eq L) (T : Over S) :
    (T ⟶ P) ≃ Classes f ε section_eq T :=
  Equiv.ofBijective _ (hL T)

variable (coherence : RigidifiedModule.PullbackCoherenceStatement.{u})

include coherence in
lemma classifyingMap_comp {P T U : Over S} (L : relative f ε section_eq P)
    (h : T ⟶ U) (k : U ⟶ P) :
    classifyingMap f ε section_eq L T (h ≫ k) =
      classesPullback f ε section_eq h (classifyingMap f ε section_eq L U k) := by
  exact congrArg (fun m ↦ m (classOf f ε section_eq L))
    ((classPresheaf coherence f ε section_eq).map_comp k.op h.op)

include coherence in
lemma classifyingMap_id {P : Over S} (L : relative f ε section_eq P) :
    classifyingMap f ε section_eq L P (𝟙 P) = classOf f ε section_eq L := by
  exact congrArg (fun m ↦ m (classOf f ε section_eq L))
    ((classPresheaf coherence f ε section_eq).map_id (op P))

/-- A universal rigidified bundle gives a representation of the actual class presheaf. -/
def representableBy {P : Over S} (L : relative f ε section_eq P)
    (hL : IsUniversal f ε section_eq L) :
    (classPresheaf coherence f ε section_eq).RepresentableBy P where
  homEquiv := classifyingEquiv f ε section_eq L hL _
  homEquiv_comp h k := classifyingMap_comp f ε section_eq coherence L h k

/-- The canonical comparison of two schemes equipped with universal rigidified bundles. -/
def comparisonIso {P Q : Over S}
    (L : relative f ε section_eq P) (M : relative f ε section_eq Q)
    (hL : IsUniversal f ε section_eq L) (hM : IsUniversal f ε section_eq M) : P ≅ Q :=
  (representableBy f ε section_eq coherence L hL).uniqueUpToIso
    (representableBy f ε section_eq coherence M hM)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
