import Langlands.GroupScheme.Torus.HomFamilyRigidity
import Langlands.GroupScheme.Torus.DiagonalizableRigidityStatement

/-! # Natural homomorphism families and diagonalizable rigidity -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomFamily

variable {S : Scheme.{u}} {G H : GroupScheme S} {X : Over S}
    {F : ∀ T : Over S, (T ⟶ X) → (T ⟶ G.X) → (T ⟶ H.X)}

/-- The morphism represented by a natural family, evaluated at the universal pair. -/
def hom (F : ∀ T : Over S, (T ⟶ X) → (T ⟶ G.X) → (T ⟶ H.X)) :
    X ⊗ G.X ⟶ H.X :=
  F (X ⊗ G.X) (fst X G.X) (snd X G.X)

/-- Evaluation of the representing morphism recovers the original natural family. -/
theorem comp_hom (hF : IsHomFamily F) {T : Over S} (x : T ⟶ X) (g : T ⟶ G.X) :
    lift x g ≫ hom F = F T x g := by
  have h := hF.naturality (lift x g) (fst X G.X) (snd X G.X)
  simpa only [hom, lift_fst, lift_snd] using h.symm

/-- The scheme-morphism form of diagonalizable rigidity implies its all-test natural-family
form, with no representability hypothesis on the supplied family. -/
theorem eq_of_diagonalizableRigidity (hRig : DiagonalizableRigidityStatement.{u})
    {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (Λ Λ' : Type u) [AddCommGroup Λ] [AddCommGroup Λ']
    (hΛ : AddGroup.FG Λ) (hΛ' : AddGroup.FG Λ')
    (eG : Nonempty (G ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp))
    (eH : Nonempty (H ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ').toGrp))
    {X : Over (Spec (CommRingCat.of k))}
    (hft : LocallyOfFiniteType X.hom) (hqc : QuasiCompact X.hom)
    (hconn : ConnectedSpace X.left)
    {F : ∀ T : Over (Spec (CommRingCat.of k)), (T ⟶ X) → (T ⟶ G.X) → (T ⟶ H.X)}
    (hF : IsHomFamily F) (x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
    (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (g : T ⟶ G.X) :
    F T x g = F T (toUnit T ≫ x₀) g := by
  have hmul : ∀ (T : Over (Spec (CommRingCat.of k))) (x : T ⟶ X) (g g' : T ⟶ G.X),
      lift x (g * g') ≫ hom F = (lift x g ≫ hom F) * (lift x g' ≫ hom F) := by
    intro T x g g'
    rw [comp_hom hF, comp_hom hF, comp_hom hF, hF.map_mul]
  simpa only [comp_hom hF] using
    hRig k G H Λ Λ' hΛ hΛ' eG eH X hft hqc hconn (hom F) hmul x₀ T x g

end Langlands.GroupScheme.HomFamily
