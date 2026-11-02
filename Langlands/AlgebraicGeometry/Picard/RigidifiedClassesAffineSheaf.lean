import Langlands.AlgebraicGeometry.Picard.RigidifiedClassDescentEffective

/-! # Conditional affine flat sheaf condition for rigidified classes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

open Langlands.Scheme.Modules Langlands.SchemeModule.RigidifiedModule

variable {S X : Scheme.{u}} (f : X ⟶ S) (ε : S ⟶ X)
  (section_eq : ε ≫ f = 𝟙 S)

/-- A chosen global rigidified bundle for compatible local data on an affine flat cover. -/
def affineFlatAmalgamation
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {T U : Over S} (h : U ⟶ T) [IsAffineHom h.left] [Flat h.left] [Surjective h.left]
    (L : relative f ε section_eq U)
    (compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
      Nonempty ((relativePullback f ε section_eq a).obj L ≅
        (relativePullback f ε section_eq b).obj L)) :
    relative f ε section_eq T :=
  (exists_rigidified_of_descent f ε section_eq h L hD2 unique compat).choose

/-- The chosen amalgamation restricts to the original local rigidified bundle. -/
lemma affineFlatAmalgamation_pullback
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {T U : Over S} (h : U ⟶ T) [IsAffineHom h.left] [Flat h.left] [Surjective h.left]
    (L : relative f ε section_eq U)
    (compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
      Nonempty ((relativePullback f ε section_eq a).obj L ≅
        (relativePullback f ε section_eq b).obj L)) :
    Nonempty ((relativePullback f ε section_eq h).obj
      (affineFlatAmalgamation f ε section_eq hD2 unique h L compat) ≅ L) :=
  (exists_rigidified_of_descent f ε section_eq h L hD2 unique compat).choose_spec

/-- Ordinary descent of line bundles and their isomorphisms gives the singleton
sheaf condition for actual rigidified classes along affine flat surjections. -/
lemma classPresheaf_isSheafFor_affineFlat
    (hD1 : LineBundleIsoDescentStatement.{u})
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {T U : Over S} (h : U ⟶ T) [IsAffineHom h.left] [Flat h.left] [Surjective h.left] :
    Presieve.IsSheafFor (classPresheaf pullbackCoherence f ε section_eq) (.singleton h) := by
  apply Presieve.isSheafFor_singleton.mpr
  intro q hq
  induction q using Quotient.inductionOn with
  | h L =>
    have compat : ∀ (W : Over S) (a b : W ⟶ U), a ≫ h = b ≫ h →
        Nonempty ((relativePullback f ε section_eq a).obj L ≅
          (relativePullback f ε section_eq b).obj L) :=
      fun W a b hab ↦ Quotient.exact (hq a b hab)
    let M := affineFlatAmalgamation f ε section_eq hD2 unique h L compat
    obtain ⟨e⟩ := affineFlatAmalgamation_pullback f ε section_eq hD2 unique h L compat
    have he : classesPullback f ε section_eq h (classOf f ε section_eq M) =
        classOf f ε section_eq L := Quotient.sound ⟨e⟩
    refine ⟨classOf f ε section_eq M, he, fun q' hq' ↦ ?_⟩
    exact classes_flatSeparated_of_isoDescent f ε section_eq hD1 unique h q'
      (classOf f ε section_eq M) (hq'.trans he.symm)

/-- The affine-ring singleton condition used by the fppf site criterion. -/
lemma classPresheaf_isSheafFor_affine
    (hD1 : LineBundleIsoDescentStatement.{u})
    (hD2 : LineBundleDescentEffectiveStatement.{u})
    (unique : ∀ (T : Over S) (L M : relative f ε section_eq T), Subsingleton (L ≅ M))
    {R R' : CommRingCat.{u}} (φ : R ⟶ R')
    (hf : Flat (Spec.map φ)) (hs : Surjective (Spec.map φ)) (s : Spec R ⟶ S) :
    Presieve.IsSheafFor (classPresheaf pullbackCoherence f ε section_eq)
      (.singleton (Over.homMk (Spec.map φ) :
        Over.mk (Spec.map φ ≫ s) ⟶ Over.mk s)) := by
  refine @classPresheaf_isSheafFor_affineFlat _ _ f ε section_eq hD1 hD2 unique
    _ _ _ ?_ hf hs
  exact isAffineHom_of_isAffine (Spec.map φ)

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
