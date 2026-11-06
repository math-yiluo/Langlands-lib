import Langlands.GroupScheme.TorsorCocycle
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.FieldTheory.Galois.Basic

/-! # Actual finite-Galois reduction of a cocycle to a torus -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cocycle

variable {K : Type u} [Field K]
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {U : Over (Spec (CommRingCat.of K))}

/-- A finite-Galois refinement and cochain making a cocycle take values in an actual
closed torus, with factorization required on every relative scheme-valued test. -/
structure TorusReduction (ξ : Cocycle G U) where
  carrier : Type u
  [field : Field carrier]
  [algebra : Algebra K carrier]
  [finiteDimensional : FiniteDimensional K carrier]
  [isGalois : IsGalois K carrier]
  refinement : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K carrier))) ⟶ U
  quasiCompact_refinement : QuasiCompact refinement.left
  flat_refinement : Flat refinement.left
  surjective_refinement : Surjective refinement.left
  cochain : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K carrier))) ⟶ G.X
  torus : GroupScheme (Spec (CommRingCat.of K))
  isTorus : IsTorus torus
  inclusion : torus ⟶ G
  isClosedSubgroup : IsClosedSubgroup inclusion
  factorization : ∀ {Z : Over (Spec (CommRingCat.of K))}
    (a b : Z ⟶ Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K carrier)))),
    ∃ t : Z ⟶ torus.X,
      t ≫ inclusion.hom.hom =
        (a ≫ cochain)⁻¹ * ξ.toFun (a ≫ refinement) (b ≫ refinement) * (b ≫ cochain)

attribute [instance] TorusReduction.field TorusReduction.algebra
  TorusReduction.finiteDimensional TorusReduction.isGalois

end Langlands.GroupScheme.Cocycle
