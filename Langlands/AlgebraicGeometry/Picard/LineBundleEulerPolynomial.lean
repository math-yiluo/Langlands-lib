import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomial
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof

/-! # Actual line-bundle Euler polynomials and the smooth relative degree bound -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

local instance (X : Scheme.{u}) :
    (Langlands.Scheme.Modules.structureSheaf X).IsQuasicoherent :=
  (Langlands.AlgebraicGeometry.Picard.LineBundle.trivial X).property.isQuasicoherent

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.Scheme.Modules

/-- The structure sheaf has finite sections on every affine open. -/
lemma hasFiniteAffineSections_structureSheaf (X : Scheme.{u}) :
    HasFiniteAffineSections (structureSheaf X) := by
  intro U
  exact inferInstanceAs (Module.Finite Γ(X, U.1) Γ(X, U.1))

/-- Actual locally free rank-one modules have finite affine sections. -/
lemma hasFiniteAffineSections_lineBundle {X : Scheme.{u}} (L : Picard.LineBundle X) :
    HasFiniteAffineSections L.obj := by
  exact ((hasFiniteAffineSections_structureSheaf X).tensor_lineBundle L.property).of_iso
    (tensorLeftUnitor L.obj)

end Langlands.AlgebraicGeometry.Modules

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules
  Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Every actual line-bundle power on a proper field scheme has finite cohomology. -/
lemma lineBundleTensorPow_hasFiniteCohomology (L : LineBundle X) (n : ℕ) :
    HasFiniteCohomology f (tensorPow L.obj n) := by
  let : (tensorPow L.obj n).IsQuasicoherent :=
    (tensorPow_isLocallyFreeRankOne X L n).isQuasicoherent
  exact hasFiniteCohomology_of_coherent f (tensorPow L.obj n)
    (hasFiniteAffineSections_lineBundle
      ⟨tensorPow L.obj n, tensorPow_isLocallyFreeRankOne X L n⟩)

/-- The actual Euler polynomial of a line bundle, with prescribed degree truncation. -/
def lineBundleEulerPolynomial (L : LineBundle X) (d : ℕ) : Polynomial ℚ :=
  coherentEulerPolynomial f (structureSheaf X) (hasFiniteAffineSections_structureSheaf X) L d

/-- Under the dimension bound, this polynomial evaluates to the actual Euler characteristic. -/
theorem lineBundleEulerPolynomial_eval [IsNoetherian X] [X.IsSeparated]
    (L : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d) (n : ℕ)
    (h : HasFiniteCohomology f (tensorPow L.obj n)) :
    (lineBundleEulerPolynomial f L d).eval (n : ℚ) =
      (eulerCharacteristic f (tensorPow L.obj n) h : ℚ) := by
  rw [lineBundleEulerPolynomial, coherentEulerPolynomial_eval f _ _ L d
    (HasSupportDimensionLT.of_topologicalKrullDim_le hX _)]
  change (eulerCharacteristic f (tensorObj (structureSheaf X) (tensorPow L.obj n)) _ : ℚ) = _
  exact congrArg (Int.cast : ℤ → ℚ)
    (eulerCharacteristic_eq_of_iso f _ h (tensorLeftUnitor (tensorPow L.obj n)))

/-- The prescribed truncation bounds the natural degree. -/
theorem lineBundleEulerPolynomial_natDegree_le (L : LineBundle X) (d : ℕ) :
    (lineBundleEulerPolynomial f L d).natDegree ≤ d :=
  coherentEulerPolynomial_natDegree_le f _ _ L d

/-- All actual line-bundle powers have a single Euler polynomial under a dimension bound. -/
theorem exists_lineBundleEulerPolynomial [IsNoetherian X] [X.IsSeparated]
    (L : LineBundle X) (d : ℕ) (hX : topologicalKrullDim X ≤ d) :
    ∃ (h : ∀ n : ℕ, HasFiniteCohomology f (tensorPow L.obj n)),
      ∃ P : Polynomial ℚ,
        (∀ n : ℕ, P.eval (n : ℚ) =
          (eulerCharacteristic f (tensorPow L.obj n) (h n) : ℚ)) ∧
        P.natDegree ≤ d := by
  refine ⟨lineBundleTensorPow_hasFiniteCohomology f L, lineBundleEulerPolynomial f L d,
    ?_, lineBundleEulerPolynomial_natDegree_le f L d⟩
  intro n
  exact lineBundleEulerPolynomial_eval f L d hX n _

/-- A smooth proper field scheme has the actual Euler polynomial of relative degree at most g. -/
theorem smoothProperLineBundleEulerPolynomial_degree_le (g : ℕ)
    (hs : SmoothOfRelativeDimension g f) (L : LineBundle X) :
    ∃ (h : ∀ n : ℕ, HasFiniteCohomology f (tensorPow L.obj n)),
      ∃ P : Polynomial ℚ,
        (∀ n : ℕ, P.eval (n : ℚ) =
          (eulerCharacteristic f (tensorPow L.obj n) (h n) : ℚ)) ∧
        P.natDegree ≤ g := by
  let : SmoothOfRelativeDimension g f := hs
  let : Smooth f := SmoothOfRelativeDimension.smooth g f
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  let : X.IsSeparated :=
    (HasAffineProperty.iff_of_isAffine (P := @IsSeparated) (f := f)).mp inferInstance
  exact exists_lineBundleEulerPolynomial f L g
    (fieldSmoothTopologicalKrullDim K X f g hs inferInstance)

end Langlands.AlgebraicGeometry.Picard
