import Langlands.Geometry.Building.RelativeDerivativeRootPairing
import Langlands.Geometry.Building.AffineIrreducibleDerivativeRoots
import Langlands.GroupScheme.Rational.RelativeRootSystemIrreducibleStatement

/-!
# Irreducible affine roots from an irreducible relative root system

`IsIrreducibleRelativeRootSystem i` says that every rational root pairing on the span of the
relative roots of a split torus `i : T ⟶ G`, with evaluation as pairing and with exactly the
relative roots as roots, is irreducible. For an almost-simple `G` and a maximal split torus with
a relative root, this is the content of the published statement
`RelativeRootSystemIrreducibleStatement` (Borel–Tits 1965, Corollary 5.11).

For an actual affine root system `Ψ` on an affine space under `TranslationSpace i` whose
derivative roots are exactly the forms `rootForm i α` of the relative roots, irreducibility of the
relative root system makes `Ψ` nonempty and irreducible (KP Definition 1.3.13), and makes the full
derivative root pairing of `Ψ` irreducible.
-/

noncomputable section

universe u uA

open CategoryTheory AlgebraicGeometry Module
open Langlands.LinearAlgebra.RationalSpan

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The relative root system of `i : T ⟶ G` is irreducible: every rational root pairing on the
rational span of the relative roots, with coroots in its rational dual, whose pairing is
evaluation and whose roots are exactly the images `1 ⊗ α` of the relative roots `α`, is
irreducible in Mathlib's sense `RootPairing.IsIrreducible`. -/
def IsIrreducibleRelativeRootSystem (i : T.toGrp ⟶ G) : Prop :=
  ∀ (J : Type u)
    (P : RootPairing J ℚ (relativeRootSpan i) (Module.Dual ℚ (relativeRootSpan i))),
    P.toLinearMap = Module.Dual.eval ℚ (relativeRootSpan i) →
    Subtype.val '' Set.range P.root = toRat '' relativeRoots i →
    P.IsIrreducible

/-- Under the published statement `RelativeRootSystemIrreducibleStatement` (Borel–Tits 1965,
Corollary 5.11), the relative root system of a maximal split torus of an almost-simple group with
at least one relative root is irreducible. -/
theorem isIrreducibleRelativeRootSystem_of_isAlmostSimple
    (hirr : RelativeRootSystemIrreducibleStatement.{u}) (hG : IsAlmostSimple G)
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i) (hne : (relativeRoots i).Nonempty) :
    IsIrreducibleRelativeRootSystem i :=
  hirr k G hG T i hi hne

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G}
  {A : Type uA} [AddTorsor (TranslationSpace i) A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- If the derivative roots of an affine root system `Ψ` are the forms of the relative roots of
`i` and `Ψ` is nonempty, then `i` has a relative root. -/
theorem relativeRoots_nonempty_of_derivativeRoots_eq
    (hderiv : derivativeRoots Ψ = Set.range (rootForm i)) (hne : Ψ.Nonempty) :
    (relativeRoots i).Nonempty := by
  obtain ⟨ψ, hψ⟩ := hne
  have h : ψ.linear ∈ Set.range (rootForm i) := hderiv ▸ linear_mem_derivativeRoots hψ
  obtain ⟨α, -⟩ := h
  exact ⟨α.val, α.property⟩

/-- If the derivative roots of an affine root system `Ψ` are exactly the forms of the relative
roots of a split torus `i` and the relative root system of `i` is irreducible, then `Ψ` is
nonempty and irreducible (KP Definition 1.3.13). -/
theorem IsIrreducibleRelativeRootSystem.nonempty_and_isIrreducibleRoots
    (h : IsIrreducibleRelativeRootSystem i) (hS : IsSplitTorus S.toGrp)
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hderiv : derivativeRoots Ψ = Set.range (rootForm i)) :
    Ψ.Nonempty ∧ IsIrreducibleRoots Ψ := by
  have hP := h (derivativeRoots Ψ) (relativeDerivativePairing i hS hΨ hderiv)
    (relativeDerivativePairing_toLinearMap i hS hΨ hderiv)
    (relativeDerivativePairing_root_image i hS hΨ hderiv)
  refine (hΨ.isIrreducible_iff_isIrreducibleRoots_of_equiv
    (relativeDerivativePairing i hS hΨ hderiv) (Equiv.refl _) fun a b => ?_).mp hP
  rw [relativeDerivativePairing_pairing, Equiv.refl_apply, Equiv.refl_apply,
    ← hΨ.rationalDerivativePairing_pairing]
  exact (map_eq_zero_iff _ (algebraMap ℚ ℝ).injective).symm

/-- Under the same hypotheses, the finite root pairing of derivatives of `Ψ` is irreducible. -/
theorem IsIrreducibleRelativeRootSystem.isIrreducible_derivativePairing
    (h : IsIrreducibleRelativeRootSystem i) (hS : IsSplitTorus S.toGrp)
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hderiv : derivativeRoots Ψ = Set.range (rootForm i)) :
    hΨ.derivativePairing.IsIrreducible := by
  obtain ⟨hne, hirr⟩ :=
    IsIrreducibleRelativeRootSystem.nonempty_and_isIrreducibleRoots h hS hΨ hderiv
  exact (hΨ.isIrreducible_iff_isIrreducibleRoots hne).mpr hirr

/-- Under `RelativeRootSystemIrreducibleStatement` (Borel–Tits 1965, Corollary 5.11): if `G` is
almost simple, `i` is a maximal split torus with a relative root, and the derivative roots of the
affine root system `Ψ` are exactly the forms of the relative roots of `i`, then `Ψ` is nonempty
and irreducible (KP Definition 1.3.13). -/
theorem nonempty_and_isIrreducibleRoots_of_isAlmostSimple
    (hstmt : RelativeRootSystemIrreducibleStatement.{u}) (hG : IsAlmostSimple G)
    (hi : IsMaximalSplitTorus i) (hne : (relativeRoots i).Nonempty)
    (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hderiv : derivativeRoots Ψ = Set.range (rootForm i)) :
    Ψ.Nonempty ∧ IsIrreducibleRoots Ψ :=
  IsIrreducibleRelativeRootSystem.nonempty_and_isIrreducibleRoots
    (isIrreducibleRelativeRootSystem_of_isAlmostSimple hstmt hG hi hne) hi.isSplitSubtorus.1 hΨ
    hderiv

/-- Variant of `nonempty_and_isIrreducibleRoots_of_isAlmostSimple` assuming `Ψ` nonempty instead
of a relative root: then `Ψ` is irreducible. -/
theorem isIrreducibleRoots_of_isAlmostSimple
    (hstmt : RelativeRootSystemIrreducibleStatement.{u}) (hG : IsAlmostSimple G)
    (hi : IsMaximalSplitTorus i) (hΨ : IsAffineRootSystemWithRankZero Ψ)
    (hderiv : derivativeRoots Ψ = Set.range (rootForm i)) (hne : Ψ.Nonempty) :
    IsIrreducibleRoots Ψ :=
  (nonempty_and_isIrreducibleRoots_of_isAlmostSimple hstmt hG hi
    (relativeRoots_nonempty_of_derivativeRoots_eq hderiv hne) hΨ hderiv).2

end Langlands.Geometry.Building
