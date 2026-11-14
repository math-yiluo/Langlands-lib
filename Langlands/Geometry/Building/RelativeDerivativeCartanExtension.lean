import Langlands.Geometry.Building.RelativeDerivativeBaseComparison
import Langlands.Geometry.Building.AffineSimpleDerivativeCartan

/-! # Affine extensions of actual integral Cartan matrices -/

noncomputable section

universe u uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem
open GalleryGeometry

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (hS : IsSplitTorus S.toGrp) [Mono i.hom.hom.left]
  {A : Type uA} [AddTorsor (TranslationSpace i) A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
  (hderiv : derivativeRoots Ψ = Set.range (rootForm i))
  {J : Type*} {P : RootDatum J (characterLattice S) (cocharacterLattice S)}
  (hP : IsRootDatumOf i P) (hfinite : (relativeRoots i).Finite) [P.IsReduced]

include hS hΨ hderiv hP hfinite

/-- A nonempty irreducible actual derivative system with transitive simple
roots and indivisible lifts gives a vertex-transitive affine extension of the
Cartan matrix of any supplied integral simple base. -/
theorem exists_transitive_integralCartanExtension
    {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hirr : IsIrreducibleRoots Ψ)
    (hmat : AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c))
    (b : P.Base) :
    ∃ N : Matrix (Option b.support) (Option b.support) ℤ,
      (∀ a d, N (some a) (some d) = b.cartanMatrix a d) ∧
      (∀ a, N a a = 2) ∧
      (∀ a d, a ≠ d → N a d ≤ 0) ∧
      (∀ a d, N a d = 0 ↔ N d a = 0) ∧
      (∃ m : Option b.support → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N := by
  classical
  obtain ⟨δ, hδ⟩ :=
    IsAffineRootSystemWithRankZero.simpleAffineRoots_nonempty hΨ hc hne
  let δ' : simpleAffineRoots Ψ (facet Ψ c) := ⟨δ, hδ⟩
  have hdel := hΨ.isIntegralSimpleDerivativeDeletion_of_indivisible_lifts
    hc hirr hmat hlift δ'
  obtain ⟨B, hB⟩ := hΨ.hasSimpleDerivativeBaseAfterDeletion_of_transitive_simpleRoots
    hc hirr hmat hlift htrans δ'
  exact hΨ.exists_transitive_cartanExtension_of_simpleDerivativeBase
    hc δ' hdel B hB hmat b.cartanMatrix
    (integralDerivativeBaseEquiv i hS hΨ hderiv hP hfinite b B)
    (cartanMatrix_integralDerivativeBaseEquiv i hS hΨ hderiv hP hfinite b B)

/-- A chosen vertex-transitive affine extension of the exact integral
Cartan matrix of the supplied base. -/
def transitiveIntegralCartanExtension
    {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hirr : IsIrreducibleRoots Ψ)
    (hmat : AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c))
    (b : P.Base) :
    Matrix (Option b.support) (Option b.support) ℤ :=
  Classical.choose (exists_transitive_integralCartanExtension
    i hS hΨ hderiv hP hfinite hc hne hirr hmat hlift htrans b)

/-- The chosen extension has the original Cartan block, generalized Cartan
entries, strictly positive integral left-kernel marks and transitive indices. -/
theorem transitiveIntegralCartanExtension_spec
    {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hirr : IsIrreducibleRoots Ψ)
    (hmat : AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c))
    (b : P.Base) :
    let N := transitiveIntegralCartanExtension
      i hS hΨ hderiv hP hfinite hc hne hirr hmat hlift htrans b
    (∀ a d, N (some a) (some d) = b.cartanMatrix a d) ∧
      (∀ a, N a a = 2) ∧
      (∀ a d, a ≠ d → N a d ≤ 0) ∧
      (∀ a d, N a d = 0 ↔ N d a = 0) ∧
      (∃ m : Option b.support → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N :=
  Classical.choose_spec (exists_transitive_integralCartanExtension
    i hS hΨ hderiv hP hfinite hc hne hirr hmat hlift htrans b)

end Langlands.Geometry.Building
