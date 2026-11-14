import Langlands.Geometry.Building.RelativeDerivativeCartanExtension
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan
import Langlands.GroupScheme.Reductive.RootDatumExistence

/-! # Affine Cartan extensions on actual absolute Tits-index vertices -/

noncomputable section

universe u uA

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Geometry.Building

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AffineRootSystem
open GalleryGeometry

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
  [Algebra L (SeparableClosure k)] [IsScalarTower k L (SeparableClosure k)]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)
  {S : CommGroupScheme (Spec (CommRingCat.of L))}
  (hS : IsSplitTorus S.toGrp)
  {i : S.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k L)).obj G}
  (hi : IsMaximalTorus i)
  {A : Type uA} [AddTorsor (TranslationSpace i) A]
  {Ψ : Set (A →ᵃ[ℝ] ℝ)} (hΨ : IsAffineRootSystemWithRankZero Ψ)
  (hderiv : derivativeRoots Ψ = Set.range (rootForm i))

include hS hi hΨ hderiv

/-- Actual split maximal-torus data and transitive affine simple roots supply
an affine extension on the original absolute Tits-index vertices. -/
theorem exists_transitive_titsIndexCartanExtension
    {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hirr : IsIrreducibleRoots Ψ)
    (hmat : AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c)) :
    ∃ N : Matrix (Option d.Vertex) (Option d.Vertex) ℤ,
      (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N := by
  classical
  let Gext := (GroupScheme.baseChange (algebraBaseMap k L)).obj G
  have hGext := connectedReductiveFieldExtensionStatement k L G
    d.isSemisimple.isConnectedReductive
  let := hGext.smooth
  have := hi.2.1.mono
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence L Gext hGext S hS i hi
  let := hJ
  let := hred
  let b := d.splitMaximalTorusBase hS hi hP
  let e : d.Vertex ≃ b.support := d.splitMaximalTorusBaseEquiv hS hi hP
  obtain ⟨N, hblock, hdiag, hnonpos, hzero, ⟨m, hm, hker⟩, htr⟩ :=
    exists_transitive_integralCartanExtension i hS hΨ hderiv hP
      (hS.finite_relativeRoots i) hc hne hirr hmat hlift htrans b
  let f : Option d.Vertex ≃ Option b.support := e.optionCongr
  refine ⟨N.submatrix f f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a c
    change N (some (e a)) (some (e c)) = d.cartan a c
    exact (hblock (e a) (e c)).trans
      (d.cartanMatrix_splitMaximalTorusBaseEquiv hS hi hP a c)
  · intro a
    exact hdiag (f a)
  · intro a c hac
    exact hnonpos (f a) (f c) (fun h => hac (f.injective h))
  · intro a c
    exact hzero (f a) (f c)
  · refine ⟨m ∘ f, fun a => hm (f a), ?_⟩
    rw [Matrix.submatrix_vecMul_equiv]
    simp only [Function.comp_assoc, f.self_comp_symm, Function.comp_id]
    funext a
    exact congrFun hker (f a)
  · intro a c
    obtain ⟨σ, hσ, hσac⟩ := htr (f a) (f c)
    refine ⟨f.trans (σ.trans f.symm), ?_, ?_⟩
    · intro x y
      change N (f (f.symm (σ (f x)))) (f (f.symm (σ (f y)))) = N (f x) (f y)
      simpa only [f.apply_symm_apply] using hσ (f x) (f y)
    · change f.symm (σ (f a)) = c
      rw [hσac, f.symm_apply_apply]

/-- A chosen affine extension on the actual absolute Tits-index vertices. -/
def titsIndexCartanExtension
    {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hirr : IsIrreducibleRoots Ψ)
    (hmat : AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c)) :
    Matrix (Option d.Vertex) (Option d.Vertex) ℤ :=
  Classical.choose (exists_transitive_titsIndexCartanExtension
    d hS hi hΨ hderiv hc hne hirr hmat hlift htrans)

/-- The chosen matrix has the exact absolute Cartan block, generalized Cartan
entries, positive integral left-kernel marks and transitive vertices. -/
theorem titsIndexCartanExtension_spec
    {c : A} (hc : IsRegular Ψ c) (hne : Ψ.Nonempty)
    (hirr : IsIrreducibleRoots Ψ)
    (hmat : AffineCartan.IsVertexTransitive (chamberCartanMatrix Ψ (facet Ψ c)))
    (hlift : HasIndivisibleDerivativeLifts Ψ)
    (htrans : HasTransitiveSimpleRoots Ψ (facet Ψ c)) :
    let N := titsIndexCartanExtension d hS hi hΨ hderiv hc hne hirr hmat hlift htrans
    (∀ a b, N (some a) (some b) = d.cartan a b) ∧
      (∀ a, N a a = 2) ∧
      (∀ a b, a ≠ b → N a b ≤ 0) ∧
      (∀ a b, N a b = 0 ↔ N b a = 0) ∧
      (∃ m : Option d.Vertex → ℤ,
        (∀ a, 0 < m a) ∧ Matrix.vecMul m N = 0) ∧
      AffineCartan.IsVertexTransitive N :=
  Classical.choose_spec (exists_transitive_titsIndexCartanExtension
    d hS hi hΨ hderiv hc hne hirr hmat hlift htrans)

end Langlands.Geometry.Building
