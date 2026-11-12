import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsLocalLift
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing

/-!
# Rational points of algebraic spaces form a small type

The rational points `X(K)` of an algebraic space are sections of a presheaf with values in
`Type (u + 1)`. For a quasi-separated space with an affine étale atlas they form a `u`-small
type: every rational point lifts to the atlas over a finite field extension, which is a
quotient of a polynomial ring in finitely many variables, and the point is determined by the
lift because pullback along a nonzero finite free extension is injective.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap ringTestMap_comp)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace RingPointsSmall

variable {K : Type u} [Field K]

/-- The finitely generated algebras `K[x₁, …, xₙ]/I`, indexed by a `u`-small type. -/
abbrev Index (K : Type u) [Field K] : Type u := Σ n : ℕ, Ideal (MvPolynomial (Fin n) K)

/-- The algebra with a given index. -/
abbrev Alg (j : Index K) : Type u := MvPolynomial (Fin j.1) K ⧸ j.2

/-- **Smallness of rational points.** For a quasi-separated algebraic space over a field with
an affine étale surjective atlas, the type of rational points is `u`-small. -/
theorem small_ringPoints {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : IsQuasiSeparated X)
    {U : Over (Spec (CommRingCat.of K))} (a : (schemeYoneda _).obj U ⟶ X.presheaf)
    (ha : IsEtale a) (hs : IsSurjective a) [IsAffine U.left] :
    Small.{u} (RingPoints K X K) := by
  obtain ⟨D, hD⟩ := ProductPointsLocalLift.exists_fibre_point a hX ha hs
  have key : ∀ x : RingPoints K X K, ∃ c : Σ j : Index K, (ringTest K (Alg j) ⟶ U),
      Nontrivial (Alg c.1) ∧ FiniteDimensional K (Alg c.1) ∧
        (schemeYoneda _).map c.2 ≫ a =
          (schemeYoneda _).map (ringTestMap K (Algebra.ofId K (Alg c.1))) ≫
            uliftYonedaEquiv.symm x := by
    intro x
    obtain ⟨L, _, iκ, iC, iT, hL, -, -, ū, hū⟩ := hD K x
    have hCκ : iC = iκ := by
      apply Algebra.algebra_ext
      intro r
      exact @IsScalarTower.algebraMap_apply K K L _ _ _ _ iκ iC iT r
    subst hCκ
    have : Algebra.FiniteType K L := inferInstance
    obtain ⟨n, ψ, hψ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
    let e : Alg ⟨n, RingHom.ker ψ⟩ ≃ₐ[K] L := Ideal.quotientKerAlgEquivOfSurjective hψ
    refine ⟨⟨⟨n, RingHom.ker ψ⟩, ringTestMap K e.symm.toAlgHom ≫ ū⟩,
      e.symm.injective.nontrivial, LinearEquiv.finiteDimensional e.symm.toLinearEquiv, ?_⟩
    rw [Functor.map_comp, Category.assoc, hū, ← Functor.map_comp_assoc, ← ringTestMap_comp]
    congr 3
    exact Subsingleton.elim _ _
  choose code hcode using key
  refine small_of_injective (f := code) fun x y hxy ↦ ?_
  have hx := hcode x
  have hy := hcode y
  rw [← hxy] at hy
  obtain ⟨hN, hF, hx⟩ := hx
  have hb := Module.finBasis K (Alg (code x).1)
  have : NeZero (Module.finrank K (Alg (code x).1)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨h₁, h₂, h₃⟩ := ProductPointsDescent.spec_properties hb
  have : Flat (ringTestMap K (Algebra.ofId K (Alg (code x).1))).left := h₁
  have : LocallyOfFinitePresentation (ringTestMap K (Algebra.ofId K (Alg (code x).1))).left := h₂
  have : Surjective (ringTestMap K (Algebra.ofId K (Alg (code x).1))).left := h₃
  apply ProductPointsDescent.pullback_injective X (ringTestMap K (Algebra.ofId K (Alg (code x).1)))
  change RingPoints.changeRing (Algebra.ofId K (Alg (code x).1)) x =
    RingPoints.changeRing (Algebra.ofId K (Alg (code x).1)) y
  apply uliftYonedaEquiv.{u + 1}.symm.injective
  rw [ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing,
    ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing]
  exact hx.symm.trans hy.2.2

end RingPointsSmall

end Langlands.AlgebraicGeometry.AlgebraicSpace
