import Langlands.GroupScheme.LocalGroupIso
import Langlands.GroupScheme.SpecialLinear
import Langlands.GroupScheme.Reductive.TitsIndex
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# A diagonal special-linear presentation of type-A groups over a finite Galois cover

This module states that a simply connected absolutely almost-simple group whose
actual Cartan pairings are numbered as type `A_n` becomes `SL_(n+1)` over a finite
Galois extension, through a local isomorphism whose Galois discrepancies are
explicit matrix automorphisms, inner or composed with inverse transpose according
to the actual star action, and which carries the maximal split torus into the
diagonal torus with explicit weights. The statement is not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SpecialLinearTitsCocycle

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

/-- The spectrum of `L`, as a scheme over `Spec K`. -/
abbrev cover : Over (Spec (CommRingCat.of K)) := Over.mk (algebraBaseMap K L)

/-- The automorphism `Spec σ` of the cover attached to `σ ∈ Aut_K(L)`. -/
def coverAut (σ : L ≃ₐ[K] L) : cover K L ⟶ cover K L :=
  Over.homMk (galoisBaseMap K L σ) (galoisBaseMap_over K L σ)

variable {K L}

/-- The coefficient map `L → Γ(Z, 𝒪_Z)` of a point `a : Z ⟶ Spec L` over `Spec K`. -/
def coefficients {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L) :
    L →+* Γ(Z.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of L)).inv ≫ a.left.appTop).hom

/-- The Galois discrepancy of a local isomorphism `E : SL_(n+1) → G` over `Spec L` at a
point `a : Z ⟶ Spec L`: the matrix `h` with `E(a ≫ Spec σ) g = E(a) h`. -/
def discrepancy {G : GroupScheme (Spec (CommRingCat.of K))} {n : ℕ}
    (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
      (cover K L))
    (σ : L ≃ₐ[K] L) {Z : Over (Spec (CommRingCat.of K))} (a : Z ⟶ cover K L)
    (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
    Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) :=
  SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
    ((E.toFun a).symm (E.toFun (a ≫ coverAut K L σ)
      ((SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z).symm g)))

end SpecialLinearTitsCocycle

open SpecialLinearTitsCocycle

/-- For a simply connected absolutely almost-simple group with an actual type-`A_n`
numbering `e` of its simple vertices, there are a finite Galois extension `L/K`
embedded in the separable closure by `ι₀`, a local isomorphism `E` from `SL_(n+1)` to
`G` over `Spec L`, matrices `x σ ∈ GL_(n+1)(L)` and characters `χ i` of the maximal
split torus such that:

* for `σ ∈ Gal(L/K)` lifted by `τ`, and every point `a : Z ⟶ Spec L`, the matrix
  `h` with `E(a ≫ Spec σ) g = E(a) h` is `X g X⁻¹` when the star action of `τ` is
  trivial and `X (g⁻¹)ᵀ X⁻¹` when it moves some vertex, where `X` is the image of
  `x σ` under the coefficient map of `a`;
* `E(a)` carries the diagonal matrix with entries `χ i (s)` to the point `s` of the
  maximal split torus;
* the restriction of the simple root numbered `i` is `χ i - χ (i + 1)`. -/
def SpecialLinearTitsCocycleStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) →
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : IsGalois K L) (ι₀ : L →ₐ[K] SeparableClosure K)
      (E : LocalGroupIso (SpecialLinear.groupScheme (Fin (n + 1)) (CommRingCat.of K)) G
        (cover K L))
      (x : (L ≃ₐ[K] L) → Matrix.GeneralLinearGroup (Fin (n + 1)) L)
      (χ : Fin (n + 1) → characterLattice d.splitTorus),
      (∀ (σ : L ≃ₐ[K] L) (τ : SeparableClosure K ≃ₐ[K] SeparableClosure K),
        (∀ y, τ (ι₀ y) = ι₀ (σ y)) →
        ∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
          (g : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)),
          ((∀ v, d.star τ v = v) →
            (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
              (Matrix.GeneralLinearGroup.map (coefficients a) (x σ) :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
                (g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
                (Matrix.GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤))) ∧
          ((∃ v, d.star τ v ≠ v) →
            (discrepancy E σ a g : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
              (Matrix.GeneralLinearGroup.map (coefficients a) (x σ) :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) *
                ((g⁻¹ : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤)) :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)).transpose *
                (Matrix.GeneralLinearGroup.map (coefficients a) (x σ)⁻¹ :
                  Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)))) ∧
      (∀ (Z : Over (Spec (CommRingCat.of K))) (a : Z ⟶ cover K L)
          (s : Z ⟶ d.splitTorus.X),
        (SpecialLinear.pointsEquiv (Fin (n + 1)) (CommRingCat.of K) Z
            ((E.toFun a).symm (s ≫ d.splitInclusion.hom.hom)) :
            Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) =
          Matrix.diagonal fun i =>
            ((Gm.pointsEquiv _ Z (s ≫ (CommGroupScheme.groupHom (χ i)).hom.hom) :
              Γ(Z.left, ⊤)ˣ) : Γ(Z.left, ⊤))) ∧
      ∀ i : Fin n, d.rootRestriction (e.symm i).val = χ i.castSucc - χ i.succ

end Langlands.GroupScheme
