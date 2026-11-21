import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting
import Langlands.GroupScheme.Rational.NumberFieldScalarEvenSpinHasse
import Langlands.GroupScheme.SimplyConnected.ClassicalTypeDSpinPresentationProof
import Langlands.GroupScheme.OrthogonalInnerForm.QuadraticTransport

/-! # Type D Hasse kernels when the vector vertex is distinguished -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix

namespace Langlands.GroupScheme

open Quaternionic OrthogonalInnerForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

section DimensionOne

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D]

/-- A spin presentation over a one-dimensional division algebra is covered by
  the scalar even spin Hasse kernel. -/
theorem numberFieldSpinCoverHasse_of_finrank_one (n : ℕ) (hn : 3 ≤ n)
    (hD : Module.finrank F D = 1) (σ : FirstKindInvolution F D)
    (q : σ.QuadraticForms (Fin (2 * n))) (hq : σ.IsNondegenerateQuadratic q)
    {G : GroupScheme (Spec (CommRingCat.of F))} (π : G ⟶ σ.isometryGroup q)
    (hπ : σ.IsSpinCover q π)
    {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (ξ : Cocycle G (GaloisCocycle.cover F L)) (hξ : ξ.LocallyTrivial) : ξ.IsTrivial := by
  let j := Langlands.Algebra.CentralSimple.algEquivOfFinrankEqOne hD
  have hσ (a : D) : σ a = a := by
    obtain ⟨k, rfl⟩ := j.surjective a
    exact σ.map_algebraMap k
  let I := Fin (2 * n)
  let τ := FirstKindInvolution.scalar F
  let φ : Matrix I I D ≃ₐ[F] Matrix I I F := j.symm.mapMatrix
  have hm (x : Matrix I I D) : φ (σ.matrix I x) = τ.matrix I (φ x) := by
    ext i k
    change j.symm (σ (x k i)) = τ (j.symm (x k i))
    rw [hσ, FirstKindInvolution.scalar_apply]
  let Q : Matrix I I D := Quotient.out q
  let q' : τ.QuadraticForms I := Submodule.Quotient.mk (φ Q * 1)
  let E : σ.isometryGroup q ≅ τ.isometryGroup q' :=
    isometryCutAlgEquivIso (σ.matrix I) τ φ 1 (τ.matrix I).map_one isUnit_one
      (fun x => by simpa only [mul_one, one_mul] using hm x) Q
  have hq' : τ.IsNondegenerateQuadratic q' := by
    change IsUnit (τ.polar (Submodule.Quotient.mk (φ Q * 1)))
    rw [mul_one, FirstKindInvolution.polar_mk, ← hm, ← _root_.map_add]
    have hQ : IsUnit (σ.polar (Submodule.Quotient.mk Q : σ.QuadraticForms I)) := by
      rw [show (Submodule.Quotient.mk Q : σ.QuadraticForms I) = q from Quotient.out_eq q]
      exact hq
    exact hQ.map φ.toMonoidHom
  obtain ⟨hs, _⟩ := ordinaryOrthogonalGeometry F n hn q' hq'
  let : Smooth (τ.isometryGroup q').X.hom := hs
  let : Smooth (σ.isometryGroup q).X.hom := hπ.smooth
  obtain ⟨p, hp, hcomp⟩ := hπ.exists_centralIsogeny
  let E₀ := IdentityComponent.mapIso E
  have hπ' : τ.IsSpinCover q' (π ≫ E.hom) := by
    refine ⟨hπ.isSimplyConnected, hs, p ≫ E₀.hom, hp.comp_iso E₀, ?_⟩
    rw [Category.assoc, IdentityComponent.mapIso_hom_identityComponentι, ← Category.assoc, hcomp]
  exact numberFieldScalarEvenSpinHasse F n hn q' hq' G (π ≫ E.hom) hπ' L ξ hξ

end DimensionOne

/-- The Hasse kernel of actual numbered type D groups with the nonfork vertices
  fixed by the star action and the vector vertex distinguished. -/
def NumberFieldTypeDVectorVertexHasseStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G) (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n → IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    (∀ (σ : SeparableClosure F ≃ₐ[F] SeparableClosure F) (a : d.Vertex),
      (e a).val + 2 < n → d.star σ a = a) →
    (∃ a : d.Vertex, (e a).val = 0 ∧ a ∈ d.distinguishedVertices) →
    ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
      (ξ : Cocycle G (GaloisCocycle.cover F L)), ξ.LocallyTrivial → ξ.IsTrivial

/-- A distinguished vector vertex forces the division degree in the spin
  presentation to be one. -/
theorem numberFieldTypeDVectorVertexHasse : NumberFieldTypeDVectorVertexHasseStatement.{u} := by
  intro F _ _ G _ _ d n e hn hsc habs hcart hstar hvec L _ _ _ _ ξ hξ
  obtain ⟨D, _, _, _, _, deg, m, hdeg, hD, hm, σ, _, q, hq, _, hmark, π, hπ⟩ :=
    classicalTypeDSpinPresentation F G d n e hn hsc habs hcart hstar
  obtain ⟨a, ha, ham⟩ := hvec
  obtain ⟨j, hj, _, hd⟩ := (hmark a (by omega)).mp ham
  have hd' : j * deg = 1 := by omega
  have hdeg' : deg = 1 := Nat.dvd_one.mp ⟨j, (hd'.symm.trans (mul_comm j deg))⟩
  subst deg
  simp only [mul_one] at hm
  subst m
  exact numberFieldSpinCoverHasse_of_finrank_one n (by omega) (by simpa using hD) σ q hq π hπ ξ hξ

end Langlands.GroupScheme
