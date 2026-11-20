import Langlands.Algebra.BrauerComparison.EvenLocalSplitting
import Langlands.Algebra.DivisionSplittingDegree
import Langlands.Algebra.LocalReducedCharpolyNeighborhood
import Langlands.Algebra.NumberFieldBrauerFiniteSupport
import Langlands.Global.Arithmetic.QuadraticCompletionDegrees
import Langlands.GroupScheme.SimplyConnected.LocalCocycleVanishingGaloisReduction

/-! # Quadratic splitting of number-field Brauer two-torsion -/

noncomputable section

open CategoryTheory NumberField IsDedekindDomain
open scoped TensorProduct Langlands.Global.AdelicFunctoriality.FiniteExtension

universe u

namespace Langlands.BrauerComparison

open Langlands.Brauer Langlands.CentralSimple Langlands.ReducedNorm

private theorem isSplit_baseChange_of_even {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (L : Type u) [Field L] [Algebra F.Carrier L] [FiniteDimensional F.Carrier L]
    (A : CSA.{u, u} F.Carrier) (hA : 2 • classOf A = 0)
    (hL : 2 ∣ Module.finrank F.Carrier L) : IsSplit (baseChange L A) := by
  let K := F.Carrier
  let B := baseChange L A
  let T := finiteGaloisSplittingField L B
  let : Algebra K T := Algebra.compHom T (algebraMap K L)
  let : IsScalarTower K L T := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K T := Module.Finite.trans L T
  let : CharZero K := Algebra.charZero_of_charZero (Padic p) K
  obtain ⟨M, hfin, hgal, ⟨j⟩⟩ := Langlands.GroupScheme.exists_finite_galois_algHom K T
  let : Algebra T M := j.toRingHom.toAlgebra
  let : IsScalarTower K T M := IsScalarTower.of_algHom j
  let i : L →ₐ[K] M := j.comp (IsScalarTower.toAlgHom K L T)
  let : Algebra L M := i.toRingHom.toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algHom i
  let : IsScalarTower L T M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  let : IsGalois L M := IsGalois.tower_top_of_isGalois K L M
  let e := (baseChangeTowerEquiv L M A).symm.trans
    (extendSplittingChart (finiteGaloisSplittingChart L B) M)
  have hd : reducedDegree L B = reducedDegree K A := reducedDegree_baseChange K A L
  let f := e.trans (Matrix.reindexAlgEquiv M M (finCongr hd))
  exact isSplit_baseChange_of_even_local_degree F L M A f hA hL

end Langlands.BrauerComparison

namespace Langlands.Brauer

open Langlands.BrauerComparison Langlands.CentralSimple
open Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

/-- Brauer classes killed by two over a number field have a quadratic splitting field. -/
def NumberFieldBrauerTwoTorsionStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (A : CSA.{u, u} F), 2 • classOf A = 0 →
    ∃ (E : Type u) (_ : Field E) (_ : Algebra F E) (_ : FiniteDimensional F E),
      Module.finrank F E = 2 ∧ IsSplit (baseChange E A)

/-- Prescribe even local degrees at the nonsplit finite places, then use Brauer locality. -/
theorem numberFieldBrauerTwoTorsion : NumberFieldBrauerTwoTorsionStatement.{u} := by
  intro F _ _ A hA
  classical
  let S := (finite_nonsplitFinitePlaces A).toFinset
  obtain ⟨E, _, _, _, _, hE, hEC, hloc⟩ := Langlands.Global.quadraticCompletionDegrees F S
  let : IsTotallyComplex E := hEC
  refine ⟨E, inferInstance, inferInstance, inferInstance, hE, ?_⟩
  apply numberFieldBrauerSplitting E (baseChange E A)
  · intro w
    let v := placeBelow F w
    let : w.asIdeal.LiesOver v.asIdeal := liesOver_placeBelow F w
    let K := v.adicCompletion F
    let M := w.adicCompletion E
    let : FiniteDimensional K M := FiniteExtension.local_finite v w
    have hK : 2 • classOf (baseChange K A) = 0 := by
      rw [← scalarExtension_classOf, ← map_nsmul, hA, map_zero]
    have hM : IsSplit (baseChange M (baseChange K A)) := by
      by_cases hv : v ∈ S
      · exact isSplit_baseChange_of_even (padicField v) M (baseChange K A) hK (hloc v hv w)
      · have hv' : v ∉ nonsplitFinitePlaces A := by
          simpa only [S, Set.Finite.mem_toFinset] using hv
        exact (Classical.not_not.mp hv').baseChange M
    obtain ⟨n, hn, ⟨e⟩⟩ := hM
    exact ⟨n, hn, ⟨(baseChangeTowerEquiv E M A).trans
      ((baseChangeTowerEquiv K M A).symm.trans e)⟩⟩
  · intro w
    let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
    let : IsAlgClosed w.Completion := ⟨fun f => Polynomial.Splits.of_splits_map
      e.toRingHom (IsAlgClosed.splits _) (fun x _ => e.surjective x)⟩
    exact isSplit_of_isAlgClosed (baseChange w.Completion (baseChange E A))

/-- A number-field central division algebra isomorphic to its opposite has degree one or two. -/
theorem numberField_division_reducedDegree_eq_one_or_two_of_equiv_opposite
    (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (f : D ≃ₐ[F] Dᵐᵒᵖ) :
    reducedDegree F D = 1 ∨ reducedDegree F D = 2 := by
  let A : CSA.{u, u} F := { toAlgCat := AlgCat.of F D }
  have hf := two_nsmul_classOf_eq_zero_of_equiv_opposite (A := A) f
  obtain ⟨E, _, _, _, hE, n, hn, ⟨e⟩⟩ := numberFieldBrauerTwoTorsion F A hf
  have h := division_splitting_size_dvd_field_degree hn
    (show E ⊗[F] D ≃ₐ[E] Matrix (Fin n) (Fin n) E from e)
  rw [hE, matrix_size_eq_reducedDegree F D E n e] at h
  exact (Nat.dvd_prime Nat.prime_two).mp h

end Langlands.Brauer
