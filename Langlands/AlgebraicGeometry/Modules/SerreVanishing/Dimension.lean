import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.KrullDimension.Polynomial
import Langlands.AlgebraicGeometry.FieldSmoothTopologicalKrullDimProof

/-! # A finite dimension bound for a finite-type scheme over a field -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

namespace Langlands.AlgebraicGeometry.Modules.SerreVanishing

/-- The topological Krull dimension is bounded by a natural number. -/
def FiniteTopologicalDimension (X : Scheme.{u}) : Prop :=
  ∃ n : ℕ, topologicalKrullDim X ≤ n

/-- A finite-type field algebra is a quotient of a polynomial ring in finitely many variables. -/
theorem exists_ringKrullDim_le (k : Type u) [Field k]
    (A : Type v) [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, ringKrullDim A ≤ n := by
  obtain ⟨n, q, hq⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  refine ⟨n, (ringKrullDim_le_of_surjective q.toRingHom hq).trans ?_⟩
  have hk : ringKrullDim k = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  simp [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, hk]

/-- A finite-type affine chart bounds the dimensions of all stalks in that chart. -/
theorem exists_stalk_bound_on_affine {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ n : ℕ, ∀ x : U, ringKrullDim (X.presheaf.stalk x.1) ≤ n := by
  let := ((Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField k)).toField
  let e : U ≤ f ⁻¹ᵁ ⊤ := by simp
  let := (f.appLE ⊤ U e).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U) :=
    f.finiteType_appLE (isAffineOpen_top _) hU e
  obtain ⟨n, hn⟩ := exists_ringKrullDim_le Γ(Spec (CommRingCat.of k), ⊤) Γ(X, U)
  refine ⟨n, fun x => ?_⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have := hU.isLocalization_stalk x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height
    (hU.primeIdealOf x).asIdeal (X.presheaf.stalk x.1)]
  exact (hU.primeIdealOf x).asIdeal.height_le_ringKrullDim_of_isPrime.trans hn

/-- Quasi-compact schemes locally of finite type over a field have finite dimension. -/
theorem finiteTopologicalDimension {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] [CompactSpace X] :
    FiniteTopologicalDimension X := by
  classical
  let 𝒰 := X.affineCover.finiteSubcover
  have hchart : ∀ j : 𝒰.I₀, ∃ n : ℕ,
      ∀ x : (𝒰.f j).opensRange, ringKrullDim (X.presheaf.stalk x.1) ≤ n :=
    fun j => exists_stalk_bound_on_affine f _ (isAffineOpen_opensRange (𝒰.f j))
  choose n hn using hchart
  refine ⟨Finset.univ.sup n,
    FieldSmoothTopologicalKrullDim.topologicalKrullDim_le_of_stalk X _ ?_⟩
  intro x _
  obtain ⟨j, y, rfl⟩ := 𝒰.exists_eq x
  exact (hn j ⟨(𝒰.f j) y, ⟨y, rfl⟩⟩).trans
    (by exact_mod_cast (Finset.le_sup (f := n) (Finset.mem_univ j)))

end Langlands.AlgebraicGeometry.Modules.SerreVanishing
