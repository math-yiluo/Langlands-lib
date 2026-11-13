import Langlands.GroupScheme.SymplecticMatrix.TypeCPinning

/-!
# The simple roots of the coordinate root datum of `Sp_{2n}`

`TypeCPinning.exists_coordinateRootDatum` gives a reduced root datum of the diagonal torus of
`Sp_{2n}` over a field `k`, with spanning coroots and a base numbered by `e : B.support ≃ Fin n`
so that the simple pairings form the Cartan matrix `C_n`. This module restates it with one more
conjunct (`exists_coordinateRootDatum_simpleRoots`): the simple root numbered `i` has coordinates
`e_i - e_{i+1}` for `i + 1 < n` and `2 e_{n-1}` for `i = n - 1`
(`weightCoord_inl_sub_simpleSnd` gives this explicit form). The proof repeats the proof of
`exists_coordinateRootDatum` and keeps the coordinate equation of the simple roots that it
establishes.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.SymplecticMatrix

namespace TypeCPinning

variable {n : ℕ}

/-- The coordinates of the `i`-th simple root `e_i - (simpleSnd i)`: `e_i - e_{i+1}` for
`i + 1 < n` and `2 e_i` otherwise. -/
theorem weightCoord_inl_sub_simpleSnd (i : Fin n) :
    weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i) =
      if h : (i : ℕ) + 1 < n then Pi.single i 1 - Pi.single ⟨i + 1, h⟩ 1
      else Pi.single i 2 := by
  unfold simpleSnd
  split_ifs with h
  · rw [weightCoord_inl, weightCoord_inl]
  · exact weightCoord_inl_sub_inr i

section Field

variable (n) (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- **Coordinate root datum of `Sp_{2n}`, with its simple roots.** The diagonal torus has a
reduced root datum with spanning coroots and a base numbered by `e` so that the simple pairings
form the Cartan matrix `C_n`, and the simple root numbered `i` has coordinates
`e_i - (simpleSnd i)`, i.e. `e_i - e_{i+1}` for `i + 1 < n` and `2 e_{n-1}` for `i = n - 1`. -/
theorem exists_coordinateRootDatum_simpleRoots :
    ∃ (J : Type u) (_ : Finite J)
      (P : RootDatum J (characterLattice 𝔻) (cocharacterLattice 𝔻))
      (_ : IsRootDatumOf (diagonalTorus (Fin n) (CommRingCat.of k)) P) (_ : P.IsReduced)
      (B : P.Base) (e : B.support ≃ Fin n),
      P.corootSpan ℤ = ⊤ ∧
        (∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.C n (e a) (e b)) ∧
        ∀ a : B.support, GeneralLinear.characterCoordEquiv (Fin n) k (P.root a.val) =
          weightCoord (Fin n) (Sum.inl (e a)) - weightCoord (Fin n) (simpleSnd (e a)) := by
  classical
  obtain ⟨J, hJ, P, hP, hred⟩ := exists_rootDatum (Fin n) k
  have : Fintype J := Fintype.ofFinite J
  have : P.IsReduced := hred
  obtain ⟨B, hB⟩ := Langlands.LinearAlgebra.RootDatumCoweightFace.exists_base_support P
    (regularCochar n k) (root'_regularCochar_ne_zero hP)
  have hsimple : ∀ j : J, j ∈ B.support ↔ ∃ i : Fin n,
      GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
        weightCoord (Fin n) (Sum.inl i) - weightCoord (Fin n) (simpleSnd i) :=
    fun j => by rw [← Finset.mem_coe, hB, mem_baseOf_iff hP]
  let g : B.support → Fin n := fun j => ((hsimple j).mp j.2).choose
  have hg : ∀ j : B.support, GeneralLinear.characterCoordEquiv (Fin n) k (P.root j) =
      weightCoord (Fin n) (Sum.inl (g j)) - weightCoord (Fin n) (simpleSnd (g j)) :=
    fun j => ((hsimple j).mp j.2).choose_spec
  have hbij : Function.Bijective g := by
    refine ⟨fun a b hab => Subtype.ext (P.root.injective ?_), fun i => ?_⟩
    · apply (GeneralLinear.characterCoordEquiv (Fin n) k).injective
      rw [hg a, hg b, hab]
    · obtain ⟨j, hj⟩ := exists_root_of_ne hP (inl_ne_simpleSnd i)
      have hjB : j ∈ B.support := (hsimple j).mpr ⟨i, hj⟩
      exact ⟨⟨j, hjB⟩, simple_injective ((hg ⟨j, hjB⟩).symm.trans hj)⟩
  refine ⟨J, hJ, P, hP, hred, B, Equiv.ofBijective g hbij, corootSpan_eq_top hP,
    fun a b => pairing_simple hP (hg a) (hg b), fun a => hg a⟩

end Field

end TypeCPinning

end Langlands.GroupScheme.SymplecticMatrix
