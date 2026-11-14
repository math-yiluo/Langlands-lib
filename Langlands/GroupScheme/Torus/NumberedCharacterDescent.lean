import Langlands.GroupScheme.Reductive.RootDatumBaseChangeStatement
import Mathlib.LinearAlgebra.RootSystem.Base

/-! # Descent of numbered character families along split-torus base change -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {k K : Type u} [CommRing k] [IsDomain k] [CommRing K] [IsDomain K]
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)

namespace characterLattice

/-- Descend a family of actual characters by the canonical lattice equivalence
of a split torus, with no choice of coordinates on the torus. -/
def descendFamily {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b).obj T)) :
    I → characterLattice T :=
  fun i => (baseChangeEquiv b T hT).symm (chi i)

@[simp]
theorem baseChange_descendFamily {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b).obj T)) (i : I) :
    baseChange b T (descendFamily b T hT chi i) = chi i :=
  (baseChangeEquiv b T hT).apply_symm_apply (chi i)

end characterLattice

/-- Descending an actual character preserves its pairing with every
cocharacter of the original split torus. -/
theorem latticePairing_descendFamily {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b).obj T))
    (i : I) (nu : cocharacterLattice T) :
    latticePairing T (characterLattice.descendFamily b T hT chi i) nu =
      latticePairing ((CommGroupScheme.baseChange b).obj T) (chi i)
        (cocharacterLattice.baseChange b T nu) := by
  rw [← latticePairing_baseChange b T
    (characterLattice.descendFamily b T hT chi i) nu,
    characterLattice.baseChange_descendFamily]

/-- Restriction along an actual torus morphism commutes with character
descent and evaluation on cocharacters. -/
theorem latticePairing_restrict_descendFamily
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
    {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b).obj T))
    (i : I) (nu : cocharacterLattice S) :
    latticePairing S (f ≫ characterLattice.descendFamily b T hT chi i) nu =
      latticePairing ((CommGroupScheme.baseChange b).obj T) (chi i)
        (cocharacterLattice.baseChange b T (nu ≫ f)) := by
  rw [← latticePairing_descendFamily b T hT chi i (nu ≫ f)]
  exact congrArg (gmEndEquiv k) (Category.assoc nu f _).symm

/-- The signed weight fibers, and hence their cardinalities, are unchanged
by descending characters of a split torus. The restricted source need not
itself be split. -/
theorem signed_weight_card_descendFamily
    {S : CommGroupScheme (Spec (CommRingCat.of k))} (f : S ⟶ T)
    {I : Type v}
    (chi : I → characterLattice ((CommGroupScheme.baseChange b).obj T))
    (nu : cocharacterLattice S) (c : ℤ) :
    Nat.card {p : I × ℤˣ //
        (p.2 : ℤ) * latticePairing S
          (f ≫ characterLattice.descendFamily b T hT chi p.1) nu = c} =
      Nat.card {p : I × ℤˣ //
        latticePairing ((CommGroupScheme.baseChange b).obj T)
          ((p.2 : ℤ) • chi p.1)
          (cocharacterLattice.baseChange b T (nu ≫ f)) = c} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun p => by
    rw [map_zsmul, LinearMap.smul_apply, smul_eq_mul,
      latticePairing_restrict_descendFamily b T hT f chi p.1 nu]

namespace SplitRootDatum

/-- All three numbered type-D root equations descend through the canonical
character-lattice equivalence. The root datum, its base and the numbering
are supplied; no representation or root-existence assertion is constructed. -/
theorem numbered_roots_descend
    {J : Type w} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (B : P.Base) {n : ℕ} (hn : 2 ≤ n) (e : B.support ≃ Fin n)
    (eps : Fin n → characterLattice ((CommGroupScheme.baseChange b).obj T))
    (hstep : ∀ (a : B.support) (h : (e a).val + 1 < n),
      (baseChange b T hT P).root a.val =
        eps (e a) - eps ⟨(e a).val + 1, h⟩)
    (hlast : ∀ (a : B.support) (h : (e a).val + 1 = n),
      (baseChange b T hT P).root a.val =
        eps ⟨n - 2, by omega⟩ + eps ⟨n - 1, by omega⟩)
    (hroots : ∀ i j : Fin n, i ≠ j → ∀ s t : ℤˣ, ∃ a : J,
      (baseChange b T hT P).root a = (s : ℤ) • eps i + (t : ℤ) • eps j) :
    (∀ (a : B.support) (h : (e a).val + 1 < n),
      P.root a.val =
        characterLattice.descendFamily b T hT eps (e a) -
          characterLattice.descendFamily b T hT eps ⟨(e a).val + 1, h⟩) ∧
    (∀ (a : B.support) (h : (e a).val + 1 = n),
      P.root a.val =
        characterLattice.descendFamily b T hT eps ⟨n - 2, by omega⟩ +
          characterLattice.descendFamily b T hT eps ⟨n - 1, by omega⟩) ∧
    (∀ i j : Fin n, i ≠ j → ∀ s t : ℤˣ, ∃ a : J,
      P.root a =
        (s : ℤ) • characterLattice.descendFamily b T hT eps i +
          (t : ℤ) • characterLattice.descendFamily b T hT eps j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a h
    apply (characterLattice.baseChangeEquiv b T hT).injective
    simpa only [map_sub, characterLattice.baseChangeEquiv_apply,
      characterLattice.baseChange_descendFamily, baseChange_root] using hstep a h
  · intro a h
    apply (characterLattice.baseChangeEquiv b T hT).injective
    simpa only [map_add, characterLattice.baseChangeEquiv_apply,
      characterLattice.baseChange_descendFamily, baseChange_root] using hlast a h
  · intro i j hij s t
    obtain ⟨a, ha⟩ := hroots i j hij s t
    refine ⟨a, (characterLattice.baseChangeEquiv b T hT).injective ?_⟩
    simpa only [map_add, map_zsmul, characterLattice.baseChangeEquiv_apply,
      characterLattice.baseChange_descendFamily, baseChange_root] using ha

end SplitRootDatum

end Langlands.GroupScheme
