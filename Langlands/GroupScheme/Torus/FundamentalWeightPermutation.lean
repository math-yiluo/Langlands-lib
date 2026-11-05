import Langlands.GroupScheme.Torus.InducedPermutationBasis
import Mathlib.LinearAlgebra.RootSystem.Base
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Fundamental weights from an integral simple-coroot basis -/

noncomputable section

universe u

namespace Langlands.PermutationBasis

section PerfectPairing

variable {R M N I : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]
  [Finite I] (b : Module.Basis I R N)

/-- The basis of the left lattice paired dually with a finite basis of the right lattice. -/
def pairedBasis : Module.Basis I R M := by
  classical
  exact b.dualBasis.map p.toPerfPair.symm

@[simp] theorem pairedBasis_pairing [DecidableEq I] (i j : I) :
    p (pairedBasis p b i) (b j) = if j = i then 1 else 0 := by
  let _ : DecidableEq I := Classical.decEq I
  unfold pairedBasis
  rw [Module.Basis.map_apply, LinearMap.apply_symm_toPerfPair_self,
    Module.Basis.dualBasis_apply_self]
  split_ifs <;> rfl

@[simp] theorem pairedBasis_repr (x : M) (i : I) :
    (pairedBasis p b).repr x i = p x (b i) := by
  classical
  change b.dualBasis.repr (p.toPerfPair x) i = _
  rw [Module.Basis.dualBasis_repr]
  rfl

/-- The annihilator of a subfamily of the right basis is the complementary span
of the dual left basis. -/
theorem mem_pairedBasis_complement_iff (s : Set I) (x : M) :
    x ∈ complementSpan (pairedBasis p b) s ↔ ∀ i ∈ s, p x (b i) = 0 := by
  rw [mem_complementSpan_iff]
  simp only [pairedBasis_repr]

/-- A pairing-preserving pair of linear maps permutes the paired basis by
the same permutation as the right basis. -/
theorem pairedBasis_permutation
    (a : M →ₗ[R] M) (c : N →ₗ[R] N) (e : Equiv.Perm I)
    (hp : ∀ x y, p (a x) (c y) = p x y)
    (hb : ∀ i, c (b i) = b (e i)) (i : I) :
    a (pairedBasis p b i) = pairedBasis p b (e i) := by
  classical
  apply p.toPerfPair.injective
  apply b.ext
  intro j
  obtain ⟨j, rfl⟩ := e.surjective j
  change p (a (pairedBasis p b i)) (b (e j)) =
    p (pairedBasis p b (e i)) (b (e j))
  rw [← hb j, hp, pairedBasis_pairing, hb j, pairedBasis_pairing]
  simp only [Equiv.apply_eq_iff_eq]

end PerfectPairing

end Langlands.PermutationBasis

namespace Langlands.RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (B : P.Base) (hspan : P.corootSpan ℤ = ⊤)

/-- Once all integral coroots span the cocharacter lattice, the simple coroots
of a supplied root-pairing base form an integral basis of that lattice. -/
def simpleCorootBasis : Module.Basis B.support ℤ Y :=
  B.flip.toWeightBasisInt.map (LinearEquiv.ofTop (P.corootSpan ℤ) hspan)

@[simp] theorem simpleCorootBasis_apply (i : B.support) :
    simpleCorootBasis P B hspan i = P.coroot i := by
  change (B.flip.toWeightBasisInt i : Y) = P.coroot i
  exact B.flip.coe_toWeightBasisInt_apply i

/-- The fundamental weights dual to the supplied simple-coroot basis. -/
def fundamentalWeightBasis : Module.Basis B.support ℤ X :=
  Langlands.PermutationBasis.pairedBasis P.toLinearMap (simpleCorootBasis P B hspan)

@[simp] theorem fundamentalWeightBasis_pairing [DecidableEq B.support]
    (i j : B.support) :
    P.toLinearMap (fundamentalWeightBasis P B hspan i) (P.coroot j) =
      if j = i then 1 else 0 := by
  rw [← simpleCorootBasis_apply P B hspan j]
  exact Langlands.PermutationBasis.pairedBasis_pairing _ _ _ _

@[simp] theorem fundamentalWeightBasis_repr (x : X) (i : B.support) :
    (fundamentalWeightBasis P B hspan).repr x i = P.toLinearMap x (P.coroot i) := by
  change (Langlands.PermutationBasis.pairedBasis P.toLinearMap
    (simpleCorootBasis P B hspan)).repr x i = _
  rw [Langlands.PermutationBasis.pairedBasis_repr, simpleCorootBasis_apply]

/-- Characters vanishing on selected simple coroots form the span of the
fundamental weights outside that set. -/
theorem mem_fundamentalWeight_complement_iff (s : Set B.support) (x : X) :
    x ∈ Langlands.PermutationBasis.complementSpan (fundamentalWeightBasis P B hspan) s ↔
      ∀ i ∈ s, P.toLinearMap x (P.coroot i) = 0 := by
  rw [Langlands.PermutationBasis.mem_complementSpan_iff]
  simp only [fundamentalWeightBasis_repr]

/-- Pairing-preserving maps carrying simple coroots by `e` carry their
fundamental weights by the same permutation. -/
theorem fundamentalWeightBasis_permutation
    (a : X →ₗ[ℤ] X) (c : Y →ₗ[ℤ] Y) (e : Equiv.Perm B.support)
    (hp : ∀ x y, P.toLinearMap (a x) (c y) = P.toLinearMap x y)
    (hc : ∀ i : B.support, c (P.coroot i) = P.coroot (e i))
    (i : B.support) :
    a (fundamentalWeightBasis P B hspan i) = fundamentalWeightBasis P B hspan (e i) := by
  apply Langlands.PermutationBasis.pairedBasis_permutation
    P.toLinearMap (simpleCorootBasis P B hspan) a c e hp
  intro j
  simpa only [simpleCorootBasis_apply] using hc j

end Langlands.RootDatum
