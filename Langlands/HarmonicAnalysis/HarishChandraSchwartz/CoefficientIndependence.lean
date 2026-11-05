import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Langlands.Representation.IsotypicRestriction
import Langlands.Representation.Plancherel.CoefficientTensors
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Langlands.Representation.Whittaker.Algebraic
import Mathlib.RingTheory.SimpleModule.Isotypic

/-! # Independence of coefficient spaces (Waldspurger, proof of Theorem VIII.1.2)

Waldspurger, VIII.5 (printed p. 332), proof of Theorem VIII.1.2: for a compact open subgroup `H`
and a character `χ`, the sum `⊕_{ω ∈ E₂(G)^H_χ} A(ω)^{H×H}` lies in the finite-dimensional space
`p_χ(°C_H)`, and `A(ω)^{H×H} ≠ {0}` for every `ω ∈ E₂(G)^H_χ`; hence `E₂(G)^H_χ` is finite.

This module proves the representation-theoretic part for an arbitrary family of pairwise
inequivalent irreducible smooth representations `ω i`:

* the coefficient spaces `A(ω i) ⊂ (G → ℂ)` are independent (the sum is direct), because
  `A(ω i)` lies in the `ω i`-isotypic component of right translation on `G → ℂ`;
* if `H` is compact open and `ω i` has a nonzero `H`-fixed vector, then `A(ω i)` contains a
  nonzero `H`-bi-invariant function;
* hence, if the `H`-bi-invariant elements of all `A(ω i)` lie in one finite-dimensional
  space `F`, the index set is finite.

The inclusion of the `H`-bi-invariant coefficients in `p_χ(°C_H)` (from Theorem VIII.4.2) and
the finite dimension of `p_χ(°C_H)` (Proposition VIII.4.1) are the hypotheses on `F`.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe u v w

section Isotypic

variable {R : Type*} {M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- **Isotypic components of pairwise non-isomorphic simple types are independent.** -/
theorem iSupIndep_isotypicComponent {ι : Type*} (S : ι → Type*) [∀ i, AddCommGroup (S i)]
    [∀ i, Module R (S i)] [∀ i, IsSimpleModule R (S i)]
    (hS : ∀ i j, Nonempty (S i ≃ₗ[R] S j) → i = j) :
    iSupIndep fun i => isotypicComponent R M (S i) := by
  -- a nonzero component is the component of a simple submodule of `M`
  have hmem : ∀ i, isotypicComponent R M (S i) ≠ ⊥ →
      ∃ m : Submodule R M, Nonempty (m ≃ₗ[R] S i) ∧
        isotypicComponent R M (S i) ∈ isotypicComponents R M := by
    intro i hi
    obtain ⟨m, ⟨e⟩, -⟩ : ∃ m ∈ {m : Submodule R M | Nonempty (m ≃ₗ[R] S i)}, m ≠ ⊥ := by
      by_contra hn
      push Not at hn
      exact hi (sSup_eq_bot.mpr hn)
    have : IsSimpleModule R m := IsSimpleModule.congr e
    exact ⟨m, ⟨e⟩, m, this, e.isotypicComponent_eq.symm⟩
  intro i
  show Disjoint (isotypicComponent R M (S i)) (⨆ (j) (_ : j ≠ i), isotypicComponent R M (S j))
  by_cases hi : isotypicComponent R M (S i) = ⊥
  · rw [hi]
    exact disjoint_bot_left
  obtain ⟨-, -, hci⟩ := hmem i hi
  refine (sSupIndep_isotypicComponents R M hci).mono_right (iSup₂_le fun j hj => ?_)
  show isotypicComponent R M (S j) ≤ _
  by_cases hj' : isotypicComponent R M (S j) = ⊥
  · rw [hj']
    exact bot_le
  obtain ⟨m, ⟨e⟩, hcj⟩ := hmem j hj'
  refine le_sSup ⟨hcj, fun hji => hj ?_⟩
  have : IsSimpleModule R m := IsSimpleModule.congr e
  have hle : m ≤ isotypicComponent R M (S i) :=
    (Submodule.le_isotypicComponent m).trans (e.isotypicComponent_eq.trans
      (Set.mem_singleton_iff.mp hji)).le
  obtain ⟨e'⟩ := isIsotypicOfType_submodule_iff.mp (IsIsotypicOfType.isotypicComponent R M (S i))
    m hle
  exact hS j i ⟨e.symm.trans e'⟩

end Isotypic

section Transfer

variable {k : Type*} [CommRing k] {H : Type*} [Monoid H] {W : Type*} [AddCommGroup W]
  [Module k W] {ρ : Representation k H W}

/-- Independence of `k[H]`-submodules of `ρ.asModule` passes to their underlying
`k`-submodules of `W`. -/
theorem iSupIndep_toSubmodule_ofSubmodule' {ι : Type*}
    {N : ι → Submodule (MonoidAlgebra k H) ρ.asModule} (hN : iSupIndep N) :
    iSupIndep fun i => (Subrepresentation.ofSubmodule' (N i)).toSubmodule := by
  intro i
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hle : (⨆ (j) (_ : j ≠ i), (Subrepresentation.ofSubmodule' (N j)).toSubmodule) ≤
      (Subrepresentation.ofSubmodule' (⨆ (j) (_ : j ≠ i), N j)).toSubmodule :=
    iSup₂_le fun j hj y hy => (le_iSup₂ (f := fun j (_ : j ≠ i) => N j) j hj :) hy
  exact Submodule.disjoint_def.mp (hN i) x hx (hle hx')

end Transfer

section Coefficients

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coefficient map `x ↦ (g ↦ ℓ(ρ(g) x))` of a functional `ℓ`, as an intertwiner into right
translation on all functions `G → ℂ`. Its underlying linear map is `matrixCoefficient ρ ℓ`. -/
def coefficientIntertwiningMap {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) :
    ρ.IntertwiningMap (Whittaker.rightTranslation ℂ G) where
  toLinearMap := matrixCoefficient ρ ℓ
  isIntertwining' s := by
    ext x g
    change ℓ (ρ g (ρ s x)) = ℓ (ρ (g * s) x)
    rw [map_mul, Module.End.mul_apply]

/-- Waldspurger's coefficient space `A(π)` (I.6, printed p. 249) of a smooth representation,
as a subspace of `G → ℂ`: the span of the coefficients `g ↦ ℓ(π(g) x)` with `x` a vector and
`ℓ` a smooth functional. -/
def coefficientFunctionSpace (A : SmoothRep.{0, u, v} ℂ G) : Submodule ℂ (G → ℂ) :=
  ⨆ ℓ : SmoothDual A.representation, LinearMap.range (matrixCoefficient A.representation ℓ.val)

omit [IsTopologicalGroup G] in
theorem matrixCoefficient_mem_coefficientFunctionSpace (A : SmoothRep.{0, u, v} ℂ G)
    (ℓ : SmoothDual A.representation) (x : A) :
    matrixCoefficient A.representation ℓ.val x ∈ coefficientFunctionSpace A :=
  Submodule.mem_iSup_of_mem ℓ ⟨x, rfl⟩

/-- `A(π)` is the image in `G → ℂ` of the Library's coefficient space
`range (coefficientTensorMap A)` of locally constant functions. -/
theorem coefficientFunctionSpace_eq_map (A : SmoothRep.{0, u, v} ℂ G) :
    coefficientFunctionSpace A =
      (LinearMap.range (coefficientTensorMap A)).map (LocallyConstant.coeFnₗ ℂ) := by
  rw [range_coefficientTensorMap, Submodule.map_span]
  apply le_antisymm
  · refine iSup_le fun ℓ => ?_
    rintro _ ⟨x, rfl⟩
    exact Submodule.subset_span ⟨_, ⟨x, ℓ, rfl⟩, rfl⟩
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨x, ℓ, rfl⟩, rfl⟩
    exact matrixCoefficient_mem_coefficientFunctionSpace A ℓ x

omit [IsTopologicalGroup G] in
/-- **Independence of coefficient spaces**: for pairwise inequivalent irreducible smooth
representations `ω i`, the coefficient spaces `A(ω i) ⊂ (G → ℂ)` are independent, i.e. their
sum is direct. -/
theorem iSupIndep_coefficientFunctionSpace {ι : Type w} (ω : ι → SmoothRep.{0, u, v} ℂ G)
    (hirr : ∀ i, (ω i).IsIrreducible)
    (hω : ∀ i j, Nonempty ((ω i).representation.Equiv (ω j).representation) → i = j) :
    iSupIndep fun i => coefficientFunctionSpace (ω i) := by
  let r := Whittaker.rightTranslation ℂ G
  let S : ι → Type v := fun i => (ω i).representation.asModule
  have : ∀ i, IsSimpleModule (MonoidAlgebra ℂ G) (S i) := fun i =>
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp (hirr i)
  have hS : ∀ i j, Nonempty (S i ≃ₗ[MonoidAlgebra ℂ G] S j) → i = j := by
    rintro i j ⟨e⟩
    refine hω i j ⟨Representation.IntertwiningMap.ofBijective
      ((Representation.IntertwiningMap.equivLinearMapAsModule _ _).symm e.toLinearMap) ?_⟩
    exact e.bijective
  have hind := iSupIndep_toSubmodule_ofSubmodule'
    (iSupIndep_isotypicComponent (M := r.asModule) S hS)
  refine hind.mono fun i => iSup_le fun ℓ => ?_
  rintro _ ⟨x, rfl⟩
  exact (Langlands.CompactSplitting.isotypicComponent_eq_iSup_range (MonoidAlgebra ℂ G)
    r.asModule (S i)).ge (le_iSup (fun f : S i →ₗ[MonoidAlgebra ℂ G] r.asModule =>
      LinearMap.range f) (Representation.IntertwiningMap.equivLinearMapAsModule _ _
        (coefficientIntertwiningMap (ω i).representation ℓ.val)) ⟨x, rfl⟩)

/-- **Nonzero bi-invariant coefficients** (proof of Theorem VIII.1.2, `A(ω)^{H×H} ≠ {0}`): if
a smooth representation has a nonzero vector fixed by a compact open subgroup `H`, then its
coefficient space contains a nonzero `H`-bi-invariant function. -/
theorem exists_isBiInvariant_coefficient_ne_zero (A : SmoothRep.{0, u, v} ℂ G)
    (H : OpenSubgroup G) (hH : IsCompact (H : Set G))
    (hfix : fixedVectors A.representation H.toSubgroup ≠ ⊥) :
    ∃ f ∈ coefficientFunctionSpace A, IsBiInvariant H.toSubgroup f ∧ f ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hx0' : (⟨x, hx⟩ : fixedVectors A.representation H.toSubgroup) ≠ 0 := by
    intro h
    exact hx0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero ℂ hx0'
  obtain ⟨ℓ, hℓ⟩ := (smoothDualFixedRestriction_bijective A.representation A.isSmooth H hH).2 φ
  have hℓx : ℓ.val.val x = φ ⟨x, hx⟩ := by
    rw [← hℓ]
    rfl
  have hℓfix : ∀ h ∈ H.toSubgroup, ∀ y : A,
      ℓ.val.val (A.representation h y) = ℓ.val.val y := by
    intro h hh y
    have hfixℓ : smoothContragredient A.representation h ℓ.val = ℓ.val :=
      (Representation.mem_invariants _ ℓ.val).mp ℓ.property ⟨h, hh⟩
    have h1 : (smoothContragredient A.representation h ℓ.val).val (A.representation h y) =
        ℓ.val.val (A.representation h y) := by
      rw [hfixℓ]
    rw [← h1]
    change ℓ.val.val (A.representation h⁻¹ (A.representation h y)) = ℓ.val.val y
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨matrixCoefficient A.representation ℓ.val.val x,
    matrixCoefficient_mem_coefficientFunctionSpace A ℓ.val x, ?_, ?_⟩
  · intro h₁ h₁m h₂ h₂m g
    have hx2 : A.representation h₂ x = x := (Representation.mem_invariants _ x).mp hx ⟨h₂, h₂m⟩
    change ℓ.val.val (A.representation (h₁ * g * h₂) x) = ℓ.val.val (A.representation g x)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hx2, hℓfix h₁ h₁m]
  · intro h0
    apply hφ
    rw [← hℓx]
    have h1 := congrFun h0 1
    change ℓ.val.val (A.representation 1 x) = 0 at h1
    rwa [map_one, Module.End.one_apply] at h1

/-- An independent family of nonzero subspaces of one finite-dimensional subspace `F` is
finite. -/
theorem finite_of_iSupIndep_of_le {K : Type*} [Field K] {E : Type*} [AddCommGroup E]
    [Module K E] {ι : Type w} {B : ι → Submodule K E} (hB : iSupIndep B) (hne : ∀ i, B i ≠ ⊥)
    (F : Submodule K E) [FiniteDimensional K F] (hle : ∀ i, B i ≤ F) : Finite ι := by
  choose v hv hv0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
  have hli : LinearIndependent K v := hB.linearIndependent B hv hv0
  let w : ι → F := fun i => ⟨v i, hle i (hv i)⟩
  have hw : LinearIndependent K w := LinearIndependent.of_comp F.subtype hli
  exact hw.finite

/-- **Finiteness step of Theorem VIII.1.2** (Waldspurger, VIII.5): let `ω i` be pairwise
inequivalent irreducible smooth representations, each with a nonzero vector fixed by the compact
open subgroup `H`. If the `H`-bi-invariant elements of all coefficient spaces `A(ω i)` lie in one
finite-dimensional space `F` (for Waldspurger, `F = p_χ(°C_H)`), then the family is finite. -/
theorem finite_of_isBiInvariant_coefficient_mem {ι : Type w} (ω : ι → SmoothRep.{0, u, v} ℂ G)
    (hirr : ∀ i, (ω i).IsIrreducible)
    (hω : ∀ i j, Nonempty ((ω i).representation.Equiv (ω j).representation) → i = j)
    (H : OpenSubgroup G) (hH : IsCompact (H : Set G))
    (hfix : ∀ i, fixedVectors (ω i).representation H.toSubgroup ≠ ⊥)
    (F : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ F]
    (hF : ∀ i, ∀ f ∈ coefficientFunctionSpace (ω i), IsBiInvariant H.toSubgroup f → f ∈ F) :
    Finite ι := by
  refine finite_of_iSupIndep_of_le (B := fun i => coefficientFunctionSpace (ω i) ⊓ F)
    ((iSupIndep_coefficientFunctionSpace ω hirr hω).mono fun i => inf_le_left) (fun i => ?_) F
    (fun i => inf_le_right)
  obtain ⟨f, hf, hfb, hf0⟩ := exists_isBiInvariant_coefficient_ne_zero (ω i) H hH (hfix i)
  exact (Submodule.ne_bot_iff _).mpr ⟨f, ⟨hf, hF i f hf hfb⟩, hf0⟩

end Coefficients

end Langlands.HarishChandraSchwartz
