import Langlands.Representation.Aubert.General.RationalWeylRootAction
import Langlands.Group.RelativeWeylIndexing

/-! # Statement: the Coxeter system of the actual relative Weyl group

The group is the published `relativeWeylGroup i = N(k)/Z(k)`. The simple reflections are
labelled by the published `simpleRelativeRoots i ν` of a generic cocharacter `ν`, which are
computed from the full, possibly nonreduced, set of relative roots. The root action is the
published `schemeWeylCharacterAction i` on the full character lattice. No Coxeter
realization, reflection theorem or root system is assumed by the final statement.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Roots

variable (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] (ν : cocharacterLattice T)

/-- The reduced positive relative roots: positive relative roots `α` such that no
`n • β` with `n ≥ 2` and `β` a relative root equals `α` (Renard V.3.4, `α/n ∉ Σ'`). -/
def reducedPositiveRelativeRoots : Set (characterLattice T) :=
  {α | α ∈ positiveRelativeRoots i ν ∧
    ∀ n : ℕ, 2 ≤ n → ∀ β ∈ relativeRoots i, n • β ≠ α}

theorem reducedPositiveRelativeRoots_subset_positive :
    reducedPositiveRelativeRoots i ν ⊆ positiveRelativeRoots i ν :=
  fun _ hα => hα.1

variable [Mono i.hom.hom.left]

/-- The reduced positive relative roots that `w` sends to negatives of positive roots. -/
def relativeInversionSet (w : relativeWeylGroup i) : Set (characterLattice T) :=
  {α | α ∈ reducedPositiveRelativeRoots i ν ∧
    -(schemeWeylCharacterAction i w α) ∈ positiveRelativeRoots i ν}

end Roots

section Coxeter

variable (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  (ν : cocharacterLattice T)

/-- A Coxeter system on the actual relative Weyl group, labelled by the actual simple
relative roots, realizes the root action when:
* the simple reflection of `a` acts on every character by `χ ↦ χ - f χ • a` for an
  integral linear form `f` with `f a = 2`;
* it sends every positive relative root other than `a` and `2 • a` to a positive root;
* `ℓ(w s_a) > ℓ(w)` exactly when `w a` is positive;
* `ℓ(w)` is the number of reduced positive relative roots that `w` makes negative;
* the Coxeter parabolic subgroup of every finite label set `I` is the published
  `standardRelativeWeylGroup` of the corresponding root set. -/
def IsRelativeWeylCoxeterRealization {M : CoxeterMatrix (SimpleRoot i ν)}
    (cs : CoxeterSystem M (relativeWeylGroup i)) : Prop :=
  (∀ a : SimpleRoot i ν, ∃ f : characterLattice T →+ ℤ, f a.1 = 2 ∧
    ∀ χ : characterLattice T,
      schemeWeylCharacterAction i (cs.simple a) χ = χ - f χ • a.1) ∧
  (∀ (a : SimpleRoot i ν), ∀ β ∈ positiveRelativeRoots i ν, β ≠ a.1 → β ≠ 2 • a.1 →
    schemeWeylCharacterAction i (cs.simple a) β ∈ positiveRelativeRoots i ν) ∧
  (∀ (w : relativeWeylGroup i) (a : SimpleRoot i ν),
    cs.length w < cs.length (w * cs.simple a) ↔
      schemeWeylCharacterAction i w a.1 ∈ positiveRelativeRoots i ν) ∧
  (∀ w : relativeWeylGroup i, cs.length w = (relativeInversionSet i ν w).ncard) ∧
  ∀ I : Finset (SimpleRoot i ν),
    standardSubgroup cs I = standardRelativeWeylGroup i ν (rootSet i ν I)

/-- The actual relative Weyl group is finite, the actual simple relative roots are finite,
and some Coxeter system on the group, labelled by those roots, realizes the root action. -/
def HasRelativeWeylCoxeterSystem : Prop :=
  Finite (relativeWeylGroup i) ∧ Finite (SimpleRoot i ν) ∧
    ∃ (M : CoxeterMatrix (SimpleRoot i ν)) (cs : CoxeterSystem M (relativeWeylGroup i)),
      IsRelativeWeylCoxeterRealization i ν cs

variable {i ν}

omit [Mono i.hom.hom.left] in
theorem rootSet_singleton (a : SimpleRoot i ν) :
    rootSet i ν {a} = {a.1} := by
  simp [rootSet]

/-- In a realization, the simple reflection of `a` lies in the published standard
relative Weyl subgroup of `{a}`. -/
theorem IsRelativeWeylCoxeterRealization.simple_mem_standardRelativeWeylGroup
    {M : CoxeterMatrix (SimpleRoot i ν)} {cs : CoxeterSystem M (relativeWeylGroup i)}
    (h : IsRelativeWeylCoxeterRealization i ν cs) (a : SimpleRoot i ν) :
    cs.simple a ∈ standardRelativeWeylGroup i ν {a.1} := by
  rw [← rootSet_singleton, ← h.2.2.2.2 {a}]
  exact simple_mem_standardSubgroup cs (Finset.mem_singleton_self a)

end Coxeter

/-- **The relative Weyl group is a finite Coxeter group** (Borel–Tits 5.3, 5.8, 5.17,
Renard V.3.7 and V.4.6). For a maximal split torus `i` of a connected reductive group `G`
over a field `k` and a generic cocharacter `ν`, the actual group `N(k)/Z(k)` carries a
Coxeter system whose simple reflections are labelled by the simple relative roots of `ν`.
Those reflections act on characters by the integral reflection formula, lengths and signs
are computed from the relative roots, and the Coxeter parabolic subgroups are the
published standard relative Weyl subgroups. Nonreduced root systems and rank zero are
included. -/
def RelativeWeylCoxeterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν → HasRelativeWeylCoxeterSystem i ν

end Langlands.GroupScheme
