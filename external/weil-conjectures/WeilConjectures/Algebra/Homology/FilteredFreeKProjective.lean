/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
import WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveStep
import WeilConjectures.Algebra.Homology.FilteredFreeKProjectiveAssembly

/-!
# Filtered free complexes are K-projective

Source: Stacks Project, Differential Graded Algebra, Tag 09KM, lemma-property-P-K-projective.
(blueprint: lem-pc-filtered-free-kprojective).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- Finite-stage induction for filtered free complexes.
(source: Stacks Project, Tag 09KM)
(blueprint: lem-pc-filtered-free-kprojective-stage)

Proof: induct on the filtration index. At zero, every map from `F 0` is zero, hence
homotopic to zero. At a successor, apply the split-extension theorem to the induction
hypothesis and the retraction and cokernel decomposition for that one step. -/
theorem isKProjective_of_filtered_free_stage {A : Type u} [CommRing A]
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0))
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    ∀ n, (F n).IsKProjective := by
  intro n
  induction n with
  | zero =>
      refine ⟨fun f _ => ⟨Homotopy.ofEq ?_⟩⟩
      exact hzero.eq_of_src f 0
  | succ n ih =>
      apply isKProjective_of_filtered_free_step (step n) ih
      · intro k
        exact hsplit n k
      · exact hquot n

/-- Telescope assembly for an exhaustive split filtration.
(source: Stacks Project, Tags 09KL to 09KM)
(blueprint: lem-pc-filtered-free-kprojective-telescope)

Proof: on `S = ⨁ n, F n`, define `a : S → S` on summand `n` as its inclusion into
summand `n` minus `step n` followed by inclusion into summand `n + 1`. Define `b : S → P`
using the compatible inclusions. The map `a` is injective, as seen by the smallest nonzero
coordinate of a finitely supported element. Exhaustion makes `b` surjective; compatibility
and a finite telescoping calculation identify its kernel with the image of `a`.
Choose degreewise retractions `r_i` in `hsplit`, and let `r_{j,i}` be their composite
from stage `j` to stage `i < j`. Define `l` on summand `j` by component `-r_{j,i}`
for `i < j` and zero otherwise. Its support is finite. In `l a` on summand `n`,
components below `n` cancel, component `n` is `r_n step_n = id`, and all later
components vanish. Thus `l a = id`, giving the required graded-module splitting.
Thus `0 → S → S → P → 0` is an admissible exact sequence and gives a distinguished
triangle in the homotopy category (Stacks Tags 09KL and 09KJ). For every acyclic `N`, the maps from
`S` to `N`, and to its shifts, vanish: restrict to each summand, use `hstage`, and assemble
the null homotopies by the coproduct universal property. The exact Hom sequence of the
triangle then gives zero maps from `P` to `N` up to homotopy, which is `IsKProjective`.
This argument uses the degreewise splitting essentially; exhaustion alone does not suffice. -/
theorem isKProjective_of_filtered_free_telescope
    {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hstage : ∀ n, (F n).IsKProjective) :
    P.IsKProjective :=
  filtered_free_telescope_assembly P F ι step hzero hmono hcompat hexhaustive hsplit hstage


/-- An exhaustive, degreewise split filtration with shifted free quotients is K-projective.
Source: Stacks Project, Tag 09KM, lemma-property-P-K-projective, specialized to the algebra
concentrated in degree zero; the larger carrier universe uses the rank-one module `ULift A`.
(blueprint: lem-pc-filtered-free-kprojective).

Proof: each shifted free module has no maps up to homotopy to an acyclic complex:
a chain map is determined by a cycle, and acyclicity writes that cycle as a boundary.
The same holds for a direct sum of these modules, by choosing a primitive on each
free generator. The degreewise split short exact sequences for the filtration give
mapping-cone triangles in the homotopy category. Induction from the zero initial
term therefore shows that every finite filtration term, and each of its shifts,
is left orthogonal to all acyclic complexes. Form the telescope sequence with first
map identity minus successor on the direct sum of the filtration terms. Exhaustion
identifies its cokernel with `P`. The degreewise retractions give a splitting of
this sequence of graded modules (successively compose retractions on each finite
stage), so it gives a distinguished triangle in the homotopy category. Maps from
both coproduct terms to an acyclic complex, including its shifts, are zero, since
maps from coproducts are families of maps. The exact Hom sequence of this triangle
makes every map from `P` to an acyclic complex zero in the homotopy category, hence
null homotopic. This is `IsKProjective`. All coproducts and choices of generators
stay in `Type (max u v)`. Empty free bases, zero rings and unbounded complexes are
included. -/
theorem isKProjective_of_filtered_free {A : Type u} [CommRing A]
    (P : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{max u v} A) ℤ)
    (ι : ∀ n, F n ⟶ P) (step : ∀ n, F n ⟶ F (n + 1))
    (hzero : IsZero (F 0)) (hmono : ∀ n, Mono (ι n))
    (hcompat : ∀ n, step n ≫ ι (n + 1) = ι n)
    (hexhaustive : ∀ (k : ℤ) (x : P.X k),
      ∃ (n : ℕ) (y : (F n).X k), (ι n).f k y = x)
    (hsplit : ∀ (n : ℕ) (k : ℤ),
      ∃ r : (F (n + 1)).X k ⟶ (F n).X k,
        (step n).f k ≫ r = 𝟙 ((F n).X k))
    (hquot : ∀ n, ∃ (I : Type (max u v)) (degree : I → ℤ),
      Nonempty (cokernel (step n) ≅
        ∐ (fun i : I ↦
          (HomologicalComplex.single (ModuleCat.{max u v} A) (.up ℤ) (degree i)).obj
            (ModuleCat.of A (ULift.{v} A))))) :
    P.IsKProjective := by
  have hstage' : ∀ n, (F n).IsKProjective :=
    isKProjective_of_filtered_free_stage F step hzero hsplit hquot
  exact isKProjective_of_filtered_free_telescope P F ι step hzero hmono hcompat
    hexhaustive hsplit hstage'

end CochainComplex
