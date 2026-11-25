/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.QuasiFiniteDegreeUpperLocusCompactAux

/-! # Quasi-compactness of upper fibre-degree loci -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- On an affine open in the degree-at-least-r locus, the degree-at-least-(r+1)
locus is quasi-compact. The closed sublevel locus and the universal degree-r
criterion are explicit hypotheses, so this is only the descent step of the argument.
Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph
(blueprint: lem-weil-pbc-qf-degree-successor-affine-compact).

Proof: Since W lies in the degree-at-least-r locus, the closed sublevel locus
restricted to W is precisely the degree-r locus. Write W as Spec A and that closed
locus as V(I). The quotient-spectrum morphism Spec(A/I) → S has image in the
degree-r locus, so the assumed universal criterion makes its base change finite
locally free of degree r. Write I as the directed union of its finitely generated
subideals; Spec(A/I) is the inverse limit of their quotient spectra with affine
transition maps. The restriction of f to W is quasi-compact (because f is) and
quasi-separated (because f is separated over an affine), and locally of finite
presentation. Descent of finite local freeness and its degree therefore gives a
finitely generated subideal J of I whose quotient-spectrum base change is finite
locally free of degree r. The universal criterion forces V(J) to lie in V(I).
The opposite inclusion follows from J ⊆ I, so V(J) = V(I). The complement is the
finite union of the basic opens of generators of J. Basic opens in an affine scheme
are quasi-compact, and a finite union is quasi-compact. This is exactly the required
intersection. The argument includes empty W, the zero ideal, and the unit ideal. -/
theorem isCompact_successor_degree_locus_inter_affine {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    IsCompact ({s : S | r + 1 ≤ (f.fiberToSpecResidueField s).finrankΓ} ∩
      (W : Set S)) := by
  obtain ⟨U, hUcompact, hUeq⟩ :=
    exists_compact_open_successor_degree_locus_inter_affine f hf r W hW hclosed hdegree hWge
  rw [← hUeq]
  exact hUcompact

end AlgebraicGeometry.Scheme.Hom
