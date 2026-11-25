/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.FiniteEquationsOfClosedAffine

/-! # Finite equations for the closed fibre-degree sublevel locus -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- The closed degree-at-most-r locus on an affine open has finitely many equations.
Source: Stacks Project, More on Morphisms, Tag 07RZ, proof, second paragraph
(blueprint: lem-weil-pbc-qf-degree-sublevel-finite-equations).

Proof: identify W with Spec A and write its closed sublevel locus as V(I). On W,
the lower bound r identifies the sublevel locus with the degree-r locus. Thus the
universal degree criterion makes the pullback to Spec(A/I) finite locally free of
rank r. The quotient A/I is the filtered colimit of A/J over finitely generated
subideals J of I, so its spectrum is the inverse limit of those quotient spectra.
The restriction of f to W is quasi-compact, separated, and locally of finite
presentation, hence finitely presented. Descent of finite local freeness with
specified rank gives a finitely generated J contained in I for which the
pullback to Spec(A/J) has rank r. The degree criterion implies V(J) is contained
in the degree-r locus V(I). Since J is contained in I, the reverse inclusion also
holds. Choose a finite generating set t of J. At every point of W, membership
in V(J) is equivalent to lying outside every basic open D(a), a in t. This is
the asserted equivalence. Empty W and the zero ideal permit t empty; the unit
ideal permits t containing 1, so no nonemptiness assumption is needed. -/
theorem exists_finite_equations_degree_sublevel_inter_affine
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] [IsSeparated f] (hf : f.IsQuasiFinite)
    (r : ℕ) (W : S.Opens) (hW : IsAffineOpen W)
    (hclosed : IsClosed {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r})
    (hdegree : ∀ (T : Scheme.{u}) (g : T ⟶ S),
      (pullback.snd f g).IsFiniteLocallyFreeOfDegree r ↔
        Set.range g ⊆ {s : S | (f.fiberToSpecResidueField s).finrankΓ = r})
    (hWge : ∀ s : S, s ∈ W → r ≤ (f.fiberToSpecResidueField s).finrankΓ) :
    ∃ t : Finset Γ(S, W), ∀ s : S, s ∈ W →
      ((f.fiberToSpecResidueField s).finrankΓ ≤ r ↔ ∀ a ∈ t, s ∉ S.basicOpen a) := by
  obtain ⟨I, hI, hIZ⟩ := exists_finitely_generated_zeroLocus_ideal_degree_sublevel_inter_affine
    f hf r W hW hclosed hdegree hWge
  obtain ⟨t, ht⟩ := exists_finite_equations_of_finitely_generated_zeroLocus hI
  refine ⟨t, fun s hs ↦ ?_⟩
  change s ∈ {s : S | (f.fiberToSpecResidueField s).finrankΓ ≤ r} ↔ _
  exact (hIZ s hs).trans (ht s hs)

end AlgebraicGeometry.Scheme.Hom
