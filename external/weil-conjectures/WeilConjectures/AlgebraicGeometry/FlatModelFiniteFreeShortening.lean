/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeConstruction
import WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeComparison

/-! # Local nonnegative finite-free replacements of bounded flat complexes -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A bounded nonnegative flat complex with a bounded-above finite-free resolution has,
near a specified point, a finite-free replacement in the same degree interval. The
replacement computes the homology of every ordinary scheme pullback of the flat complex.
This is a general algebraic shortening lemma and has no proper morphism or direct image.

Source: the coherence unit's Mumford-complex step; Stacks Project, Tags 064U, 0653 and 00NX
(the flat opcycles criterion and finite-projective local freeness).
Proof:
1. Work on an affine neighbourhood inside `U`. The bounded flat complex `C` has Tor
   amplitude `[0,d]`. Its bounded-above free resolution `Q` is K-flat, so the resolution
   computes tensor with every module, and all negative tensor cohomology vanishes.
2. Set `M = coker(Q^{-1} -> Q^0)`. The negative part of `Q` resolves `M`, since `C`
   has no negative cohomology. The negative tensor vanishing shows that `M` is flat;
   it is finitely presented because `Q^{-1}` and `Q^0` are finite free. Hence `M` is
   finite projective, and is free on an open neighbourhood of the chosen point.
3. Replace the negative tail and degree zero by `M` in degree zero and keep degrees
   `1,...,d`. This quotient complex is quasi-isomorphic to `Q`. On the chosen smaller
   open its degree-zero term and all higher terms are finite free, and it is zero
   outside `[0,d]`. Thus it gives `P` with the stated three structural properties.
4. Both `C` and `P` are bounded flat complexes. Their quasi-isomorphism in the derived
   category is preserved by derived pullback, which ordinary pullback computes for
   such complexes. Taking cohomology gives the isomorphisms for every `g` and `q`.
   Express the smaller neighbourhood as `V <= U` in the ambient scheme to use
   `T.homOfLE hVU` as its open inclusion. No global triviality is claimed.

(blueprint: lem-pc-flat-model-finite-free-shortening). -/
theorem exists_local_finiteFree_shortening {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ),
      t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
      (∀ n : ℤ, ∃ r : ℕ,
        Nonempty (P.X n ≅ SheafOfModules.free
          (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)))) ∧
      ∀ {T' : Scheme.{u}} (g : T' ⟶ V.toScheme) (q : ℕ),
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (((Modules.pullback (g ≫ T.homOfLE hVU)).mapHomologicalComplex _).obj C).homology q)
    := by
  obtain ⟨V, hVU, P, hstruct, hP⟩ :=
    exists_local_finiteFree_construction U C Q d hCge hCle hCflat hQle hQfree e he t ht
  obtain ⟨eP, heP⟩ := hP
  refine ⟨V, hVU, P, hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2, ?_⟩
  exact local_finiteFree_homology_comparison U C Q d hCge hCle hCflat hQle hQfree e he t
    V hVU P hstruct eP heP

end AlgebraicGeometry.Scheme.Modules
