/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.FlatModelFiniteFreeQuasiIso

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- The structural local finite-free replacement part of the shortening argument.
Source: Stacks Project, Tags 064U, 0653 and 00NX; this is the construction portion
of `lem-pc-flat-model-finite-free-shortening`.
Proof: restrict to an affine neighbourhood, form the degree-zero opcycle, use the
flat opcycles Tor criterion and finite-projective standard-free cover, then truncate
the bounded-above free resolution.
(blueprint: lem-pc-flat-model-finite-free-shortening-construction).
Proof: The construction argument supplies the stated local data and its induced
quasi-isomorphism. Pulling it back along any scheme map preserves it for these
finite-free and flat complexes; taking homology gives the displayed isomorphism.
-/
theorem exists_local_finiteFree_construction {T : Scheme.{u}} (U : T.Opens)
    (C Q : CochainComplex U.toScheme.Modules ℤ) (d : ℕ)
    (hCge : C.IsStrictlyGE 0) (hCle : C.IsStrictlyLE d)
    (hCflat : ∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme))
    (hQle : Q.IsStrictlyLE d)
    (hQfree : ∀ n : ℤ, ∃ r : ℕ,
      Nonempty (Q.X n ≅ SheafOfModules.free
        (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))
    (e : Q ⟶ C) (he : QuasiIso e) (t : T) (ht : t ∈ U) :
    ∃ (V : T.Opens) (hVU : V ≤ U) (P : CochainComplex V.toScheme.Modules ℤ),
      (t ∈ V ∧ P.IsStrictlyGE 0 ∧ P.IsStrictlyLE d ∧
        (∀ n : ℤ, ∃ r : ℕ,
          Nonempty (P.X n ≅ SheafOfModules.free
            (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))))) ∧
      ∃ (eP : P ⟶ ((Modules.pullback (T.homOfLE hVU)).mapHomologicalComplex _).obj C),
        QuasiIso eP := by
  obtain ⟨V, hVU, P, hstruct, eQ, eP, hQ, hP, hcomm⟩ :=
    exists_local_finiteFree_quasiIso U C Q d hCge hCle hCflat hQle hQfree e he t ht
  exact ⟨V, hVU, P, hstruct, eP, hP⟩

end AlgebraicGeometry.Scheme.Modules
