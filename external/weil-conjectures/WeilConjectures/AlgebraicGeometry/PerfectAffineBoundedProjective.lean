/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.PerfectAffineModulePreimage
import WeilConjectures.AlgebraicGeometry.AffineProjectiveLocalStrictModel
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect

/-! # Perfect objects on affine schemes

Source: literature/stacks-project/perfect.tex, Lemma perfect-lemma-perfect-affine
(Tag 08EB) (blueprint: lem-pc-perfect-affine-bounded-projective).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- On an affine scheme `Y = Spec A`, an object `E` of `D_QCoh(𝒪_Y)` is perfect if and only if
it is isomorphic in `D(𝒪_Y)` to `tilde(P)` for a bounded complex `P` of finite projective
`A`-modules.
Source: literature/stacks-project/perfect.tex, Lemma perfect-lemma-perfect-affine
(Tag 08EB) (blueprint: lem-pc-perfect-affine-bounded-projective).

Proof: By the affine derived equivalence write `E ≅ tilde(M)` with `M = RΓ(Y, E)` in `D(A)`.
If `E` is perfect, it is pseudo-coherent and locally of finite Tor amplitude; as `Y` is
quasi-compact, finitely many opens give one global amplitude `[a, b]`. The affine Tor-amplitude
and pseudo-coherence criteria transfer both properties to `M`, and the ring criterion gives a
bounded complex `P` of finite projective `A`-modules with `M ≅ P` in `D(A)`, hence
`E ≅ tilde(P)`. Conversely, each `P^i` is a direct summand of some `A^{n_i}`, so `tilde(P)` is
a bounded complex of direct summands of finite free `𝒪_Y`-modules, i.e. strictly perfect, and
`E` is perfect by the definition of `Scheme.IsPerfect` with the one-member cover. -/
theorem perfect_iff_affine_bounded_projective (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u}
        ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (E : schemeDerivedQCohCategory (Spec (.of A))) :
    Scheme.IsPerfect (Spec (.of A)) E.obj ↔
      ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
        (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
        (∀ n : ℤ, Module.Finite A (P.X n)) ∧
        (∀ n : ℤ, Module.Projective A (P.X n)) ∧
        Nonempty (E.obj ≅ DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj P)) := by
  constructor
  · intro hE
    let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) :=
      HasDerivedCategory.standard (ModuleCat.{u} A)
    obtain ⟨e, C, hPC, hTor, ⟨hEC⟩, ⟨hcompare⟩⟩ :=
      perfect_affine_module_preimage A E hE
    obtain ⟨P, hb, hf, hp, ⟨hP⟩⟩ :=
      DerivedCategory.isPerfect_of_pseudoCoherent_finiteTorAmplitude C hPC hTor
    refine ⟨P, hb, hf, hp, ?_⟩
    exact ⟨hEC ≪≫
      ((schemeDerivedQCohProperty (Spec (.of A))).ι.mapIso
        (e.functor.mapIso hP.symm)) ≪≫ hcompare.app P⟩
  · rintro ⟨P, hb, hf, hp, ⟨hEP⟩⟩ x
    obtain ⟨U, hx, K, hK, ⟨hmodel⟩⟩ :=
      affine_projective_local_strict_model A P hb hf hp x
    refine ⟨U, hx, K, hK, ?_⟩
    exact ⟨(SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.mapIso hEP ≪≫
      hmodel⟩

end AlgebraicGeometry
