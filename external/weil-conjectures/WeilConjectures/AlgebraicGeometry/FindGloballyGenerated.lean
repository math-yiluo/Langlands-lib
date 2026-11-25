/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.AffineComplementReciprocalCover
import WeilConjectures.AlgebraicGeometry.ReciprocalCoverLineBundle
import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre

/-! # Globally generated invertible modules with a prescribed affine section locus

Source: Stacks Project, Varieties Lemma 09NB (varieties-lemma-find-globally-generated),
specialized to Noetherian integral separated schemes of dimension one
(blueprint: lem-sc-find-globally-generated).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A nonempty affine open with finite complement in an integral separated Noetherian
one-dimensional scheme is the nonvanishing locus of a section of a globally generated
invertible module. Source: Stacks Project, Varieties Lemma 09NB
(blueprint: lem-sc-find-globally-generated).

Proof:
1. Write `U = Spec A` and `K = k(X)`. At each point `xᵢ` of the finite complement,
   `Bᵢ = O_{X,xᵢ}` is Noetherian by `pqf-def-locnoeth`, the affine-stalk localization
   description `lem-weil-pbc-spec-domain-stalks-function-field`, and
   `lem-weil-pbc-localization-noetherian`. Its dimension is one by
   `lem-sc-scheme-stalk-dimension-generalization-chains`: dimension is at most one,
   and the generic point in `U` gives a strict specialization to `xᵢ`.
   The pullback of `U` to `Spec Bᵢ` is `Spec K`. Embed `A` and `Bᵢ` in `K` using
   `lem-sc-integral-scheme-stalks-in-function-field`; separatedness gives surjectivity
   of `A ⊗ Bᵢ → K` by `lem-sc-separated-affine-function-field-surjective`.
2. Each `Bᵢ` is a one-dimensional local domain with fraction field `K`, by
   `lem-sc-integral-scheme-stalks-in-function-field`. The fraction field of `A` is
   `K` by `lem-sc-integral-function-field-affine-fraction`. Apply
   `lem-sc-jacobson-denominator-function-field` to find nonzero `f ∈ A` with
   `f⁻¹ ∈ mᵢ` for every complement point.
3. Choose neighbourhoods `Uᵢ` where `f⁻¹` is regular. Together with `U` they cover `X`.
   On `U ∩ Uᵢ`, the functions `f` and `f⁻¹` are inverse units by the injectivity into
   `K` from `lem-sc-integral-scheme-stalks-in-function-field`; on `Uᵢ ∩ Uⱼ` use `1`.
4. These transition functions satisfy the cocycle identities and glue the trivial
   modules to an invertible module `L` by `lem-sc-glue-component-transition-cocycle`.
   The local sections `1` on `U`, `f⁻¹` on `Uᵢ` glue to `s`; the local sections `f`
   on `U`, `1` on `Uᵢ` glue to `t`.
5. The section `s` is nonvanishing on `U` and vanishes at each complement point,
   so its nonvanishing locus equals `U`. The section `t` is nonvanishing on every
   `Uᵢ`. Thus `s` and `t` generate `L` at every point, giving global generation.
-/
theorem exists_globallyGenerated_invertible_nonvanishing_eq
    (X : Scheme.{u}) [IsIntegral X] [X.IsSeparated] [IsLocallyNoetherian X]
    [CompactSpace X] (hdim : topologicalKrullDim X = 1) (U : X.Opens)
    (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (hfin : (Set.compl (U : Set X)).Finite) :
    ∃ L : X.Modules, L.IsInvertible ∧ Nonempty (SheafOfModules.GeneratingSections L) ∧
      ∃ s : L.val.presheaf.obj (Opposite.op ⊤), nonvanishingLocus L s = (U : Set X) := by
  classical
  obtain ⟨V, f, g, hcover, hinv, hlocus⟩ :=
    exists_affine_complement_reciprocal_cover X hdim U hU hne hfin
  obtain ⟨L, s, t, hL, hs, ht⟩ :=
    exists_line_bundle_sections_of_reciprocal_cover X U V f g hcover hinv hlocus
  have : L.IsInvertible := hL
  let a : ULift.{u} (Fin 2) → L.sections := fun i ↦ if i.down = 0 then s else t
  have ha : CategoryTheory.Epi (L.freeHomEquiv.symm a) :=
    (invertible_generating_sections_fibre_criterion X L 1 a).1.mpr (by
      intro x
      have hx : x ∈ U ⊔ V := by rw [hcover]; trivial
      rcases hx with hx | hx
      · refine ⟨⟨0⟩, ?_⟩
        simpa only [a, ↓reduceIte, hs] using hx
      · refine ⟨⟨1⟩, ?_⟩
        simpa [a] using ht hx)
  exact ⟨L, hL, ⟨{ I := ULift.{u} (Fin 2), s := a, epi := ha }⟩,
    s.val (Opposite.op ⊤), hs⟩

end AlgebraicGeometry.Scheme.Modules
