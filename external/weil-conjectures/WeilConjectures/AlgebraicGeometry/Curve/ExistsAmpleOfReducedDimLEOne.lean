/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.Curve.GluedComponentAffineSection
import WeilConjectures.AlgebraicGeometry.ComponentSupportedAffineSection
import WeilConjectures.AlgebraicGeometry.ComponentIntersectionsFinite
import WeilConjectures.AlgebraicGeometry.IntegralDimOneAmple
import WeilConjectures.AlgebraicGeometry.ZeroDimNoetherianAffine
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-! # Ample invertible modules on reduced Noetherian schemes of dimension at most one

Source: Stacks Project, Varieties, Lemma 09NX; Properties, Lemmas 0AAX and 0CKV
(blueprint: lem-sc-reduced-dim-le-one-ample).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A reduced Noetherian separated scheme of dimension at most one admits an ample
invertible module. The empty scheme is included.
Source: Stacks Project, Varieties, Lemma 09NX, with the dimension-zero branch from
Properties, Lemmas 0AAX and 0CKV (blueprint: lem-sc-reduced-dim-le-one-ample).

Proof:
1. If `X` is empty or has dimension at most zero, `lem-sc-zero-dim-noetherian-affine`
makes it affine, and its structure sheaf is ample. Otherwise its dimension is one.
2. Its finitely many reduced irreducible components are integral, Noetherian, separated,
and of dimension zero or one. Choose ample modules on them using
`lem-sc-integral-dim-one-ample` and `lem-sc-zero-dim-noetherian-affine`. Their pairwise
intersections form a finite set `T` of closed points, and each point outside `T` lies on
one component, by `lem-sc-component-intersections-finite` (and `def-pc-integral-scheme`).
3. Use `lem-sc-ample-finite-principal-affine` to replace each component module by a
positive power with a section whose affine nonvanishing locus contains its part of `T`.
The pairwise intersections are finite discrete spaces, so
`lem-sc-glue-component-line-bundles` glues the modules and sections to a module `L`
and section `s` on `X`.
4. The open `X_s` contains `T` and is covered by the affine closed subschemes given by
the component sections. It is affine by `lem-sc-closed-affine-union-affine`.
5. For `x` outside `T`, let `Z₁` be its unique component and let `I` be the ideal of the
reduced union of the other components. Its image `I₁` on `Z₁` does not vanish at `x`.
Use `lem-sc-ample-ideal-section` to obtain a section `t₁` of `I₁ L₁^m₁` nonvanishing
at `x`, and the definition `def-weil-pbc-ample-invertible-module` to obtain a section
`t₂` of `L₁^m₂` with affine nonvanishing locus containing `x`.
6. Their product `t` belongs to `I₁ L₁^(m₁+m₂)` and its nonvanishing locus contains `x`.
It is affine by `lem-sc-affine-cap-section-open`, applied inside the affine locus of `t₂`.
7. By `lem-sc-conductor-sections`, extend `t` to a section of `L^(m₁+m₂)` vanishing on
all other components. Its nonvanishing locus is the affine locus from step 6.
Together with `X_s` from step 4, these sections satisfy the absolute ampleness criterion
`def-weil-pbc-ample-invertible-module` at every point; `X` is already quasi-compact.
-/
theorem exists_isAmple_of_reduced_dim_le_one (X : Scheme.{u})
    [IsLocallyNoetherian X] [CompactSpace X] [IsReduced X] [X.IsSeparated]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ L : X.Modules, ∃ hL : L.IsInvertible, @IsAmple X L hL := by
  classical
  by_cases hzero : topologicalKrullDim X ≤ 0
  · exact ⟨CategoryTheory.MonoidalCategory.tensorUnit X.Modules, inferInstance,
      (isAffine_and_isAmple_tensorUnit_of_dim_le_zero X hzero).2⟩
  let A := {Z : Set X // Z ∈ irreducibleComponents X}
  have hparts := component_intersections_finite X hdim
  let : Fintype A := hparts.1.fintype
  let r := Fintype.card A
  let e : Fin r ≃ A := (Fintype.equivFin A).symm
  let Z (a : Fin r) : TopologicalSpace.Closeds X :=
    ⟨(e a).1, isClosed_of_mem_irreducibleComponents _ (e a).2⟩
  let I (a : Fin r) := Scheme.IdealSheafData.vanishingIdeal (Z a)
  let C (a : Fin r) := (I a).subscheme
  let i (a : Fin r) : C a ⟶ X := (I a).subschemeι
  have hrange (a : Fin r) : Set.range (i a) = (e a).1 := by
    change Set.range (I a).subschemeι = (e a).1
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I, Z]
  have hcomponents (a : Fin r) : Set.range (i a) ∈ irreducibleComponents X :=
    (hrange a).symm ▸ (e a).2
  have hdistinct : Function.Injective fun a ↦ Set.range (i a) := by
    intro a b hab
    apply e.injective
    apply Subtype.ext
    simpa only [hrange] using hab
  have hcover : (⋃ a, Set.range (i a)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨W, hW, hxW⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible {x}
      isIrreducible_singleton
    obtain ⟨a, ha⟩ := e.surjective ⟨W, hW⟩
    apply Set.mem_iUnion.mpr
    refine ⟨a, ?_⟩
    rw [hrange, ha]
    exact hxW (Set.mem_singleton x)
  have (a : Fin r) : IsClosedImmersion (i a) := inferInstance
  have (a : Fin r) : IsReduced (C a) := inferInstance
  have (a : Fin r) : IsIntegral (C a) := by
    have : IrreducibleSpace (C a) := Subtype.irreducibleSpace (e a).2.1
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  have : IsNoetherian X := ⟨⟩
  have (a : Fin r) : IsNoetherian (C a) := isNoetherian_of_locallyOfFiniteType (i a)
  have (a : Fin r) : (C a).IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from (i a)]
    infer_instance
  have hamp (a : Fin r) : ∃ M : (C a).Modules,
      ∃ hM : M.IsInvertible, @IsAmple (C a) M hM := by
    have hCdim : topologicalKrullDim (C a) ≤ 1 :=
      ((i a).isClosedEmbedding.isInducing.topologicalKrullDim_le).trans hdim
    by_cases hCzero : topologicalKrullDim (C a) ≤ 0
    · exact ⟨CategoryTheory.MonoidalCategory.tensorUnit (C a).Modules, inferInstance,
        (isAffine_and_isAmple_tensorUnit_of_dim_le_zero (C a) hCzero).2⟩
    · apply exists_isAmple_of_integral_dim_one
      apply le_antisymm hCdim
      simpa using (ENat.WithBot.add_one_le_iff (n := 0)).mpr (lt_of_not_ge hCzero)
  choose M hM hMample using hamp
  let (a : Fin r) : (M a).IsInvertible := hM a
  let T : Set X := {x | ∃ W₁ ∈ irreducibleComponents X,
    ∃ W₂ ∈ irreducibleComponents X, W₁ ≠ W₂ ∧ x ∈ W₁ ∩ W₂}
  have hT : T = {x | ∃ a b : Fin r, a ≠ b ∧
      x ∈ Set.range (i a) ∩ Set.range (i b)} := by
    ext x
    constructor
    · rintro ⟨W₁, hW₁, W₂, hW₂, hne, hx⟩
      obtain ⟨a, ha⟩ := e.surjective ⟨W₁, hW₁⟩
      obtain ⟨b, hb⟩ := e.surjective ⟨W₂, hW₂⟩
      have hab : a ≠ b := by
        intro hab
        apply hne
        exact congrArg Subtype.val (ha.symm.trans (hab ▸ hb))
      exact ⟨a, b, hab, by simpa only [hrange, ha, hb] using hx⟩
    · rintro ⟨a, b, hab, hx⟩
      exact ⟨_, hcomponents a, _, hcomponents b,
        fun heq ↦ hab (hdistinct heq), hx⟩
  obtain ⟨L, hL, hres, s, U, hTU, hU, hUs⟩ :=
    exists_glued_component_affine_section X r C i hcover T hT
      hparts.2.2.1 hparts.2.2.2.1 M hMample
  let : L.IsInvertible := hL
  refine ⟨L, hL, inferInstance, ?_⟩
  intro x
  by_cases hx : x ∈ T
  · refine ⟨1, Nat.zero_lt_one, s, U, hTU hx, hU, ?_⟩
    intro y
    change y ∈ U ↔ y ∈ nonvanishingLocus (L.tensorPow 1) s
    rw [← hUs]
    rfl
  · have hunique : ∃! a, x ∈ Set.range (i a) := by
      obtain ⟨W, ⟨hW, hxW⟩, huniq⟩ := hparts.2.2.2.2 x hx
      obtain ⟨a, ha⟩ := e.surjective ⟨W, hW⟩
      refine ⟨a, by simpa only [hrange, ha] using hxW, ?_⟩
      intro b hxb
      apply hdistinct
      change Set.range (i b) = Set.range (i a)
      rw [hrange a, ha]
      exact huniq _ ⟨hcomponents b, hxb⟩
    obtain ⟨n, hn, t, V, hxV, hV, hVt⟩ :=
      exists_component_supported_affine_section X r C i hcomponents hdistinct hcover
        L hres x hunique
    refine ⟨n, hn, t, V, hxV, hV, ?_⟩
    intro y
    change y ∈ V ↔ y ∈ nonvanishingLocus (L.tensorPow n) t
    rw [← hVt]
    rfl

end AlgebraicGeometry.Scheme.Modules
