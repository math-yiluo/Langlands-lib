/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import WeilConjectures.AlgebraicGeometry.StrictPerfectClosedPushforwardStalkModel
import WeilConjectures.Algebra.Homology.BoundedProjectiveNonpositiveModel
import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks

/-! # Bounded projective resolutions of closed-pushforward stalks

Source: Stacks Project, Duality for Schemes, Tag 0A9U, hypothesis translation;
Cohomology of Sheaves, Tags 08C4 and 08CM; More on Algebra, Tag 066Q
(lemma-perfect-module).
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-resolution).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Reverse the nonpositive indices and augment by degree-zero homology.
Source: Stacks Project, Tag 066Q, and the index-reversal portion of
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-resolution). -/
private theorem nonpositiveProjective_resolution
    {C : Type*} [Category C] [Abelian C]
    (Q : CochainComplex C ℤ) (M : C) (a : ℤ)
    (hbelow : ∀ j : ℤ, j < a → IsZero (Q.X j))
    (hproj : ∀ j : ℤ, Projective (Q.X j))
    (hpositive : ∀ j : ℤ, 0 < j → IsZero (Q.X j))
    (hnegative : ∀ j : ℤ, j < 0 → IsZero (Q.homology j))
    (e : Q.homology 0 ≅ M) :
    ∃ (P : ProjectiveResolution M) (n : ℕ),
      ∀ j : ℕ, n < j → IsZero (P.complex.X j) := by
  let emb := ComplexShape.embeddingUpIntLE 0
  let T := Q.restriction emb
  have hd : Q.d 0 1 = 0 := (hpositive 1 (by omega)).eq_of_tgt _ _
  let E : T.opcycles 0 ≅ M :=
    Q.restrictionOpcyclesIso emb 1 0 (i' := -1) (j' := 0) (by simp) (by simp [emb])
      (by simp [emb]) (by simp) ≪≫ (Q.isoHomologyι 0 1 (by simp) hd).symm ≪≫ e
  let π : T ⟶ (ChainComplex.single₀ C).obj M :=
    (ChainComplex.toSingle₀Equiv T M).symm
      ⟨T.pOpcycles 0 ≫ E.hom, by simp⟩
  have hπ : QuasiIso π := by
    constructor
    intro j
    cases j with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk (T.d 1 0) (π.f 0) _).Exact ∧ Epi (π.f 0)
        dsimp only [π]
        simp only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
        refine ⟨?_, inferInstance⟩
        let S := ShortComplex.mk (T.d 1 0) (T.pOpcycles 0) (by simp)
        have hS : S.Exact :=
          ShortComplex.exact_of_g_is_cokernel S (T.opcyclesIsCokernel 1 0 (by simp))
        exact ShortComplex.exact_of_iso (S₁ := S)
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) E (by simp [S]) (by simp [S])) hS
      all_goals simp
    | succ j =>
      rw [quasiIsoAt_iff_exactAt' π (j + 1)
        (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff_isZero_homology]
      let H : T.homology (j + 1) ≅ Q.homology (-(j + 1 : ℤ)) :=
        Q.restrictionHomologyIso emb (j + 2) (j + 1) j
          (i' := -(j + 2 : ℤ)) (j' := -(j + 1 : ℤ)) (k' := -(j : ℤ)) (by simp) (by simp)
          (by simp [emb]) (by simp [emb]) (by simp [emb])
          (by simp; omega) (by simp)
      exact (hnegative _ (by omega)).of_iso H
  let P : ProjectiveResolution M :=
    { complex := T
      projective := fun j ↦ hproj (emb.f j)
      π := π
      quasiIso := hπ }
  refine ⟨P, a.natAbs, ?_⟩
  intro j hj
  exact hbelow (emb.f j) (by simp only [emb, ComplexShape.embeddingUpIntLE_f]; omega)

/-- A specified strictly perfect local model of the ordinary pushforward in degree zero
along a closed immersion gives a bounded projective resolution of the source stalk
restricted to the target stalk. No Tor assertion or tensor test module is involved.

Source: Stacks Project, Tags 08C4 and 08CM, and More on Algebra, Tag 066Q
(lemma-perfect-module); hypothesis translation for Duality, Tag 0A9U.
(blueprint: lem-sc-strict-perfect-closed-pushforward-stalk-resolution).

Proof. Closed-pushforward stalks identify the ordinary pushforward at i(x) with
restriction of scalars of the source stalk. Restriction to a neighbourhood preserves
the stalk, and the exact stalk functor preserves quasi-isomorphisms. Apply it to the
given derived isomorphism over U. Taking stalks of K thus gives a bounded complex
representing the restricted source stalk in degree zero. Each term is projective:
the finite-free retraction in
IsStrictlyPerfect becomes a retraction of a finite free module on stalks.
The first two steps are isolated in `strictPerfectClosedPushforward_stalkModel`.
The remaining tail removal is `CochainComplex.boundedProjective_nonpositiveModel`.
The helper `nonpositiveProjective_resolution` proves the augmentation, quasi-isomorphism,
index reversal and bound from the output of these two intermediate statements.
Starting at the highest positive nonzero degree, split the surjection onto the
last projective term, which exists by exactness in that degree. Remove the resulting
contractible two-term summand and repeat down to degree one. The remaining complex
is concentrated in nonpositive degrees, with projective terms, and its degree-zero
cokernel is the restricted source stalk. Reverse the indices to obtain an augmented
projective resolution indexed by natural numbers. The original lower bound for K
makes its terms zero above a natural-number bound. This works also for an acyclic
model: the restricted stalk is then zero, and its zero resolution suffices. -/
theorem strictPerfectClosedPushforward_stalkResolution
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (x : Z) (U : Y.Opens) (hx : i x ∈ U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (hK : Y.IsStrictlyPerfect U K)
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))) ≅
      DerivedCategory.Q.obj K) :
    ∃ (P : ProjectiveResolution
      ((ModuleCat.restrictScalars (i.stalkMap x).hom).obj
        (ModuleCat.of (Z.presheaf.stalk x) (Z.presheaf.stalk x)))) (n : ℕ),
      ∀ j : ℕ, n < j → IsZero (P.complex.X j) := by
  obtain ⟨L, hbound, hproj, ⟨eL⟩, hhomology⟩ :=
    strictPerfectClosedPushforward_stalkModel i x U hx K hK e
  obtain ⟨Q, a, hbelow, hQproj, hpositive, ι, hι⟩ :=
    L.boundedProjective_nonpositiveModel hbound hproj
      (fun j hj ↦ hhomology j (by omega))
  have hQhomology (j : ℤ) : Nonempty (Q.homology j ≅ L.homology j) :=
    ⟨asIso (HomologicalComplex.homologyMap ι j)⟩
  obtain ⟨eQ⟩ := hQhomology 0
  apply nonpositiveProjective_resolution Q _ a hbelow hQproj hpositive
    (fun j hj ↦ ?_) (eQ ≪≫ eL)
  obtain ⟨ej⟩ := hQhomology j
  exact (hhomology j (by omega)).of_iso ej

end AlgebraicGeometry
