/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.DeligneLaumon.Reduction.FibreCohomology
public import WeilConjectures.DeligneLaumon.Reduction.FormalSteps
public import WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights
public import WeilConjectures.WeilSheaf.LisseLocus
public import WeilConjectures.WeilSheaf.StalkExact
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.Triangle

/-!
# Compactly supported cohomology through direct images with compact support

For a separated `k₀`-scheme `X` of finite type, the compactly supported cohomology `H_c^r(X, F)`
of a Weil sheaf is `H_c^0` of the higher direct image `Rʳf₀!F` to `Spec k₀`, and for a separated
quasi-finite morphism `f : X ⟶ Y` it is `H_c^r(Y, f₀!F)`. Exact sequences of Weil sheaves
give exact sequences of stalks (`AlgebraicGeometry.WeilSheaf.range_stalkAtMap_eq_ker`), so that
punctual upper weight bounds pass to the middle term of an exact sequence.

## Main statements

- `AlgebraicGeometry.WeilSheaf.HasWeightsAtMost.of_exact`
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek`
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  (ι : PadicAlgCl l →+* ℂ)

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

variable {ι}

/-- In an exact sequence `A ⟶ B ⟶ C` of Weil sheaves whose outer terms have punctual weights at
most `v`, so has the middle term: the stalks form an exact sequence of Frobenius modules
(blueprint: `lemma-weight-bounds-partitions`, step 0, punctual form). -/
theorem HasWeightsAtMost.of_exact {S : ShortComplex (WeilSheaf k₀ l X)} (hS : S.Exact) {v : ℝ}
    (h₁ : S.X₁.HasWeightsAtMost ι v) (h₃ : S.X₃.HasWeightsAtMost ι v) :
    S.X₂.HasWeightsAtMost ι v := by
  have := hS.epi_kernelLift
  intro x
  exact FrobeniusModule.HasWeightsAtMost.of_exact _ (stalkAtMap_frobenius _ _ _ (kernel.ι S.g))
    _ (stalkAtMap_frobenius _ _ _ (Abelian.coimage.π S.g)) (injective_stalkAtMap _ _ _ _)
    (range_stalkAtMap_eq_ker (ShortComplex.exact_cokernel (kernel.ι S.g)) _ _ _)
    ((h₁.of_epi (kernel.lift S.g S.f S.zero)) x) ((h₃.of_mono (Abelian.factorThruCoimage S.g)) x)

end WeilSheaf

section CompactSupport

/-- Isomorphic Weil sheaves have isomorphic compactly supported cohomology, with its
Frobenius. -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_of_iso {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] {F G : WeilSheaf k₀ l X} (e : F ≅ G) (r : ℤ) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv (G.compactlySupportedCohomology r)) :=
  ⟨WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf r).mapIso
    ((WeilComplex.derivedLowerShriek k₀ l _).mapIso (WeilSheaf.toComplex.mapIso e)))⟩

/-- **Compactly supported cohomology as a direct image to the point.** For a separated
`k₀`-scheme `X` of finite type and a morphism `f : X ⟶ Spec k₀` over `k₀` (that is, the structure
morphism), `H_c^0(Spec k₀, Rʳf₀!F) ≅ H_c^r(X, F)` as Frobenius modules: `R(id)₀!` is concentrated
in degree zero on Weil sheaves, and `R(f ≫ id)₀! ≅ R(id)₀! ∘ Rf₀!` (blueprint:
`theorem-pure-lisse-sheaves-over-relative--1`, the stalks of `Rʳf₀!F` over a point). -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Spec (CommRingCat.of k₀)) [f.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (F : WeilSheaf k₀ l X) (r : ℕ) :
    Nonempty ((((WeilSheaf.higherLowerShriek k₀ l f r).obj F).compactlySupportedCohomology
      0).Equiv (F.compactlySupportedCohomology r)) := by
  have ha (G : WeilSheaf k₀ l (Spec (CommRingCat.of k₀))) (n : ℤ) (hn : n ≠ 0) :
      IsZero ((WeilComplex.homologySheaf n).obj
        ((WeilComplex.derivedLowerShriek k₀ l
          (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))).obj
            (WeilSheaf.toComplex.obj G))) := by
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg G hn
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn.le).symm⟩
      exact isZero_higherLowerShriek_of_quasiFinite
        (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀)) m (by exact_mod_cast hn) G
  let L := (WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)
  obtain ⟨e₂⟩ := WeilComplex.nonempty_homologySheaf_map_iso
    (WeilComplex.derivedLowerShriek k₀ l
      (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))) ha L r
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f
    (Spec (CommRingCat.of k₀) ↘ Spec (CommRingCat.of k₀))
  let E := (e₅.app _).symm ≪≫
    (WeilComplex.derivedLowerShriekCongr (comp_over f _)).app (WeilSheaf.toComplex.obj F)
  exact ⟨WeilSheaf.globalSectionsEquivOfIso
    (e₂.symm ≪≫ (WeilComplex.homologySheaf r).mapIso E)⟩

/-- **Compactly supported cohomology along a quasi-finite morphism.** For a separated
quasi-finite morphism `f : X ⟶ Y` of separated `k₀`-schemes of finite type and a Weil sheaf `F`
on `X`, `H_c^r(X, F) ≅ H_c^r(Y, f₀!F)` as Frobenius modules, for every `r`: `Rf₀!F` is `f₀!F`
placed in degree zero, and `R(f ≫ a_Y)₀! ≅ R(a_Y)₀! ∘ Rf₀!` (blueprint:
`lemma-finite-quasi-finite-direct-images`, `proposition-composition-base-change-rf-shriek--1`). -/
theorem WeilSheaf.nonempty_equiv_compactlySupportedCohomology_higherLowerShriek_zero
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] [QuasiCompact f] (F : WeilSheaf k₀ l X) (r : ℤ) :
    Nonempty ((F.compactlySupportedCohomology r).Equiv
      (((WeilSheaf.higherLowerShriek k₀ l f 0).obj F).compactlySupportedCohomology r)) := by
  -- `Rf₀!F` is `f₀!F` placed in degree zero
  obtain ⟨e₂⟩ := WeilComplex.nonempty_iso_toComplex_homologySheaf_zero
    ((WeilComplex.derivedLowerShriek k₀ l f).obj (WeilSheaf.toComplex.obj F)) fun b hb ↦ by
      rcases lt_or_gt_of_ne hb with hb | hb
      · exact WeilSheaf.isZero_homologySheaf_derivedLowerShriek_of_neg F hb
      · obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = n := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
        exact isZero_higherLowerShriek_of_quasiFinite f n (by exact_mod_cast hb) F
  obtain ⟨e₅⟩ := WeilComplex.nonempty_derivedLowerShriek_comp_iso (k₀ := k₀) (l := l) f
    (Y ↘ Spec (CommRingCat.of k₀))
  let E := (WeilComplex.derivedLowerShriekCongr (comp_over f _).symm).app
      (WeilSheaf.toComplex.obj F) ≪≫ e₅.app _ ≪≫
    (WeilComplex.derivedLowerShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))).mapIso e₂
  exact ⟨WeilSheaf.globalSectionsEquivOfIso ((WeilComplex.homologySheaf r).mapIso E)⟩

end CompactSupport

section FiniteComplement

omit [Finite k₀] in
/-- **The closed complement of an open with finite complement.** If `U` is an open subscheme of a
`k₀`-scheme `X` locally of finite type whose complement is finite, the reduced closed subscheme
`Z` on the complement is finite over `k₀`. -/
theorem Scheme.Opens.exists_isClosedImmersion_isFinite_compl {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (U : X.Opens) (hU : ((U : Set X)ᶜ).Finite) :
    ∃ (Z : Scheme.{u}) (_ : Z.Over (Spec (CommRingCat.of k₀))) (i : Z ⟶ X)
      (_ : IsClosedImmersion i) (_ : i.IsOver (Spec (CommRingCat.of k₀))),
      Set.range i.base = (U : Set X)ᶜ ∧ IsFinite (Z ↘ Spec (CommRingCat.of k₀)) := by
  let C : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let i := (Scheme.IdealSheafData.vanishingIdeal C).subschemeι
  let : (Scheme.IdealSheafData.vanishingIdeal C).subscheme.Over (Spec (CommRingCat.of k₀)) :=
    ⟨i ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : i.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  have hrange : Set.range i.base = C := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  refine ⟨_, _, i, inferInstance, ‹_›, hrange, ?_⟩
  have : LocallyQuasiFinite (i ≫ X ↘ Spec (CommRingCat.of k₀)) :=
    .of_finite_preimage_singleton _ fun _ ↦
      (hU.preimage i.isClosedEmbedding.injective.injOn).subset fun z _ ↦
        (hrange ▸ ⟨z, rfl⟩ : i.base z ∈ (C : Set X))
  have : Finite (Scheme.IdealSheafData.vanishingIdeal C).subscheme :=
    Set.finite_univ_iff.mp ((hU.preimage i.isClosedEmbedding.injective.injOn).subset fun z _ ↦
      (hrange ▸ ⟨z, rfl⟩ : i.base z ∈ (C : Set X)))
  have : QuasiCompact (i ≫ X ↘ Spec (CommRingCat.of k₀)) :=
    (quasiCompact_iff_compactSpace _).mpr inferInstance
  exact IsFinite.of_locallyQuasiFinite (i ≫ X ↘ Spec (CommRingCat.of k₀))

variable {ι}

/-- **Removing finitely many points.** Let `U` be an open subscheme with finite complement of a
separated `k₀`-scheme `X` of finite type and let `F` be a Weil sheaf on `X`. For `r > 0`, the
group `H_c^r(X, F)` is a Frobenius-equivariant quotient of `H_c^r(U, F|_U)`: in the open–closed
exact sequence the term `H_c^r` of the finite complement vanishes. Hence upper weight bounds pass
from `H_c^r(U, F|_U)` to `H_c^r(X, F)`. -/
theorem WeilSheaf.hasWeightsAtMostOver_compactlySupportedCohomology_of_upperStar_of_isOpenImmersion
    {X U : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [U.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
    [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (hU : ((Set.range j.base)ᶜ).Finite) (F : WeilSheaf k₀ l X) {r : ℕ} (hr : 0 < r) {v : ℝ}
    (h : (((WeilSheaf.upperStar j).obj F).compactlySupportedCohomology r).HasWeightsAtMostOver
      k₀ ι v) :
    (F.compactlySupportedCohomology r).HasWeightsAtMostOver k₀ ι v := by
  obtain ⟨Z, _, i, _, _, hrange, _⟩ :=
    j.opensRange.exists_isClosedImmersion_isFinite_compl (k₀ := k₀) (by simpa using hU)
  have : LocallyQuasiFinite (i ≫ X ↘ Spec (CommRingCat.of k₀)) := by
    rw [comp_over]
    infer_instance
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := WeilSheaf.exists_exact_higherLowerShriek_of_openClosed
    (j := j) (i := i) (f := X ↘ Spec (CommRingCat.of k₀))
    (by rw [hrange, Scheme.Hom.coe_opensRange]; exact isCompl_compl) F r
  have h₁ : S.X₁.HasWeightsAtMost ι v := by
    obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
      (j ≫ X ↘ Spec (CommRingCat.of k₀)) ((WeilSheaf.upperStar j).obj F) r
    exact (WeilSheaf.hasWeightsAtMost_of_compactlySupportedCohomology_zero
      (FrobeniusModule.HasWeightsAtMost.of_equiv E h)).of_epi e₁.inv
  have h₃ : S.X₃.HasWeightsAtMost ι v :=
    WeilSheaf.HasWeightsAtMost.of_epi e₃.inv (WeilSheaf.isPunctuallyPureOfWeight_of_isZero
      (isZero_higherLowerShriek_of_quasiFinite _ r hr _) v).hasWeightsAtMost
  obtain ⟨E⟩ := WeilSheaf.nonempty_equiv_compactlySupportedCohomology_zero_higherLowerShriek
    (X ↘ Spec (CommRingCat.of k₀)) F r
  exact FrobeniusModule.HasWeightsAtMost.of_equiv E.symm
    ((WeilSheaf.HasWeightsAtMost.of_exact hS h₁ h₃).of_epi
      e₂.hom).compactlySupportedCohomology_zero

end FiniteComplement

end AlgebraicGeometry
