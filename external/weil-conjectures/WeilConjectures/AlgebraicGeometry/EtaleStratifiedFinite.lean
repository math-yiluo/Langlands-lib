/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.EtaleAffineCoverStratification
import WeilConjectures.AlgebraicGeometry.EtaleSeparatedStratifiedFinite
import WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluing
import Mathlib.AlgebraicGeometry.Cover.Open
import WeilConjectures.AlgebraicGeometry.ConstructibleStratificationAssembly
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Etale morphisms become finite etale on constructible strata

Source: Stacks Project, Etale Cohomology, Lemma 59.72.1, Tag 03S0
(blueprint: lem-weil-pbc-etale-stratified-finite).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem exists_finite_affine_open_cover (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] :
    ∃ (n : ℕ) (W : Fin n → X.Opens),
      (∀ i, IsAffineOpen (W i)) ∧ TopologicalSpace.IsOpenCover W := by
  classical
  let C := X.affineCover.finiteSubcover
  let e := (Fintype.equivFin C.I₀).symm
  let W (i : C.I₀) := (C.f i).opensRange
  refine ⟨Fintype.card C.I₀, fun i ↦ W (e i), ?_, ?_⟩
  · intro i
    exact isAffineOpen_opensRange (C.f (e i))
  · exact TopologicalSpace.IsOpenCover.mk
      ((e.surjective.iSup_comp W).trans C.iSup_opensRange)

private theorem finite_etale_pullback_comp {X U Y Z : Scheme.{u}}
    (j : U ⟶ X) (g : Y ⟶ X) (h : Z ⟶ Y)
    [IsFinite (pullback.snd (pullback.snd j g) h)]
    [Etale (pullback.snd (pullback.snd j g) h)] :
    IsFinite (pullback.snd j (h ≫ g)) ∧ Etale (pullback.snd j (h ≫ g)) := by
  let e := pullbackLeftPullbackSndIso j g h
  have he : e.inv ≫ pullback.snd (pullback.snd j g) h =
      pullback.snd j (h ≫ g) := pullbackLeftPullbackSndIso_inv_snd_snd j g h
  rw [← he]
  exact ⟨inferInstance, inferInstance⟩

private theorem exists_etale_stratified_finite_affine {X U : Scheme.{u}}
    [IsAffine X] [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j] :
    ∃ S : Stratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i)) := by
  classical
  obtain ⟨m, A, hA, hcover⟩ := exists_finite_affine_open_cover U
  obtain ⟨n, Y, ι, hY, hd, hu, _, _, hsep⟩ :=
    exists_etale_affine_cover_stratification j m A hA hcover.iSup_eq_top
  have hlocal (i : Fin n) : ∃ T : Stratification (Y i),
      (∀ b, Topology.IsConstructible (T.stratum b)) ∧
      ∀ b, IsFinite (pullback.snd (pullback.snd j (ι i)) (T.immersion b)) ∧
        Etale (pullback.snd (pullback.snd j (ι i)) (T.immersion b)) := by
    have : IsAffine (Y i) := (hY i).1
    have : IsSeparated (pullback.snd j (ι i)) := hsep i
    exact exists_etale_separated_stratified_finite (pullback.snd j (ι i))
  choose T hc hfinite using hlocal
  apply exists_stratification_of_stratified_partition n Y ι
    (fun i ↦ (hY i).2.1) (fun i ↦ (hY i).2.2) hd hu T
    (fun Z f ↦ IsFinite (pullback.snd j f) ∧ Etale (pullback.snd j f))
  intro i b
  have := (hfinite i b).1
  have := (hfinite i b).2
  exact finite_etale_pullback_comp j (ι i) ((T i).immersion b)

/-- An etale morphism between quasi-compact quasi-separated schemes is finite etale
after restriction to each member of a finite constructible locally closed stratification.
Source: Stacks Project, Tag 03S0 (blueprint: lem-weil-pbc-etale-stratified-finite).

Proof:
1. Obtain finite affine open covers of both U and X using Mathlib's
   `Scheme.OpenCover.finiteSubcover`, reindexing their finite types by Fin.
2. On an affine base, `lem-weil-pbc-etale-affine-cover-gluing` gives a constructible
   immersed affine partition on which the pullback of j is separated.
3. Apply `lem-weil-pbc-etale-separated-stratified-finite` on each affine piece.
   `lem-weil-pbc-constructible-stratification-assembly` assembles these local
   stratifications using the composite immersion maps. Pullback pasting identifies
   their finite etale morphisms with the pullbacks along those composite maps.
4. Apply this affine result to the pullback of j to every member of the finite affine
   open cover of X. Quasi-compactness and quasi-separatedness persist under these
   pullbacks. Pullback pasting again gives the required composite stratum maps, and
   `lem-weil-pbc-etale-stratification-local-gluing` provides the global partition. -/
theorem exists_etale_stratified_finite {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace U] [QuasiSeparatedSpace U] (j : U ⟶ X) [Etale j] :
    ∃ S : Stratification X,
      (∀ i : Fin S.n, Topology.IsConstructible (S.stratum i)) ∧
      (∀ i : Fin S.n,
        IsFinite (pullback.snd j (S.immersion i)) ∧
        Etale (pullback.snd j (S.immersion i))) := by
  classical
  obtain ⟨n, W, hW, hcover⟩ := exists_finite_affine_open_cover X
  apply exists_constructible_stratification_finite_etale_of_affine_local j
  refine ⟨n, W, hW, hcover.iSup_set_eq_univ, ?_⟩
  intro a
  have : IsAffine (W a) := hW a
  have : QuasiSeparatedSpace (pullback (C := Scheme.{u}) j (W a).ι) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd j (W a).ι)
  obtain ⟨S, hc, hf⟩ :=
    exists_etale_stratified_finite_affine (pullback.snd j (W a).ι)
  refine ⟨S, hc, ?_⟩
  intro b
  have := (hf b).1
  have := (hf b).2
  exact finite_etale_pullback_comp j (W a).ι (S.immersion b)

end AlgebraicGeometry.Scheme
