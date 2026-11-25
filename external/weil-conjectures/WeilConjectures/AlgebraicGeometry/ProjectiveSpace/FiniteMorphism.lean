/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfAmple

/-!
# Finite morphisms and projective morphisms

A projective morphism is presented (H-projective convention) by a closed immersion
`i: X ⟶ ℙ(n; S)` over `S` with a finite type `n` of homogeneous coordinates.

* A projective morphism whose geometric fibres are finite sets is finite.
* A projective family over a Noetherian domain whose generic fibre has dimension `≤ 0` is finite
  over a nonempty open of the base.
* A scheme finite over a projective scheme over an affine base is projective over that base.

## Main statements

- `AlgebraicGeometry.ProjectiveSpace.isFinite_of_finite_pullback`
- `AlgebraicGeometry.ProjectiveSpace.exists_isFinite_morphismRestrict_of_generic_fibre`
- `AlgebraicGeometry.ProjectiveSpace.exists_isClosedImmersion_of_isFinite`

## Implementation details

The first two statements are consequences of Zariski's main theorem in the form
`AlgebraicGeometry.exists_isFinite_morphismRestrict_of_finite_preimage_singleton` (a proper
morphism is finite over a neighbourhood of every point with finite fibre), rather than of a
Serre-vanishing argument; no Noetherian hypothesis on the base is needed for the first. The third
embeds `Y` by the pullback of `𝒪(1)` along the finite morphism, whose coordinate sections have
affine non-vanishing loci covering `Y`; with the H-projective convention it needs the base to be
affine, but not Noetherian.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProjectiveSpace

variable {n : Type u} [Finite n]

/-- **Projective morphisms with finite fibres are finite.** Let `f: D ⟶ T` be projective, i.e.
`f = π ∘ i` for a closed immersion `i: D ⟶ ℙ(n; T)`. If every geometric fibre `D ×_T Spec Ω`,
for `Ω` algebraically closed, has only finitely many points, then `f` is finite. -/
theorem isFinite_of_finite_pullback {D T : Scheme.{u}} (f : D ⟶ T) (i : D ⟶ ℙ(n; T))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; T) ↘ T = f)
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T),
      Finite (pullback f t : Scheme.{u})) :
    IsFinite f := by
  subst hi
  have : LocallyQuasiFinite (i ≫ ℙ(n; T) ↘ T) := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun x ↦ ?_
    let K := T.residueField x
    let t : Spec (.of (AlgebraicClosure K)) ⟶ T :=
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))) ≫ T.fromSpecResidueField x
    have := hfib (AlgebraicClosure K) t
    refine (Set.finite_range (pullback.fst (i ≫ ℙ(n; T) ↘ T) t)).subset fun y hy ↦ ?_
    obtain ⟨p⟩ : Nonempty (Spec (.of (AlgebraicClosure K))) := inferInstance
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i ≫ ℙ(n; T) ↘ T) (g := t)
      y p (by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy
      rw [hy]; exact (T.fromSpecResidueField_apply x _).symm)
    exact ⟨z, hz⟩
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **A projective family with finite generic fibre is generically finite.** Let `A` be a
Noetherian domain with fraction field `K` and `f: D ⟶ Spec A` projective. If the
generic fibre `D_K = D ×_{Spec A} Spec K` has dimension at most zero, then `f` is finite over a
nonempty open `U` of `Spec A`. -/
theorem exists_isFinite_morphismRestrict_of_generic_fibre {A : Type u} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] {D : Scheme.{u}} (f : D ⟶ Spec (.of A)) (i : D ⟶ ℙ(n; Spec (.of A)))
    [IsClosedImmersion i] (hi : i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A) = f)
    (hD : topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))) : Scheme.{u}) ≤ 0) :
    ∃ U : (Spec (.of A)).Opens, U ≠ ⊥ ∧ IsFinite (f ∣_ U) := by
  subst hi
  set η := Spec.map (CommRingCat.ofHom (algebraMap A (FractionRing A)))
  have : IsLocallyNoetherian (pullback (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) η : Scheme.{u}) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd _ η)
  have : IsLocallyArtinian (pullback (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) η : Scheme.{u}) :=
    .of_topologicalKrullDim_le_zero hD
  have : CompactSpace (pullback (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) η : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ η)
  have : Finite (pullback (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) η : Scheme.{u}) :=
    finite_of_compact_of_discrete
  obtain ⟨p⟩ : Nonempty (Spec (.of (FractionRing A))) := inferInstance
  obtain ⟨V, hV, hfin⟩ := exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) (η p) <| by
      refine (Set.finite_range
        (pullback.fst (i ≫ ℙ(n; Spec (.of A)) ↘ Spec (.of A)) η)).subset fun y hy ↦ ?_
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback y p hy
      exact ⟨z, hz⟩
  exact ⟨V, fun h ↦ by simp [h] at hV, hfin⟩

/-- **Finite covers of projective schemes are projective.** Let `S` be affine, `f: T ⟶ S`
projective, i.e. `f = π ∘ i` for a closed immersion `i: T ⟶ ℙ(n; S)`, and `h: Y ⟶ T` finite.
Then `h ≫ f` is projective: there is a closed immersion `j: Y ⟶ ℙ(m; S)` over `S` for a finite
type `m`. -/
theorem exists_isClosedImmersion_of_isFinite {S T Y : Scheme.{u}} [IsAffine S] (f : T ⟶ S)
    (i : T ⟶ ℙ(n; S)) [IsClosedImmersion i] (hi : i ≫ ℙ(n; S) ↘ S = f) (h : Y ⟶ T)
    [IsFinite h] :
    ∃ (m : Type u) (_ : Finite m) (j : Y ⟶ ℙ(m; S)),
      IsClosedImmersion j ∧ j ≫ ℙ(m; S) ↘ S = h ≫ f := by
  subst hi
  have hs (j : n) : IsAffineOpen
      (Scheme.Modules.Hom.zeroLocus (coordinateSection n S j)).support.compl := by
    rw [compl_support_zeroLocus_coordinateSection]
    exact isAffineOpen_standardOpen n S j
  have hcov : ⨆ j, (Scheme.Modules.Hom.zeroLocus (coordinateSection n S j)).support.compl =
      ⊤ := by
    simp_rw [compl_support_zeroLocus_coordinateSection]
    exact iSup_standardOpen n S
  obtain ⟨L, hL, s, hs', hcov'⟩ :=
    Scheme.Modules.exists_isAffineOpen_compl_support_zeroLocus_of_isAffineHom (h ≫ i)
      (twist n S 1) (coordinateSection n S) hs hcov
  obtain ⟨m, hm, j, hj, hjS⟩ :=
    exists_isImmersion_projectiveSpace_of_isAffineOpen (h ≫ i ≫ ℙ(n; S) ↘ S) L s hs' hcov'
  refine ⟨m, hm, j, ?_, by simpa using hjS⟩
  have : IsProper (j ≫ ℙ(m; S) ↘ S) := hjS ▸ inferInstance
  have : IsProper j := IsProper.of_comp j (ℙ(m; S) ↘ S)
  exact (IsClosedImmersion.iff_isProper_and_mono j).mpr ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.ProjectiveSpace
