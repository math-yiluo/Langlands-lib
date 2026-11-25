/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.AffineRestrictedTwistVanishing
import WeilConjectures.AlgebraicGeometry.HigherDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.LocalUniformHigherDirectImageBound
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction

/-! # Vanishing of twists over one affine open

Source: Stacks Project, Tag 02O1, affine-local part of Lemma 30.16.2.
(blueprint: lem-pc-q3-affine-open-twist-vanishing-independent)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

private theorem affine_zero_of_sections {T : Scheme.{u}} [IsAffine T]
    (N : T.Modules) [N.IsQuasicoherent] [Subsingleton Γ(N, ⊤)] : IsZero N := by
  let P := N.restrict T.isoSpec.inv
  have : P.IsQuasicoherent := isQuasicoherent_restrictFunctor _ _
  have : Subsingleton Γ(P, ⊤) := by
    have h : T.isoSpec.inv ''ᵁ (⊤ : (Spec Γ(T, ⊤)).Opens) = ⊤ := by simp
    have : Subsingleton Γ(N, T.isoSpec.inv ''ᵁ ⊤) := h.symm ▸ inferInstance
    exact (N.restrictAppIso T.isoSpec.inv ⊤).addCommGroupIsoToAddEquiv.toEquiv.injective
      |>.subsingleton
  have hP : IsZero P := by
    have : Subsingleton ((moduleSpecΓFunctor (R := Γ(T, ⊤))).obj P) :=
      inferInstanceAs (Subsingleton Γ(P, ⊤))
    have hz := (tilde.functor Γ(T, ⊤)).map_isZero
      (ModuleCat.isZero_of_subsingleton ((moduleSpecΓFunctor (R := Γ(T, ⊤))).obj P))
    exact hz.of_iso (asIso P.fromTildeΓ).symm
  have hz := (restrictFunctor T.isoSpec.hom).map_isZero hP
  let e := ((restrictFunctorComp T.isoSpec.hom T.isoSpec.inv).symm ≪≫
    restrictFunctorCongr T.isoSpec.hom_inv_id ≪≫ restrictFunctorId).app N
  exact hz.of_iso e.symm

/-- Serre vanishing over a specified affine open, without the global-cover step.

Source: Stacks Project, Tag 02O1, proof of Lemma 30.16.2, and Tag 0B5T.
(blueprint: lem-pc-q3-affine-open-twist-vanishing-independent)

Proof: put X_V = f inverse-image V. The restriction f_V is proper over the
Noetherian affine scheme V. Coherence and quasi-coherence of F restrict to X_V;
the given invertible restriction of L is ample there. Serre vanishing (Tag 0B5T (4))
gives a threshold in each positive degree.
A finite affine cover of the separated quasi-compact scheme X_V bounds the
cohomological degree of every quasi-coherent module by its Cech complex.
The maximum of the thresholds in these finitely many positive degrees
therefore works for F|X_V tensor (L|X_V)^n in every positive degree. The affine-base
comparison identifies these cohomology
groups with sections of R^q(f_V)_* of that twist. These higher images are
quasi-coherent, hence zero when their sections over the affine base vanish.
Restriction of higher direct images to V identifies them with the higher
images of f_V, and restriction commutes with tensor products and tensor powers.
Transporting these identifications gives the displayed restricted vanishing.
There is no finite-cover or uniform-threshold argument here. Empty V causes
no exception: its category of modules is zero and threshold zero works.
-/
theorem exists_isZero_higherDirectImage_twist_on_affine_open
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (L : X.Modules) [L.IsInvertible]
    (V : S.Opens) (hV : IsAffineOpen V)
    (hL : ∃ h : (L.restrict (f ⁻¹ᵁ V).ι).IsInvertible,
      @IsAmple (f ⁻¹ᵁ V).toScheme (L.restrict (f ⁻¹ᵁ V).ι) h)
    [HasInjectiveResolutions X.Modules] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ q : ℕ, 0 < q →
      IsZero (((higherDirectImage f q).obj (F ⊗ L.tensorPow n)).restrict V.ι) := by
  classical
  let Y := (f ⁻¹ᵁ V).toScheme
  let T := V.toScheme
  let g : Y ⟶ T := f ∣_ V
  let : IsAffine T := hV
  let : EnoughInjectives Y.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives Y.toRingedSpace).2
  choose U b ht hb using exists_local_uniform_higherDirectImage_bound g
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun t ↦ (U t : Set T))
    (fun t ↦ (U t).isOpen) (fun t _ ↦ Set.mem_iUnion.mpr ⟨t, ht t⟩)
  let d := s.sup b
  have hd (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) (hq : d ≤ q) :
      IsZero ((higherDirectImage g q).obj M) := by
    refine isZero_of_iSup_eq_top _ (fun t : s ↦ U t) ?_
      (fun t ↦ hb t M inferInstance q ((Finset.le_sup t.property).trans hq))
    apply eq_top_iff.mpr
    intro t _
    obtain ⟨i, hi, hti⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hti⟩
  have degree (q : Fin d) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < q.val →
      IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace q.val).obj
        ((F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι)) := by
    by_cases hq : 0 < q.val
    · obtain ⟨n₀, hn₀⟩ := exists_isZero_restricted_twist_moduleCohomology_degree
        f F hF L V hV hL q.val hq
      exact ⟨n₀, fun n hn _ ↦ hn₀ n hn⟩
    · exact ⟨0, fun _ _ h ↦ (hq h).elim⟩
  choose n₀ hn₀ using degree
  refine ⟨∑ q, n₀ q, ?_⟩
  intro n hn q hq
  let M := (F ⊗ L.tensorPow n).restrict (f ⁻¹ᵁ V).ι
  have : (F ⊗ L.tensorPow n).IsQuasicoherent :=
    isQuasicoherent_tensorObj F (L.tensorPow n)
  have : M.IsQuasicoherent := isQuasicoherent_restrictFunctor _ _
  have hz : IsZero ((higherDirectImage g q).obj M) := by
    by_cases hqd : d ≤ q
    · exact hd M q hqd
    · let i : Fin d := ⟨q, by omega⟩
      have hi : n₀ i ≤ n := le_trans
        (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)) hn
      have hcoh := hn₀ i n hi hq
      obtain ⟨c, _⟩ := exists_moduleCohomology_source_comparison Y q
      have : Subsingleton ((RingedSpace.moduleCohomology Y.toRingedSpace q).obj M) :=
        ModuleCat.subsingleton_of_isZero hcoh
      have : Subsingleton (M.H q) := (c M).symm.toEquiv.injective.subsingleton
      obtain ⟨e⟩ := nonempty_sections_higherDirectImage_iso_H g M q
      have : Subsingleton Γ((higherDirectImage g q).obj M, ⊤) :=
        e.toEquiv.injective.subsingleton
      have : ((higherDirectImage g q).obj M).IsQuasicoherent :=
        isQuasicoherent_higherDirectImage g M q
      exact affine_zero_of_sections ((higherDirectImage g q).obj M)
  let G : X.Modules := F ⊗ L.tensorPow n
  obtain ⟨e⟩ := nonempty_higherDirectImage_openRestriction_iso f V G q
  exact hz.of_iso e.symm

end AlgebraicGeometry.Scheme.Modules
