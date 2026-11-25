/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank

/-! # Finitely many ranks on an affine part of the universal rank locus

Source: Stacks Project, Tag 0BDP, first proof paragraph.
(blueprint: lem-sc-picard-universal-rank-match-finite-ranks).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem finiteLocallyFreeOfRank_of_isEmpty {T : Scheme.{u}} [IsEmpty T]
    (M : T.Modules) (r : ℕ) : M.IsFiniteLocallyFreeOfRank r := by
  apply (SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free
    (M := M) (r := r)).mpr
  refine ⟨PEmpty.{u + 1}, PEmpty.elim, ?_, fun i ↦ PEmpty.elim i⟩
  intro V x hx
  exact isEmptyElim x

/-- A finite rank bound for all fibre restrictions over an affine open.
Source: Stacks Project, Tag 0BDP, rank decomposition paragraph.
Properness makes the inverse image of an affine open quasi-compact. A finite
trivializing subcover of the finite locally free sheaf then has finitely many
ranks; every rank on a nonempty fibre is one of these ranks: choose a fibre point,
choose a covering open containing its image, and compare both trivializations
over the residue field of that point. Adjoin zero to the finite set. Empty
fibres are excluded from the rank comparison because all ranks coincide there. -/
private theorem picardUniversalRankMatch_finiteRankBound {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ R : Finset ℕ, 0 ∈ R ∧ ∀ s : S, s ∈ U →
      Nonempty (pullback f (S.fromSpecResidueField s) : Scheme.{u}) → ∀ r : ℕ,
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r →
      r ∈ R := by
  classical
  choose V I hI hx e using Modules.exists_mem_over_iso_free E
  let n (x : X) := Fintype.card (I x)
  have hE (x : X) : (E.restrict (V x).ι).IsFiniteLocallyFreeOfRank (n x) := by
    let e' : E.restrict (V x).ι ≅ SheafOfModules.free (ULift.{u} (Fin (n x))) :=
      Modules.overIsoFreeEquiv E (V x) (I x) (e x).some ≪≫
        SheafOfModules.freeFunctor.mapIso
          ((Fintype.equivFin (I x)).trans Equiv.ulift.symm).toIso
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e'.symm
  obtain ⟨A, hA⟩ := (f.isCompact_preimage hU.isCompact).elim_finite_subcover
    (fun x ↦ (V x : Set X)) (fun x ↦ (V x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨insert 0 (A.image n), Finset.mem_insert_self .., ?_⟩
  intro s hs hne r hr
  obtain ⟨z⟩ := hne
  let g := S.fromSpecResidueField s
  let q := pullback.fst f g
  have hz : q z ∈ f ⁻¹ᵁ U := by
    change f ((pullback.fst f g) z) ∈ U
    rw [← Hom.comp_apply, pullback.condition, Hom.comp_apply]
    change (S.fromSpecResidueField s) ((pullback.snd f g) z) ∈ U
    rwa [fromSpecResidueField_apply]
  obtain ⟨x, hxA, hzx⟩ := Set.mem_iUnion₂.mp (hA hz)
  let W := q ⁻¹ᵁ V x
  let a := q ∣_ V x
  let N := (Modules.pullback q).obj E
  let ec : Modules.tensorPullback q ≅ Modules.pullback q :=
    (Modules.nonempty_tensorPullbackAdjunction q).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction q)
  let := hr
  have hNr : N.IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (ec.app E)
  let := hNr
  let := hE x
  let ee : N.restrict W.ι ≅ (Modules.pullback a).obj (E.restrict (V x).ι) :=
    (Modules.restrictFunctorIsoPullback W.ι).app N ≪≫
      (Modules.pullbackComp W.ι q).app E ≪≫
      (Modules.pullbackCongr (morphismRestrict_ι q (V x)).symm).app E ≪≫
      (Modules.pullbackComp a (V x).ι).symm.app E ≪≫
      (Modules.pullback a).mapIso ((Modules.restrictFunctorIsoPullback (V x).ι).symm.app E)
  have hNn : (N.restrict W.ι).IsFiniteLocallyFreeOfRank (n x) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ee.symm
  have hn : r = n x := by
    let z' : W.toScheme := ⟨z, hzx⟩
    have h₁ := Modules.finiteLocallyFreeOfRank_stalk_finrank (N.restrict W.ι) r z'
    let := hNn
    have h₂ := Modules.finiteLocallyFreeOfRank_stalk_finrank (N.restrict W.ι) (n x) z'
    exact h₁.symm.trans h₂
  rw [hn]
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hxA, rfl⟩)

/-- Local rank extraction from the universal rank condition.
Source: Stacks Project, Tag 0BDP, specialization to the identity of the residue field.
The identity test scheme has one point, so the neighbourhood supplied by
`PicardUniversalRankMatch` is the whole scheme; pulling back along its inclusion
therefore gives a finite locally free fibre module of one constant rank. -/
private theorem picardUniversalRankMatch_localRank {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (s : S)
    (h : PicardUniversalRankMatch f E (S.fromSpecResidueField s)) :
    ∃ r : ℕ,
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r := by
  classical
  let T := Spec (S.residueField s)
  let g := S.fromSpecResidueField s
  obtain ⟨U, ht, r, _, _, hr⟩ := h (𝟙 T) (IsLocalRing.closedPoint (S.residueField s))
  have hU : U = ⊤ := by
    apply eq_top_iff.mpr
    intro t _
    rwa [Subsingleton.elim t (IsLocalRing.closedPoint (S.residueField s))]
  subst U
  have : IsIso (⊤ : T.Opens).ι := inferInstanceAs (IsIso T.topIso.hom)
  let a := pullback.map f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g) f g
    (𝟙 X) (⊤ : T.Opens).ι (𝟙 S) (by simp) (by simp)
  have : IsIso a := by dsimp [a]; infer_instance
  have ha : a ≫ pullback.fst f g = pullback.fst f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g) := by
    simp [a]
  have he : inv a ≫ pullback.fst f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g) = pullback.fst f g := by
    rw [← ha, IsIso.inv_hom_id_assoc]
  let N := (Modules.tensorPullback (pullback.fst f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g))).obj E
  have hN : N.IsFiniteLocallyFreeOfRank r := by
    exact hr
  let := hN
  let e₁ : Modules.tensorPullback (inv a) ≅ Modules.pullback (inv a) :=
    (Modules.nonempty_tensorPullbackAdjunction (inv a)).some.leftAdjointUniq
      (Modules.pullbackPushforwardAdjunction (inv a))
  let e : ((Modules.pullback (inv a)).obj N) ≅
      (Modules.tensorPullback (pullback.fst f g)).obj E :=
    e₁.symm.app N ≪≫
      (Modules.nonempty_tensorPullbackComp (inv a)
        (pullback.fst f ((⊤ : T.Opens).ι ≫ 𝟙 T ≫ g))).some.symm.app E ≪≫
      eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj E) he)
  exact ⟨r, SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e⟩

/-- On an affine base open, finitely many fibre ranks cover the universal rank locus.
Source: Stacks Project, Tag 0BDP, rank decomposition paragraph; finite local freeness
and properness give the finite bound even without connected fibres.
(blueprint: lem-sc-picard-universal-rank-match-finite-ranks).

Proof:
1. The inverse image of the affine open is quasi-compact, since f is proper.
   Trivialize E on an open cover of that inverse image, and take a finite subcover.
   Let R be the finite set of ranks of these trivializations, with zero adjoined.
2. At a point s satisfying the universal rank condition, apply that condition to the
   identity of Spec kappa(s) and its unique point. Its nonempty neighbourhood is the
   whole one-point scheme. The third clause gives a constant rank r for E on the fibre;
   pullback along this open inclusion and the identity changes no rank.
3. If the fibre is nonempty, choose a point of it and a member of the finite
   trivializing cover containing its image in X. Pulling both trivializations to its
   residue field and comparing dimensions shows that r is that member's rank, hence
   belongs to R. If the fibre is empty, E on it has rank zero, so choose zero in R.
   This proves the bound without assuming f is surjective or the fibres connected. -/
theorem picardUniversalRankMatch_finiteRanks {X S : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (U : S.Opens) (hU : IsAffineOpen U) :
    ∃ R : Finset ℕ, ∀ s : S, s ∈ U →
      PicardUniversalRankMatch f E (S.fromSpecResidueField s) →
      ∃ r ∈ R,
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f (S.fromSpecResidueField s))).obj E) r := by
  classical
  obtain ⟨R, hzero, hR⟩ := picardUniversalRankMatch_finiteRankBound f E U hU
  refine ⟨R, ?_⟩
  intro s hs hmatch
  by_cases hne : Nonempty (pullback f (S.fromSpecResidueField s) : Scheme.{u})
  · obtain ⟨r, hr⟩ := picardUniversalRankMatch_localRank f E s hmatch
    exact ⟨r, hR s hs hne r hr, hr⟩
  · have : IsEmpty (pullback f (S.fromSpecResidueField s) : Scheme.{u}) := not_nonempty_iff.mp hne
    exact ⟨0, hzero, finiteLocallyFreeOfRank_of_isEmpty _ 0⟩

end AlgebraicGeometry.Scheme
