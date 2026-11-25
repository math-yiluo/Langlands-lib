/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover

/-!
# Finite disjoint refinements over w-contractible affine schemes

Let `W` be an object of the small pro-étale site of a scheme whose underlying scheme is the
spectrum of a w-contractible ring. Every covering sieve of `W` contains the members of a finite
cover of `W` by pairwise disjoint open immersions
(`AlgebraicGeometry.Scheme.ProEt.hasFiniteDisjointRefinements_of_iso`); this is the finite form
of `AlgebraicGeometry.Scheme.ProEt.isWeaklyContractible_of_iso`. Moreover every scheme admits a
pro-étale cover by spectra of w-contractible rings
(`AlgebraicGeometry.Scheme.exists_isWContractibleRing_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme.ProEt

variable {T : Scheme.{u}}

/-- Let `W` be an object of the small pro-étale site whose underlying scheme admits a section
`s` of a morphism `∐ V j ⟶ W.left`. The preimages under `s` of the components `V j` form a
disjoint cover of `W`, indexed by the same type, by members of every sieve `S` containing the
morphisms to `W` factoring through some `V j`. -/
lemma isDisjointCover_of_comp_sigmaDesc_eq_id {W : T.ProEt} {κ : Type u}
    {V : κ → Scheme.{u}} (v : ∀ j, V j ⟶ W.left) (s : W.left ⟶ ∐ V)
    (hs : s ≫ Sigma.desc v = 𝟙 _) (S : Sieve W)
    (hS : ∀ j {Y : T.ProEt} (a : Y ⟶ W) (b : Y.left ⟶ V j), b ≫ v j = a.left → S a) :
    ∃ (Y : κ → T.ProEt) (f : ∀ i, Y i ⟶ W),
      (topology T).IsDisjointCover f ∧ ∀ i, S (f i) := by
  let O (j : κ) : W.left.Opens := s ⁻¹ᵁ (Sigma.ι V j).opensRange
  have hO (j : κ) : Set.range ((O j).ι ≫ s).base ⊆ Set.range (Sigma.ι V j).base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨fun j ↦ ofOpenImmersion W (O j).ι, fun j ↦ ofOpenImmersionHom W (O j).ι,
    ⟨?_, fun j ↦ ?_, ?_⟩, fun j ↦ hS j _ (IsOpenImmersion.lift (Sigma.ι V j) ((O j).ι ≫ s)
      (hO j)) ?_⟩
  · refine mem_topology_of_openImmersion _ (fun j ↦ (O j).ι) (fun x ↦ ?_)
      (fun j ↦ Sieve.ofArrows_mk _ _ j)
    obtain ⟨j, y, hy⟩ := (sigmaOpenCover V).exists_eq (s x)
    refine ⟨j, ?_⟩
    rw [Opens.range_ι]
    exact ⟨y, hy⟩
  · refine (ProEt.forget T ⋙ CategoryTheory.Over.forget T).mono_of_mono_map ?_
    exact inferInstanceAs (Mono (O j).ι)
  · intro i j hij Z a b hab
    have : IsEmpty Z.left := by
      refine ⟨fun z ↦ ?_⟩
      have hab' : a.left ≫ (O i).ι = b.left ≫ (O j).ι := congrArg (fun g ↦ g.left) hab
      have hi : (a.left ≫ (O i).ι).base z ∈ O i := by
        exact (Opens.range_ι (O i)).subset ⟨a.left z, rfl⟩
      have hj : (a.left ≫ (O i).ι).base z ∈ O j := by
        rw [hab']
        exact (Opens.range_ι (O j)).subset ⟨b.left z, rfl⟩
      exact (disjoint_opensRange_sigmaι V i j hij).le_bot ⟨hi, hj⟩
    exact bot_mem_topology Z
  · rw [← Sigma.ι_comp_desc v j, ← Category.assoc, IsOpenImmersion.lift_fac, Category.assoc, hs,
      Category.comp_id]
    rfl

/-- An object of the small pro-étale site whose underlying scheme is the spectrum of a
w-contractible ring has finite disjoint refinements: every covering sieve contains the members
of a finite cover by pairwise disjoint open immersions. -/
theorem hasFiniteDisjointRefinements_of_iso {W : T.ProEt} {R : CommRingCat.{u}}
    [IsWContractibleRing R] (e : W.left ≅ Spec R) :
    (topology T).HasFiniteDisjointRefinements W := by
  intro S hS
  obtain ⟨P, hP, hPS⟩ := mem_topology_iff.1 hS
  obtain ⟨𝒰, _, h𝒰⟩ := (mem_propQCPrecoverage_iff_exists_quasiCompactCover
    (P := @WeaklyEtale)).1 (mem_precoverage_iff.1 hP)
  have : IsAffine W.left := .of_isIso e.hom
  obtain ⟨𝒱, g, _, _⟩ := Cover.QuasiCompact.exists_hom.{u + 1, u} 𝒰
  have hmem (i : 𝒰.I₀) : P.map (ProEt.forget T ⋙ CategoryTheory.Over.forget T) (𝒰.f i) := by
    rw [h𝒰]
    exact ⟨i⟩
  choose Z hZ a ha hZa using fun i ↦ Presieve.map_iff.1 (hmem i)
  let ε : ULift.{u} (Fin (Nat.card 𝒱.I₀)) ≃ 𝒱.I₀ := Equiv.ulift.trans (Finite.equivFin _).symm
  let v (k : ULift.{u} (Fin (Nat.card 𝒱.I₀))) := 𝒱.f (ε k)
  have : WeaklyEtale (Sigma.desc v) := IsZariskiLocalAtSource.sigmaDesc fun k ↦ 𝒱.map_prop _
  have : Surjective (Sigma.desc v) := by
    refine Surjective.sigmaDesc_of_union_range_eq_univ (Set.eq_univ_of_forall fun x ↦ ?_)
    obtain ⟨k, hk⟩ := ε.surjective (𝒱.idx x)
    refine Set.mem_iUnion.2 ⟨k, ?_⟩
    simp only [v]
    rw [hk]
    exact 𝒱.covers x
  obtain ⟨s, hs⟩ := exists_comp_eq_id_of_isWContractibleRing (Sigma.desc v ≫ e.hom)
  obtain ⟨Yd, fd, hf, hfS⟩ := isDisjointCover_of_comp_sigmaDesc_eq_id v (e.hom ≫ s) (by
    rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hs]
    simp) S (by
    intro j Y b c hbc
    have ha' (i : 𝒰.I₀) : (a i).left = eqToHom (hZ i) ≫ 𝒰.f i := hZa i
    let d : Y.left ⟶ (Z (g.s₀ (ε j))).left := c ≫ g.h₀ (ε j) ≫ eqToHom (hZ _).symm
    have hd : d ≫ (a (g.s₀ (ε j))).left = b.left := by
      rw [← hbc, ha', Category.assoc, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp, g.w₀]
      rfl
    have hb : b = MorphismProperty.Over.homMk d (by
        rw [← MorphismProperty.Over.w (a (g.s₀ (ε j))), ← Category.assoc, hd]
        exact MorphismProperty.Over.w b) ≫ a (g.s₀ (ε j)) :=
      MorphismProperty.Over.Hom.ext hd.symm
    rw [hb]
    exact S.downward_closed (hPS _ _ (ha _)) _)
  refine ⟨Nat.card 𝒱.I₀, fun i ↦ Yd ⟨i⟩, fun i ↦ fd ⟨i⟩,
    ⟨(topology T).superset_covering ?_ hf.ofArrows_mem, fun i ↦ hf.mono _,
      fun i j hij ↦ hf.bot_mem _ _ (fun h ↦ hij (congrArg ULift.down h))⟩, fun i ↦ hfS _⟩
  rintro _ _ ⟨_, c, _, ⟨k⟩, rfl⟩
  exact Sieve.downward_closed _
    (Sieve.ofArrows_mk (fun i : Fin (Nat.card 𝒱.I₀) ↦ Yd ⟨i⟩) (fun i ↦ fd ⟨i⟩) k.down) c

end Scheme.ProEt

/-- **Every scheme has a pro-étale cover by spectra of w-contractible rings** (Stacks 0990):
cover `X` by affine opens `Spec A`, and each `Spec A` by `Spec B` for a faithfully flat,
ind-étale, w-contractible `A`-algebra `B`. -/
theorem Scheme.exists_isWContractibleRing_cover (X : Scheme.{u}) :
    ∃ (ι : Type (u + 1)) (R : ι → CommRingCat.{u}) (_ : ∀ i, IsWContractibleRing (R i))
      (g : ∀ i, Spec (R i) ⟶ X),
      Presieve.ofArrows (fun i ↦ Spec (R i)) g ∈ Scheme.proetalePrecoverage X := by
  have 𝒜 : X.AffineOpenCover := X.affineOpenCover
  choose S iS iA hind hff hw using fun x : 𝒜.I₀ ↦ exists_isWContractibleRing (𝒜.X x)
  let φ (x : 𝒜.I₀) : 𝒜.X x ⟶ CommRingCat.of (S x) := CommRingCat.ofHom (algebraMap _ _)
  have (x : 𝒜.I₀) : WeaklyEtale (Spec.map (φ x)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).2 (hind x))
  have (x : 𝒜.I₀) : Surjective (Spec.map (φ x)) :=
    ((flat_and_surjective_SpecMap_iff (φ x)).2
      (RingHom.faithfullyFlat_algebraMap_iff.2 (hff x))).2
  have h𝒜 : Presieve.ofArrows (fun x ↦ Spec (𝒜.X x)) 𝒜.f ∈ Scheme.proetalePrecoverage X :=
    zariskiPrecoverage_le_propQCPrecoverage _ 𝒜.openCover.mem₀
  have h𝒜' : Presieve.ofArrows (fun x : ULift.{u + 1} 𝒜.I₀ ↦ Spec (𝒜.X x.down))
      (fun x ↦ 𝒜.f x.down) ∈ Scheme.proetalePrecoverage X := by
    convert h𝒜 using 1
    funext Y g
    apply propext
    constructor
    · rintro ⟨i⟩
      exact ⟨i.down⟩
    · rintro ⟨i⟩
      exact ⟨ULift.up i⟩
  have h := Precoverage.IsStableUnderComposition.comp_mem_coverings _ h𝒜'
    (σ := fun _ ↦ PUnit.{u + 2}) (fun x _ ↦ Spec.map (φ x.down)) fun x ↦ by
      rw [Presieve.ofArrows_pUnit]
      exact Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance
  exact ⟨_, fun p : (Σ _ : ULift.{u + 1} 𝒜.I₀, PUnit.{u + 2}) ↦ CommRingCat.of (S p.1.down),
    fun p ↦ hw p.1.down, _, h⟩

end AlgebraicGeometry
