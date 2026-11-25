/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Sectionwise gluing for a split cover

Source: Stacks Project, etale-cohomology.tex, proof of Lemma 095B,
and sites.tex, Definition 00VM
(blueprint: lem-weil-pbc-split-cover-sections-limit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Source: Stacks Project, etale-cohomology.tex, proof of Lemma 095B,
lines 9982--9991, and sites.tex, Definition 00VM.
(blueprint: lem-weil-pbc-split-cover-sections-limit).

Proof: Base change the clopen coproduct Y by W → X. Its j-th piece is W,
using the inverse t j to i j ≫ f; its inclusion is the displayed pullback lift.
These inclusions cover W ×_X Y and have empty pairwise overlaps for distinct
indices. The self-overlap projections agree because the inclusions are monic.
The sheaf condition makes sections the equalizer of the two overlap maps.
Sections on the empty object are zero, by its empty covering. Thus every family
of sections on the pieces is compatible and glues uniquely. For any module M,
a family of linear maps from M to these section modules therefore glues to a
unique map to H(W ×_X Y); uniqueness of gluing proves additivity and scalar
linearity. This is exactly the limiting-fan property, also for the empty family.
-/
theorem splitCoverSectionsLimit
    {X Y : Scheme.{u}} {J : Type w} [Finite J]
    {Λ : Type (u + 1)} [CommRing Λ]
    (f : Y ⟶ X) (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y)
    (t : ∀ j, X ⟶ V j)
    (hcolim : IsColimit (Cofan.mk Y i))
    (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
    (hinv₂ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
    (hopens : ∀ j, AlgebraicGeometry.IsOpenImmersion (i j))
    (hclosed : ∀ j, AlgebraicGeometry.IsClosedImmersion (i j))
    (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (W : X.Etale) :
    letI : ∀ j, IsOpenImmersion (i j) := hopens
    letI : ∀ j, IsIso (t j) := fun j ↦
      ⟨⟨i j ≫ f, hinv₁ j, hinv₂ j⟩⟩
    let s := fun j ↦ t j ≫ i j
    Nonempty (IsLimit (Fan.mk
      (H.obj.obj (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)))
      (fun j ↦ H.obj.map (MorphismProperty.Over.homMk
        (A := (MorphismProperty.Over.map ⊤ (inferInstance : Etale (s j))).obj W)
        (B := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
        (pullback.lift (𝟙 W.left) (W.hom ≫ s j)
          (by
            change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s j) ≫ f
            simp [s, Category.assoc, hinv₁ j]))
        (by simp)).op))) := by
  classical
  have _ := hclosed
  let : ∀ j, IsOpenImmersion (i j) := hopens
  let : ∀ j, IsIso (t j) := fun j ↦ ⟨⟨i j ≫ f, hinv₁ j, hinv₂ j⟩⟩
  let s := fun j ↦ t j ≫ i j
  let B := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let A := fun j ↦ (MorphismProperty.Over.map ⊤ (inferInstance : Etale (s j))).obj W
  let σ : ∀ j, A j ⟶ B := fun j ↦ MorphismProperty.Over.homMk
    (pullback.lift (𝟙 W.left) (W.hom ≫ s j)
      (by
        change (𝟙 W.left) ≫ W.hom = (W.hom ≫ s j) ≫ f
        simp [s, Category.assoc, hinv₁ j])) (by simp [A, B])
  change Nonempty (IsLimit (Fan.mk (H.obj.obj (op B))
    (fun j ↦ H.obj.map (σ j).op)))
  have : ∀ j, IsIso (i j ≫ f) := fun j ↦ ⟨⟨t j, hinv₂ j, hinv₁ j⟩⟩
  have hpb (j : J) : IsPullback (σ j).left (W.hom ≫ t j)
      (pullback.snd W.hom f) (i j) := by
    apply IsPullback.of_right (t := IsPullback.of_hasPullback W.hom f)
    · simpa [σ, A, B] using
        (IsPullback.of_horiz_isIso (fst := 𝟙 W.left) (snd := W.hom ≫ t j)
          (f := W.hom) (g := i j ≫ f) ⟨by simp [Category.assoc, hinv₁ j]⟩)
    · simp [σ, A, B, s, Category.assoc]
  have hr (j : J) : Set.range (σ j).left =
      (pullback.snd W.hom f) ⁻¹' Set.range (i j) :=
    Scheme.range_snd_of_isPullback (hpb j).flip
  have : ∀ j, Mono (σ j) := fun j ↦ by
    have : IsOpenImmersion (σ j).left := (hpb j).isOpenImmersion_fst
    exact (MorphismProperty.Over.forget @Etale ⊤ Y ⋙ Over.forget Y).mono_of_mono_map (by
      change Mono (σ j).left
      infer_instance)
  let e : (∐ V) ≅ Y := colimit.isoColimitCocone ⟨Cofan.mk Y i, hcolim⟩
  have he (j : J) : Sigma.ι V j ≫ e.hom = i j :=
    colimit.isoColimitCocone_ι_hom ⟨Cofan.mk Y i, hcolim⟩ ⟨j⟩
  have hy (y : Y) : ∃ j, y ∈ Set.range (i j) := by
    obtain ⟨x, hx⟩ := (Scheme.homeoOfIso e).surjective y
    obtain ⟨z, hz⟩ := (sigmaOpenCover V).covers x
    change Sigma.ι V ((sigmaOpenCover V).idx x) z = x at hz
    refine ⟨(sigmaOpenCover V).idx x, z, ?_⟩
    rw [← he, Scheme.Hom.comp_apply, hz]
    exact hx
  have hd (j k : J) (hjk : j ≠ k) : Disjoint (Set.range (i j)) (Set.range (i k)) := by
    rw [Set.disjoint_iff_forall_ne]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    have heq : Sigma.ι V j x = Sigma.ι V k y :=
      (Scheme.homeoOfIso e).injective (by
        simpa only [Scheme.coe_homeoOfIso, ← Scheme.Hom.comp_apply, he] using hxy)
    exact hjk (Sigma.mk.inj_iff.mp ((sigmaι_eq_iff V j k x y).mp heq)).1
  have hcov : Sieve.ofArrows A σ ∈ Y.smallEtaleTopology B := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨j, hj⟩ := hy (pullback.snd W.hom f z)
    exact Set.mem_iUnion.mpr ⟨j, (hr j).symm ▸ hj⟩
  have hdisj : ∀ j k, j ≠ k →
      Disjoint (Set.range (σ j).left.base) (Set.range (σ k).left.base) := by
    intro j k hjk
    rw [hr, hr]
    exact (hd j k hjk).preimage _
  exact (Fan.nonempty_isLimit_iff_isIso_piLift _).mpr
    (Scheme.Etale.isIso_piLift_of_disjoint H A σ hcov hdisj)

end AlgebraicGeometry
