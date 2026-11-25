/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SimplicialOrdinalPath
public import WeilConjectures.AlgebraicGeometry.EtaleSimplicialMatching
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicTopology.OrdinalBoundaryFamily
import WeilConjectures.AlgebraicGeometry.EtaleFiniteSimplexLifting
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Tactic

/-!
# The ordered endpoint pullback of étale hypercovers is a hypercover

Source: Stacks, Tags 01GN and 01GS. In degree n the relative matching problem is
extension from the two endpoint n-simplices and doubled proper faces to Δ[2n+1].
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject SimplexCategory.OrdinalPath

namespace AlgebraicGeometry.EtaleSimplicialMatching

/-- Relative matching data in an ordered endpoint pullback have local lifts.
Source: Stacks, Tag 01GN. Glue the endpoint and proper-face families, extend across
the finite simplex locally, and combine each extended simplex with the given simplex
of U using the endpoint pullback. The generator equations identify all proper faces,
and the matching universal property identifies the lifted matching datum.
(auxiliary; not a blueprint node) -/
theorem locally_lift_ordinal_matching {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : SimplicialObject X.Etale}
    (a b : U ⟶ V) (hV : IsEtaleHypercover V) (n : ℕ) (T : X.Etale)
    (q : T ⟶ matching (ordinalPathPullback a b) n) (u : T ⟶ U.obj (op ⦋n⦌))
    (hu : u ≫ matchingMap U n = q ≫ matchingNat (ordinalPathPullbackFst a b) n) :
    ∃ (ι : Type u) (Tc : ι → X.Etale) (p : ∀ c : ι, Tc c ⟶ T),
      Sieve.ofArrows Tc p ∈ X.smallEtaleTopology T ∧
        ∃ k : ∀ c : ι, Tc c ⟶ (ordinalPathPullback a b).obj (op ⦋n⦌),
          ∀ c, k c ≫ matchingMap (ordinalPathPullback a b) n = p c ≫ q := by
  classical
  let K := ordinalPathPullback a b
  let c := ordinalPathPullbackFst a b
  let s := ordinalPathPullbackSnd a b
  have huθ (Δ : SimplexCategory) (h : Δ.len < n) (θ : Δ ⟶ ⦋n⦌) :
      u ≫ U.map θ.op = q ≫ projection K n Δ h θ ≫ c.app (op Δ) := by
    calc
      u ≫ U.map θ.op = (u ≫ matchingMap U n) ≫ projection U n Δ h θ := by
        rw [Category.assoc, matchingMap_projection]
      _ = (q ≫ matchingNat c n) ≫ projection U n Δ h θ := by rw [hu]
      _ = q ≫ projection K n Δ h θ ≫ c.app (op Δ) := by
        rw [Category.assoc, matchingNat_projection]
  let p₀ : (Functor.const _).obj T ⟶ (ordinalPath V).properFaceDiagram n :=
    (Functor.const _).map (q ≫ matchingNat s n) ≫ (properCone (ordinalPath V) n).π
  have hp₀ (d : ProperFaceCategory n) :
      p₀.app (op d) = q ≫ projection K n d.obj.left d.property.1 d.obj.hom ≫
        s.app (op d.obj.left) := by
    change (q ≫ matchingNat s n) ≫ projection (ordinalPath V) n _ _ d.obj.hom = _
    rw [Category.assoc, matchingNat_projection]
  have hl (d : ProperFaceCategory n) :
      p₀.app (op d) ≫ V.map (left d.obj.left).op =
        (u ≫ a.app (op ⦋n⦌)) ≫ V.map d.obj.hom.op := by
    have he := congrArg (fun z ↦ z.app (op d.obj.left)) (ordinalPathPullback_left a b)
    change c.app (op d.obj.left) ≫ a.app (op d.obj.left) =
      s.app (op d.obj.left) ≫ V.map (left d.obj.left).op at he
    calc
      _ = q ≫ projection K n d.obj.left d.property.1 d.obj.hom ≫ s.app (op d.obj.left) ≫
          V.map (left d.obj.left).op := by rw [hp₀]; simp only [Category.assoc]
      _ = q ≫ projection K n d.obj.left d.property.1 d.obj.hom ≫ c.app (op d.obj.left) ≫
          a.app (op d.obj.left) := by rw [← he]
      _ = (u ≫ U.map d.obj.hom.op) ≫ a.app (op d.obj.left) := by
        rw [huθ d.obj.left d.property.1 d.obj.hom]; simp only [Category.assoc]
      _ = _ := by rw [Category.assoc, a.naturality]; simp only [Category.assoc]
  have hr (d : ProperFaceCategory n) :
      p₀.app (op d) ≫ V.map (right d.obj.left).op =
        (u ≫ b.app (op ⦋n⦌)) ≫ V.map d.obj.hom.op := by
    have he := congrArg (fun z ↦ z.app (op d.obj.left)) (ordinalPathPullback_right a b)
    change c.app (op d.obj.left) ≫ b.app (op d.obj.left) =
      s.app (op d.obj.left) ≫ V.map (right d.obj.left).op at he
    calc
      _ = q ≫ projection K n d.obj.left d.property.1 d.obj.hom ≫ s.app (op d.obj.left) ≫
          V.map (right d.obj.left).op := by rw [hp₀]; simp only [Category.assoc]
      _ = q ≫ projection K n d.obj.left d.property.1 d.obj.hom ≫ c.app (op d.obj.left) ≫
          b.app (op d.obj.left) := by rw [← he]
      _ = (u ≫ U.map d.obj.hom.op) ≫ b.app (op d.obj.left) := by
        rw [huθ d.obj.left d.property.1 d.obj.hom]; simp only [Category.assoc]
      _ = _ := by rw [Category.assoc, b.naturality]; simp only [Category.assoc]
  obtain ⟨f, hf, hval⟩ := OrdinalBoundary.exists_family.{u + 1, u, 0} V n T
    (u ≫ a.app (op ⦋n⦌)) (u ≫ b.app (op ⦋n⦌)) p₀ hl hr
  obtain ⟨ι, Tc, p, hp, g, hg⟩ := locally_extend_simplex V hV (2 * n + 1)
    (OrdinalBoundary.subcomplex n) (OrdinalBoundary.subcomplex_nonempty n) T f hf
  have hggen (i : ι) (j : OrdinalBoundary.Generator n) :
      g i ≫ V.map (OrdinalBoundary.face n j).op =
        p i ≫ f (OrdinalBoundary.degree n j)
          ⟨_, faceUnion_generator_mem (OrdinalBoundary.degree n) (OrdinalBoundary.face n) j⟩ := by
    simpa only [Equiv.apply_symm_apply] using hg i (OrdinalBoundary.degree n j)
      ⟨_, faceUnion_generator_mem (OrdinalBoundary.degree n) (OrdinalBoundary.face n) j⟩
  have hgl (i : ι) : (p i ≫ u) ≫ a.app (op ⦋n⦌) = g i ≫ V.map (left ⦋n⦌).op := by
    have h := hggen i (.inl false)
    rw [hval (.inl false)] at h
    simpa only [OrdinalBoundary.face, Category.assoc] using h.symm
  have hgr (i : ι) : (p i ≫ u) ≫ b.app (op ⦋n⦌) = g i ≫ V.map (right ⦋n⦌).op := by
    have h := hggen i (.inl true)
    rw [hval (.inl true)] at h
    simpa only [OrdinalBoundary.face, Category.assoc] using h.symm
  choose k hk₁ hk₂ using fun i ↦
    ordinalPathPullback_lift_degree a b n (p i ≫ u) (g i) (hgl i) (hgr i)
  refine ⟨ι, Tc, p, hp, k, ?_⟩
  intro i
  apply (properConeIsLimit K n).hom_ext
  intro d
  change (k i ≫ matchingMap K n) ≫ projection K n _ _ d.unop.obj.hom =
    (p i ≫ q) ≫ projection K n _ _ d.unop.obj.hom
  rw [Category.assoc, matchingMap_projection]
  apply ordinalPathPullback_hom_ext_degree a b d.unop.obj.left.len
  · rw [Category.assoc, c.naturality, ← Category.assoc, hk₁,
      Category.assoc, huθ d.unop.obj.left d.unop.property.1 d.unop.obj.hom]
    simp only [Category.assoc, c]
  · rw [Category.assoc, s.naturality, ← Category.assoc, hk₂]
    have h := hggen i (.inr d.unop)
    rw [hval (.inr d.unop)] at h
    change g i ≫ V.map (map d.unop.obj.hom).op = p i ≫ p₀.app (op d.unop) at h
    rw [hp₀] at h
    change g i ≫ V.map (map d.unop.obj.hom).op =
      ((p i ≫ q) ≫ projection K n _ d.unop.property.1 d.unop.obj.hom) ≫
        s.app (op d.unop.obj.left)
    simpa only [Category.assoc] using h

/-- The ordered endpoint pullback of two maps of étale hypercovers is a hypercover.
Source: Stacks, Tags 01GN and 01GS. Pull U's matching cover back to the matching
scheme of the endpoint pullback. Over that surjective cover, the relative lifting
lemma supplies an étale covering with lifts to its degree n. The covering criterion
then gives surjectivity of the absolute matching arrow in every degree.
(auxiliary; not a blueprint node) -/
theorem isEtaleHypercover_ordinalPathPullback {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : SimplicialObject X.Etale}
    (a b : U ⟶ V) (hU : IsEtaleHypercover U) (hV : IsEtaleHypercover V) :
    IsEtaleHypercover (ordinalPathPullback a b) := by
  apply isEtaleHypercover_of_matchingCover
  intro n
  let K := ordinalPathPullback a b
  let c := ordinalPathPullbackFst a b
  let t := matchingNat c n
  let T := pullback (matchingMap U n) t
  let u : T ⟶ U.obj (op ⦋n⦌) := pullback.fst _ _
  let q : T ⟶ matching K n := pullback.snd _ _
  have hu : u ≫ matchingMap U n = q ≫ t := pullback.condition
  let _ : Surjective (matchingMap U n).left := matchingCover_of_isEtaleHypercover U hU n
  have hq : Surjective q.left :=
    MorphismProperty.of_isPullback (P := @Surjective)
      ((IsPullback.of_hasPullback (matchingMap U n) t).map
        (Scheme.Etale.forget X ⋙ Over.forget X))
      (by change Surjective (matchingMap U n).left; infer_instance)
  obtain ⟨ι, Tc, p, hp, k, hk⟩ := locally_lift_ordinal_matching a b hV n T q u hu
  constructor
  intro x
  let := hq
  obtain ⟨y, hy⟩ := q.left.surjective x
  have hcover := (Scheme.ofArrows_mem_smallEtaleTopology_iff p).mp hp
  have hmem : y ∈ ⋃ i, Set.range (p i).left := by rw [hcover]; trivial
  obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp hmem
  refine ⟨(k i).left z, ?_⟩
  have he := congrArg (fun f ↦ f.left) (hk i)
  change (k i).left ≫ (matchingMap K n).left = (p i).left ≫ q.left at he
  change ((k i).left ≫ (matchingMap K n).left) z = x
  rw [he]
  change q.left ((p i).left z) = x
  rw [hz, hy]

end AlgebraicGeometry.EtaleSimplicialMatching
