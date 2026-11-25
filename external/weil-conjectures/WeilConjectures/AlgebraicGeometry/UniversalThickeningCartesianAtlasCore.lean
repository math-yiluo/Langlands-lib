/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
import WeilConjectures.AlgebraicGeometry.UniversalThickeningOverlapGlueData

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Gluing the thickened charts gives a covering family of open immersions with
compatible local maps and the prescribed source overlaps. This statement constructs
only the ambient scheme and its charts, not the global source or structure morphisms.

Source: Stacks Project, More on Morphisms, proof of Lemma 37.7.1 (Tag 04F3),
paragraphs beginning "Choose an affine open covering" and "By the general remarks".
(blueprint: lem-weil-pbc-universal-thickening-cartesian-atlas-core)

Proof: Form the source intersections as pullbacks of the open chart maps of `C`.
Each `i k` is a homeomorphism: its kernel has square zero, so its closed image is
all of the target. Thus a source intersection determines a unique open in each
of the two thickened charts. Restrict the universal thickenings to these opens
using the open-pieces theorem with the whole base open. Identify their sources
with the source intersection. Universal uniqueness gives an isomorphism of the
thickened overlaps over `X` inducing the identity on that intersection. On triple
intersections all composites extend the same identity over `X`, so uniqueness
gives the cocycle identity; the same argument gives identity and inverse maps.
These opens and transitions form scheme glue data. Take its glued scheme `W`
and canonical chart maps `e k`, which are open immersions and jointly surjective.
The gluing relation identifies precisely the prescribed thickened overlaps.
Since transitions are over `X`, the two structure maps agree on the pullback of
any two chart maps. Since they fix the source intersection, the maps `i k ≫ e k`
agree on the source pullbacks. Finally a point `i l z` lies in the overlap with
chart `k` exactly when `C.f l z` lies in the image of source chart `k`, by the
choice of the overlap opens and the gluing relation. This proves the last clause.
For an empty index type the source and the glued scheme are empty; all clauses
hold vacuously. Repeated charts cause no difficulty because the identity
transition is fixed by uniqueness. -/
theorem universalFirstOrderThickening_cartesianAtlas_core
    {Z X : Scheme.{u}} (h : Z ⟶ X) (C : Z.OpenCover.{u})
    (Z' : C.I₀ → Scheme.{u}) (i : ∀ k, C.X k ⟶ Z' k)
    (h' : ∀ k, Z' k ⟶ X)
    (H : ∀ k, IsUniversalFirstOrderThickening (C.f k ≫ h) (i k) (h' k)) :
    ∃ (W : Scheme.{u}) (e : ∀ k, Z' k ⟶ W),
      (∀ k, IsOpenImmersion (e k)) ∧ (∀ w : W, ∃ k z, e k z = w) ∧
      (∀ k l, pullback.fst (e k) (e l) ≫ h' k = pullback.snd _ _ ≫ h' l) ∧
      (∀ k l, pullback.fst (C.f k) (C.f l) ≫ (i k ≫ e k) =
        pullback.snd _ _ ≫ (i l ≫ e l)) ∧
      ∀ k l (z : C.X l),
        e l (i l z) ∈ Set.range (e k) ↔ C.f l z ∈ Set.range (C.f k) := by
  obtain ⟨D, a, b, hbase, hsource, hrange⟩ :=
    universalFirstOrderThickening_overlapGlueData h C Z' i h' H
  let e : ∀ k, Z' k ⟶ D.glued := fun k ↦ (b k).hom ≫ D.ι (a k)
  refine ⟨D.glued, e, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    dsimp [e]
    infer_instance
  · intro w
    obtain ⟨j, z, hz⟩ := D.ι_jointly_surjective w
    obtain ⟨k, rfl⟩ := a.surjective j
    refine ⟨k, (b k).inv z, ?_⟩
    simpa [e, ← Scheme.Hom.comp_apply] using hz
  · intro k l
    let c : PullbackCone (D.ι (a k)) (D.ι (a l)) :=
      PullbackCone.mk (pullback.fst (e k) (e l) ≫ (b k).hom)
        (pullback.snd (e k) (e l) ≫ (b l).hom) (by
          simpa only [Category.assoc] using pullback.condition (f := e k) (g := e l))
    let q := (D.vPullbackConeIsLimit (a k) (a l)).lift c
    have hq₁ : q ≫ D.f (a k) (a l) = pullback.fst (e k) (e l) ≫ (b k).hom :=
      (D.vPullbackConeIsLimit (a k) (a l)).fac c WalkingCospan.left
    have hq₂ : q ≫ D.t (a k) (a l) ≫ D.f (a l) (a k) =
        pullback.snd (e k) (e l) ≫ (b l).hom :=
      (D.vPullbackConeIsLimit (a k) (a l)).fac c WalkingCospan.right
    calc
      pullback.fst (e k) (e l) ≫ h' k =
          q ≫ D.f (a k) (a l) ≫ (b k).inv ≫ h' k := by rw [← Category.assoc, hq₁]; simp
      _ = q ≫ D.t (a k) (a l) ≫ D.f (a l) (a k) ≫ (b l).inv ≫ h' l := by
        rw [hbase k l]
      _ = pullback.snd (e k) (e l) ≫ h' l := by
        simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
          congrArg (fun f ↦ f ≫ (b l).inv ≫ h' l) hq₂
  · intro k l
    obtain ⟨s, hs₁, hs₂⟩ := hsource k l
    calc
      pullback.fst (C.f k) (C.f l) ≫ (i k ≫ e k) =
          s ≫ D.f (a k) (a l) ≫ D.ι (a k) := by
        dsimp [e]
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ D.ι (a k)) hs₁.symm
      _ = s ≫ D.t (a k) (a l) ≫ D.f (a l) (a k) ≫ D.ι (a l) := by
        rw [D.glue_condition]
      _ = pullback.snd (C.f k) (C.f l) ≫ (i l ≫ e l) := by
        dsimp [e]
        simpa only [Category.assoc] using
          congrArg (fun f ↦ f ≫ D.ι (a l)) hs₂
  · intro k l z
    rw [← hrange k l z]
    constructor
    · rintro ⟨y, hy⟩
      have heq : D.ι (a l) ((b l).hom (i l z)) = D.ι (a k) ((b k).hom y) :=
        (show D.ι (a k) ((b k).hom y) = D.ι (a l) ((b l).hom (i l z)) by
          simpa only [e, Scheme.Hom.comp_apply] using hy).symm
      obtain ⟨v, hv, _⟩ := (D.ι_eq_iff _ _ _ _).mp heq
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      let y := (D.t (a l) (a k) ≫ D.f (a k) (a l)) v
      have heq : D.ι (a l) ((b l).hom (i l z)) = D.ι (a k) y :=
        (D.ι_eq_iff _ _ _ _).mpr ⟨v, hv, rfl⟩
      refine ⟨(b k).inv y, ?_⟩
      change D.ι (a k) ((b k).hom ((b k).inv y)) =
        D.ι (a l) ((b l).hom (i l z))
      have hb : (b k).hom ((b k).inv y) = y := by
        change ((b k).inv ≫ (b k).hom) y = y
        rw [Iso.inv_hom_id]
        rfl
      rw [hb]
      exact heq.symm

end AlgebraicGeometry
