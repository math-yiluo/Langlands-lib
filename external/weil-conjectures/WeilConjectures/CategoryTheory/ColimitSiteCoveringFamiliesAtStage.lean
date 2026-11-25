/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.CategoryTheory.ColimitPresieveIndexedPresentation

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- One finite layer of covering families lifts over targets already fixed at a stage.
Source: Stacks Project, Sites, Tag 09YL, finite-diagram observation.
(blueprint: lem-weil-pbc-colimit-site-covering-families-at-stage)

Proof: For each family use hQ to choose a finite covering stage presieve with the
specified image. For every requested indexed arrow choose a member of that presieve
mapping to it, with its source equality. Conversely choose an index for each member
of the stage presieve with the same image. Both collections are finite, including
when indices repeat. Filteredness gives a common stage above these stages and j₀.
Eventual equality in the object colimit aligns each presieve target with the
transition image of T₀ i. Eventual equality in the arrow colimit identifies every
presieve member with its selected indexed representative, including the endpoint
objects. Move to a common successor where all these finitely many equalities hold.
Transport along the endpoint equalities to obtain a i t into the transition of
T₀ i. The comparisons in both directions show that this indexed presieve equals
the transition image of the original covering presieve; hcover makes it covering.
Cocone naturality gives each prescribed image-arrow equality. If a family's index
is empty, its representing presieve is empty because its image is empty, so only
its target must be aligned. If the family of targets is empty, take j₀ and its
identity transition. This construction has only one layer of arrows, and does not
involve composing or simultaneously lifting nested coverings. -/
theorem colimit_site_covering_families_at_stage
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (P : ∀ j : J, Precoverage (F.obj j))
    (hfinite : ∀ (j : J) (X : F.obj j) (R : Presieve X), R ∈ P j X → Finite R.uncurry)
    (hcover : ∀ (j k : J) (a : j ⟶ k) (X : F.obj j) (R : Presieve X),
      R ∈ P j X → R.map (F.map a).toFunctor ∈ P k ((F.map a).toFunctor.obj X))
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V)) (Q : Precoverage V.pt)
    (hQ : ∀ (Y : V.pt) (R : Presieve Y), R ∈ Q Y ↔
      ∃ (j : J) (X : F.obj j) (S : Presieve X)
        (h : (V.ι.app j).toFunctor.obj X = Y),
        S ∈ P j X ∧ h ▸ S.map (V.ι.app j).toFunctor = R)
    {κ : Type u} [Finite κ] (j₀ : J) (T₀ : κ → F.obj j₀)
    {S : κ → V.pt} (hT₀ : ∀ i, (V.ι.app j₀).toFunctor.obj (T₀ i) = S i)
    {τ : κ → Type u} [∀ i, Finite (τ i)] {X : ∀ i, τ i → V.pt}
    (f : ∀ i t, X i t ⟶ S i)
    (hf : ∀ i, Presieve.ofArrows (X i) (f i) ∈ Q (S i)) :
    ∃ (j : J) (e : j₀ ⟶ j) (A : ∀ i, τ i → F.obj j)
      (a : ∀ i t, A i t ⟶ (F.map e).toFunctor.obj (T₀ i)),
      (∀ i, Presieve.ofArrows (A i) (a i) ∈ P j ((F.map e).toFunctor.obj (T₀ i))) ∧
      (∀ i t, Arrow.mk ((V.ι.app j).toFunctor.map (a i t)) = Arrow.mk (f i t)) := by
  classical
  have hi (i : κ) :
      ∃ (j : J) (e : j₀ ⟶ j) (A : τ i → F.obj j)
        (a : ∀ t, A t ⟶ (F.map e).toFunctor.obj (T₀ i)),
        Presieve.ofArrows A a ∈ P j ((F.map e).toFunctor.obj (T₀ i)) ∧
        ∀ t, Arrow.mk ((V.ι.app j).toFunctor.map (a t)) = Arrow.mk (f i t) := by
    obtain ⟨k, U, R, hU, hcov, hR⟩ := (hQ (S i) _).mp (hf i)
    have : Finite R.uncurry := hfinite k U R hcov
    obtain ⟨j, e, d, h, A, a, heq, himage⟩ :=
      colimit_presieve_indexed_presentation J F V hobjects harrows j₀ k (T₀ i) U R
        (hT₀ i) hU (f i) hR
    refine ⟨j, e, A, a, ?_, himage⟩
    rw [heq]
    exact Eq.rec (motive := fun Z h => (h ▸ R.map (F.map d).toFunctor) ∈ P j Z)
      (hcover k j d U R hcov) h
  choose ji ei Ai ai hcov himage using hi
  obtain ⟨j, e, d, hd⟩ := IsFiltered.wideSpan ei
  have hj (i : κ) :
      ∃ (A : τ i → F.obj j) (a : ∀ t, A t ⟶ (F.map e).toFunctor.obj (T₀ i)),
        Presieve.ofArrows A a ∈ P j ((F.map e).toFunctor.obj (T₀ i)) ∧
        ∀ t, Arrow.mk ((V.ι.app j).toFunctor.map (a t)) = Arrow.mk (f i t) := by
    rw [← hd i]
    have ht : (F.map (ei i ≫ d i)).toFunctor.obj (T₀ i) =
        (F.map (d i)).toFunctor.obj ((F.map (ei i)).toFunctor.obj (T₀ i)) :=
      congrArg (fun H : F.obj j₀ ⟶ F.obj j => H.toFunctor.obj (T₀ i))
        (F.map_comp (ei i) (d i))
    rw [ht]
    refine ⟨fun t => (F.map (d i)).toFunctor.obj (Ai i t),
      fun t => (F.map (d i)).toFunctor.map (ai i t), ?_, ?_⟩
    · simpa only [Presieve.map_ofArrows] using
        hcover (ji i) j (d i) _ _ (hcov i)
    · intro t
      calc
        Arrow.mk ((V.ι.app j).toFunctor.map ((F.map (d i)).toFunctor.map (ai i t))) =
            Arrow.mk ((V.ι.app (ji i)).toFunctor.map (ai i t)) :=
          congrArg (fun H : F.obj (ji i) ⟶ V.pt =>
            Arrow.mk (H.toFunctor.map (ai i t))) (V.w (d i))
        _ = Arrow.mk (f i t) := himage i t
  choose A a hcov himage using hj
  exact ⟨j, e, A, a, hcov, himage⟩

end CategoryTheory
