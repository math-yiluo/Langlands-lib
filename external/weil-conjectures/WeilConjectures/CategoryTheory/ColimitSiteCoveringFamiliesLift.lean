/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Sites.Precoverage
import WeilConjectures.CategoryTheory.ColimitSiteCoveringFamiliesAtStage

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Simultaneous lifting of an outer covering and its finite family of inner coverings.
Source: Stacks Project, Sites, Tag 09YL, the paragraph verifying axiom (2), together
with the finite-diagram observation at the start of its proof.
(blueprint: lem-weil-pbc-colimit-site-covering-families-lift)

Proof: Use hQ to choose a stage covering presieve for the outer family and for
each inner family. Each of these presieves has finitely many arrows by hfinite.
For every arrow of a requested indexed family, the equality of presieves in hQ
supplies a stage member with that image, including its source equality. Conversely,
choose for every member of each stage presieve an index of the requested family
with the same image arrow. There are finitely many choices, since the outer index,
each inner index, and each stage presieve are finite. Move the finitely many stages
and all these representatives to a common stage using filteredness.

Apply eventual equality in the object colimit to align the target of the outer
presieve, its members' sources with the requested outer-source representatives,
and the targets and sources of each inner presieve with the corresponding outer
and inner representatives. Apply eventual equality in the arrow colimit to the
finitely many pairs consisting of a chosen member and its indexed representative,
in both directions of the presieve comparison. Refine to one common stage where
all these equalities hold. Transport along the endpoint equalities defines a and b.
The comparisons in both directions say that their indexed presieves equal the
transported original stage presieves, which are covering by hcover. Cocone
naturality preserves their image arrows, giving the two Arrow.mk equalities.
For an empty outer family, hQ still supplies its target and an empty covering
presieve (a nonempty presieve cannot have empty image); its image stays empty
at every transition. An empty inner family is treated in the same way. Repeated
indices impose only finitely many arrow equalities and do not change a presieve.
No stage composition axiom is used: this statement lifts the input families only. -/
theorem colimit_site_covering_families_lift
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
    {ι : Type u} [Finite ι] {S : V.pt} {X : ι → V.pt}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ Q S)
    {σ : ι → Type u} [∀ i, Finite (σ i)] {Y : ∀ i, σ i → V.pt}
    (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ Q (X i)) :
    ∃ (j : J) (T : F.obj j) (A : ι → F.obj j)
      (B : ∀ i, σ i → F.obj j) (a : ∀ i, A i ⟶ T) (b : ∀ i k, B i k ⟶ A i),
      (V.ι.app j).toFunctor.obj T = S ∧
      Presieve.ofArrows A a ∈ P j T ∧
      (∀ i, Presieve.ofArrows (B i) (b i) ∈ P j (A i)) ∧
      (∀ i, Arrow.mk ((V.ι.app j).toFunctor.map (a i)) = Arrow.mk (f i)) ∧
      (∀ i k, Arrow.mk ((V.ι.app j).toFunctor.map (b i k)) = Arrow.mk (g i k)) := by
  obtain ⟨j₀, T₀, R₀, hT₀, _, _⟩ := (hQ S _).mp hf
  obtain ⟨j₁, e₁, A₁, a₁, ha₁, himage₁⟩ :=
    colimit_site_covering_families_at_stage J F P hfinite hcover V hobjects harrows Q hQ
      (κ := PUnit.{u + 1}) j₀ (fun _ => T₀) (fun _ => hT₀)
      (τ := fun _ => ι) (X := fun _ => X) (fun _ => f) (fun _ => hf)
  let T₁ := (F.map e₁).toFunctor.obj T₀
  have hA₁ : ∀ i, (V.ι.app j₁).toFunctor.obj (A₁ PUnit.unit i) = X i := by
    intro i
    exact congrArg Arrow.left (himage₁ PUnit.unit i)
  obtain ⟨j₂, e₂, B₂, b₂, hb₂, himage₂⟩ :=
    colimit_site_covering_families_at_stage J F P hfinite hcover V hobjects harrows Q hQ
      j₁ (A₁ PUnit.unit) hA₁ g hg
  refine ⟨j₂, (F.map e₂).toFunctor.obj T₁,
    fun i => (F.map e₂).toFunctor.obj (A₁ PUnit.unit i), B₂,
    fun i => (F.map e₂).toFunctor.map (a₁ PUnit.unit i), b₂, ?_, ?_, hb₂, ?_, himage₂⟩
  · calc
      (V.ι.app j₂).toFunctor.obj ((F.map e₂).toFunctor.obj T₁) =
          (V.ι.app j₁).toFunctor.obj T₁ :=
        congrArg (fun H : F.obj j₁ ⟶ V.pt => H.toFunctor.obj T₁) (V.w e₂)
      _ = (V.ι.app j₀).toFunctor.obj T₀ :=
        congrArg (fun H : F.obj j₀ ⟶ V.pt => H.toFunctor.obj T₀) (V.w e₁)
      _ = S := hT₀
  · simpa only [Presieve.map_ofArrows] using
      hcover j₁ j₂ e₂ T₁ _ (ha₁ PUnit.unit)
  · intro i
    calc
      Arrow.mk ((V.ι.app j₂).toFunctor.map
          ((F.map e₂).toFunctor.map (a₁ PUnit.unit i))) =
          Arrow.mk ((V.ι.app j₁).toFunctor.map (a₁ PUnit.unit i)) :=
        congrArg (fun H : F.obj j₁ ⟶ V.pt =>
          Arrow.mk (H.toFunctor.map (a₁ PUnit.unit i))) (V.w e₂)
      _ = Arrow.mk (f i) := himage₁ PUnit.unit i

end CategoryTheory
