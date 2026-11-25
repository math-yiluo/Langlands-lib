/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.CardinalGenerated
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Covering a `κ`-generated subobject along an epimorphism

Let `C` be a Grothendieck abelian category, `G : C` a separator and `κ` a regular cardinal
dominating the cardinalities of the subobject lattices of the finite copowers of `G`.

We prove the *cover lemma*: if `p : X ⟶ Y` is an epimorphism and `V` is a `κ`-generated
subobject of `Y`, then `V` is the image under `p` of a `κ`-generated subobject of `X`.

The proof reduces to the case where `V` is the image of a single morphism `g : G ⟶ Y`.
There the pullback `E := pullback p g` maps epimorphically onto `G`, and it is enough to
cover `G` by the images of fewer than `κ` many morphisms `G ⟶ E`: the images in `G` of all
morphisms `G ⟶ E` join to the whole of `G` (because `G` is a separator), and they take fewer
than `κ` distinct values inside `Subobject G`, so one witness per value suffices.

## Main results

- `CategoryTheory.exists_isCardinalGenerated_subobject_of_epi`: the cover lemma.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

section Image

variable {A X Y : C}

/-- The image subobject of an epimorphism is the whole target. -/
private lemma imageSubobject_eq_top_of_epi (f : X ⟶ Y) [Epi f] : imageSubobject f = ⊤ := by
  have : Epi (image.ι f) := epi_of_epi_fac (image.fac f)
  exact (Subobject.epi_iff_mk_eq_top (image.ι f)).1 this

/-- A morphism whose image subobject is the whole target is an epimorphism. -/
private lemma epi_of_imageSubobject_eq_top (f : X ⟶ Y) (hf : imageSubobject f = ⊤) : Epi f := by
  have : IsIso (imageSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 hf
  rw [← imageSubobject_arrow_comp f]
  infer_instance

/-- The image of a subobject `S` of `X` under `p : X ⟶ Y` is the image subobject of
`S.arrow ≫ p`. -/
private lemma exists_obj_eq_imageSubobject (p : X ⟶ Y) (S : Subobject X) :
    (Subobject.«exists» p).obj S = imageSubobject (S.arrow ≫ p) :=
  Subobject.exists_obj_eq_mk p S (factorThruImage _) (image.ι _) (image.fac _)

/-- The image under `p` of the image subobject of `f` is the image subobject of `f ≫ p`. -/
private lemma exists_obj_imageSubobject (f : A ⟶ X) (p : X ⟶ Y) :
    (Subobject.«exists» p).obj (imageSubobject f) = imageSubobject (f ≫ p) := by
  have h : factorThruImageSubobject f ≫ ((imageSubobject f).arrow ≫ p) = f ≫ p := by
    rw [← Category.assoc, imageSubobject_arrow_comp]
  rw [exists_obj_eq_imageSubobject, ← h, imageSubobject_comp_of_epi (factorThruImageSubobject f)]

variable [IsGrothendieckAbelian.{w} C]

/-- The image subobject of a morphism out of a coproduct is the join of the image subobjects
of its components. -/
private lemma imageSubobject_sigmaDesc {ι : Type w} (f : ι → (A ⟶ X)) :
    imageSubobject (Sigma.desc f) = ⨆ i, imageSubobject (f i) := by
  refine le_antisymm (imageSubobject_le _ (Sigma.desc (fun i ↦ factorThruImageSubobject (f i) ≫
    Subobject.ofLE _ _ (le_iSup (fun i ↦ imageSubobject (f i)) i))) ?_) (iSup_le fun i ↦ ?_)
  · ext i
    simp
  · simpa using imageSubobject_comp_le (Sigma.ι (fun (_ : ι) ↦ A) i) (Sigma.desc f)

end Image

variable [IsGrothendieckAbelian.{w} C] (G : C) (κ : Cardinal.{w})

/-- If `e : E ⟶ G` is an epimorphism onto a separator `G` and `Subobject G` has fewer than `κ`
elements, then `E` receives a morphism from a coproduct of fewer than `κ` copies of `G` whose
composition with `e` is still an epimorphism. -/
private lemma exists_epi_comp_of_epi (hG : IsSeparator G)
    (hsubG : HasCardinalLT (Subobject G) κ) {E : C} (e : E ⟶ G) [Epi e] :
    ∃ (ι : Type w) (_ : HasCardinalLT ι κ) (ε : (∐ fun (_ : ι) ↦ G) ⟶ E), Epi (ε ≫ e) := by
  classical
  -- the subobjects of `G` which arise as the image of a composition `G ⟶ E ⟶ G`
  let R : Type max u v := { S : Subobject G // ∃ h : G ⟶ E, imageSubobject (h ≫ e) = S }
  have hR : HasCardinalLT R κ := hsubG.of_injective Subtype.val Subtype.val_injective
  have : Small.{w} R := hR.small
  choose hh hhe using fun (r : R) ↦ r.2
  refine ⟨Shrink.{w} R, (hasCardinalLT_iff_of_equiv (equivShrink.{w} R) κ).1 hR,
    Sigma.desc (fun s ↦ hh ((equivShrink.{w} R).symm s)), epi_of_imageSubobject_eq_top _ ?_⟩
  have hcomp : Sigma.desc (fun s ↦ hh ((equivShrink.{w} R).symm s)) ≫ e =
      Sigma.desc (fun s ↦ hh ((equivShrink.{w} R).symm s) ≫ e) := by
    ext s
    simp
  -- the images in `G` of all the morphisms `G ⟶ E` already join to the whole of `G`
  have htop : ⨆ (h : G ⟶ E), imageSubobject (h ≫ e) = ⊤ := by
    have h₁ : ∀ (h : G ⟶ E), imageSubobject (h ≫ e) =
        (Subobject.«exists» e).obj (imageSubobject h) :=
      fun h ↦ (exists_obj_imageSubobject h e).symm
    simp only [h₁]
    rw [← Subobject.exists_obj_iSup, iSup_imageSubobject_eq_top_of_isSeparator G hG E,
      exists_obj_eq_imageSubobject]
    exact imageSubobject_eq_top_of_epi _
  rw [hcomp, imageSubobject_sigmaDesc]
  refine le_antisymm le_top ?_
  rw [← htop]
  refine iSup_le fun h ↦ le_iSup_of_le (equivShrink.{w} R ⟨_, h, rfl⟩) (le_of_eq ?_)
  rw [Equiv.symm_apply_apply, hhe]

/-- The cover lemma for the image of a single morphism from the generator: for an epimorphism
`p : X ⟶ Y` and a morphism `g : G ⟶ Y`, the image subobject of `g` is the image under `p` of a
`κ`-generated subobject of `X`. -/
private lemma exists_isCardinalGenerated_subobject_imageSubobject (hG : IsSeparator G)
    (hsubG : HasCardinalLT (Subobject G) κ) {X Y : C} (p : X ⟶ Y) [Epi p] (g : G ⟶ Y) :
    ∃ (W : Subobject X), isCardinalGenerated G κ (W : C) ∧
      (Subobject.«exists» p).obj W = imageSubobject g := by
  obtain ⟨ι, hι, ε, hε⟩ := exists_epi_comp_of_epi G κ hG hsubG (pullback.snd p g)
  refine ⟨imageSubobject (ε ≫ pullback.fst p g),
    isCardinalGenerated_of_epi G κ (factorThruImageSubobject (ε ≫ pullback.fst p g))
      ⟨ι, hι, 𝟙 _, inferInstance⟩, ?_⟩
  rw [exists_obj_imageSubobject, Category.assoc, pullback.condition, ← Category.assoc,
    imageSubobject_comp_of_epi]

set_option linter.unusedVariables false in
/-- **The cover lemma.** Every `κ`-generated subobject of the target of an epimorphism is the
image of a `κ`-generated subobject of the source.

The hypothesis `hκ` is part of the standing hypotheses of this development; it is not needed
here, since the regularity of `κ` already provides `Cardinal.aleph0 ≤ κ`. -/
lemma exists_isCardinalGenerated_subobject_of_epi [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) (hG : IsSeparator G)
    (hsub : ∀ n : ℕ, HasCardinalLT (Subobject (∐ (fun (_ : Fin n) ↦ G))) κ)
    {X Y : C} (p : X ⟶ Y) [Epi p] (V : Subobject Y)
    (hV : isCardinalGenerated G κ (V : C)) :
    ∃ (W : Subobject X), isCardinalGenerated G κ (W : C) ∧
      (Subobject.«exists» p).obj W = V := by
  classical
  have hsubG : HasCardinalLT (Subobject G) κ := by
    have : IsSplitMono (Sigma.ι (fun (_ : Fin 1) ↦ G) 0) :=
      ⟨⟨Sigma.desc (fun _ ↦ 𝟙 G), by simp⟩⟩
    exact Subobject.hasCardinalLT_of_mono (hsub 1) (Sigma.ι (fun (_ : Fin 1) ↦ G) 0)
  obtain ⟨ι, hι, q, hq⟩ := hV
  choose W hW hWe using fun (i : ι) ↦ exists_isCardinalGenerated_subobject_imageSubobject
    G κ hG hsubG p (Sigma.ι (fun (_ : ι) ↦ G) i ≫ q ≫ V.arrow)
  refine ⟨⨆ i, W i, isCardinalGenerated_iSup G κ W hι hW, ?_⟩
  have hdesc : Sigma.desc (fun (i : ι) ↦ Sigma.ι (fun (_ : ι) ↦ G) i ≫ q ≫ V.arrow) =
      q ≫ V.arrow := by
    ext i
    simp
  rw [Subobject.exists_obj_iSup]
  simp only [hWe]
  rw [← imageSubobject_sigmaDesc, hdesc, imageSubobject_comp_of_epi, imageSubobject_mono,
    Subobject.mk_arrow]

end CategoryTheory
