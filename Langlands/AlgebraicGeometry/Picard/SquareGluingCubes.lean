import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Cover.Open

/-! # Commuting cubes between commuting squares of schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.SquareGluingDescent

/-- A commuting square of schemes `i₁ ≫ j₁ = i₂ ≫ j₂`. -/
structure Sq where
  /-- The common corner. -/
  X₀ : Scheme.{u}
  /-- The first leg. -/
  X₁ : Scheme.{u}
  /-- The second leg. -/
  X₂ : Scheme.{u}
  /-- The total scheme. -/
  X : Scheme.{u}
  /-- The first corner map. -/
  i₁ : X₀ ⟶ X₁
  /-- The second corner map. -/
  i₂ : X₀ ⟶ X₂
  /-- The first leg map. -/
  j₁ : X₁ ⟶ X
  /-- The second leg map. -/
  j₂ : X₂ ⟶ X
  /-- Commutativity. -/
  w : i₁ ≫ j₁ = i₂ ≫ j₂

lemma Sq.w_assoc (S : Sq.{u}) {Z : Scheme.{u}} (h : S.X ⟶ Z) :
    S.i₁ ≫ S.j₁ ≫ h = S.i₂ ≫ S.j₂ ≫ h := by
  rw [← Category.assoc, S.w, Category.assoc]

/-- A commuting cube from the square `T` to the square `S`. -/
structure CubeMap (S T : Sq.{u}) where
  /-- The map of total schemes. -/
  t : T.X ⟶ S.X
  /-- The map of first legs. -/
  g₁ : T.X₁ ⟶ S.X₁
  /-- The map of second legs. -/
  g₂ : T.X₂ ⟶ S.X₂
  /-- The map of corners. -/
  g₀ : T.X₀ ⟶ S.X₀
  /-- The first leg face commutes. -/
  h₁ : T.j₁ ≫ t = g₁ ≫ S.j₁
  /-- The second leg face commutes. -/
  h₂ : T.j₂ ≫ t = g₂ ≫ S.j₂
  /-- The first corner face commutes. -/
  k₁ : T.i₁ ≫ g₁ = g₀ ≫ S.i₁
  /-- The second corner face commutes. -/
  k₂ : T.i₂ ≫ g₂ = g₀ ≫ S.i₂

namespace CubeMap

variable {S T T' T'' W : Sq.{u}}

lemma ext' {c c' : CubeMap S T} (ht : c.t = c'.t) (h₁ : c.g₁ = c'.g₁)
    (h₂ : c.g₂ = c'.g₂) (h₀ : c.g₀ = c'.g₀) : c = c' := by
  cases c
  cases c'
  subst ht h₁ h₂ h₀
  rfl

/-- Composition of cubes. -/
@[simps]
def comp (c' : CubeMap T T') (c : CubeMap S T) : CubeMap S T' where
  t := c'.t ≫ c.t
  g₁ := c'.g₁ ≫ c.g₁
  g₂ := c'.g₂ ≫ c.g₂
  g₀ := c'.g₀ ≫ c.g₀
  h₁ := by rw [reassoc_of% c'.h₁, c.h₁, Category.assoc]
  h₂ := by rw [reassoc_of% c'.h₂, c.h₂, Category.assoc]
  k₁ := by rw [reassoc_of% c'.k₁, c.k₁, Category.assoc]
  k₂ := by rw [reassoc_of% c'.k₂, c.k₂, Category.assoc]

lemma comp_assoc (c : CubeMap S T) (c' : CubeMap T T') (c'' : CubeMap T' T'') :
    comp (comp c'' c') c = comp c'' (comp c' c) :=
  ext' (Category.assoc _ _ _) (Category.assoc _ _ _) (Category.assoc _ _ _)
    (Category.assoc _ _ _)

/-- The cube is cartesian: its two leg faces and its first corner face are
pullback squares. -/
def Cart (c : CubeMap S T) : Prop :=
  IsPullback c.g₁ T.j₁ S.j₁ c.t ∧ IsPullback c.g₂ T.j₂ S.j₂ c.t ∧
    IsPullback c.g₀ T.i₁ S.i₁ c.g₁

/-- Cartesian cubes compose. -/
lemma Cart.comp {c' : CubeMap T T'} {c : CubeMap S T} (hc' : Cart c') (hc : Cart c) :
    Cart (comp c' c) :=
  ⟨hc'.1.paste_horiz hc.1, hc'.2.1.paste_horiz hc.2.1, hc'.2.2.paste_horiz hc.2.2⟩

section OpenImmersion

variable {c : CubeMap S T} (hc : Cart c) [IsOpenImmersion c.t]
include hc

lemma Cart.isOpenImmersion_g₁ : IsOpenImmersion c.g₁ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) hc.1.flip ‹_›

lemma Cart.isOpenImmersion_g₂ : IsOpenImmersion c.g₂ :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) hc.2.1.flip ‹_›

lemma Cart.isOpenImmersion_g₀ : IsOpenImmersion c.g₀ :=
  have := hc.isOpenImmersion_g₁
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) hc.2.2.flip ‹_›

end OpenImmersion

/-- A pullback square of schemes is surjective onto pairs of points with the same
image. -/
lemma isPullback_exists_preimage {P X Y Z : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g)
    (x : X) (y : Y) (e : f x = g y) : ∃ z : P, fst z = x ∧ snd z = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y e
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz₂]

section Overlap

variable (c : CubeMap S T) (c' : CubeMap S T')

/-- The overlap square of two cubes into the same square: every corner is the
scheme pullback of the corresponding components. -/
@[reducible, simps]
def PB : Sq.{u} where
  X₀ := pullback c.g₀ c'.g₀
  X₁ := pullback c.g₁ c'.g₁
  X₂ := pullback c.g₂ c'.g₂
  X := pullback c.t c'.t
  i₁ := pullback.map c.g₀ c'.g₀ c.g₁ c'.g₁ T.i₁ T'.i₁ S.i₁ c.k₁.symm c'.k₁.symm
  i₂ := pullback.map c.g₀ c'.g₀ c.g₂ c'.g₂ T.i₂ T'.i₂ S.i₂ c.k₂.symm c'.k₂.symm
  j₁ := pullback.map c.g₁ c'.g₁ c.t c'.t T.j₁ T'.j₁ S.j₁ c.h₁.symm c'.h₁.symm
  j₂ := pullback.map c.g₂ c'.g₂ c.t c'.t T.j₂ T'.j₂ S.j₂ c.h₂.symm c'.h₂.symm
  w := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, T.w]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, T'.w]

/-- The first projection cube out of the overlap square. -/
@[simps]
def fstC : CubeMap T (PB c c') where
  t := pullback.fst _ _
  g₁ := pullback.fst _ _
  g₂ := pullback.fst _ _
  g₀ := pullback.fst _ _
  h₁ := pullback.lift_fst _ _ _
  h₂ := pullback.lift_fst _ _ _
  k₁ := pullback.lift_fst _ _ _
  k₂ := pullback.lift_fst _ _ _

/-- The second projection cube out of the overlap square. -/
@[simps]
def sndC : CubeMap T' (PB c c') where
  t := pullback.snd _ _
  g₁ := pullback.snd _ _
  g₂ := pullback.snd _ _
  g₀ := pullback.snd _ _
  h₁ := pullback.lift_snd _ _ _
  h₂ := pullback.lift_snd _ _ _
  k₁ := pullback.lift_snd _ _ _
  k₂ := pullback.lift_snd _ _ _

lemma fstC_comp : comp (fstC c c') c = comp (sndC c c') c' :=
  ext' pullback.condition pullback.condition pullback.condition pullback.condition

/-- The first projection cube is cartesian when the second cube is. -/
lemma cart_fstC (hc' : Cart c') : Cart (fstC c c') := by
  refine ⟨?_, ?_, ?_⟩
  · refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback c.t c'.t)
    have e : (PB c c').j₁ ≫ pullback.snd c.t c'.t = pullback.snd c.g₁ c'.g₁ ≫ T'.j₁ :=
      pullback.lift_snd _ _ _
    rw [e, c.h₁]
    exact (IsPullback.of_hasPullback c.g₁ c'.g₁).paste_vert hc'.1
  · refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback c.t c'.t)
    have e : (PB c c').j₂ ≫ pullback.snd c.t c'.t = pullback.snd c.g₂ c'.g₂ ≫ T'.j₂ :=
      pullback.lift_snd _ _ _
    rw [e, c.h₂]
    exact (IsPullback.of_hasPullback c.g₂ c'.g₂).paste_vert hc'.2.1
  · refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback c.g₁ c'.g₁)
    have e : (PB c c').i₁ ≫ pullback.snd c.g₁ c'.g₁ = pullback.snd c.g₀ c'.g₀ ≫ T'.i₁ :=
      pullback.lift_snd _ _ _
    rw [e, c.k₁]
    exact (IsPullback.of_hasPullback c.g₀ c'.g₀).paste_vert hc'.2.2

/-- The second projection cube is cartesian when the first cube is. -/
lemma cart_sndC (hc : Cart c) : Cart (sndC c c') := by
  refine ⟨?_, ?_, ?_⟩
  · refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback c.t c'.t).flip
    have e : (PB c c').j₁ ≫ pullback.fst c.t c'.t = pullback.fst c.g₁ c'.g₁ ≫ T.j₁ :=
      pullback.lift_fst _ _ _
    rw [e, c'.h₁]
    exact (IsPullback.of_hasPullback c.g₁ c'.g₁).flip.paste_vert hc.1
  · refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback c.t c'.t).flip
    have e : (PB c c').j₂ ≫ pullback.fst c.t c'.t = pullback.fst c.g₂ c'.g₂ ≫ T.j₂ :=
      pullback.lift_fst _ _ _
    rw [e, c'.h₂]
    exact (IsPullback.of_hasPullback c.g₂ c'.g₂).flip.paste_vert hc.2.1
  · refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback c.g₁ c'.g₁).flip
    have e : (PB c c').i₁ ≫ pullback.fst c.g₁ c'.g₁ = pullback.fst c.g₀ c'.g₀ ≫ T.i₁ :=
      pullback.lift_fst _ _ _
    rw [e, c'.k₁]
    exact (IsPullback.of_hasPullback c.g₀ c'.g₀).flip.paste_vert hc.2.2

variable {c c'}

section CompEq

variable {a : CubeMap T W} {b : CubeMap T' W} (e : comp a c = comp b c')
include e

lemma comp_eq_t : a.t ≫ c.t = b.t ≫ c'.t := congrArg CubeMap.t e

lemma comp_eq_g₁ : a.g₁ ≫ c.g₁ = b.g₁ ≫ c'.g₁ := congrArg CubeMap.g₁ e

lemma comp_eq_g₂ : a.g₂ ≫ c.g₂ = b.g₂ ≫ c'.g₂ := congrArg CubeMap.g₂ e

lemma comp_eq_g₀ : a.g₀ ≫ c.g₀ = b.g₀ ≫ c'.g₀ := congrArg CubeMap.g₀ e

end CompEq

/-- The cube into the overlap square induced by two cubes with equal composites. -/
@[simps]
def PB.lift (a : CubeMap T W) (b : CubeMap T' W) (e : comp a c = comp b c') :
    CubeMap (PB c c') W where
  t := pullback.lift a.t b.t (comp_eq_t e)
  g₁ := pullback.lift a.g₁ b.g₁ (comp_eq_g₁ e)
  g₂ := pullback.lift a.g₂ b.g₂ (comp_eq_g₂ e)
  g₀ := pullback.lift a.g₀ b.g₀ (comp_eq_g₀ e)
  h₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      simp only [pullback.lift_fst, pullback.lift_fst_assoc, a.h₁]
    · simp only [Category.assoc]
      simp only [pullback.lift_snd, pullback.lift_snd_assoc, b.h₁]
  h₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      simp only [pullback.lift_fst, pullback.lift_fst_assoc, a.h₂]
    · simp only [Category.assoc]
      simp only [pullback.lift_snd, pullback.lift_snd_assoc, b.h₂]
  k₁ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      simp only [pullback.lift_fst, pullback.lift_fst_assoc, a.k₁]
    · simp only [Category.assoc]
      simp only [pullback.lift_snd, pullback.lift_snd_assoc, b.k₁]
  k₂ := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      simp only [pullback.lift_fst, pullback.lift_fst_assoc, a.k₂]
    · simp only [Category.assoc]
      simp only [pullback.lift_snd, pullback.lift_snd_assoc, b.k₂]

lemma PB.lift_fstC (a : CubeMap T W) (b : CubeMap T' W) (e : comp a c = comp b c') :
    comp (PB.lift a b e) (fstC c c') = a :=
  ext' (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _)
    (pullback.lift_fst _ _ _)

lemma PB.lift_sndC (a : CubeMap T W) (b : CubeMap T' W) (e : comp a c = comp b c') :
    comp (PB.lift a b e) (sndC c c') = b :=
  ext' (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
    (pullback.lift_snd _ _ _)

end Overlap

end CubeMap

end Langlands.AlgebraicGeometry.Picard.SquareGluingDescent
