import Langlands.AlgebraicGeometry.Picard.LineBundleOpenCoverGluing
import Langlands.AlgebraicGeometry.Modules.CommonSourceCocycle
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoproductChart

/-! # Line bundles on the relative space of a coproduct chart -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

namespace DisjointCoverGluing

open Langlands.Scheme.Modules

variable {Y : Scheme.{u}} (𝒰 : Y.OpenCover.{u})

/-- Distinct members of an open cover have empty overlaps. -/
def IsDisjoint : Prop :=
  ∀ i j, i ≠ j → IsEmpty ↑(pullback (𝒰.f i) (𝒰.f j))

/-- Morphisms of modules on an empty scheme are equal. -/
lemma modules_hom_ext {W : Scheme.{u}} [IsEmpty W] {A B : W.Modules} (φ ψ : A ⟶ B) :
    φ = ψ := by
  ext U a
  have : Subsingleton Γ(B, U) := Module.subsingleton Γ(W, U) _
  exact Subsingleton.elim _ _

/-- Any two modules on an empty scheme are isomorphic. -/
def isoOfIsEmpty {W : Scheme.{u}} [IsEmpty W] (A B : W.Modules) : A ≅ B where
  hom := 0
  inv := 0
  hom_inv_id := modules_hom_ext _ _
  inv_hom_id := modules_hom_ext _ _

/-- The diagonal overlap identification of a piece with itself, induced by
the piece itself as a common source. -/
def diagTransition (i : 𝒰.I₀) (M : (𝒰.X i).Modules) :
    (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f i))).obj M ≅
      (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f i))).obj M :=
  CommonSourceCocycle.transition (pullback.fst (𝒰.f i) (𝒰.f i))
    (pullback.snd (𝒰.f i) (𝒰.f i)) (𝟙 _) (𝟙 _)
    (by rw [fst_eq_snd_of_mono_eq]) M
    ((Scheme.Modules.pullbackId _).app M) ((Scheme.Modules.pullbackId _).app M)

variable {𝒰}

open Classical in
/-- Overlap identifications on a disjoint cover: the diagonal identification on
each repeated pair and the unique identification on empty overlaps. -/
def transition (h : IsDisjoint 𝒰) (M : ∀ i, (𝒰.X i).Modules) (i j : 𝒰.I₀) :
    (Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (M i) ≅
      (Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (M j) :=
  if hij : i = j then by subst hij; exact diagTransition 𝒰 i (M i)
  else haveI := h i j hij; isoOfIsEmpty _ _

lemma transition_self (h : IsDisjoint 𝒰) (M : ∀ i, (𝒰.X i).Modules) (i : 𝒰.I₀) :
    transition h M i i = diagTransition 𝒰 i (M i) := by
  simp [transition]

/-- These identifications satisfy the module-gluing cocycle condition. -/
lemma cocycle (h : IsDisjoint 𝒰) (M : ∀ i, (𝒰.X i).Modules) :
    OpenCoverModuleGluing.CocycleCondition 𝒰 M (transition h M) := by
  intro i j k
  by_cases hij : i = j
  · subst hij
    by_cases hik : i = k
    · subst hik
      rw [transition_self]
      apply OpenCoverModuleGluing.CompEq4.of_eq
      apply CommonSourceCocycle.transition_cocycle
    · have := h i k hik
      have : IsEmpty ↑(pullback (pullback.fst (𝒰.f i) (𝒰.f i))
          (pullback.fst (𝒰.f i) (𝒰.f k))) :=
        Function.isEmpty (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f i))
          (pullback.fst (𝒰.f i) (𝒰.f k)))
      exact modules_hom_ext _ _
  · have := h i j hij
    have : IsEmpty ↑(pullback (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f k))) :=
      Function.isEmpty (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j))
        (pullback.fst (𝒰.f i) (𝒰.f k)))
    exact modules_hom_ext _ _

/-- Gluing data for line bundles on the members of a disjoint open cover. -/
def gluingData (h : IsDisjoint 𝒰) (L : ∀ i, LineBundle (𝒰.X i)) :
    LineBundleGluingData 𝒰 where
  bundle := L
  transition := transition h (fun i ↦ (L i).obj)
  cocycle := cocycle h (fun i ↦ (L i).obj)

/-- A line bundle on a scheme with a disjoint open cover, with prescribed pieces. -/
def glue (h : IsDisjoint 𝒰) (L : ∀ i, LineBundle (𝒰.X i)) : LineBundle Y :=
  (gluingData h L).glue

/-- The glued line bundle restricts to each prescribed piece. -/
def glueIso (h : IsDisjoint 𝒰) (L : ∀ i, LineBundle (𝒰.X i)) (i : 𝒰.I₀) :
    (LineBundle.pullback (𝒰.f i)).obj (glue h L) ≅ L i :=
  (gluingData h L).iso i

end DisjointCoverGluing

namespace CoproductChartBundle

open AlgebraicSpace.CoproductChart

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- The relative space of a map over `S` is the base change of the relative
space of its target. -/
lemma isPullback_relativeSpace_map {T U : Over S} (h : T ⟶ U) :
    IsPullback ((relativeSpace f).map h) (pullback.fst T.hom f)
      (pullback.fst U.hom f) h.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd U.hom f) (h₂₂ := U.hom) (v₁₃ := f)
    ?_ ?_ (IsPullback.of_hasPullback U.hom f).flip
  · have hs := (IsPullback.of_hasPullback T.hom f).flip
    rw [relativeSpace_map_snd, Over.w]
    exact hs
  · exact pullback.lift_fst _ _ _

variable {ι : Type u} (V : ι → Over S)

/-- The open cover of the relative space of a coproduct chart by the relative
spaces of its components. -/
def relativeCover : ((relativeSpace f).obj (sigmaOver V)).OpenCover.{u} :=
  Scheme.Cover.copy
    ((sigmaOpenCover (fun i ↦ (V i).left)).pullback₁ (pullback.fst (sigmaOver V).hom f))
    ι (fun i ↦ (relativeSpace f).obj (V i))
    (fun i ↦ (relativeSpace f).map (sigmaOverι V i)) (Equiv.refl _)
    (fun i ↦ (isPullback_relativeSpace_map f (sigmaOverι V i)).isoPullback)
    (fun i ↦ ((isPullback_relativeSpace_map f (sigmaOverι V i)).isoPullback_hom_fst).symm)

@[simp]
lemma relativeCover_f (i : ι) :
    (relativeCover f V).f i = (relativeSpace f).map (sigmaOverι V i) := rfl

@[simp]
lemma relativeCover_X (i : ι) :
    (relativeCover f V).X i = (relativeSpace f).obj (V i) := rfl

/-- Distinct components have disjoint relative spaces. -/
lemma relativeCover_isDisjoint : DisjointCoverGluing.IsDisjoint (relativeCover f V) := by
  intro i j hij
  have : IsEmpty ↑(pullback (sigmaOverι V i).left (sigmaOverι V j).left) :=
    isEmpty_pullback_sigmaι_of_ne (fun i ↦ (V i).left) hij
  exact Function.isEmpty (pullback.map _ _ _ _ (pullback.fst (V i).hom f)
    (pullback.fst (V j).hom f) (pullback.fst (sigmaOver V).hom f)
    (isPullback_relativeSpace_map f (sigmaOverι V i)).w
    (isPullback_relativeSpace_map f (sigmaOverι V j)).w)

/-- The line bundle on the relative space of a coproduct chart glued from line
bundles on the relative spaces of its components. -/
def bundle (L : ∀ i, LineBundle ((relativeSpace f).obj (V i))) :
    LineBundle ((relativeSpace f).obj (sigmaOver V)) :=
  DisjointCoverGluing.glue (relativeCover_isDisjoint f V) L

/-- The glued bundle restricts to each component bundle. -/
def bundleIso (L : ∀ i, LineBundle ((relativeSpace f).obj (V i))) (i : ι) :
    (LineBundle.pullback ((relativeSpace f).map (sigmaOverι V i))).obj (bundle f V L) ≅
      L i :=
  DisjointCoverGluing.glueIso (relativeCover_isDisjoint f V) L i

end CoproductChartBundle

end Langlands.AlgebraicGeometry.Picard
