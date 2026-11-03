import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Extensive

/-! # Triple-overlap components from a double-overlap decomposition -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.Descent

variable {B S : Scheme.{u}} (p : S ⟶ B) {I : Type} {Z : I → Scheme.{u}}
    (q : (i : I) → Z i ⟶ Overlap p)

/-- Map from a pair of double-overlap components to the triple overlap. -/
def componentPullbackMap (ij : I × I) :
    pullback (q ij.1 ≫ snd p) (q ij.2 ≫ fst p) ⟶ Triple p :=
  pullback.map _ _ _ _ (q ij.1) (q ij.2) (𝟙 S) (by simp) (by simp)

/-- Pullbacks of finite components decompose the actual triple overlap. -/
theorem componentPullbackMap_isIso_desc [Finite I] [IsIso (Sigma.desc q)] :
    IsIso (Sigma.desc (componentPullbackMap p q)) := by
  let a : (i : I) → Z i ⟶ S := fun i => q i ≫ snd p
  let b : (i : I) → Z i ⟶ S := fun i => q i ≫ fst p
  let c := Sigma.desc q
  let t := Sigma.desc fun (ij : I × I) =>
    pullback.map (a ij.1) (b ij.2) (Sigma.desc a) (Sigma.desc b)
      (Sigma.ι Z ij.1) (Sigma.ι Z ij.2) (𝟙 S) (by simp) (by simp)
  have ht : IsIso t := by dsimp only [t]; infer_instance
  have ha : Sigma.desc a ≫ 𝟙 S = c ≫ snd p := by
    apply Sigma.hom_ext
    intro i
    simp [a, c]
  have hb : Sigma.desc b ≫ 𝟙 S = c ≫ fst p := by
    apply Sigma.hom_ext
    intro i
    simp [b, c]
  let d := pullback.map (Sigma.desc a) (Sigma.desc b) (snd p) (fst p)
    c c (𝟙 S) ha hb
  have hd : IsIso d := by dsimp only [d, c]; infer_instance
  have h : Sigma.desc (componentPullbackMap p q) = t ≫ d := by
    apply Sigma.hom_ext
    intro ij
    apply pullback.hom_ext <;> simp [t, d, componentPullbackMap, pullback.map, a, b, c]
  rw [h]
  infer_instance

variable [∀ i, IsIso (q i ≫ fst p)]

/-- A triple component identified with the first of its two double components. -/
def tripleComponent (ij : I × I) : Z ij.1 ⟶ Triple p :=
  inv (pullback.fst (q ij.1 ≫ snd p) (q ij.2 ≫ fst p)) ≫
    componentPullbackMap p q ij

/-- These actual triple components form a finite coproduct decomposition. -/
instance tripleComponent_isIso_desc [Finite I] [IsIso (Sigma.desc q)] :
    IsIso (Sigma.desc (tripleComponent p q)) := by
  have : IsIso (Sigma.desc (componentPullbackMap p q)) :=
    componentPullbackMap_isIso_desc p q
  have h : Sigma.desc (tripleComponent p q) =
      CategoryTheory.Limits.Sigma.map (fun (ij : I × I) =>
        inv (pullback.fst (q ij.1 ≫ snd p) (q ij.2 ≫ fst p))) ≫
      Sigma.desc (componentPullbackMap p q) := by
    apply Sigma.hom_ext
    intro ij
    simp [tripleComponent]
  rw [h]
  infer_instance

@[reassoc (attr := simp)]
theorem tripleComponent_p1 (ij : I × I) :
    tripleComponent p q ij ≫ p1 p = q ij.1 ≫ fst p := by
  simp [tripleComponent, p1, p12, componentPullbackMap, pullback.map]

@[reassoc (attr := simp)]
theorem tripleComponent_p3 (ij : I × I) :
    tripleComponent p q ij ≫ p3 p =
      (q ij.1 ≫ snd p) ≫ inv (q ij.2 ≫ fst p) ≫ (q ij.2 ≫ snd p) := by
  simp [tripleComponent, p3, p23, componentPullbackMap, pullback.map]

instance tripleComponent_p1_isIso (ij : I × I) :
    IsIso (tripleComponent p q ij ≫ p1 p) := by
  rw [tripleComponent_p1]
  infer_instance

instance tripleComponent_p3_isIso [∀ i, IsIso (q i ≫ snd p)] (ij : I × I) :
    IsIso (tripleComponent p q ij ≫ p3 p) := by
  rw [tripleComponent_p3]
  infer_instance

end Langlands.GroupScheme.Descent
