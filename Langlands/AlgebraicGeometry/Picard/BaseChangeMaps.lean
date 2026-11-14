import Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base change maps between affine base changes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open Scheme.TwoAffineOpenCover

section Maps

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)}
  {B : Type u} [CommRing B] [Algebra R B]

/-- The base change map `Y_K ⟶ Y_B` along an algebra map `ψ : B → K`. -/
abbrev bcMap (K : Type u) [CommRing K] [Algebra R K] (ψ : B →ₐ[R] K) :
    pullback π (specMap R K) ⟶ pullback π (specMap R B) :=
  pullback.map π (specMap R K) π (specMap R B) (𝟙 _)
    (Spec.map (CommRingCat.ofHom ψ.toRingHom)) (𝟙 _) (by simp) (by
      rw [Category.comp_id, specMap, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact ψ.comp_algebraMap.symm)

lemma bcMap_fst (K : Type u) [CommRing K] [Algebra R K] (ψ : B →ₐ[R] K) :
    bcMap (π := π) K ψ ≫ pullback.fst π (specMap R B) = pullback.fst π (specMap R K) := by
  simp [bcMap]

lemma bcMap_snd (K : Type u) [CommRing K] [Algebra R K] (ψ : B →ₐ[R] K) :
    bcMap (π := π) K ψ ≫ pullback.snd π (specMap R B) =
      pullback.snd π (specMap R K) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
  simp [bcMap]

end Maps

section Points

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) {G : Scheme.{u}}
  (p : G ⟶ Spec (.of R))

/-- The base change map `X_B ⟶ X ×_R G` along a `B`-point `k` of `G`. -/
abbrev ptMap {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ G)
    (hk : k ≫ p = specMap R B) : pullback π (specMap R B) ⟶ pullback π p :=
  pullback.map π (specMap R B) π p (𝟙 _) k (𝟙 _) (by simp) (by rw [hk]; simp)

lemma specMap_comp {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ specMap R B = specMap R B' := by
  rw [specMap, specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact φ.comp_algebraMap

lemma bcMap_ptMap {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (k : Spec (.of B) ⟶ G) (hk : k ≫ p = specMap R B) :
    bcMap (π := π) B' φ ≫ ptMap π p k hk =
      ptMap π p (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ k)
        (by rw [Category.assoc, hk, specMap_comp]) := by
  apply pullback.hom_ext <;> simp [ptMap, bcMap]

/-- The structure of `Γ(G, O)` as an `R`-algebra through `p`. -/
abbrev affAlg (O : G.affineOpens) : Algebra R Γ(G, O.1) := algebraOfHom p O.1

/-- The canonical point `Spec Γ(G, O) ⟶ G` of an affine open. -/
def affPt (O : G.affineOpens) : Spec Γ(G, O.1) ⟶ G := O.2.fromSpec

instance (O : G.affineOpens) : IsOpenImmersion (affPt O) := by
  unfold affPt; infer_instance

lemma range_affPt (O : G.affineOpens) : Set.range (affPt O) = (O.1 : Set G) :=
  IsAffineOpen.range_fromSpec O.2

lemma affPt_comp (O : G.affineOpens) :
    letI := affAlg p O
    affPt O ≫ p = specMap R Γ(G, O.1) := by
  letI := affAlg p O
  unfold affPt
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) O.2 le_top,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, specMap]
  rfl

end Points

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule
