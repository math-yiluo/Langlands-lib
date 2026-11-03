import Langlands.GroupScheme.Torus.MaximalTransport
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # A common maximal torus from a normalizer double coset -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G B B' : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Actual common-torus maps from conjugate overgroups and a factorization of
the conjugating point in their chosen torus's normalizer double coset.
No Borel or reductivity assumption is needed for this construction. -/
def commonTorusOfNormalizerDoubleCoset
    (i : B ⟶ G) (i' : B' ⟶ G) (j : T.toGrp ⟶ G) (f : T.toGrp ⟶ B)
    (hj : IsMaximalTorus j) (hf : f ≫ i = j)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) (φ : B ≅ B')
    (hconj : i ≫ (G.innerIso g).hom = φ.hom ≫ i')
    (b₁ b₂ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X)
    (n : normalizerPoints j)
    (hg : g = (b₁ ≫ i.hom.hom) * (n : Over.mk (𝟙 _) ⟶ G.X) *
      (b₂ ≫ i.hom.hom)) :
    Σ t : T.toGrp ⟶ G, Σ f₁ : T.toGrp ⟶ B,
      {f₂ : T.toGrp ⟶ B' // IsMaximalTorus t ∧ f₁ ≫ i = t ∧ f₂ ≫ i' = t} := by
  let σ : T ≅ T := normalizingAut j n
  let a : T.toGrp ⟶ T.toGrp := CommGroupScheme.groupHom σ.inv
  let t : T.toGrp ⟶ G := j ≫ (G.innerIso (b₁ ≫ i.hom.hom)).hom
  let f₁ : T.toGrp ⟶ B := f ≫ (B.innerIso b₁).hom
  let f₂ : T.toGrp ⟶ B' := a ≫ f ≫ (B.innerIso b₂⁻¹).hom ≫ φ.hom
  have hn : j ≫ (G.innerIso (n : Over.mk (𝟙 _) ⟶ G.X)).hom =
      CommGroupScheme.groupHom σ.hom ≫ j :=
    isNormalizingPoint_normalizingAut j n
  have hσ : a ≫ CommGroupScheme.groupHom σ.hom = 𝟙 T.toGrp := by
    change CommGroupScheme.groupHom (σ.inv ≫ σ.hom) = 𝟙 T.toGrp
    rw [Iso.inv_hom_id]
    rfl
  refine ⟨t, f₁, f₂, hj.comp_iso (G.innerIso (b₁ ≫ i.hom.hom)), ?_, ?_⟩
  · change (f ≫ (B.innerIso b₁).hom) ≫ i =
      j ≫ (G.innerIso (b₁ ≫ i.hom.hom)).hom
    rw [Category.assoc, innerIso_hom_comp, ← Category.assoc, hf]
  · have hcancel :
        (b₁ ≫ i.hom.hom) * (n : Over.mk (𝟙 _) ⟶ G.X) *
            (b₂ ≫ i.hom.hom) * (b₂⁻¹ ≫ i.hom.hom) =
          (b₁ ≫ i.hom.hom) * (n : Over.mk (𝟙 _) ⟶ G.X) := by
      rw [GrpObj.inv_comp]
      group
    change (a ≫ f ≫ (B.innerIso b₂⁻¹).hom ≫ φ.hom) ≫ i' =
      j ≫ (G.innerIso (b₁ ≫ i.hom.hom)).hom
    calc
      _ = a ≫ f ≫ (B.innerIso b₂⁻¹).hom ≫ i ≫ (G.innerIso g).hom := by
        rw [Category.assoc, Category.assoc, Category.assoc, ← hconj]
      _ = (a ≫ j) ≫ (G.innerIso (b₂⁻¹ ≫ i.hom.hom)).hom ≫
          (G.innerIso g).hom := by
        simp only [Category.assoc]
        rw [← Category.assoc (B.innerIso b₂⁻¹).hom i,
          innerIso_hom_comp i b₂⁻¹]
        simp only [Category.assoc]
        rw [← Category.assoc f i, hf]
      _ = a ≫ j ≫ (G.innerIso (g * (b₂⁻¹ ≫ i.hom.hom))).hom := by
        rw [innerIso_mul_hom]
        simp only [Category.assoc]
      _ = a ≫ j ≫ (G.innerIso ((b₁ ≫ i.hom.hom) *
          (n : Over.mk (𝟙 _) ⟶ G.X))).hom := by rw [hg, hcancel]
      _ = (a ≫ CommGroupScheme.groupHom σ.hom) ≫ j ≫
          (G.innerIso (b₁ ≫ i.hom.hom)).hom := by
        rw [innerIso_mul_hom, ← Category.assoc j, hn]
        simp only [Category.assoc]
      _ = j ≫ (G.innerIso (b₁ ≫ i.hom.hom)).hom := by
        rw [hσ, Category.id_comp]

end Langlands.GroupScheme
