import Langlands.GroupScheme.Absolute.CentralizerClosureRigidity
import Langlands.GroupScheme.HomConjugacy

/-! # Conjugacy and rational points of the centralizer product -/

noncomputable section

set_option maxHeartbeats 1200000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace ConjugationInto

variable {S : Scheme.{u}} {H B G : GroupScheme S}
variable (s : H ⟶ G) (b : B ⟶ G) [Mono b.hom.hom]
variable (r : Over.mk (𝟙 S) ⟶ G.X) (hr : Holds s b r)

include hr

omit [Mono b.hom.hom] in
/-- The all-test conjugation condition contains the range of the actual conjugated map. -/
theorem inverseConjugate_range :
    SubgroupFunctor.range (s ≫ (G.innerIso r⁻¹).hom) ≤ SubgroupFunctor.range b := by
  intro V y hy
  obtain ⟨t, ht⟩ := SubgroupFunctor.mem_range.mp hy
  rw [← ht]
  change t ≫ (s ≫ (G.innerIso r⁻¹).hom).hom.hom ∈
    (SubgroupFunctor.range b).carrier V
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  simpa only [constantPoint, GrpObj.comp_inv, inv_inv] using
    hr V (Over.homMk V.hom (by simp)) t

/-- Inverse conjugation by a base point factors as an actual homomorphism into `B`. -/
def inverseConjugateHom : H ⟶ B := by
  let hb : (SubgroupFunctor.range b).IsRepresentedBy b := ⟨inferInstance, rfl⟩
  exact hb.factorHom (s ≫ (G.innerIso r⁻¹).hom) (inverseConjugate_range s b r hr)

/-- The lifted homomorphism has the prescribed ambient composite. -/
theorem inverseConjugateHom_comp :
    inverseConjugateHom s b r hr ≫ b = s ≫ (G.innerIso r⁻¹).hom :=
  SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _

/-- On every test scheme, the lifted homomorphism is the unique conjugate point. -/
theorem comp_inverseConjugateHom (V : Over S) (t : V ⟶ H.X) :
    t ≫ (inverseConjugateHom s b r hr).hom.hom =
      conjugatePoint s b r hr V (Over.homMk V.hom (by simp)) t := by
  apply (cancel_mono b.hom.hom).mp
  rw [Category.assoc, ← Grp.comp_hom_hom, inverseConjugateHom_comp,
    Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom, conjugatePoint_comp]
  simp only [constantPoint, GrpObj.comp_inv, inv_inv]

end ConjugationInto

namespace CentralizerProduct

section Base

variable {S : Scheme.{u}} {M B G : GroupScheme S}

/-- Conjugacy of the inverse-conjugated cocharacter to its restriction supplies an actual
base point of `M × B` mapping to the given ambient point. -/
theorem point_factors_of_homConjugate
    (χ : (Gm S).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j)
    (b : B ⟶ G) [Mono b.hom.hom]
    (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    (r : Over.mk (𝟙 S) ⟶ G.X) (hr : ConjugationInto.Holds χ b r)
    (hc : HomConjugate (ConjugationInto.inverseConjugateHom χ b r hr)
      (Dynamic.restrictCocharacter b χ hχ)) :
    ∃ p : Over.mk (𝟙 S) ⟶ M.X ⊗ B.X, p ≫ productHom j b = r := by
  obtain ⟨x, hx⟩ := (homConjugate_iff_points _ _).mp hc
  let v : Over.mk (𝟙 S) ⟶ G.X := x ≫ b.hom.hom
  have hm : r * v⁻¹ ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 S)) := by
    rw [← torusCentralizer_gm_eq_dynamicCentralizer]
    intro V a t
    have ha : a = Over.homMk V.hom (by simp) := by
      apply Over.OverMorphism.ext
      simpa using a.w
    subst a
    have he := congrArg (fun z : V ⟶ B.X => z ≫ b.hom.hom) (hx V t)
    simp only [MonObj.mul_comp, GrpObj.inv_comp] at he
    rw [ConjugationInto.comp_inverseConjugateHom, ConjugationInto.conjugatePoint_comp] at he
    have hχt : (t ≫ (Dynamic.restrictCocharacter b χ hχ).hom.hom) ≫ b.hom.hom =
        t ≫ χ.hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, Dynamic.restrictCocharacter_comp]
    rw [hχt] at he
    simp only [constantPoint, Category.assoc] at he
    change (Over.homMk V.hom (by simp) ≫ v) *
      ((Over.homMk V.hom (by simp) ≫ r)⁻¹ * (t ≫ χ.hom.hom) *
        (Over.homMk V.hom (by simp) ≫ r)) *
        (Over.homMk V.hom (by simp) ≫ v)⁻¹ = t ≫ χ.hom.hom at he
    apply (commute_iff_eq _ _).mpr
    rw [MonObj.comp_mul, GrpObj.comp_inv]
    calc
      _ = ((Over.homMk V.hom (by simp) ≫ r) *
          (Over.homMk V.hom (by simp) ≫ v)⁻¹) *
          ((Over.homMk V.hom (by simp) ≫ v) *
            ((Over.homMk V.hom (by simp) ≫ r)⁻¹ * (t ≫ χ.hom.hom) *
              (Over.homMk V.hom (by simp) ≫ r)) *
                (Over.homMk V.hom (by simp) ≫ v)⁻¹) :=
        congrArg (fun z => ((Over.homMk V.hom (by simp) ≫ r) *
          (Over.homMk V.hom (by simp) ≫ v)⁻¹) * z) he.symm
      _ = _ := by group
  rw [← hrep.2] at hm
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.mp hm
  refine ⟨lift m x, ?_⟩
  rw [lift_productHom, hm]
  change (r * v⁻¹) * v = r
  group

end Base

section Field

variable {k : Type u} [Field k]
variable {M B G D : GroupScheme (Spec (CommRingCat.of k))}

/-- Rigidity identifies the projection of the inverse-conjugated cocharacter at every
base point of the reduced product closure. -/
theorem inverseConjugateHom_comp_projection
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G) [Mono b.hom.hom]
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    (q : B ⟶ D) (hD : IsSplitTorus D)
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ imageClosure j b) :
    ConjugationInto.inverseConjugateHom χ b (a ≫ closureInclusion j b)
      ((closure_holds χ j hrep b hb hχ).comp a) ≫ q =
        Dynamic.restrictCocharacter b χ hχ ≫ q := by
  apply hom_ext_points
  intro V t
  rw [Grp.comp_hom_hom, ← Category.assoc, ConjugationInto.comp_inverseConjugateHom]
  have he : ConjugationInto.conjugatePoint χ b (a ≫ closureInclusion j b)
      ((closure_holds χ j hrep b hb hχ).comp a) V (Over.homMk V.hom (by simp)) t =
      ConjugationInto.conjugatePoint χ b (closureInclusion j b)
        (closure_holds χ j hrep b hb hχ) V ((Over.homMk V.hom (by simp)) ≫ a) t := by
    apply (cancel_mono b.hom.hom).mp
    simp only [ConjugationInto.conjugatePoint_comp, Category.assoc]
  rw [he]
  exact projected_conjugation_eq χ j hrep b hb hχ q hD V _ t

/-- Same-projection conjugacy, when supplied, puts every rational closure point in the
actual multiplication image. -/
theorem closure_point_factors_of_same_projection
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) (j : M ⟶ G)
    (hrep : (Dynamic.centralizer χ).IsRepresentedBy j) (b : B ⟶ G) [Mono b.hom.hom]
    (hb : IsClosedSubgroup b) (hχ : SubgroupFunctor.range χ ≤ SubgroupFunctor.range b)
    [Smooth M.X.hom] [IsAffineHom M.X.hom] [ConnectedSpace M.X.left]
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    (q : B ⟶ D) (hD : IsSplitTorus D)
    (hc : ∀ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ B,
      ψ ≫ q = Dynamic.restrictCocharacter b χ hχ ≫ q →
        HomConjugate ψ (Dynamic.restrictCocharacter b χ hχ))
    (a : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ imageClosure j b) :
    ∃ p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ M.X ⊗ B.X,
      p ≫ productHom j b = a ≫ closureInclusion j b := by
  apply point_factors_of_homConjugate χ j hrep b hχ _
    ((closure_holds χ j hrep b hb hχ).comp a)
  exact hc _ (inverseConjugateHom_comp_projection χ j hrep b hb hχ q hD a)

end Field

end CentralizerProduct

end Langlands.GroupScheme
