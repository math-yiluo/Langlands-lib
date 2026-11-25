/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleDescentDataExistence
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover

/-!
# Essential surjectivity of finite etale descent

Source: Stacks Project, Descent, Tags 0245, 02LA, 02VN; Topologies, Tag 022C
(blueprint: lem-galois-descent-essentially-surjective).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem compatible_hom {Y Y' : Scheme.{v}} {g : Y' ⟶ Y}
    (A B : Over.DescentDataCategory g) (P : Over Y)
    (qA : A.V.left ⟶ P.left) (qB : B.V.left ⟶ P.left)
    (hpB : IsPullback qB B.V.hom P.hom g)
    (htA : ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ g = f₂ ≫ g)
      (z : Over.mk f₁ ⟶ A.V), (A.datum.transport f₁ f₂ h z).left ≫ qA = z.left ≫ qA)
    (htB : ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ g = f₂ ≫ g)
      (z : Over.mk f₁ ⟶ B.V), (B.datum.transport f₁ f₂ h z).left ≫ qB = z.left ≫ qB)
    (k : A.V ⟶ B.V) (hk : k.left ≫ qB = qA) :
    ∀ {T : Scheme.{v}} (f₁ f₂ : T ⟶ Y') (h : f₁ ≫ g = f₂ ≫ g)
      (z : Over.mk f₁ ⟶ A.V),
      B.datum.transport f₁ f₂ h (z ≫ k) = A.datum.transport f₁ f₂ h z ≫ k := by
  intro T f₁ f₂ h z
  apply Over.OverMorphism.ext
  apply hpB.hom_ext
  · simp only [Over.comp_left, Category.assoc, hk]
    simpa only [Over.comp_left, Category.assoc, hk] using
      (htB _ _ h (z ≫ k)).trans (by
        simpa only [Over.comp_left, Category.assoc, hk] using (htA _ _ h z).symm)
  · exact (Over.w (B.datum.transport f₁ f₂ h (z ≫ k))).trans
      (Over.w (A.datum.transport f₁ f₂ h z ≫ k)).symm

/-- Canonical base change is essentially surjective along an etale surjection.
Source: Stacks Project, Descent, Tags 0245, 02LA, 02VN; Steps 4--5 of
`lem-galois-descent` (blueprint: lem-galois-descent-essentially-surjective).

Proof: an etale surjection is an fppf, hence fpqc, singleton covering.
A finite scheme over the cover is affine. Effective affine descent gives
an object over the base and an invariant pullback projection. Its standard
pullback is isomorphic to the original finite etale object, so finiteness
and etaleness descend. The two pullback squares identify this object with
the image of the descended finite etale scheme. Invariance of both first
projections proves that this isomorphism and its inverse respect transport. -/
theorem finiteEtaleDescent_essSurj {Y Y' : Scheme.{v}} (g : Y' ⟶ Y)
    [Surjective g] [Etale g]
    (F : Y.FiniteEtale ⥤ AlgebraicGeometry.FiniteEtaleDescentData g)
    (q : ∀ P : Y.FiniteEtale, (F.obj P).obj.V.left ⟶ P.obj.left)
    (h : FiniteEtaleDescentCompatible F q) : F.EssSurj := by
  have hg : Presieve.singleton g ∈ Scheme.fpqcPrecoverage Y :=
    Scheme.fppfPrecoverage_le_fpqcPrecoverage _ g.singleton_mem_fppfPrecoverage
  have hg' : Presieve.ofArrows (fun _ : PUnit.{1} ↦ Y') (fun _ ↦ g) ∈
      Scheme.fpqcPrecoverage Y := by
    simpa only [Presieve.ofArrows_pUnit] using hg
  constructor
  intro A
  have : IsFinite A.obj.V.hom := A.property.1
  have : Etale A.obj.V.hom := A.property.2
  obtain ⟨P, r, hp, ht⟩ := A.obj.datum.isEffective_of_isAffineHom_fpqc g hg
  have hfinite : IsFinite (pullback.snd P.hom g) := by
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  have hetale : Etale (pullback.snd P.hom g) := by
    rw [← hp.isoPullback_inv_snd]
    infer_instance
  have : IsFinite P.hom :=
    isFinite_of_fpqc_cover P.hom (fun _ : PUnit.{1} ↦ Y') (fun _ ↦ g) hg'
      (fun _ ↦ hfinite)
  have : Etale P.hom :=
    etale_of_fpqc_cover P.hom (fun _ : PUnit.{1} ↦ Y') (fun _ ↦ g) hg' (fun _ ↦ hetale)
  let P₀ : Y.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ P.hom inferInstance, (show IsFinite P.hom from inferInstance)⟩
  obtain ⟨_, hp₀, ht₀⟩ := h.1 P₀
  let e := hp₀.isoIsPullback _ _ hp
  let eh : (F.obj P₀).obj.V ⟶ A.obj.V := Over.homMk e.hom (by simp [e])
  let ei : A.obj.V ⟶ (F.obj P₀).obj.V := Over.homMk e.inv (by simp [e])
  let dh : (F.obj P₀).obj ⟶ A.obj :=
    ⟨eh, compatible_hom _ _ P (q P₀) r hp ht₀ ht eh (by exact hp₀.isoIsPullback_hom_fst _ _ hp)⟩
  let di : A.obj ⟶ (F.obj P₀).obj :=
    ⟨ei, compatible_hom _ _ P r (q P₀) hp₀ ht ht₀ ei (by exact hp₀.isoIsPullback_inv_fst _ _ hp)⟩
  refine ⟨P₀, ⟨ObjectProperty.isoMk _ ?_⟩⟩
  refine ⟨dh, di, ?_, ?_⟩
  · apply Over.DescentDataCategory.Hom.ext
    apply Over.OverMorphism.ext
    change e.hom ≫ e.inv = 𝟙 _
    exact e.hom_inv_id
  · apply Over.DescentDataCategory.Hom.ext
    apply Over.OverMorphism.ext
    change e.inv ≫ e.hom = 𝟙 _
    exact e.inv_hom_id

end AlgebraicGeometry
