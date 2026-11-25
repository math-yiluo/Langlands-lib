/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import WeilConjectures.CategoryTheory.Comma.Over.DescentDatum
import WeilConjectures.AlgebraicGeometry.GluedEffectiveModelCharts
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing effective descent on invariant open subschemes

Source: Stacks Project, Descent, Lemma 35.35.13, Tag 0AP4.
(blueprint: lem-pd-effective-invariant-open-cover).
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

namespace CategoryTheory.Over.DescentDatum

/-- Effective compatible data on an open covering glue to an effective datum.
Source: Stacks Project, Descent, Lemma 35.35.13, Tag 0AP4.
(blueprint: lem-pd-effective-invariant-open-cover).

Proof: First select one covering open for each point of V if the index universe is
larger than that of V. Choose effective models W_i over Y for the selected data E_i.
Their pullbacks identify
with U_i, compatibly with D by hcompat. The preimages of U_i intersect U_j in each
U_i are invariant under E_i: transport compatibility and the restriction to U_j
show invariance in both directions, the latter using inverse transport. Descend
these opens along the fpqc map U_i -> W_i using descent of compatible opens (03N0).
The identity on U_i intersect U_j then descends by fpqc full faithfulness (02W0)
to an isomorphism of the resulting opens of W_i and W_j. Faithfulness proves the
identity and triple-overlap cocycle laws. Scheme gluing gives W over Y. The local
pullback identifications glue to an isomorphism V = W times_Y X, since hcover says
the U_i cover V. Its projection witnesses IsEffective; transport compatibility is
checked on the inverse-image covering of each test scheme. For an empty cover,
hcover forces V empty; the empty scheme over Y and its empty pullback give the
same construction. No affineness of the U_i or finiteness of p is required. -/
theorem isEffective_of_effective_open_cover
    {X Y : Scheme.{u}} {p : X ⟶ Y}
    (hp : Presieve.singleton p ∈ Scheme.fpqcPrecoverage Y)
    {V : Over X} (D : Over.DescentDatum p V)
    {I : Type v} (U : I → V.left.Opens)
    (hcover : ∀ x : V.left, ∃ i, x ∈ U i)
    (E : ∀ i, Over.DescentDatum p (Over.mk ((U i).ι ≫ V.hom)))
    (hcompat : ∀ (i : I) {T : Scheme.{u}} (f₁ f₂ : T ⟶ X)
      (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ Over.mk ((U i).ι ≫ V.hom)),
      ((E i).transport f₁ f₂ h a).left ≫ (U i).ι =
        (D.transport f₁ f₂ h (Over.homMk (a.left ≫ (U i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w a))).left)
    (heffective : ∀ i, (E i).IsEffective) : D.IsEffective := by
  classical
  -- Point-indexed subcovers keep the geometric gluing in the universe of schemes.
  choose idx hidx using hcover
  let U' : V.left → V.left.Opens := fun x ↦ U (idx x)
  let E' := fun x : V.left ↦ E (idx x)
  have hc : ∀ x : V.left, ∃ y, x ∈ U' y := fun x ↦ ⟨x, hidx x⟩
  choose W q hcart hinv using fun x : V.left ↦ heffective (idx x)
  obtain ⟨W₀, q₀, j, hj, hjcover, hjY, hchart⟩ :=
    exists_glued_effective_model_charts hp D U' hc E'
      (fun x ↦ hcompat (idx x)) W q hcart hinv
  let 𝒲 : W₀.left.OpenCover := {
    I₀ := V.left
    X := fun x ↦ (W x).left
    f := j
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun w ↦ by
        obtain ⟨i, z, hz⟩ := hjcover w
        exact ⟨i, ⟨z, hz⟩⟩, hj⟩ }
  refine ⟨W₀, q₀, ?_, ?_⟩
  · apply Scheme.isPullback_of_openCover q₀ V.hom W₀.hom p 𝒲
    intro i
    apply (hcart i).of_iso (hchart i).flip.isoPullback
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp [𝒲, Scheme.Cover.pullbackHom]
    · change (U' i).ι ≫ V.hom =
        (hchart i).flip.isoPullback.hom ≫ Limits.pullback.fst q₀ (j i) ≫ V.hom
      simp
    · simpa [𝒲] using (hjY i).symm
    · simp
  · intro T f₁ f₂ h a
    apply Scheme.hom_ext_of_forall
    intro x
    obtain ⟨i, hi⟩ := hc (a.left x)
    let A : T.Opens := a.left ⁻¹ᵁ U' i
    let g : A.toScheme ⟶ T := A.ι
    let b : Over.mk (g ≫ f₁) ⟶ Over.mk ((U' i).ι ≫ V.hom) :=
      Over.homMk (a.left ∣_ U' i) (by
        change (a.left ∣_ U' i) ≫ (U' i).ι ≫ V.hom = g ≫ f₁
        rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w a]
        rfl)
    have hb : b.left ≫ (U' i).ι = g ≫ a.left := morphismRestrict_ι a.left (U' i)
    have heq : (Over.homMk g : Over.mk (g ≫ f₁) ⟶ Over.mk f₁) ≫ a =
        Over.homMk (b.left ≫ (U' i).ι)
          (by simpa only [Over.mk_hom, Category.assoc] using Over.w b) := by
      ext
      exact hb.symm
    have ht := D.transport_homMk_comp g f₁ f₂ h a
    rw [heq] at ht
    have ht' := congrArg (fun c ↦ c.left) ht
    simp only [Over.comp_left, Over.homMk_left] at ht'
    have hk := hcompat (idx i) (g ≫ f₁) (g ≫ f₂)
      (by simpa only [Category.assoc] using congrArg (fun k ↦ g ≫ k) h) b
    have hq := (hchart i).w
    refine ⟨A, hi, ?_⟩
    change g ≫ (D.transport f₁ f₂ h a).left ≫ q₀ = g ≫ a.left ≫ q₀
    rw [← Category.assoc, ← ht', ← hk]
    simp only [Category.assoc]
    calc
      ((E' i).transport (g ≫ f₁) (g ≫ f₂) _ b).left ≫ (U' i).ι ≫ q₀ =
          ((E' i).transport (g ≫ f₁) (g ≫ f₂) _ b).left ≫ q i ≫ j i := by rw [← hq]
      _ = b.left ≫ q i ≫ j i := by
        simpa only [Category.assoc] using
          congrArg (fun k ↦ k ≫ j i) (hinv i (g ≫ f₁) (g ≫ f₂) _ b)
      _ = g ≫ a.left ≫ q₀ := by rw [hq, ← Category.assoc, hb, Category.assoc]

end CategoryTheory.Over.DescentDatum
