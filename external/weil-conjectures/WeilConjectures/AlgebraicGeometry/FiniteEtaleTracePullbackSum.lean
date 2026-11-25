/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalSums
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Local sum characterization of finite étale traces

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-pullback-sum)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

private theorem cofan_cover {Z : Scheme.{u}} {J : Type u} (V : J → Scheme.{u})
    (i : ∀ j, V j ⟶ Z) (hc : IsColimit (Cofan.mk Z i)) (z : Z) :
    ∃ j, ∃ v : V j, (i j).base v = z := by
  have : IsIso (Sigma.desc i) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Z i)).mp ⟨hc⟩
  obtain ⟨y, rfl⟩ := (Sigma.desc i).surjective z
  obtain ⟨⟨j, v⟩, rfl⟩ := (sigmaMk V).surjective y
  refine ⟨j, v, ?_⟩
  simp [sigmaMk_mk, ← Scheme.Hom.comp_apply]

private theorem cofan_index_eq {Z : Scheme.{u}} {J : Type u} (V : J → Scheme.{u})
    (i : ∀ j, V j ⟶ Z) (hc : IsColimit (Cofan.mk Z i))
    {j k : J} (v : V j) (w : V k) (h : (i j).base v = (i k).base w) : j = k := by
  have : IsIso (Sigma.desc i) :=
    (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk Z i)).mp ⟨hc⟩
  have he : (Sigma.ι V j).base v = (Sigma.ι V k).base w := by
    apply (Sigma.desc i).injective
    simpa [← Scheme.Hom.comp_apply] using h
  exact congrArg Sigma.fst ((sigmaι_eq_iff V j k v w).mp he)

/-- A trace characterized by local sums satisfies the split formula for a splitting
of the original finite cover, by pulling that splitting back to each site object.
Source: Stacks Project, Section 03SH, after Definition 03SE, split case.
(blueprint: lem-weil-pbc-finite-etale-trace-pullback-sum)

Proof. Fix `W`. Pull every piece `V_j → Y` back along `W ×_X Y → Y`. Its new inclusion
is open and closed by base change. The pullback pieces cover and are disjoint, since
preimages preserve unions and intersections. The resulting cofan is a coproduct:
open immersions with disjoint images covering a scheme exhibit it as their coproduct.
The map of each new piece to `W` is the base change of the isomorphism `V_j → X`;
its inverse has projections `id_W` and `W → X → V_j`. Hence its section into
`W ×_X Y` is precisely `pullback.lift id_W (W.hom ≫ t j ≫ i j)`.
Apply the local sum characterization to this splitting. Its sum is the displayed
sum, since the universal property identifies the two descriptions of the sections.
The same argument includes an empty family: then the pullback is empty and the sum
in the characterization is zero. -/
theorem finiteEtaleTrace_sum_of_localSums {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : Etale f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (τ : (lowerStar AddCommGrpCat.{u + 1} f).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj F) ⟶ F)
    (hτ : FiniteEtaleTraceLocalSums f hf F τ) :
    let A := AddCommGrpCat.{u + 1}
    let B := fun (W : X.Etale) ↦ (MorphismProperty.Over.map ⊤ hf).obj
      ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W)
    ∀ (J : Type u) [Fintype J] (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ Y)
      (t : ∀ j, X ⟶ V j) (_ : IsColimit (Cofan.mk Y i))
      (hinv₁ : ∀ j, t j ≫ i j ≫ f = 𝟙 X)
      (_ : ∀ j, i j ≫ f ≫ t j = 𝟙 (V j))
      (_ : ∀ j, IsOpenImmersion (i j)) (_ : ∀ j, IsClosedImmersion (i j))
      (W : X.Etale),
      (((upperStarIsoLocalizationRestriction A f hf).app F).inv.hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj W))) ≫
          τ.hom.app (op W) = ∑ j, F.obj.map (MorphismProperty.Over.homMk
            (A := W) (B := B W)
            (pullback.lift (𝟙 W.left) (W.hom ≫ t j ≫ i j)
              (by simp [Category.assoc, hinv₁]))
            (by simp [B, Category.assoc, hinv₁] )).op := by
  classical
  dsimp only
  intro J hJ V i t hc hinv₁ hinv₂ hopen hclosed W
  let (j : J) : IsOpenImmersion (i j) := hopen j
  let (j : J) : IsClosedImmersion (i j) := hclosed j
  let Z := pullback W.hom f
  let D : J → Scheme.{u} := fun j ↦ pullback (i j) (pullback.snd W.hom f)
  let a : ∀ j, D j ⟶ Z := fun j ↦ pullback.snd (i j) (pullback.snd W.hom f)
  let σ : ∀ j, W.left ⟶ Z := fun j ↦
    pullback.lift (𝟙 W.left) (W.hom ≫ t j ≫ i j)
      (by simp [Category.assoc, hinv₁])
  let b : ∀ j, W.left ⟶ D j := fun j ↦
    pullback.lift (W.hom ≫ t j) (σ j) (by simp [σ])
  have hba (j : J) : b j ≫ a j = σ j := by simp [b, a]
  have hσ (j : J) : σ j ≫ pullback.fst W.hom f = 𝟙 W.left := by simp [σ]
  have hproj (j : J) :
      a j ≫ pullback.fst W.hom f ≫ W.hom =
        pullback.fst (i j) (pullback.snd W.hom f) ≫ i j ≫ f := by
    calc
      a j ≫ pullback.fst W.hom f ≫ W.hom =
          a j ≫ pullback.snd W.hom f ≫ f := by rw [pullback.condition]
      _ = pullback.fst (i j) (pullback.snd W.hom f) ≫ i j ≫ f := by
        simpa only [Category.assoc, a] using
          congrArg (fun k ↦ k ≫ f)
            (pullback.condition (f := i j) (g := pullback.snd W.hom f)).symm
  have hleft (j : J) : b j ≫ a j ≫ pullback.fst W.hom f = 𝟙 W.left := by
    rw [← Category.assoc, hba, hσ]
  have hright (j : J) : a j ≫ pullback.fst W.hom f ≫ b j = 𝟙 (D j) := by
    apply pullback.hom_ext
    · simp only [b, Category.assoc, pullback.lift_fst, Category.id_comp]
      simpa only [Category.assoc, hinv₂, Category.comp_id] using
        congrArg (fun k ↦ k ≫ t j) (hproj j)
    · simp only [b, Category.assoc, pullback.lift_snd, Category.id_comp]
      apply pullback.hom_ext
      · simp [σ, a]
      · simp only [σ, Category.assoc, pullback.lift_snd]
        calc
          (a j ≫ pullback.fst W.hom f) ≫ W.hom ≫ t j ≫ i j =
              pullback.fst (i j) (pullback.snd W.hom f) ≫ i j := by
            have hi := congrArg (fun k ↦ k ≫ t j) (hproj j)
            simp only [Category.assoc, hinv₂, Category.comp_id] at hi
            simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ i j) hi
          _ = pullback.snd (i j) (pullback.snd W.hom f) ≫
              pullback.snd W.hom f := pullback.condition
  have ha (j : J) : Set.range (a j).base =
      (pullback.snd W.hom f).base ⁻¹' Set.range (i j).base :=
    Scheme.Pullback.range_snd _ _
  have hcov : ⨆ j, (a j).opensRange = ⊤ := by
    apply top_unique
    intro z hz
    obtain ⟨j, v, hv⟩ := cofan_cover V i hc ((pullback.snd W.hom f).base z)
    have haz : z ∈ (a j).opensRange := by
      change z ∈ Set.range (a j).base
      rw [ha]
      exact ⟨v, hv⟩
    exact (le_iSup (fun j ↦ (a j).opensRange) j) haz
  have hdisj : Pairwise (fun j k ↦ Disjoint (a j).opensRange (a k).opensRange) := by
    intro j k hjk
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro z hz
    rcases hz with ⟨hzj, hzk⟩
    change z ∈ Set.range (a j).base at hzj
    change z ∈ Set.range (a k).base at hzk
    rw [ha] at hzj hzk
    obtain ⟨v, hv⟩ := hzj
    obtain ⟨w, hw⟩ := hzk
    exact (hjk (cofan_index_eq V i hc v w (hv.trans hw.symm))).elim
  have hcol := nonempty_isColimit_cofanMk_of a hcov hdisj
  have hs := hτ W J D a b hcol.some hleft hright
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)
  simpa only [hba] using hs

end AlgebraicGeometry.Etale
