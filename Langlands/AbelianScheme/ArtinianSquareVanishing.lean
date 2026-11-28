import Langlands.AbelianScheme.ArtinianSquareObstruction
import Langlands.AbelianScheme.PrimitiveCechVanishingTensor

/-! # The obstruction of the charts of an abelian scheme is a Čech coboundary -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.GroupSchemeShear
open Langlands.AlgebraicGeometry.Deformation
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections
open Langlands.AlgebraicGeometry.Deformation.ElementaryMorphismLifts
open Langlands.AlgebraicGeometry.Deformation.TransitionObstruction
open Langlands.AlgebraicGeometry.Modules.CechResolution.AllSeq
open Langlands.Cohomology
open Langlands.AlgebraicGeometry.SquareZeroAffinePairs (specMap)

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] (S : Setting R' R)
  (B : AbelianScheme (Spec (CommRingCat.of R)))

/-- The constant abelian scheme over the quotient of `R'` by its maximal ideal. -/
abbrev Cres : AbelianScheme (Spec (CommRingCat.of (R' ⧸ maximalIdeal R'))) :=
  (AbelianScheme.baseChange (specMap (Ideal.Quotient.mk (maximalIdeal R')))).obj (S.C B)

/-- The reduction of the constant abelian scheme modulo the maximal ideal. -/
abbrev Fres : Reduction (S.C B).X (maximalIdeal R') :=
  Reduction.pullback (S.C B).X (maximalIdeal R')

/-- The reduction of the square of the constant abelian scheme modulo the maximal ideal. -/
abbrev F₂res : Reduction ((S.C B).X ⊗ (S.C B).X) (maximalIdeal R') :=
  (S.Fres B).fibreProduct (S.Fres B)

theorem appLE_hom_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) {U : Y.Opens}
    {V : X.Opens} (h : V ≤ f ⁻¹ᵁ U) (h' : V ≤ g ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (f.appLE U V h).hom x = (g.appLE U V h').hom x := by
  subst hfg
  rfl

theorem appLE_hom_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {U : Z.Opens} {V : Y.Opens}
    {W : X.Opens} (e₁ : V ≤ g ⁻¹ᵁ U) (e₂ : W ≤ f ⁻¹ᵁ V) (x : Γ(Z, U)) :
    (f.appLE V W e₂).hom ((g.appLE U V e₁).hom x) =
      ((f ≫ g).appLE U W (e₂.trans ((TopologicalSpace.Opens.map f.base).map (homOfLE e₁)).le)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- The reduction of the multiplication of the constant abelian scheme is the multiplication of
its reduction. -/
theorem map_mul_reduction :
    (S.F₂res B).map (S.Fres B) (fst (S.C B).X (S.C B).X * snd (S.C B).X (S.C B).X) =
      fst (S.Cres B).X (S.Cres B).X * snd (S.Cres B).X (S.Cres B).X := by
  let b := specMap (Ideal.Quotient.mk (maximalIdeal R'))
  let T := (S.Cres B).X ⊗ (S.Cres B).X
  let E := Langlands.GroupScheme.baseChangePointsEquiv b (S.C B).toGrp T
  let t : (Over.map b).obj T ⟶ (S.C B).X ⊗ (S.C B).X := Over.homMk (S.F₂res B).toOriginal
    (S.F₂res B).cartesian.w
  have hE (g : (S.C B).X ⊗ (S.C B).X ⟶ (S.C B).X) : E ((S.F₂res B).map (S.Fres B) g) = t ≫ g := by
    apply Over.OverMorphism.ext
    rw [Langlands.GroupScheme.baseChangePointsEquiv_left, Over.comp_left]
    exact Reduction.map_left_toOriginal (A := S.F₂res B) (B := S.Fres B) g
  apply E.injective
  rw [map_mul, hE, MonObj.comp_mul, ← hE, ← hE, Reduction.map_fst, Reduction.map_snd]
  rfl

namespace Charts

variable {S B} (K : S.Charts B)

theorem iSup_V : ⨆ i, K.chartFamily.V i = ⊤ := by
  change ⨆ i, pullback.fst (S.A₀ B).X.hom S.sσ ⁻¹ᵁ (S.jB B ⁻¹ᵁ K.U i) = ⊤
  rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, K.cover, Scheme.Hom.preimage_top,
    Scheme.Hom.preimage_top]

variable [IsArtinianRing R'] [IsArtinianRing R] [IsLocalRing R] (D : K.chartFamily.Lifts)

theorem iSup_cover : ⨆ l, D.family.cover (S.Fres B) l = ⊤ := by
  change ⨆ l, (S.Fres B).toOriginal ⁻¹ᵁ K.chartFamily.V l = ⊤
  rw [← Scheme.Hom.preimage_iSup, K.iSup_V, Scheme.Hom.preimage_top]

theorem iSup_cover_inl : ⨆ a, (K.squareLifts D).family.cover (S.F₂res B) (.inl a) = ⊤ := by
  change ⨆ a : K.J × K.J, (S.F₂res B).toOriginal ⁻¹ᵁ Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.prodOpen
    (pullback.fst (S.C B).X.hom (S.C B).X.hom) (pullback.snd (S.C B).X.hom (S.C B).X.hom)
    (K.chartFamily.V a.1) (K.chartFamily.V a.2) = ⊤
  rw [← Scheme.Hom.preimage_iSup, eq_top_iff.mpr (Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.iSup_prodOpen_eq_top
    (K.iSup_V).ge (K.iSup_V).ge), Scheme.Hom.preimage_top]

theorem iSup_cover_inr : ⨆ a, (K.squareLifts D).family.cover (S.F₂res B) (.inr a) = ⊤ := by
  change ⨆ a : K.J × K.J, (S.F₂res B).toOriginal ⁻¹ᵁ ((shear (S.C B).X).hom.left ⁻¹ᵁ
    Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.prodOpen
    (pullback.fst (S.C B).X.hom (S.C B).X.hom) (pullback.snd (S.C B).X.hom (S.C B).X.hom)
    (K.chartFamily.V a.1) (K.chartFamily.V a.2)) = ⊤
  rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup,
    eq_top_iff.mpr (Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity.iSup_prodOpen_eq_top
    (K.iSup_V).ge (K.iSup_V).ge), Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]

theorem iSup_cover_square : ⨆ l, (K.squareLifts D).family.cover (S.F₂res B) l = ⊤ :=
  eq_top_iff.mpr ((K.iSup_cover_inl D).ge.trans
    (iSup_le fun a ↦ le_iSup ((K.squareLifts D).family.cover (S.F₂res B)) (.inl a)))

theorem cover_inl_le_fst (a : K.J × K.J) :
    (K.squareLifts D).family.cover (S.F₂res B) (.inl a) ≤
      (fst (S.Cres B).X (S.Cres B).X).left ⁻¹ᵁ D.family.cover (S.Fres B) a.1 := by
  intro x hx
  change (S.Fres B).toOriginal ((fst (S.Fres B).obj (S.Fres B).obj).left x) ∈ K.chartFamily.V a.1
  rw [← Scheme.Hom.comp_apply, ← Reduction.fibreProduct_toOriginal_fst, Scheme.Hom.comp_apply]
  exact hx.1

theorem cover_inr_le_snd (a : K.J × K.J) :
    (K.squareLifts D).family.cover (S.F₂res B) (.inr a) ≤
      (snd (S.Cres B).X (S.Cres B).X).left ⁻¹ᵁ D.family.cover (S.Fres B) a.2 := by
  intro x hx
  change (S.Fres B).toOriginal ((snd (S.Fres B).obj (S.Fres B).obj).left x) ∈ K.chartFamily.V a.2
  rw [← Scheme.Hom.comp_apply, ← Reduction.fibreProduct_toOriginal_snd, Scheme.Hom.comp_apply,
    ← shear_hom_snd, Over.comp_left, Scheme.Hom.comp_apply]
  exact hx.2

theorem cover_inr_le_mul (a : K.J × K.J) :
    (K.squareLifts D).family.cover (S.F₂res B) (.inr a) ≤
      (fst (S.Cres B).X (S.Cres B).X * snd (S.Cres B).X (S.Cres B).X).left ⁻¹ᵁ
        D.family.cover (S.Fres B) a.1 := by
  intro x hx
  rw [← map_mul_reduction]
  change (S.Fres B).toOriginal (((S.F₂res B).map (S.Fres B) _).left x) ∈ K.chartFamily.V a.1
  rw [← Scheme.Hom.comp_apply, Reduction.map_left_toOriginal, Scheme.Hom.comp_apply,
    ← shear_hom_fst, Over.comp_left, Scheme.Hom.comp_apply]
  exact hx.1

variable [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)]
  (b : (S.target B).Coordinates (RingHom.ker S.φ))

/-- The obstruction cocycle of lifts of the transitions of the charts. -/
abbrev obsB (j : Fin b.cotangentRank × Fin b.idealRank) :=
  D.family.cocycle b (S.Fres B) D.agrees (𝟙 _) j

/-- The obstruction cocycle of the induced lifts on the charts of the square, through the first
projection. -/
abbrev obsSq (j : Fin b.cotangentRank × Fin b.idealRank) :=
  (K.squareLifts D).family.cocycle b (S.F₂res B) (K.squareLifts D).agrees
    (fst (S.C B).X (S.C B).X) j

/-- On the product charts, the obstruction of the square is the pullback of the obstruction
along the first projection. -/
theorem refine_obsSq_inl (j : Fin b.cotangentRank × Fin b.idealRank) :
    (refineCochain (S.F₂res B).obj.hom ((K.squareLifts D).family.cover (S.F₂res B))
        (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inl a)) Sum.inl (fun _ ↦ le_rfl)
        (unitModule _)).f 2
        (K.obsSq D b j : cochain (S.F₂res B).obj.hom ((K.squareLifts D).family.cover (S.F₂res B))
          (unitModule (S.F₂res B).obj.left) 2) =
      (unitCochainMap (fst (S.Cres B).X (S.Cres B).X) (D.family.cover (S.Fres B))
        (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inl a)) Prod.fst
        (K.cover_inl_le_fst D)).f 2
        (K.obsB D b j : cochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
          (unitModule (S.Fres B).obj.left) 2) := by
  refine (refineCochain_unit_eq _ _ _ _ _ 2 _).trans (Eq.trans ?_
    (unitCochainMap_eq_pull (fst (S.Cres B).X (S.Cres B).X) _ _ _ (K.cover_inl_le_fst D) 2 _).symm)
  funext σ
  rw [Cech.refine_apply, Cech.pull_apply, Family.cocycle_apply, Family.cocycle_apply]
  simp only [Function.comp_apply, map_eq_res]
  rw [Cech.res_res, K.obstruction_inl, Cech.res_appLE]
  exact (appLE_hom_congr (congrArg Over.Hom.left (Reduction.map_fst _ _)) _ _ _).trans
    (Cech.appLE_res _ _ _ _).symm

/-- On the sheared product charts, the obstruction of the square is the difference of the
pullbacks of the obstruction along the multiplication and along the second projection. -/
theorem refine_obsSq_inr (j : Fin b.cotangentRank × Fin b.idealRank) :
    (refineCochain (S.F₂res B).obj.hom ((K.squareLifts D).family.cover (S.F₂res B))
        (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inr a)) Sum.inr (fun _ ↦ le_rfl)
        (unitModule _)).f 2
        (K.obsSq D b j : cochain (S.F₂res B).obj.hom ((K.squareLifts D).family.cover (S.F₂res B))
          (unitModule (S.F₂res B).obj.left) 2) =
      (unitCochainMap (fst (S.Cres B).X (S.Cres B).X * snd (S.Cres B).X (S.Cres B).X)
        (D.family.cover (S.Fres B))
        (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inr a)) Prod.fst
        (K.cover_inr_le_mul D)).f 2
        (K.obsB D b j : cochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
          (unitModule (S.Fres B).obj.left) 2) -
      (unitCochainMap (snd (S.Cres B).X (S.Cres B).X) (D.family.cover (S.Fres B))
        (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inr a)) Prod.snd
        (K.cover_inr_le_snd D)).f 2
        (K.obsB D b j : cochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
          (unitModule (S.Fres B).obj.left) 2) := by
  have hm := unitCochainMap_eq_pull (fst (S.Cres B).X (S.Cres B).X * snd (S.Cres B).X (S.Cres B).X)
    _ _ _ (K.cover_inr_le_mul D) 2
    (K.obsB D b j : cochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
      (unitModule (S.Fres B).obj.left) 2)
  have hs := unitCochainMap_eq_pull (snd (S.Cres B).X (S.Cres B).X) _ _ _ (K.cover_inr_le_snd D) 2
    (K.obsB D b j : cochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
      (unitModule (S.Fres B).obj.left) 2)
  refine (refineCochain_unit_eq _ _ _ _ _ 2 _).trans ?_
  funext σ
  have hm' := congrFun hm σ
  have hs' := congrFun hs σ
  rw [Pi.sub_apply, hm', hs', Cech.refine_apply, Cech.pull_apply, Cech.pull_apply,
    Family.cocycle_apply, Family.cocycle_apply]
  simp only [Function.comp_apply, map_eq_res]
  rw [Cech.res_res, K.obstruction_inr, K.prodObstruction_fst, K.prodObstruction_snd, map_sub,
    map_sub, appLE_hom_comp, appLE_hom_comp, Cech.res_appLE, Cech.res_appLE]
  congr 1
  · refine (appLE_hom_congr ?_ _ _ _).trans (Cech.appLE_res _ _ _ _).symm
    rw [← Over.comp_left, ← Reduction.map_comp, shear_hom_fst, map_mul_reduction]
  · refine (appLE_hom_congr ?_ _ _ _).trans (Cech.appLE_res _ _ _ _).symm
    rw [← Over.comp_left, ← Reduction.map_comp, shear_hom_snd, Reduction.map_snd]
    rfl

omit [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)] in
theorem exists_coboundary [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)]
    (b : (S.target B).Coordinates (RingHom.ker S.φ)) (j : Fin b.cotangentRank × Fin b.idealRank) :
    ∃ y, dCochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
      (unitModule (S.Fres B).obj.left) 1 y =
        (K.obsB D b j : cochain (S.Fres B).obj.hom (D.family.cover (S.Fres B))
          (unitModule (S.Fres B).obj.left) 2) := by
  let : Field (R' ⧸ maximalIdeal R') := Ideal.Quotient.field _
  exact PrimitiveCechVanishing.exists_coboundary_tensor (S.Cres B) (D.family.cover (S.Fres B))
    (K.iSup_cover D) (fun l ↦ (S.Fres B).affine_preimage (D.family.affine l))
    ((K.squareLifts D).family.cover (S.F₂res B)) (K.iSup_cover_square D)
    (fun l ↦ (S.F₂res B).affine_preimage ((K.squareLifts D).family.affine l))
    (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inl a)) (K.iSup_cover_inl D)
    (fun a ↦ (S.F₂res B).affine_preimage ((K.squareLifts D).family.affine (.inl a)))
    (fun a ↦ (K.squareLifts D).family.cover (S.F₂res B) (.inr a)) (K.iSup_cover_inr D)
    (fun a ↦ (S.F₂res B).affine_preimage ((K.squareLifts D).family.affine (.inr a)))
    Sum.inl (fun _ ↦ le_rfl) Sum.inr (fun _ ↦ le_rfl) Prod.fst (K.cover_inl_le_fst D)
    Prod.fst (K.cover_inr_le_mul D) Prod.snd (K.cover_inr_le_snd D) (K.obsB D b j)
    (K.obsSq D b j) (K.refine_obsSq_inl D b j) (K.refine_obsSq_inr D b j)

omit [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)] in
/-- The transition maps of the charts of an abelian scheme over an elementary local Artinian
extension lift to the constant scheme over the thicker ring with the cocycle condition. -/
theorem nonempty_liftedTransitions_of_elementary
    [Fact (maximalIdeal R' * RingHom.ker S.φ = ⊥)] : Nonempty K.LiftedTransitions := by
  obtain ⟨D, hself⟩ := K.chartFamily.exists_lifts
  have : Smooth (S.target B).G.X.hom := by
    change Smooth (pullback.snd (S.C B).X.hom (specMap (residue R')))
    infer_instance
  let b : (S.target B).Coordinates (RingHom.ker S.φ) :=
    Target.Coordinates.ofTarget (S.target B) (RingHom.ker S.φ) (S.ker_le_maximalIdeal)
  choose y hy using K.exists_coboundary D b
  exact K.nonempty_liftedTransitions b (S.Fres B) D hself y hy

end Charts

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
