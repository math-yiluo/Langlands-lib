import Langlands.AbelianScheme.ArtinianChartOperations
import Langlands.AlgebraicGeometry.GroupSchemeShear

/-! # Products of models and of chart families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open MonoidalCategory CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.ArtinianConstantCharts.Setting

open Langlands.AlgebraicGeometry.TwistedOpenGluing
open Langlands.AlgebraicGeometry.ProductOpenCharts
open Langlands.AlgebraicGeometry.GroupSchemeShear
open Langlands.AlgebraicGeometry.Deformation.AffineOpenQuotientSections.Reduction
  (productMap productMap_isPullback)
open Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity (prodOpen isAffineOpen_prodOpen)

variable {R' R : Type u} [CommRing R'] [CommRing R] [IsLocalRing R'] {S : Setting R' R}

namespace Model

variable (M M' : S.Model)

/-- The product of two models, with the products of their base changes and residue fibres. -/
def prod : S.Model where
  Y := M.Y ⊗ M'.Y
  YS := pullback M.pS M'.pS
  q := productMap (Y' := Over.mk M.pS) (Z' := Over.mk M'.pS) M.q M'.q S.t M.isPullback_q.w
    M'.isPullback_q.w
  pS := pullback.fst M.pS M'.pS ≫ M.pS
  isPullback_q := productMap_isPullback (Y' := Over.mk M.pS) (Z' := Over.mk M'.pS)
    M.isPullback_q M'.isPullback_q
  E := pullback M.pE M'.pE
  iE := productMap (Y := Over.mk M.pS) (Z := Over.mk M'.pS) (Y' := Over.mk M.pE)
    (Z' := Over.mk M'.pE) M.iE M'.iE S.c M.isPullback_iE.w M'.isPullback_iE.w
  pE := pullback.fst M.pE M'.pE ≫ M.pE
  isPullback_iE := productMap_isPullback (Y := Over.mk M.pS) (Z := Over.mk M'.pS)
    (Y' := Over.mk M.pE) (Z' := Over.mk M'.pE) M.isPullback_iE M'.isPullback_iE

@[reassoc (attr := simp)]
theorem prod_q_fst :
    (M.prod M').q ≫ pullback.fst M.Y.hom M'.Y.hom = pullback.fst M.pS M'.pS ≫ M.q :=
  productMap_pullback_fst (Y' := Over.mk M.pS) (Z' := Over.mk M'.pS) M.q M'.q S.t
    M.isPullback_q.w M'.isPullback_q.w

@[reassoc (attr := simp)]
theorem prod_q_snd :
    (M.prod M').q ≫ pullback.snd M.Y.hom M'.Y.hom = pullback.snd M.pS M'.pS ≫ M'.q :=
  productMap_pullback_snd (Y' := Over.mk M.pS) (Z' := Over.mk M'.pS) M.q M'.q S.t
    M.isPullback_q.w M'.isPullback_q.w

@[reassoc (attr := simp)]
theorem prod_iE_fst :
    (M.prod M').iE ≫ pullback.fst M.pS M'.pS = pullback.fst M.pE M'.pE ≫ M.iE :=
  productMap_pullback_fst (Y := Over.mk M.pS) (Z := Over.mk M'.pS) (Y' := Over.mk M.pE)
    (Z' := Over.mk M'.pE) M.iE M'.iE S.c M.isPullback_iE.w M'.isPullback_iE.w

@[reassoc (attr := simp)]
theorem prod_iE_snd :
    (M.prod M').iE ≫ pullback.snd M.pS M'.pS = pullback.snd M.pE M'.pE ≫ M'.iE :=
  productMap_pullback_snd (Y := Over.mk M.pS) (Z := Over.mk M'.pS) (Y' := Over.mk M.pE)
    (Z' := Over.mk M'.pE) M.iE M'.iE S.c M.isPullback_iE.w M'.isPullback_iE.w

theorem prod_pS : (M.prod M').pS = pullback.fst M.pS M'.pS ≫ M.pS := rfl

/-- The open of the product model over two opens. -/
abbrev prodV (V : M.Y.left.Opens) (V' : M'.Y.left.Opens) : (M.prod M').Y.left.Opens :=
  prodOpen (pullback.fst M.Y.hom M'.Y.hom) (pullback.snd M.Y.hom M'.Y.hom) V V'

theorem VT_prodV (V : M.Y.left.Opens) (V' : M'.Y.left.Opens) :
    (M.prod M').VT (M.prodV M' V V') = pOpen (p₁ := M.pS) (p₂ := M'.pS) (M.VT V) (M'.VT V') := by
  change (M.prod M').q ⁻¹ᵁ (pullback.fst M.Y.hom M'.Y.hom ⁻¹ᵁ V ⊓
    pullback.snd M.Y.hom M'.Y.hom ⁻¹ᵁ V') = _
  rw [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage,
    prod_q_fst, prod_q_snd, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]

theorem prodV_inf_le_fst {V W : M.Y.left.Opens} {V' W' : M'.Y.left.Opens} :
    M.prodV M' V V' ⊓ M.prodV M' W W' ≤ pullback.fst M.Y.hom M'.Y.hom ⁻¹ᵁ (V ⊓ W) :=
  fun _ hx ↦ ⟨hx.1.1, hx.2.1⟩

theorem prodV_inf_le_snd {V W : M.Y.left.Opens} {V' W' : M'.Y.left.Opens} :
    M.prodV M' V V' ⊓ M.prodV M' W W' ≤ pullback.snd M.Y.hom M'.Y.hom ⁻¹ᵁ (V' ⊓ W') :=
  fun _ hx ↦ ⟨hx.1.2, hx.2.2⟩

theorem VT_prodV_inf_le_fst {V W : M.Y.left.Opens} {V' W' : M'.Y.left.Opens} :
    (M.prod M').VT (M.prodV M' V V') ⊓ (M.prod M').VT (M.prodV M' W W') ≤
      pullback.fst M.pS M'.pS ⁻¹ᵁ (M.VT V ⊓ M.VT W) := by
  rw [VT_prodV, VT_prodV]
  exact fun _ hx ↦ ⟨hx.1.1, hx.2.1⟩

theorem VT_prodV_inf_le_snd {V W : M.Y.left.Opens} {V' W' : M'.Y.left.Opens} :
    (M.prod M').VT (M.prodV M' V V') ⊓ (M.prod M').VT (M.prodV M' W W') ≤
      pullback.snd M.pS M'.pS ⁻¹ᵁ (M'.VT V' ⊓ M'.VT W') := by
  rw [VT_prodV, VT_prodV]
  exact fun _ hx ↦ ⟨hx.1.2, hx.2.2⟩

end Model

namespace ChartFamily

variable {M M' : S.Model} {X X' : Over (Spec (CommRingCat.of R))} {e : M.E ⟶ X.left}
  {e' : M'.E ⟶ X'.left} (K : ChartFamily M X e) (K' : ChartFamily M' X' e')
  (he : e ≫ X.hom = M.pE ≫ S.c) (he' : e' ≫ X'.hom = M'.pE ≫ S.c)

/-- The product of the residue maps. -/
abbrev prodE : (M.prod M').E ⟶ (X ⊗ X').left :=
  productMap (Y' := Over.mk M.pE) (Z' := Over.mk M'.pE) e e' S.c he he'

/-- The chart of the product model over a pair of charts. -/
def prodκ (l : K.L) (l' : K'.L) :
    ((M.prod M').VT (M.prodV M' (K.V l) (K'.V l'))).toScheme ⟶ (X ⊗ X').left :=
  (M.prod M').YS.homOfLE (M.VT_prodV M' _ _).le ≫
    prodChart (K.κ l) (K'.κ l') (K.κ_base l) (K'.κ_base l')

instance (l : K.L) (l' : K'.L) : IsOpenImmersion (K.prodκ K' l l') := by
  unfold prodκ
  infer_instance

@[reassoc (attr := simp)]
theorem prodκ_fst (l : K.L) (l' : K'.L) :
    K.prodκ K' l l' ≫ pullback.fst X.hom X'.hom =
      (pullback.fst M.pS M'.pS).resLE (M.VT (K.V l)) _
        ((M.VT_prodV M' _ _).le.trans inf_le_left) ≫ K.κ l := by
  rw [prodκ, Category.assoc, prodChart_fst, ← Category.assoc, Scheme.Hom.map_resLE]

@[reassoc (attr := simp)]
theorem prodκ_snd (l : K.L) (l' : K'.L) :
    K.prodκ K' l l' ≫ pullback.snd X.hom X'.hom =
      (pullback.snd M.pS M'.pS).resLE (M'.VT (K'.V l')) _
        ((M.VT_prodV M' _ _).le.trans inf_le_right) ≫ K'.κ l' := by
  rw [prodκ, Category.assoc, prodChart_snd, ← Category.assoc, Scheme.Hom.map_resLE]

/-- The product of two chart families. -/
abbrev prod : ChartFamily (M.prod M') (X ⊗ X') (prodE he he') where
  L := K.L × K'.L
  V l := M.prodV M' (K.V l.1) (K'.V l.2)
  affine l := isAffineOpen_prodOpen (IsPullback.of_hasPullback M.Y.hom M'.Y.hom) (K.affine l.1)
    (K'.affine l.2)
  κ l := K.prodκ K' l.1 l.2
  κ_base l := by
    change K.prodκ K' l.1 l.2 ≫ pullback.fst X.hom X'.hom ≫ X.hom = _ ≫ pullback.fst M.pS M'.pS ≫ M.pS
    rw [prodκ_fst_assoc, K.κ_base, Scheme.Hom.resLE_comp_ι_assoc]
  fibre l := by
    apply productMap_ext
    · change _ ≫ pullback.fst X.hom X'.hom = _ ≫ pullback.fst X.hom X'.hom
      rw [Category.assoc, prodκ_fst, Category.assoc, productMap_pullback_fst, ← Category.assoc]
      refine (K.κ_comp_of_fibre l.1 _ (_ ≫ pullback.fst M.pE M'.pE) ?_).trans
        (Category.assoc _ _ _)
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
        Model.prod_iE_fst]
    · change _ ≫ pullback.snd X.hom X'.hom = _ ≫ pullback.snd X.hom X'.hom
      rw [Category.assoc, prodκ_snd, Category.assoc, productMap_pullback_snd, ← Category.assoc]
      refine (K'.κ_comp_of_fibre l.2 _ (_ ≫ pullback.snd M.pE M'.pE) ?_).trans
        (Category.assoc _ _ _)
      simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
        Model.prod_iE_snd]

theorem prod_V (l : K.L × K'.L) : (K.prod K' he he').V l = M.prodV M' (K.V l.1) (K'.V l.2) :=
  rfl

theorem prod_κ (l : K.L × K'.L) : (K.prod K' he he').κ l = K.prodκ K' l.1 l.2 := rfl

variable [IsArtinianRing R] [IsLocalRing R]

/-- The first projection on a double overlap of base changes of product opens. -/
abbrev fstRes (l m : K.L × K'.L) :
    ((M.prod M').VT (M.prodV M' (K.V l.1) (K'.V l.2)) ⊓
      (M.prod M').VT (M.prodV M' (K.V m.1) (K'.V m.2))).toScheme ⟶
        (M.VT (K.V l.1) ⊓ M.VT (K.V m.1)).toScheme :=
  (pullback.fst M.pS M'.pS).resLE _ _ (M.VT_prodV_inf_le_fst M')

/-- The second projection on a double overlap of base changes of product opens. -/
abbrev sndRes (l m : K.L × K'.L) :
    ((M.prod M').VT (M.prodV M' (K.V l.1) (K'.V l.2)) ⊓
      (M.prod M').VT (M.prodV M' (K.V m.1) (K'.V m.2))).toScheme ⟶
        (M'.VT (K'.V l.2) ⊓ M'.VT (K'.V m.2)).toScheme :=
  (pullback.snd M.pS M'.pS).resLE _ _ (M.VT_prodV_inf_le_snd M')

theorem prod_lift_fst (l m : K.L × K'.L) :
    (K.prod K' he he').lift l m ≫ (M.prod M').YS.homOfLE (M.VT_prodV M' _ _).le ≫
        (pullback.fst M.pS M'.pS).resLE (M.VT (K.V l.1)) _ inf_le_left =
      K.fstRes K' l m ≫ K.lift l.1 m.1 := by
  rw [← cancel_mono (K.κ l.1)]
  have h := (K.prod K' he he').lift_κ l m
  rw [prod_κ, prod_κ] at h
  have h' := congrArg (· ≫ pullback.fst X.hom X'.hom) h
  simp only [Category.assoc, prodκ_fst] at h'
  simp only [Category.assoc, lift_κ]
  rw [Scheme.Hom.map_resLE_assoc] at h' ⊢
  rw [h', Scheme.Hom.resLE_map_assoc]

theorem prod_lift_snd (l m : K.L × K'.L) :
    (K.prod K' he he').lift l m ≫ (M.prod M').YS.homOfLE (M.VT_prodV M' _ _).le ≫
        (pullback.snd M.pS M'.pS).resLE (M'.VT (K'.V l.2)) _ inf_le_right =
      K.sndRes K' l m ≫ K'.lift l.2 m.2 := by
  rw [← cancel_mono (K'.κ l.2)]
  have h := (K.prod K' he he').lift_κ l m
  rw [prod_κ, prod_κ] at h
  have h' := congrArg (· ≫ pullback.snd X.hom X'.hom) h
  simp only [Category.assoc, prodκ_snd] at h'
  simp only [Category.assoc, lift_κ]
  rw [Scheme.Hom.map_resLE_assoc] at h' ⊢
  rw [h', Scheme.Hom.resLE_map_assoc]

/-- The transition maps of a product of chart families are the products of the transition
maps: first factor. -/
theorem prod_θS_fst (l m : K.L × K'.L) :
    (K.prod K' he he').θS l m ≫ pullback.fst M.pS M'.pS = K.fstRes K' l m ≫ K.θS l.1 m.1 := by
  simp only [θS]
  rw [← Category.assoc, ← prod_lift_fst K K' he he']
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]

/-- The transition maps of a product of chart families are the products of the transition
maps: second factor. -/
theorem prod_θS_snd (l m : K.L × K'.L) :
    (K.prod K' he he').θS l m ≫ pullback.snd M.pS M'.pS = K.sndRes K' l m ≫ K'.θS l.2 m.2 := by
  simp only [θS]
  rw [← Category.assoc, ← prod_lift_snd K K' he he']
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]

variable {K K'}

/-- Products of lifts of transition maps. -/
def Lifts.prod (D : K.Lifts) (D' : K'.Lifts) : (K.prod K' he he').Lifts where
  θ l m := pullback.lift
    ((pullback.fst M.Y.hom M'.Y.hom).resLE _ _ (M.prodV_inf_le_fst M') ≫ D.θ l.1 m.1)
    ((pullback.snd M.Y.hom M'.Y.hom).resLE _ _ (M.prodV_inf_le_snd M') ≫ D'.θ l.2 m.2) (by
      rw [Category.assoc, Category.assoc, D.overBase, D'.overBase,
        Scheme.Hom.resLE_comp_ι_assoc, Scheme.Hom.resLE_comp_ι_assoc, pullback.condition])
  overBase l m := by
    change _ ≫ pullback.fst M.Y.hom M'.Y.hom ≫ M.Y.hom = _ ≫ pullback.fst M.Y.hom M'.Y.hom ≫ M.Y.hom
    rw [pullback.lift_fst_assoc, Category.assoc, D.overBase, Scheme.Hom.resLE_comp_ι_assoc]
  reduces l m := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, Model.prod_q_fst]
      have e₁ : (K.prod K' he he').res₂ l m ≫
          (pullback.fst M.Y.hom M'.Y.hom).resLE _ _ (M.prodV_inf_le_fst M') =
          K.fstRes K' l m ≫ K.res₂ l.1 m.1 := by
        rw [← cancel_mono (K.V l.1 ⊓ K.V m.1).ι]
        simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
          Model.prod_q_fst]
      rw [← Category.assoc, e₁, Category.assoc, D.reduces, ← Category.assoc
        ((K.prod K' he he').θS l m), prod_θS_fst, Category.assoc]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, Model.prod_q_snd]
      have e₁ : (K.prod K' he he').res₂ l m ≫
          (pullback.snd M.Y.hom M'.Y.hom).resLE _ _ (M.prodV_inf_le_snd M') =
          K.sndRes K' l m ≫ K'.res₂ l.2 m.2 := by
        rw [← cancel_mono (K'.V l.2 ⊓ K'.V m.2).ι]
        simp only [Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι_assoc,
          Model.prod_q_snd]
      rw [← Category.assoc, e₁, Category.assoc, D'.reduces, ← Category.assoc
        ((K.prod K' he he').θS l m), prod_θS_snd, Category.assoc]

@[reassoc (attr := simp)]
theorem Lifts.prod_θ_fst (D : K.Lifts) (D' : K'.Lifts) (l m : K.L × K'.L) :
    (D.prod he he' D').θ l m ≫ pullback.fst M.Y.hom M'.Y.hom =
      (pullback.fst M.Y.hom M'.Y.hom).resLE _ _ (M.prodV_inf_le_fst M') ≫ D.θ l.1 m.1 :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem Lifts.prod_θ_snd (D : K.Lifts) (D' : K'.Lifts) (l m : K.L × K'.L) :
    (D.prod he he' D').θ l m ≫ pullback.snd M.Y.hom M'.Y.hom =
      (pullback.snd M.Y.hom M'.Y.hom).resLE _ _ (M.prodV_inf_le_snd M') ≫ D'.θ l.2 m.2 :=
  pullback.lift_snd _ _ _

end ChartFamily

end Langlands.AbelianScheme.ArtinianConstantCharts.Setting
