/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.DirectedColimitBaseChangeElementwise
import WeilConjectures.AlgebraicGeometry.AffineBaseChangeChartColimit
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Detection of affine module section vanishing at one stage

Source: Stacks Project, Limits, Tag 01ZR (3), affine part of the first proof;
Algebra, Tags 05N7 (3) and 05LI (1).
(blueprint: lem-pc-affine-section-zero-at-stage).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem unit_zero_iff {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Y.Modules) (V : Y.Opens) (s : Γ(G, V))
    (a b : Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g) :
    (a.unit.app G).val.app (op V) s = 0 ↔
      (b.unit.app G).val.app (op V) s = 0 := by
  have go (a b : Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
      (h : (a.unit.app G).val.app (op V) s = 0) :
      (b.unit.app G).val.app (op V) s = 0 := by
    have hu := a.unit_leftAdjointUniq_hom_app b G
    have hv := congrArg (fun z ↦ z.app V s) hu
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at hv
    change (a.unit.app G).app V s = 0 at h
    rw [h, map_zero] at hv
    exact hv.symm
  exact ⟨go a b, go b a⟩

private theorem unit_zero_iff_tensor {X Y : Scheme.{u}} (g : X ⟶ Y)
    (G : Y.Modules) (hG : G.IsQuasicoherent) (V : Y.affineOpens)
    (W : X.affineOpens) (hW : W.1 = g ⁻¹ᵁ V.1)
    (a : Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    (s : Γ(G, V.1)) :
    letI : Algebra Γ(Y, V.1) Γ(X, W.1) :=
      (g.appLE V.1 W.1 hW.le).hom.toAlgebra
    (a.unit.app G).val.app (op V.1) s = 0 ↔
      TensorProduct.tmul Γ(Y, V.1) (1 : Γ(X, W.1)) s = 0 := by
  classical
  dsimp only
  let : Algebra Γ(Y, V.1) Γ(X, W.1) :=
    (g.appLE V.1 W.1 hW.le).hom.toAlgebra
  obtain ⟨c, hc, _, hp, _⟩ :=
    Scheme.Modules.exists_tensorPullback_affine_sections g V W hW.le
  let e := TensorProduct.comm Γ(Y, V.1) Γ(X, W.1) Γ(G, V.1)
  let b := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  have ht : c G hG (TensorProduct.tmul Γ(Y, V.1) s (1 : Γ(X, W.1))) =
      ((Scheme.Modules.tensorPullback g).obj G).presheaf.map (homOfLE hW.le).op
        ((b.unit.app G).val.app (op V.1) s) := by
    simpa only [one_smul] using hp G hG s 1
  have hzero : c G hG (TensorProduct.tmul Γ(Y, V.1) s (1 : Γ(X, W.1))) = 0 ↔
      TensorProduct.tmul Γ(Y, V.1) s (1 : Γ(X, W.1)) = 0 := by
    exact (hc G hG).1.eq_iff' (map_zero (c G hG))
  have hcomm : TensorProduct.tmul Γ(Y, V.1) s (1 : Γ(X, W.1)) = 0 ↔
      TensorProduct.tmul Γ(Y, V.1) (1 : Γ(X, W.1)) s = 0 := by
    constructor
    · intro h
      have := congrArg e.symm h
      simpa only [e, TensorProduct.comm_symm, TensorProduct.comm_tmul, map_zero] using this
    · intro h
      have := congrArg e h
      simpa only [e, TensorProduct.comm_tmul, map_zero] using this
  rw [← hcomm, ← hzero, ht]
  rw [unit_zero_iff g G V.1 s a
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g))]
  have hmap : Function.Injective
      (((Scheme.Modules.tensorPullback g).obj G).presheaf.map (homOfLE hW.le).op) := by
    have : IsIso (homOfLE hW.le) := by
      have he : homOfLE hW.le = eqToHom hW := Subsingleton.elim _ _
      rw [he]
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso _).1
  exact (hmap.eq_iff' (map_zero _)).symm

private theorem cocone_tensor_one_zero_at_stage
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)]
    (F : J ⥤ CommRingCat.{u}) (B : Cocone F) (hB : IsColimit B)
    (j : J) (M : Type u) [AddCommGroup M] [Module (F.obj j) M] (s : M) :
    letI : Algebra (F.obj j) B.pt := (B.ι.app j).hom.toAlgebra
    TensorProduct.tmul (F.obj j) (1 : B.pt) s = 0 →
    ∃ (k : J) (hjk : j ≤ k),
      letI : Algebra (F.obj j) (F.obj k) := (F.map (homOfLE hjk)).hom.toAlgebra
      TensorProduct.tmul (F.obj j) (1 : F.obj k) s = 0 := by
  classical
  let : HasColimit F := ⟨⟨B, hB⟩⟩
  let : Algebra (F.obj j) B.pt := (B.ι.app j).hom.toAlgebra
  let L : CommRingCat.{u} := colimit F
  let : Algebra (F.obj j) L := (colimit.ι F j).hom.toAlgebra
  intro hs
  let e := hB.coconePointUniqueUpToIso (colimit.isColimit F)
  let a : B.pt →ₐ[F.obj j] L :=
    { e.hom.hom with
      commutes' := fun r ↦ ConcreteCategory.congr_hom
        (hB.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) j) r }
  have hz : TensorProduct.tmul (F.obj j) (1 : L) s = 0 := by
    have hh := congrArg (a.toLinearMap.rTensor M) hs
    simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one, map_zero] using hh
  let : Algebra (F.obj j) (F.obj j) := (F.map (homOfLE (le_refl j))).hom.toAlgebra
  let : Module (F.obj j) (F.obj j) :=
    @Algebra.toModule (F.obj j) (F.obj j) _ _ inferInstance
  have hz' := (TensorProduct.directedColimitBaseChangeElementwise F j M).2
    j le_rfl (TensorProduct.tmul (F.obj j) (1 : F.obj j) s)
  simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at hz'
  obtain ⟨k, hjk, hk⟩ := hz' hz
  refine ⟨k, hjk, ?_⟩
  simpa only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] using hk

/-- A section killed at the affine inverse limit is killed at one stage.
Source: Stacks Project, Limits, Tag 01ZR (3), first proof; Algebra, Tag 05LI (1).
(blueprint: lem-pc-affine-section-zero-at-stage).

Proof: the inverse images of U are affine by base change of affine morphisms.
Restrict the ring diagram to the upper tail of j. Pullback pasting and
isLimitBaseChangeCone identify the limit chart with the inverse limit of the
stage charts; the affine Spec/Gamma equivalence identifies its ring with their
filtered colimit. Quasi-coherence identifies pullback sections with scalar
extension of G on the j-th chart. The canonical unit sends y to 1 tensor y.
Apply the zero clause of TensorProduct.directedColimitBaseChangeElementwise to
this tensor to obtain one later stage. The affine pullback comparison is
bijective and therefore reflects zero. Finally uniqueness of left adjoints
intertwines any supplied adjunction unit with the canonical unit by an
isomorphism. Its section components preserve and reflect zero. This includes
empty charts and zero modules and does not require finite presentation. -/
theorem section_affine_open_zero_at_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (G : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hG_qc : G.IsQuasicoherent)
    (U : Xi.Opens) (hU : IsAffineOpen U)
    (y : Γ(G, (pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U))
    (adjlim : Scheme.Modules.tensorPullback
      (baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))) ⊣
      Scheme.Modules.pushforward
        (baseChangeMap f
          (T := Over.mk (Spec.map (R.map (homOfLE hij))))
          (T' := Over.mk (c.π.app (op i)))
          (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))))
    (adjstage : ∀ (k : I) (hjk : j ≤ k),
      let g := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    (hy : (adjlim.unit.app G).val.app
      (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0) :
    ∃ (l : I) (hjl : j ≤ l),
      ((adjstage l hjl).unit.app G).val.app
        (op ((pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U)) y = 0 := by
  classical
  let J := {k : I // j ≤ k}
  let j₀ : J := ⟨j, le_rfl⟩
  let : IsDirected J (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨k, ha, hb⟩ := exists_ge_ge a.val b.val
    exact ⟨⟨k, a.property.trans ha⟩, ha, hb⟩⟩
  let F := AffineBaseChangeChart.rings R i f j hij U
  let B := AffineBaseChangeChart.cocone R i f j hij U c
  obtain ⟨hB⟩ := AffineBaseChangeChart.isColimit_cocone R i f j hij U c hc hU
  let : IsAffineHom (pullback.fst f (Spec.map (R.map (homOfLE hij)))) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (Spec.map
      (R.map (homOfLE hij))))
  let : IsAffineHom (c.π.app (op i)) :=
    @isAffineHom_of_isAffine c.pt (Spec (R.obj i)) (c.π.app (op i))
      inferInstance inferInstance
  let : IsAffineHom (pullback.fst f (c.π.app (op i))) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom (c.π.app (op i)))
  let V : (pullback f (Spec.map (R.map (homOfLE hij)))).affineOpens :=
    ⟨(pullback.fst f (Spec.map (R.map (homOfLE hij)))) ⁻¹ᵁ U,
      hU.preimage (pullback.fst f (Spec.map (R.map (homOfLE hij))))⟩
  let W : (pullback f (c.π.app (op i))).affineOpens := ⟨(pullback.fst f (c.π.app (op i))) ⁻¹ᵁ U,
      hU.preimage (pullback.fst f (c.π.app (op i)))⟩
  let g := baseChangeMap f (AffineBaseChangeChart.projection R i j hij c j₀)
  have hW : W.1 = g ⁻¹ᵁ V.1 := by
    dsimp [W, V, g, AffineBaseChangeChart.projection, AffineBaseChangeChart.stage]
    simp [← Scheme.Hom.comp_preimage, baseChangeMap]
  have hy' := (unit_zero_iff_tensor g G hG_qc V W hW adjlim y).mp hy
  obtain ⟨l, hjl, hl⟩ :=
    @cocone_tensor_one_zero_at_stage J _ _ F B hB j₀ Γ(G, V.1)
      (inferInstance : AddCommGroup Γ(G, V.1)) (G.val.obj (op V.1)).isModule y hy'
  let gl := baseChangeMap f
    (AffineBaseChangeChart.transition R i j hij (homOfLE hjl : j₀ ⟶ l))
  let : IsAffineHom (AffineBaseChangeChart.stage R i j hij l).hom :=
    @isAffineHom_of_isAffine (Spec (R.obj l.val)) (Spec (R.obj i))
      (AffineBaseChangeChart.stage R i j hij l).hom inferInstance inferInstance
  let : IsAffineHom (pullback.fst f (AffineBaseChangeChart.stage R i j hij l).hom) :=
    MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom
      (AffineBaseChangeChart.stage R i j hij l).hom)
  let Wl : (pullback f (AffineBaseChangeChart.stage R i j hij l).hom).affineOpens :=
    ⟨AffineBaseChangeChart.chart R i f j hij U l,
      hU.preimage (pullback.fst f (AffineBaseChangeChart.stage R i j hij l).hom)⟩
  have hWl : Wl.1 = gl ⁻¹ᵁ V.1 := by
    dsimp [Wl, V, gl, AffineBaseChangeChart.chart,
      AffineBaseChangeChart.transition, AffineBaseChangeChart.stage]
    simp [← Scheme.Hom.comp_preimage, baseChangeMap]
  exact ⟨l.val, l.property,
    (unit_zero_iff_tensor gl G hG_qc V Wl hWl (adjstage l.val l.property) y).mpr hl⟩

end AlgebraicGeometry
