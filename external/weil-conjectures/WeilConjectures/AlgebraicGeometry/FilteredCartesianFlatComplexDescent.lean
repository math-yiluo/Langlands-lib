/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import WeilConjectures.AlgebraicGeometry.FiniteFlatProperSupportDescent
import WeilConjectures.AlgebraicGeometry.TensorPullbackFlatProperSupport
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Flat complex descent from a cartesian model

Source: Stacks Project, Tags 0032, 01ZR, 05LY, 081G and 0CYS.
(blueprint: lem-pc-filtered-cartesian-flat-complex-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A bounded finitely presented base-flat complex with proper support on the limit
of a fixed finitely presented model descends to a stage in a small filtered category.
There is no perfect derived object in this assertion.

Proof:
1. Use a final directed poset in the filtered under-category of the fixed stage
   (Tag 0032). The projection from that under-category is final, so restriction of
   the ring cocone is still colimiting. All its rings are still Noetherian.
2. Replace the given cartesian model by the canonical pullback using its unique
   pullback isomorphism. Transport G along this scheme isomorphism, degreewise;
   tensor pullback composition transports the differentials and their equations.
   Boundedness, finite presentation, base-flatness and proper support are invariant
   under this isomorphism. Spec takes the ring colimit to the affine scheme limit.
3. Apply finite_flat_proper_support_descent to this directed system and the
   transported complex. It supplies a stage complex and the commuting degreewise
   comparison isomorphisms. Return its stage through the final functor. The stage
   scheme is the base change of the fixed model, so its morphism has all three
   finite-presentation properties. Compose the comparison with the isomorphism in
   step 2 to recover G on the original X.
Source: Stacks Project, Tags 0032, 01ZR, 05LY, 081G and 0CYS.
(blueprint: lem-pc-filtered-cartesian-flat-complex-descent).
-/
theorem filtered_cartesian_flat_complex_descent
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) [∀ i : I, IsNoetherianRing (R.obj i)]
    (c : Cocone R) (hc : IsColimit c)
    (X : Scheme.{u}) (f : X ⟶ Spec c.pt)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (g : X ⟶ Xi) (hcart : IsPullback g f fi (Spec.map (c.ι.app i)))
    {G : CochainComplex X.Modules ℤ}
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    [∀ n : ℤ, (G.X n).IsFinitePresentation]
    (hGflat : ∀ n : ℤ, (G.X n).IsFlatOver f)
    (hGproper : ∀ n : ℤ, Scheme.Modules.HasSupportProperOver f (G.X n)) :
    ∃ (i : I) (Xi : Scheme.{u}) (fi : Xi ⟶ Spec (R.obj i)),
      LocallyOfFinitePresentation fi ∧ QuasiCompact fi ∧ QuasiSeparated fi ∧
      ∃ (hfi : LocallyOfFiniteType fi) (g : X ⟶ Xi),
        IsPullback g f fi (Spec.map (c.ι.app i)) ∧
        ∃ (Gi : CochainComplex Xi.Modules ℤ),
          (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Gi.X n)) ∧
          (∀ n : ℤ, (Gi.X n).IsFinitePresentation) ∧
          (∀ n : ℤ, (Gi.X n).IsFlatOver fi) ∧
          (∀ n : ℤ, @Scheme.Modules.HasSupportProperOver _ _ fi hfi (Gi.X n)) ∧
          ∃ e : ∀ n : ℤ, Scheme.Modules.tensorPullbackObj g (Gi.X n) ≅ G.X n,
            ∀ n m : ℤ, Scheme.Modules.tensorPullbackMap g (Gi.d n m) ≫ (e m).hom =
              (e n).hom ≫ G.d n m := by
  classical
  obtain ⟨A, hAorder, hAdir, hAnonempty, F, hFfinal⟩ :=
    IsFiltered.exists_directed (Under i)
  let : PartialOrder A := hAorder
  let : IsDirected A (· ≤ ·) := hAdir
  let : Nonempty A := hAnonempty
  have : F.Final := hFfinal
  let H := F ⋙ Under.forget i
  let R' := H ⋙ R
  let c' := c.whisker H
  have hc' : IsColimit c' := (Functor.Final.isColimitWhiskerEquiv H c).symm hc
  let (b : A) : IsNoetherianRing (R'.obj b) := by dsimp [R', H]; infer_instance
  let b₀ : A := Classical.choice hAnonempty
  let t₀ : Spec (R'.obj b₀) ⟶ Spec (R.obj i) := Spec.map (R.map (F.obj b₀).hom)
  let X₀ := pullback fi t₀
  let f₀ : X₀ ⟶ Spec (R'.obj b₀) := pullback.snd fi t₀
  have hbase : Spec.map (c'.ι.app b₀) ≫ t₀ = Spec.map (c.ι.app i) := by
    dsimp [t₀, c', H]
    rw [← Spec.map_comp, c.w]
  have hcart₀ : IsPullback g f fi (Spec.map (c'.ι.app b₀) ≫ t₀) := by
    rw [hbase]
    exact hcart
  let g₀ : X ⟶ X₀ := (IsPullback.of_hasPullback fi t₀).lift g (f ≫ Spec.map (c'.ι.app b₀))
    (by rw [Category.assoc, hbase]; exact hcart.w)
  have hsquare₀ : IsPullback g₀ f f₀ (Spec.map (c'.ι.app b₀)) :=
    hcart₀.of_right' (IsPullback.of_hasPullback fi t₀)
  let e₀ := hsquare₀.isoPullback
  let Q := Scheme.Modules.tensorPullback e₀.inv
  obtain ⟨adjQ⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction e₀.inv
  have : Q.Additive := adjQ.left_adjoint_additive
  let G₀ := (Q.mapHomologicalComplex (ComplexShape.up ℤ)).obj G
  have hinv : IsPullback e₀.inv (pullback.snd f₀ (Spec.map (c'.ι.app b₀)))
      f (𝟙 (Spec c.pt)) := by
    have h : e₀.inv ≫ f = pullback.snd f₀ (Spec.map (c'.ι.app b₀)) :=
      hsquare₀.isoPullback_inv_snd
    have : IsIso (𝟙 (Spec c.pt)) := inferInstance
    exact IsPullback.of_horiz_isIso ⟨h.trans (Category.comp_id _).symm⟩
  have hprops (n : ℤ) := tensorPullback_flat_proper_support f
    (pullback.snd f₀ (Spec.map (c'.ι.app b₀))) e₀.inv (𝟙 (Spec c.pt)) hinv
    (G.X n) (hGflat n) (hGproper n)
  have hG₀b : ∃ lo hi : ℤ, ∀ n : ℤ, n < lo ∨ hi < n → IsZero (G₀.X n) := by
    obtain ⟨lo, hi, hb⟩ := hGb
    exact ⟨lo, hi, fun n hn ↦ Q.map_isZero (hb n hn)⟩
  let d : Cone (R'.op ⋙ Scheme.Spec) := Scheme.Spec.mapCone c'.op
  have hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc'.op
  have : IsAffine d.pt := by change IsAffine (Spec c.pt); infer_instance
  obtain ⟨b, hle, Gb, hGb, hGfp, hGflatb, hGproperb, eGb, heGb⟩ :=
    finite_flat_proper_support_descent R' d hd b₀ f₀ G₀ hG₀b
      (fun n ↦ (hprops n).1) (fun n ↦ (hprops n).2.1)
      (fun n ↦ (hprops n).2.2)
  let t : Spec (R'.obj b) ⟶ Spec (R'.obj b₀) := Spec.map (R'.map (homOfLE hle))
  let Xb := pullback f₀ t
  let fb : Xb ⟶ Spec (R'.obj b) := pullback.snd f₀ t
  let p : Xb ⟶ Xi := pullback.fst f₀ t ≫ pullback.fst fi t₀
  have htrans : t ≫ t₀ = Spec.map (R.map (F.obj b).hom) := by
    dsimp [t, t₀, R', H]
    rw [← Spec.map_comp, ← R.map_comp]
    congr 2
    exact Under.w (F.map (homOfLE hle))
  have hp : IsPullback p fb fi (Spec.map (R.map (F.obj b).hom)) := by
    rw [← htrans]
    exact (IsPullback.of_hasPullback f₀ t).paste_horiz
      (IsPullback.of_hasPullback fi t₀)
  have hbaseb : Spec.map (c'.ι.app b) ≫ Spec.map (R.map (F.obj b).hom) =
      Spec.map (c.ι.app i) := by
    dsimp [c', H]
    rw [← Spec.map_comp, c.w]
  let gb : X ⟶ Xb := hp.lift g (f ≫ Spec.map (c'.ι.app b))
    (by rw [Category.assoc, hbaseb]; exact hcart.w)
  have hgp : gb ≫ p = g := hp.lift_fst _ _ _
  have hgcart : IsPullback gb f fb (Spec.map (c'.ι.app b)) := by
    have hh : IsPullback g f fi
        (Spec.map (c'.ι.app b) ≫ Spec.map (R.map (F.obj b).hom)) := by
      rw [hbaseb]
      exact hcart
    exact hh.of_right' hp
  refine ⟨H.obj b, Xb, fb, inferInstance, inferInstance, inferInstance,
    inferInstance, gb, hgcart, Gb, hGb, hGfp, hGflatb, hGproperb, ?_⟩
  let v : Over.mk (Spec.map (c'.ι.app b₀)) ⟶ Over.mk t :=
    Over.homMk (Spec.map (c'.ι.app b))
      (by dsimp [t]; rw [← Spec.map_comp, c'.w (homOfLE hle)])
  let bm := baseChangeMap f₀ v
  have hb1 : bm ≫ pullback.fst f₀ t = pullback.fst f₀ (Spec.map (c'.ι.app b₀)) :=
    baseChangeMap_fst f₀ v
  have hb2 : bm ≫ pullback.snd f₀ t =
      pullback.snd f₀ (Spec.map (c'.ι.app b₀)) ≫ Spec.map (c'.ι.app b) :=
    baseChangeMap_snd f₀ v
  have hcan : e₀.hom ≫ bm = gb := by
    apply hp.hom_ext
    · change (e₀.hom ≫ bm) ≫ (pullback.fst f₀ t ≫ pullback.fst fi t₀) = gb ≫ p
      rw [Category.assoc, ← Category.assoc bm, hb1,
        ← Category.assoc, hsquare₀.isoPullback_hom_fst, hgp]
      exact (IsPullback.of_hasPullback fi t₀).lift_fst _ _ _
    · change (e₀.hom ≫ bm) ≫ pullback.snd f₀ t = gb ≫ fb
      rw [Category.assoc, hb2, ← Category.assoc, hsquare₀.isoPullback_hom_snd]
      exact (hp.lift_snd _ _ _).symm
  let B := Scheme.Modules.tensorPullback bm
  let P := Scheme.Modules.tensorPullback e₀.hom
  let T := Scheme.Modules.tensorPullback gb
  obtain ⟨adjB⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction bm
  obtain ⟨adjP⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction e₀.hom
  obtain ⟨adjT⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction gb
  have : B.Additive := adjB.left_adjoint_additive
  have : P.Additive := adjP.left_adjoint_additive
  have : T.Additive := adjT.left_adjoint_additive
  let eC : (B.mapHomologicalComplex (.up ℤ)).obj Gb ≅ G₀ :=
    HomologicalComplex.Hom.isoOfComponents eGb (fun n m _ ↦ (heGb n m).symm)
  obtain ⟨ec⟩ := Scheme.Modules.nonempty_tensorPullbackComp e₀.hom bm
  let ec' : B ⋙ P ≅ T := ec.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback hcan)
  obtain ⟨eqc⟩ := Scheme.Modules.nonempty_tensorPullbackComp e₀.hom e₀.inv
  obtain ⟨eu⟩ := Scheme.Modules.nonempty_tensorPullbackId X
  let er : Q ⋙ P ≅ 𝟭 X.Modules := eqc.symm ≪≫
    eqToIso (congrArg Scheme.Modules.tensorPullback e₀.hom_inv_id) ≪≫ eu
  let eFinal : (T.mapHomologicalComplex (.up ℤ)).obj Gb ≅ G :=
    ((Functor.mapHomologicalComplexCompIso ec' (.up ℤ)).app Gb).symm ≪≫
      (P.mapHomologicalComplex (.up ℤ)).mapIso eC ≪≫
        (Functor.mapHomologicalComplexCompIso er (.up ℤ)).app G ≪≫
          (Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)).app G
  refine ⟨fun n ↦ HomologicalComplex.Hom.isoApp eFinal n, ?_⟩
  intro n m
  exact (eFinal.hom.comm n m).symm

end AlgebraicGeometry
