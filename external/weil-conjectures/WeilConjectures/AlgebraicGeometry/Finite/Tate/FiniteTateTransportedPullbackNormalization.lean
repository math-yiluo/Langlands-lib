/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescentDefinitions

import WeilConjectures.AlgebraicGeometry.Affine.AffineRootsRepresentability
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Root normalization of a transported finite Tate pullback

Source: Stacks Project, Tags 03PK, 03Q1, 099R and 0GLZ.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.Scheme

private theorem etale_roots_sections (T : Scheme.{u}) (m : ℕ) (U : T.Etaleᵒᵖ) :
    ∃ e : (T.rootsOfUnitySheaf m).obj.obj U ≃
        {z : Γ(U.unop.left, ⊤)ˣ // z ^ m = 1},
      ∀ z, (e z).val = finiteTateEtaleRootValue T m U z := by
  let ev := sheafToPresheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
    (CategoryTheory.evaluation _ _).obj U
  let φ := ev.map (m • 𝟙 T.gmSheaf)
  let e := PreservesKernel.iso ev (m • 𝟙 T.gmSheaf) ≪≫ AddCommGrpCat.kernelIsoKer φ
  let g : φ.hom.ker ≃ {z : Γ(U.unop.left, ⊤)ˣ // z ^ m = 1} :=
    { toFun := fun y ↦ ⟨y.1.down.toMul, by
        have hy : m • y.1 = 0 := y.2
        exact congrArg (fun z ↦ z.down.toMul) hy⟩
      invFun := fun z ↦ ⟨ULift.up (Additive.ofMul z.val), by
        change m • (ULift.up (Additive.ofMul z.val)) = 0
        apply ULift.ext
        apply Additive.toMul.injective
        exact z.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  refine ⟨e.addCommGroupIsoToAddEquiv.toEquiv.trans g, ?_⟩
  intro z
  have he : e.hom ≫ AddCommGrpCat.ofHom φ.hom.ker.subtype =
      ev.map (kernel.ι (m • 𝟙 T.gmSheaf)) := by
    rw [Iso.trans_hom, Category.assoc, AddCommGrpCat.kernelIsoKer_hom_comp_subtype,
      PreservesKernel.iso_hom, kernelComparison_comp_ι]
  exact congrArg (fun q ↦ q.down.toMul) (ConcreteCategory.congr_hom he z)

private theorem etale_root_restrict (T : Scheme.{u}) (m : ℕ)
    {U V : T.Etaleᵒᵖ} (f : U ⟶ V) (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    finiteTateEtaleRootValue T m V ((T.rootsOfUnitySheaf m).obj.map f z) =
      Units.map f.unop.left.appTop.hom.toMonoidHom (finiteTateEtaleRootValue T m U z) := by
  exact congrArg (fun q ↦ q.down.toMul)
    (ConcreteCategory.congr_hom ((kernel.ι (m • 𝟙 T.gmSheaf)).hom.naturality f) z)

private theorem root_test_object (T : Scheme.{u}) (m : ℕ) (hm : 0 < m)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    ∃ (V : T.Etale) (z : (T.rootsOfUnitySheaf m).obj.obj (op V)),
      ∀ (W : T.ProEt) (y : Γ(W.left, ⊤)ˣ), y ^ m = 1 →
        ∃ f : W ⟶ (toProEt T).obj V,
          Units.map f.left.appTop.hom.toMonoidHom
            (finiteTateEtaleRootValue T m (op V) z) = y := by
  let B := Γ(T, ⊤)
  have : Etale (affineRootsOver B m).hom := by
    change Etale (Spec.map (CommRingCat.ofHom (algebraMap B
      (AdjoinRoot ((Polynomial.X : Polynomial B) ^ m - 1)))))
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr
      (AdjoinRoot.etale_X_pow_sub_C (Nat.ne_of_gt hm) hT isUnit_one)
  let P := (Over.pullback T.toSpecΓ).obj (affineRootsOver B m)
  have : Etale P.hom := by
    change Etale (pullback.snd (affineRootsOver B m).hom T.toSpecΓ)
    infer_instance
  let V := Etale.mk P.hom
  obtain ⟨_, _, _, _, _, _, _, hbase⟩ := affineRoots_representability B m hm
  obtain ⟨e, _, hnat, _⟩ := hbase T T.toSpecΓ
  obtain ⟨s, hs⟩ := etale_roots_sections T m (op V)
  let z := s.symm (e P (𝟙 P))
  refine ⟨V, z, ?_⟩
  intro W y hy
  let q := (e (Over.mk W.hom)).symm ⟨y, hy⟩
  let f : W ⟶ (toProEt T).obj V := MorphismProperty.Over.homMk q.left q.w
  refine ⟨f, ?_⟩
  have hz : finiteTateEtaleRootValue T m (op V) z = (e P (𝟙 P)).val :=
    (hs z).symm.trans (congrArg Subtype.val (s.apply_symm_apply _))
  rw [hz]
  exact (hnat (Over.mk W.hom) P q (𝟙 P)).symm.trans
    (congrArg Subtype.val (by
      simpa only [Category.comp_id] using (e (Over.mk W.hom)).apply_symm_apply ⟨y, hy⟩))

private theorem finite_root_tuple_presentation
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r k : ℕ) (W : T.ProEtᵒᵖ)
    (x : Fin k → (purTwistZlOne T l).obj.obj W) :
    ∃ (U : T.Etaleᵒᵖ) (f : W.unop ⟶ (toProEt T).obj U.unop)
      (z : Fin k → (T.rootsOfUnitySheaf (l ^ (r + 1))).obj.obj U),
      ∀ i, finiteTateLimitRootValue l T r W (x i) =
        Units.map f.left.appTop.hom.toMonoidHom
          (finiteTateEtaleRootValue T (l ^ (r + 1)) U (z i)) := by
  classical
  let m := l ^ (r + 1)
  have hm : 0 < m := pow_pos (Fact.out : l.Prime).pos _
  have hTm : IsUnit (m : Γ(T, ⊤)) := by
    simpa only [m, Nat.cast_pow] using hT.pow (r + 1)
  obtain ⟨V, z, hV⟩ := root_test_object T m hm hTm
  have hpow (i : Fin k) : finiteTateLimitRootValue l T r W (x i) ^ m = 1 := by
    have h := congrArg (fun q ↦ q.hom.app W
      ((limit.π (proEtaleRootsOfUnityTower T l (Fact.out : l.Prime)) (op r)).hom.app W
        (x i))) (kernel.condition (proEtaleUnitsPower T m))
    exact congrArg (fun q ↦ q.down.toMul) h
  choose f hf using fun i ↦ hV W.unop (finiteTateLimitRootValue l T r W (x i)) (hpow i)
  let D : Fin k → T.Etale := fun _ ↦ V
  let U := ∏ᶜ D
  let p := piComparison (toProEt T) D
  let g : W.unop ⟶ (toProEt T).obj U := Pi.lift f ≫ inv p
  refine ⟨op U, g, fun i ↦ (T.rootsOfUnitySheaf m).obj.map (Pi.π D i).op z, ?_⟩
  intro i
  rw [etale_root_restrict]
  have hgi : g ≫ (toProEt T).map (Pi.π D i) = f i := by
    dsimp only [g]
    rw [Category.assoc, inv_piComparison_comp_map_π, Pi.lift_comp_π]
  have hleft := congrArg (fun q ↦ q.left) hgi
  rw [← hf i]
  exact congrArg (fun q : W.unop.left ⟶ V.left ↦
    Units.map q.appTop.hom.toMonoidHom (finiteTateEtaleRootValue T m (op V) z))
      hleft.symm

private theorem composite_transpose
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I)
    (X : C) (Z : E) (f : (F ⋙ H).obj X ⟶ Z) :
    (adj₁.comp adj₂).homEquiv X Z f =
      adj₁.homEquiv X (I.obj Z) (adj₂.homEquiv (F.obj X) Z f) := by
  rw [Adjunction.comp_homEquiv]
  rfl

private theorem transpose_mate
    {C : Type*} {D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (δ : R₁ ⟶ R₂)
    (X : C) (Y : D) (f : L₁.obj X ⟶ Y) :
    adj₂.homEquiv X Y (((conjugateEquiv adj₁ adj₂).symm δ).app X ≫ f) =
      adj₁.homEquiv X Y f ≫ δ.app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    ← unit_conjugateEquiv_symm]
  rw [Category.assoc, ← δ.naturality, ← Category.assoc, ← Adjunction.homEquiv_unit]

private theorem comparison_pullback_adjunct_unit
    (A : Type (u + 1)) [CommRing A] {T T' : Scheme.{u}} (v : T' ⟶ T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (G : Sheaf T'.smallEtaleTopology (ModuleCat.{u + 1} A))
    (P : Sheaf (ProEt.topology T') (ModuleCat.{u + 1} A))
    (c : (Etale.upperStar (ModuleCat.{u + 1} A) v).obj F ⟶ G)
    (b : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').obj G ⟶ P)
    (U : T.Etaleᵒᵖ) (t : F.obj.obj U) :
    (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
      (((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) v).app F).hom ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map c ≫ b)).hom.app
          (op ((toProEt T).obj U.unop)))
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app U t) =
    b.hom.app (op ((toProEt T').obj
        ((MorphismProperty.Over.pullback @Etale ⊤ v).obj U.unop)))
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T').unit.app G).hom.app
        ((MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U)
          (((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
            c).hom.app U t)) := by
  have h := transpose_mate
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).comp
      (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T'))
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).comp
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v))
    (ProEtale.lowerStarCompComparisonLowerStarIso v (ModuleCat.{u + 1} A)).inv F P
    ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map c ≫ b)
  rw [composite_transpose, composite_transpose] at h
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right] at h
  rw [Adjunction.homEquiv_unit] at h
  have ht := congrArg (fun q ↦ q.hom.app U t) h
  let U' := (MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U
  let z := ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ c).hom.app U t
  change _ =
    ((ProEtale.lowerStarCompComparisonLowerStarIso v (ModuleCat.{u + 1} A)).inv.app P).hom.app U
      (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T').homEquiv _ _ b).hom.app U' z) at ht
  have hδ :
      ((ProEtale.lowerStarCompComparisonLowerStarIso v (ModuleCat.{u + 1} A)).inv.app P).hom.app U =
        𝟙 (P.obj.obj ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ v).op.obj
          ((toProEt T).op.obj U))) := by
    simp only [Functor.comp_obj, ProEtale.lowerStarCompComparisonLowerStarIso,
      Functor.sheafPushforwardContinuousComp, Functor.sheafPushforwardContinuousIso,
      Functor.sheafPushforwardContinuousNatTrans, ProEtale.toProEtCompOverPullbackIso,
      ObjectProperty.ι_obj, Iso.refl_symm, Iso.trans_inv, Iso.refl_inv, Category.assoc,
      NatTrans.comp_app, NatTrans.id_app, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.FullSubcategory.id_hom, Functor.whiskerRight_app,
      Functor.op_obj, NatTrans.op_app, NatIso.ofComponents_hom_app, Iso.refl_hom, op_id]
    erw [CategoryTheory.Functor.map_id]
    erw [Category.id_comp, Category.id_comp]
    rfl
  have ht' := ht.trans (ConcreteCategory.congr_hom hδ _)
  have hb := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T').homEquiv_unit _ _ b
  exact ht'.trans (congrArg
    (fun q : G ⟶ (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) T').obj P ↦
      q.hom.app U' z) hb)

private theorem etale_root_pullback_value (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
    (U : T.Etaleᵒᵖ) (z : (T.rootsOfUnitySheaf m).obj.obj U) :
    finiteTateEtaleRootValue T' m _
      (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
        ((finiteEtaleTwistPullbackData A m hm hA).r v hT).hom).hom.app U z) =
      Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue T m U z) := by
  have h := congrArg
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _)
      ((finiteEtaleTwistPullbackData A m hm hA).laws.2.1 v hT)
  rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  unfold upperStarGmSheafToGmSheaf at h
  rw [Equiv.apply_symm_apply] at h
  exact congrArg (fun f ↦ Additive.toMul ((f.hom.app U z).down)) h.symm

/-- Transport of one normalized etale pullback respects the prescribed pro-etale roots.
Source: `lem-amb-finite-tate-normalized-coherence`, pullback generator calculation;
Stacks Tags 03PK, 03Q1, 099R and 0GLZ.
(blueprint: lem-amb-finite-tate-transported-pullback-normalization)

Proof: fix a pro-etale object W over T and tuples x on W and x' on W times_T T'
whose projections to every finite root level agree under pullback. Work at the
single annihilating level r. The comparison of finite root sheaves identifies the
r-th projections with the same units on both sites. Locally on W, the finitely many
finite roots are restrictions of etale roots: use the etale root scheme and its
universal root for each coordinate, take their finite product over T, and refine
W by its resulting pro-etale cover. Restrict the already given tuple x to this
cover, so no new choice of a root-tower lift is required.
The normalization of b identifies the source pure tensor with the image of the
etale generator on this cover. Transpose the displayed composite under the
pro-etale inverse-image adjunction. The canonical comparison/pullback isomorphism
is the mate of the identity between the two restriction direct images; hence its
adjunct carries this generator to the comparison unit applied to the etale
pullback adjunct of c. Its prescribed root formula is hc. The r-th projection of
x' is precisely the pulled-back r-th projection of x, so hb' identifies the last
image with the target pure tensor. Separatedness of the target identifies the two
sections on W times_T T'. In degree zero the tuples are empty and the same mate
calculation is the identity on constant scalars. In positive degrees the formulas
are tensored coordinate by coordinate using the monoidal adjunction; sheafification
and separatedness preserve the equalities. This proof uses finite root projections
only and does not commute inverse image with the infinite root limit. The empty
scheme and zero coefficient ring satisfy the same sheaf identities. -/
theorem finite_tate_transported_pullback_normalized
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (T T' : Scheme.{u}) (v : T' ⟶ T)
    (hT : IsUnit (l : Γ(T, ⊤))) (hT' : IsUnit (l : Γ(T', ⊤)))
    (r : ℕ) (hA : ((l ^ (r + 1) : ℕ) : finiteTateCoefficient l E n) = 0) (k : ℕ)
    (b : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T k)
    (b' : (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').obj
        (finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k) ≅ finiteTateProSheaf l E n T' k)
    (hb : IsFiniteTateSiteComparison l E n T r hA k b)
    (hb' : IsFiniteTateSiteComparison l E n T' r hA k b')
    (c : (Etale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).obj
        (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≅
          finiteEtaleTateTwist T' (l ^ (r + 1)) _ hA k)
    (hc : IsFiniteTateEtalePullback l E n T v r hA k c) :
    IsFiniteTateProPullback l E n T v k
      ((ProEtale.upperStar (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).mapIso b.symm ≪≫
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) v).app
            (finiteEtaleTateTwist T (l ^ (r + 1)) _ hA k) ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (finiteTateCoefficient l E n)) T').mapIso c ≪≫ b') := by
  have _ := hT'
  intro W a x x' hx
  let A := finiteTateCoefficient l E n
  let m := l ^ (r + 1)
  have hm : 0 < m := pow_pos (Fact.out : l.Prime).pos _
  have hTm : IsUnit (m : Γ(T, ⊤)) := by
    simpa only [m, Nat.cast_pow] using hT.pow (r + 1)
  obtain ⟨U, f, z, hz⟩ := finite_root_tuple_presentation l T hT r k W x
  let U' := (MorphismProperty.Over.pullback @Etale ⊤ v).op.obj U
  let W' := (MorphismProperty.Over.pullback @WeaklyEtale ⊤ v).op.obj W
  let f' : W'.unop ⟶ (toProEt T').obj U'.unop :=
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ v).map f
  let z' (i : Fin k) :=
    (((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).homEquiv _ _
      ((finiteEtaleTwistPullbackData A m hm hA).r v hTm).hom).hom.app U (z i))
  have hz' (i : Fin k) : finiteTateEtaleRootValue T' m U' (z' i) =
      Units.map (pullback.fst U.unop.hom v).appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue T m U (z i)) :=
    etale_root_pullback_value A m hm hA v hTm U (z i)
  have hx' (i : Fin k) : finiteTateLimitRootValue l T' r W' (x' i) =
      Units.map f'.left.appTop.hom.toMonoidHom
        (finiteTateEtaleRootValue T' m U' (z' i)) := by
    rw [hx r i, hz i, hz' i]
    have hsq : f'.left ≫ pullback.fst U.unop.hom v =
        pullback.fst W.unop.hom v ≫ f.left := by
      exact pullback.lift_fst _ _ _
    have hv := congrArg (fun q ↦
      Units.map q.appTop.hom.toMonoidHom (finiteTateEtaleRootValue T m U (z i))) hsq
    exact hv.symm
  let F := finiteEtaleTateTwist T m A hA k
  let F' := finiteEtaleTateTwist T' m A hA k
  let P' := finiteTateProSheaf l E n T' k
  let d : (ProEtale.upperStar (ModuleCat.{u + 1} A) v).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F) ⟶ P' :=
    ((ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) v).app F).hom ≫
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T').map c.hom ≫ b'.hom
  let q := (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _ d
  change (((ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) v).homEquiv _ _
    ((ProEtale.upperStar (ModuleCat.{u + 1} A) v).map b.inv ≫ d)).hom.app W)
      (finiteTateProPowerGenerator l E n T W a k x) = _
  rw [Adjunction.homEquiv_naturality_left]
  change q.hom.app W (b.inv.hom.app W
    (finiteTateProPowerGenerator l E n T W a k x)) = _
  let t := finiteTateEtalePowerGenerator T A m hA U a k z
  let η := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F
  have hinv : b.inv.hom.app W (finiteTateProPowerGenerator l E n T W a k x) =
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map f.op
        (η.hom.app U t) := by
    rw [← hb U W f a z x hz]
    exact ConcreteCategory.congr_hom (congrArg (fun h ↦ h.hom.app W) b.hom_inv_id) _
  rw [hinv]
  have hq := ConcreteCategory.congr_hom (q.hom.naturality f.op) (η.hom.app U t)
  simp only [ModuleCat.comp_apply] at hq
  refine hq.trans ?_
  have hu := comparison_pullback_adjunct_unit A v F F' P' c.hom b'.hom U t
  change q.hom.app (op ((toProEt T).obj U.unop)) (η.hom.app U t) = _ at hu
  rw [hu, hc U a z z' hz']
  let t' := finiteTateEtalePowerGenerator T' A m hA U' a k z'
  let η' := (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) T').unit.app F'
  have hb'nat := ConcreteCategory.congr_hom (b'.hom.hom.naturality f'.op)
    (η'.hom.app U' t')
  exact hb'nat.symm.trans (hb' U' W' f' a z' x' hx')

end AlgebraicGeometry.Scheme
