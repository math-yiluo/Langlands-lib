import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.GeometricFibreComponentGeometry

/-! # Points under a change of relative base -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Topology

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace RestrictionPoints

variable {S T : Scheme.{u}} {F G : Presheaf S}

def sectionPair {U : Over S} (x : F.obj (op U)) (y : G.obj (op U)) :
    (F ⨯ G).obj (op U) :=
  uliftYonedaEquiv.{u + 1}
    (prod.lift (uliftYonedaEquiv.{u + 1}.symm x)
      (uliftYonedaEquiv.{u + 1}.symm y))

@[simp]
theorem fst_sectionPair {U : Over S} (x : F.obj (op U)) (y : G.obj (op U)) :
    (prod.fst (X := F) (Y := G)).app (op U) (sectionPair x y) = x := by
  change uliftYonedaEquiv.{u + 1} (_ ≫ prod.fst) = x
  simp

@[simp]
theorem snd_sectionPair {U : Over S} (x : F.obj (op U)) (y : G.obj (op U)) :
    (prod.snd (X := F) (Y := G)).app (op U) (sectionPair x y) = y := by
  change uliftYonedaEquiv.{u + 1} (_ ≫ prod.snd) = y
  simp

theorem section_ext {U : Over S} (x y : (F ⨯ G).obj (op U))
    (h₁ : (prod.fst (X := F) (Y := G)).app (op U) x =
      (prod.fst (X := F) (Y := G)).app (op U) y)
    (h₂ : (prod.snd (X := F) (Y := G)).app (op U) x =
      (prod.snd (X := F) (Y := G)).app (op U) y) : x = y := by
  apply uliftYonedaEquiv.{u + 1}.symm.injective
  apply prod.hom_ext
  · apply uliftYonedaEquiv.{u + 1}.injective
    simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using h₁
  · apply uliftYonedaEquiv.{u + 1}.injective
    simpa only [uliftYonedaEquiv_comp, Equiv.apply_symm_apply] using h₂

@[simp]
theorem map_sectionPair {U V : Over S} (f : V ⟶ U)
    (x : F.obj (op U)) (y : G.obj (op U)) :
    (F ⨯ G).map f.op (sectionPair x y) =
      sectionPair (F.map f.op x) (G.map f.op y) := by
  apply section_ext
  · rw [(prod.fst (X := F) (Y := G)).naturality_apply, fst_sectionPair,
      fst_sectionPair]
  · rw [(prod.snd (X := F) (Y := G)).naturality_apply, snd_sectionPair,
      snd_sectionPair]

/-- A field point over T is a product point over S, retaining its structure map to T. -/
def toProduct (g : T ⟶ S) (p : FieldPoint ((restrictPresheaf g).obj F)) :
    FieldPoint (F ⨯ (schemeYoneda S).obj (Over.mk g)) where
  field := p.field
  base := p.base ≫ g
  val := sectionPair p.val (ULift.up (Over.homMk p.base rfl))

theorem toProduct_rel (g : T ⟶ S)
    {p q : FieldPoint ((restrictPresheaf g).obj F)}
    (h : FieldPoint.Rel _ p q) :
    FieldPoint.Rel _ (toProduct g p) (toProduct g q) := by
  obtain ⟨Ω, _, i, j, hb, he⟩ := h
  have hb' : Spec.map (CommRingCat.ofHom j) ≫ q.base ≫ g =
      Spec.map (CommRingCat.ofHom i) ≫ p.base ≫ g := by
    rw [← Category.assoc, hb, Category.assoc]
  refine ⟨Ω, inferInstance, i, j, hb', ?_⟩
  dsimp only [toProduct]
  rw [map_sectionPair, map_sectionPair]
  apply section_ext
  · simp only [fst_sectionPair]
    let c : (toProduct g p).extendTest i ⟶ (Over.map g).obj (p.extendTest i) :=
      Over.homMk (𝟙 _) (by simp [toProduct, Category.assoc])
    change F.map ((Over.map g).map (p.extendMap i)).op p.val =
      F.map ((Over.map g).map
        (Over.homMk (Spec.map (CommRingCat.ofHom j)) hb)).op q.val at he
    have hc := congrArg (fun x => F.map c.op x) he
    simp only [← Functor.map_comp_apply, ← op_comp] at hc
    convert hc using 1 <;> congr 2
  · simp only [snd_sectionPair]
    exact congrArg ULift.up (Over.OverMorphism.ext hb.symm)

def productStructure (g : T ⟶ S)
    (p : FieldPoint (F ⨯ (schemeYoneda S).obj (Over.mk g))) :
    Over.mk p.base ⟶ Over.mk g :=
  ((prod.snd (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).app _ p.val).down

@[simp]
theorem productStructure_toProduct (g : T ⟶ S)
    (p : FieldPoint ((restrictPresheaf g).obj F)) :
    productStructure g (toProduct g p) = Over.homMk p.base rfl := by
  dsimp only [productStructure, toProduct]
  rw [snd_sectionPair]

def fromProductMap (g : T ⟶ S)
    (p : FieldPoint (F ⨯ (schemeYoneda S).obj (Over.mk g))) :
    (Over.map g).obj (Over.mk (productStructure g p).left) ⟶ Over.mk p.base :=
  Over.homMk (𝟙 _) (by simpa using (productStructure g p).w.symm)

/-- The represented factor of a product point gives its structure morphism to T. -/
def fromProduct (g : T ⟶ S)
    (p : FieldPoint (F ⨯ (schemeYoneda S).obj (Over.mk g))) :
    FieldPoint ((restrictPresheaf g).obj F) where
  field := p.field
  base := (productStructure g p).left
  val := F.map (fromProductMap g p).op
    ((prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).app _ p.val)

theorem fromProduct_rel (g : T ⟶ S)
    {p q : FieldPoint (F ⨯ (schemeYoneda S).obj (Over.mk g))}
    (h : FieldPoint.Rel _ p q) :
    FieldPoint.Rel _ (fromProduct g p) (fromProduct g q) := by
  obtain ⟨Ω, _, i, j, hb, he⟩ := h
  let π₁ := prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))
  let π₂ := prod.snd (X := F) (Y := (schemeYoneda S).obj (Over.mk g))
  have hv := congrArg (fun x => π₁.app _ x) he
  have hs := congrArg (fun x => (π₂.app _ x).down.left) he
  rw [π₁.naturality_apply, π₁.naturality_apply] at hv
  simp only [π₂.naturality_apply] at hs
  have hbT : Spec.map (CommRingCat.ofHom j) ≫ (productStructure g q).left =
      Spec.map (CommRingCat.ofHom i) ≫ (productStructure g p).left := hs.symm
  refine ⟨Ω, inferInstance, i, j, hbT, ?_⟩
  let c : (Over.map g).obj ((fromProduct g p).extendTest i) ⟶ p.extendTest i :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom i) ≫ p.base =
        (Spec.map (CommRingCat.ofHom i) ≫ (productStructure g p).left) ≫ g
      rw [Category.id_comp, Category.assoc]
      exact congrArg (fun k => Spec.map (CommRingCat.ofHom i) ≫ k)
        (productStructure g p).w.symm)
  have hc := congrArg (fun x => F.map c.op x) hv
  dsimp only [fromProduct]
  change F.map ((Over.map g).map _).op (F.map _ _)=
    F.map ((Over.map g).map _).op (F.map _ _)
  simp only [← Functor.map_comp_apply, ← op_comp] at hc ⊢
  convert hc using 1 <;> congr 2

theorem fromProduct_toProduct_rel (g : T ⟶ S)
    (p : FieldPoint ((restrictPresheaf g).obj F)) :
    FieldPoint.Rel _ (fromProduct g (toProduct g p)) p := by
  let q := fromProduct g (toProduct g p)
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id p.field)) = 𝟙 _ := Spec.map_id _
  have hb : Spec.map (CommRingCat.ofHom (RingHom.id p.field)) ≫ p.base =
      Spec.map (CommRingCat.ofHom (RingHom.id p.field)) ≫ q.base := by
    rw [hid, Category.id_comp, Category.id_comp]
    exact (congrArg CommaMorphism.left (productStructure_toProduct g p)).symm
  refine ⟨p.field, inferInstance, RingHom.id _, RingHom.id _, hb, ?_⟩
  change F.map ((Over.map g).map (q.extendMap (RingHom.id _))).op
      (F.map (fromProductMap g (toProduct g p)).op
        ((prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).app _
          (sectionPair p.val (ULift.up (Over.homMk p.base rfl))))) = _
  rw [fst_sectionPair]
  let d : q.extendTest (RingHom.id _) ⟶ Over.mk p.base :=
    Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.id p.field))) hb
  have hcomp : (Over.map g).map (q.extendMap (RingHom.id _)) ≫
      fromProductMap g (toProduct g p) =
      (Over.map g).map d := by
    apply Over.OverMorphism.ext
    simp [fromProductMap, d, toProduct]
  exact (F.map_comp_apply (fromProductMap g (toProduct g p)).op
    ((Over.map g).map (q.extendMap (RingHom.id _))).op p.val).symm.trans
      (congrArg (fun k => F.map k.op p.val) hcomp)

theorem toProduct_fromProduct_rel (g : T ⟶ S)
    (p : FieldPoint (F ⨯ (schemeYoneda S).obj (Over.mk g))) :
    FieldPoint.Rel _ (toProduct g (fromProduct g p)) p := by
  let q := toProduct g (fromProduct g p)
  have hid : Spec.map (CommRingCat.ofHom (RingHom.id p.field)) = 𝟙 _ := Spec.map_id _
  have hb : Spec.map (CommRingCat.ofHom (RingHom.id p.field)) ≫ p.base =
      Spec.map (CommRingCat.ofHom (RingHom.id p.field)) ≫ q.base := by
    simpa only [hid, Category.id_comp, q, toProduct, fromProduct, Over.mk_hom] using
      (productStructure g p).w.symm
  refine ⟨p.field, inferInstance, RingHom.id _, RingHom.id _, hb, ?_⟩
  change (F ⨯ (schemeYoneda S).obj (Over.mk g)).map
      (q.extendMap (RingHom.id _)).op
      (sectionPair (fromProduct g p).val
        (ULift.up (Over.homMk (productStructure g p).left rfl))) = _
  rw [map_sectionPair]
  apply section_ext
  · rw [fst_sectionPair]
    rw [(prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).naturality_apply]
    change F.map (q.extendMap (RingHom.id _)).op
      (F.map (fromProductMap g p).op
        ((prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).app _ p.val)) = _
    have hcomp : q.extendMap (RingHom.id _) ≫ fromProductMap g p =
        Over.homMk (Spec.map (CommRingCat.ofHom (RingHom.id p.field))) hb := by
      apply Over.OverMorphism.ext
      simp [fromProductMap]
    exact (F.map_comp_apply (fromProductMap g p).op (q.extendMap (RingHom.id _)).op
      ((prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).app _ p.val)).symm.trans
        (congrArg (fun k => F.map k.op
          ((prod.fst (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).app _ p.val)) hcomp)
  · rw [snd_sectionPair]
    rw [(prod.snd (X := F) (Y := (schemeYoneda S).obj (Over.mk g))).naturality_apply]
    apply ULift.ext
    apply Over.OverMorphism.ext
    rfl

/-- The quotient point sets agree for restriction and represented product. -/
def equiv (g : T ⟶ S) (F : Presheaf S) :
    Points ((restrictPresheaf g).obj F) ≃
      Points (F ⨯ (schemeYoneda S).obj (Over.mk g)) where
  toFun := Quot.lift (fun p => Quot.mk _ (toProduct g p))
    (fun _ _ h => Quot.sound (toProduct_rel g h))
  invFun := Quot.lift (fun p => Quot.mk _ (fromProduct g p))
    (fun _ _ h => Quot.sound (fromProduct_rel g h))
  left_inv x := by
    induction x using Quot.ind with
    | _ p => exact Quot.sound (fromProduct_toProduct_rel g p)
  right_inv x := by
    induction x using Quot.ind with
    | _ p => exact Quot.sound (toProduct_fromProduct_rel g p)

/-- The two chart constructions have the same underlying pullback scheme. -/
def chartIso (g : T ⟶ S) (U : Over S) :
    (Over.map g).obj ((Over.pullback g).obj U) ≅ U ⨯ Over.mk g :=
  Over.isoMk (Over.prodLeftIsoPullback U (Over.mk g)).symm (by
    rw [← (prod.snd (X := U) (Y := Over.mk g)).w, ← Category.assoc]
    exact congrArg (fun k => k ≫ g) (Over.prodLeftIsoPullback_inv_snd U (Over.mk g)))

@[simp]
theorem chartIso_hom_fst (g : T ⟶ S) (U : Over S) :
    (chartIso g U).hom.left ≫ (prod.fst (X := U) (Y := Over.mk g)).left =
      Limits.pullback.fst U.hom g := by
  simp [chartIso]

@[simp]
theorem chartIso_hom_snd (g : T ⟶ S) (U : Over S) :
    (chartIso g U).hom.left ≫ (prod.snd (X := U) (Y := Over.mk g)).left =
      Limits.pullback.snd U.hom g := by
  simp [chartIso]

theorem toProduct_restrictAtlas (g : T ⟶ S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F)
    (p : FieldPoint ((schemeYoneda T).obj ((Over.pullback g).obj U))) :
    toProduct g (p.map (restrictAtlas g a)) =
      (FieldPoint.map (productAtlasMap a (Over.mk g))
        { field := p.field
          base := p.base ≫ g
          val := ULift.up ((Over.map g).map p.val.down ≫ (chartIso g U).hom) }) := by
  dsimp only [toProduct, FieldPoint.map]
  congr 1
  apply section_ext
  · rw [fst_sectionPair]
    change _ = ((prodComparison (schemeYoneda S) U (Over.mk g) ≫
      prod.map a (𝟙 _) ≫ prod.fst).app _ _)
    simp only [prod.map_fst, prodComparison_fst_assoc]
    change a.app _ _ = a.app _ _
    apply congrArg (a.app (op (Over.mk (p.base ≫ g))))
    apply ULift.ext
    apply Over.OverMorphism.ext
    change p.val.down.left ≫ Limits.pullback.fst U.hom g =
      (p.val.down.left ≫ (chartIso g U).hom.left) ≫
        (prod.fst (X := U) (Y := Over.mk g)).left
    rw [Category.assoc, chartIso_hom_fst]
  · rw [snd_sectionPair]
    change _ = ((prodComparison (schemeYoneda S) U (Over.mk g) ≫
      prod.map a (𝟙 _) ≫ prod.snd).app _ _)
    simp only [prod.map_snd, Category.comp_id, prodComparison_snd]
    apply ULift.ext
    apply Over.OverMorphism.ext
    change p.base = (p.val.down.left ≫ (chartIso g U).hom.left) ≫
      (prod.snd (X := U) (Y := Over.mk g)).left
    rw [Category.assoc, chartIso_hom_snd]
    exact p.val.down.w.symm

/-- The point equivalence commutes with the two actual base-changed charts. -/
theorem equiv_chartPointMap (g : T ⟶ S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (x : ((Over.pullback g).obj U).left) :
    equiv g F (chartPointMap (restrictAtlas g a) x) =
      chartPointMap (productAtlasMap a (Over.mk g)) ((chartIso g U).hom.left x) := by
  let W := (Over.pullback g).obj U
  let p : FieldPoint ((schemeYoneda T).obj W) :=
    ⟨W.left.residueField x, W.left.fromSpecResidueField x ≫ W.hom,
      ULift.up (Over.homMk (W.left.fromSpecResidueField x) rfl)⟩
  let q : FieldPoint ((schemeYoneda S).obj (U ⨯ Over.mk g)) :=
    ⟨p.field, p.base ≫ g,
      ULift.up ((Over.map g).map p.val.down ≫ (chartIso g U).hom)⟩
  have hq : q.schemeValue = (chartIso g U).hom.left x := by
    change (chartIso g U).hom.left
      (W.left.fromSpecResidueField x (IsLocalRing.closedPoint _)) = _
    rw [Scheme.fromSpecResidueField_apply]
  change Quot.mk _ (toProduct g (p.map (restrictAtlas g a))) = _
  rw [toProduct_restrictAtlas]
  change Points.map (productAtlasMap a (Over.mk g)) (Quot.mk _ q) = _
  rw [← schemePoint_schemeValue q, hq]
  rfl

theorem equiv_symm_chartPointMap (g : T ⟶ S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (x : (U ⨯ Over.mk g).left) :
    (equiv g F).symm (chartPointMap (productAtlasMap a (Over.mk g)) x) =
      chartPointMap (restrictAtlas g a) ((chartIso g U).inv.left x) := by
  apply (equiv g F).injective
  rw [Equiv.apply_symm_apply, equiv_chartPointMap]
  congr 1
  have h := congrArg CommaMorphism.left (chartIso g U).inv_hom_id
  exact (congrArg (fun f : (U ⨯ Over.mk g).left ⟶ (U ⨯ Over.mk g).left => f x) h).symm

/-- A surjective étale atlas makes the cross-base point equivalence a homeomorphism. -/
def homeomorph (g : T ⟶ S) {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ F) (ha : IsEtale a) (hs : IsSurjective a) :
    letI := pointTopology ((restrictPresheaf g).obj F)
    letI := pointTopology (F ⨯ (schemeYoneda S).obj (Over.mk g))
    Points ((restrictPresheaf g).obj F) ≃ₜ
      Points (F ⨯ (schemeYoneda S).obj (Over.mk g)) := by
  letI := pointTopology ((restrictPresheaf g).obj F)
  letI := pointTopology (F ⨯ (schemeYoneda S).obj (Over.mk g))
  refine
    { toEquiv := equiv g F
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (isQuotientMap_chartPointMap (restrictAtlas g a)
      (relative_restrictAtlas _ ha) (relative_restrictAtlas _ hs)).continuous_iff.mpr
    change Continuous (equiv g F ∘ chartPointMap (restrictAtlas g a))
    have heq : equiv g F ∘ chartPointMap (restrictAtlas g a) =
        chartPointMap (productAtlasMap a (Over.mk g)) ∘ (chartIso g U).hom.left := by
      funext x
      exact equiv_chartPointMap g a x
    rw [heq]
    exact (continuous_schemePoint_chart _ (isEtale_productAtlasMap a ha (Over.mk g))).comp
      (chartIso g U).hom.left.continuous
  · apply (isQuotientMap_chartPointMap (productAtlasMap a (Over.mk g))
      (isEtale_productAtlasMap a ha _) (isSurjective_productAtlasMap a hs _)).continuous_iff.mpr
    change Continuous ((equiv g F).symm ∘ chartPointMap (productAtlasMap a (Over.mk g)))
    have heq : (equiv g F).symm ∘ chartPointMap (productAtlasMap a (Over.mk g)) =
        chartPointMap (restrictAtlas g a) ∘ (chartIso g U).inv.left := by
      funext x
      exact equiv_symm_chartPointMap g a x
    rw [heq]
    exact (continuous_schemePoint_chart _ (relative_restrictAtlas _ ha)).comp
      (chartIso g U).inv.left.continuous

end RestrictionPoints

variable {S T : Scheme.{u}}

/-- Relative base change and represented product have the same actual point topology. -/
def baseChangePointsHomeomorph (g : T ⟶ S) (X : AlgebraicSpace S) :
    letI := pointTopology (baseChange g X).presheaf
    letI := pointTopology (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk g))
    Points (baseChange g X).presheaf ≃ₜ
      Points (X.presheaf ⨯ (schemeYoneda S).obj (Over.mk g)) := by
  let a := X.property.2.choose_spec.choose
  exact RestrictionPoints.homeomorph g a
    X.property.2.choose_spec.choose_spec.1 X.property.2.choose_spec.choose_spec.2

end Langlands.AlgebraicGeometry.AlgebraicSpace
