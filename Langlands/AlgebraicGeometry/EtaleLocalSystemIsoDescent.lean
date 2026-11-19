import Langlands.AlgebraicGeometry.EtaleLocalSystemConstantIso
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! # Pullback and gluing of local-system isomorphisms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.EtaleLocalSystem

set_option backward.isDefEq.respectTransparency false

variable {S T U W : Scheme.{u}}
  {F G H : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}} {f : T ⟶ S} {g : U ⟶ S}

/-- A lift of the structure morphism identifies the test object with a restriction object. -/
private def overLiftIso {V : Over S} (a : V.left ⟶ T) (ha : a ≫ f = V.hom) :
    (Over.map f).obj (Over.mk a) ≅ V :=
  Over.isoMk (Iso.refl _) (by simpa using ha.symm)

@[simp] private theorem overLiftIso_hom_left {V : Over S} (a : V.left ⟶ T)
    (ha : a ≫ f = V.hom) : (overLiftIso a ha).hom.left = 𝟙 V.left := rfl

@[simp] private theorem overLiftIso_inv_left {V : Over S} (a : V.left ⟶ T)
    (ha : a ≫ f = V.hom) : (overLiftIso a ha).inv.left = 𝟙 V.left := rfl

/-- Evaluate a restricted isomorphism on a test object given a lift to the restricting base. -/
def isoAtLift (e : restrict f F ≅ restrict f G) {V : Over S}
    (a : V.left ⟶ T) (ha : a ≫ f = V.hom) : F.obj (op V) ≅ G.obj (op V) :=
  F.mapIso (overLiftIso a ha).op ≪≫ e.app (op (Over.mk a)) ≪≫
    (G.mapIso (overLiftIso a ha).op).symm

private theorem isoAtLift_congr (e : restrict f F ≅ restrict f G) {V : Over S}
    {a b : V.left ⟶ T} (ha : a ≫ f = V.hom) (hb : b ≫ f = V.hom) (h : a = b) :
    isoAtLift e a ha = isoAtLift e b hb := by
  subst b
  rfl

private theorem isoAtLift_naturality (e : restrict f F ≅ restrict f G) {V V' : Over S}
    (k : V ⟶ V') (a : V.left ⟶ T) (b : V'.left ⟶ T)
    (ha : a ≫ f = V.hom) (hb : b ≫ f = V'.hom) (hk : k.left ≫ b = a) :
    F.map k.op ≫ (isoAtLift e a ha).hom = (isoAtLift e b hb).hom ≫ G.map k.op := by
  let d : Over.mk a ⟶ Over.mk b := Over.homMk k.left hk
  have h₁ : k.op ≫ (overLiftIso a ha).op.hom =
      (overLiftIso b hb).op.hom ≫ ((Over.map f).map d).op := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change ((overLiftIso a ha).hom ≫ k).left =
      ((Over.map f).map d ≫ (overLiftIso b hb).hom).left
    simp [d]
  have h₂ : ((Over.map f).map d).op ≫ (overLiftIso a ha).op.inv =
      (overLiftIso b hb).op.inv ≫ k.op := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    change ((overLiftIso a ha).inv ≫ (Over.map f).map d).left =
      (k ≫ (overLiftIso b hb).inv).left
    simp [d]
  have h₃ := e.hom.naturality d.op
  change F.map ((Over.map f).map d).op ≫ e.hom.app (op (Over.mk a)) =
    e.hom.app (op (Over.mk b)) ≫ G.map ((Over.map f).map d).op at h₃
  simp only [isoAtLift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← F.map_comp_assoc, h₁, F.map_comp_assoc, reassoc_of% h₃, ← G.map_comp, h₂, G.map_comp]

/-- Pull back an isomorphism of restrictions along a triangle over the original base. -/
def pullIso (e : restrict f F ≅ restrict f G) (a : U ⟶ T) (ha : a ≫ f = g) :
    restrict g F ≅ restrict g G :=
  NatIso.ofComponents
    (fun V => isoAtLift e (V.unop.hom ≫ a) (by simp [Category.assoc, ha]))
    (fun k => isoAtLift_naturality e ((Over.map g).map k.unop) _ _ _ _
      (by simp [← Category.assoc]))

@[simp] theorem pullIso_app (e : restrict f F ≅ restrict f G) (a : U ⟶ T)
    (ha : a ≫ f = g) (V : Over U) :
    (pullIso e a ha).app (op V) =
      isoAtLift e (V.hom ≫ a) (by simp [Category.assoc, ha]) := rfl

private theorem isoAtLift_pullIso (e : restrict f F ≅ restrict f G) (a : U ⟶ T)
    (ha : a ≫ f = g) {V : Over S} (b : V.left ⟶ U) (hb : b ≫ g = V.hom) :
    isoAtLift (pullIso e a ha) b hb =
      isoAtLift e (b ≫ a) (by rw [Category.assoc, ha, hb]) := by
  have h : overLiftIso (b ≫ a) (by rw [Category.assoc, ha, hb]) =
      overLiftIso (V := (Over.map g).obj (Over.mk b)) (b ≫ a)
        (by simp [Category.assoc, ha]) ≪≫ overLiftIso b hb := by
    apply Iso.ext
    apply Over.OverMorphism.ext
    simp
  unfold isoAtLift
  rw [pullIso_app, h, Iso.op_trans, F.mapIso_trans, G.mapIso_trans]
  simp only [isoAtLift, Iso.trans_assoc, Iso.trans_symm, Over.mk_hom]

/-- Equal comparison arrows induce the same pullback isomorphism. -/
theorem pullIso_congr (e : restrict f F ≅ restrict f G) {a b : U ⟶ T}
    (ha : a ≫ f = g) (hb : b ≫ f = g) (h : a = b) :
    pullIso e a ha = pullIso e b hb := by
  subst b
  rfl

@[simp] theorem pullIso_comp (e : restrict f F ≅ restrict f G) (a : U ⟶ T)
    (ha : a ≫ f = g) {h : W ⟶ S} (b : W ⟶ U) (hb : b ≫ g = h) :
    pullIso (pullIso e a ha) b hb =
      pullIso e (b ≫ a) (by rw [Category.assoc, ha, hb]) := by
  apply Iso.ext
  apply NatTrans.ext
  ext1 V
  change ((pullIso (pullIso e a ha) b hb).app (op V.unop)).hom =
    ((pullIso e (b ≫ a) (by rw [Category.assoc, ha, hb])).app (op V.unop)).hom
  rw [pullIso_app, pullIso_app, isoAtLift_pullIso]
  exact congrArg Iso.hom (isoAtLift_congr e _ _ (Category.assoc _ _ _))

@[simp] theorem pullIso_trans (e : restrict f F ≅ restrict f G)
    (e' : restrict f G ≅ restrict f H) (a : U ⟶ T) (ha : a ≫ f = g) :
    pullIso (e ≪≫ e') a ha = pullIso e a ha ≪≫ pullIso e' a ha := by
  apply Iso.ext
  apply NatTrans.ext
  ext1 V
  change ((pullIso (e ≪≫ e') a ha).app (op V.unop)).hom =
    ((pullIso e a ha).app (op V.unop) ≪≫ (pullIso e' a ha).app (op V.unop)).hom
  apply congrArg Iso.hom
  rw [pullIso_app, pullIso_app, pullIso_app]
  simp [isoAtLift]

@[simp] theorem pullIso_symm (e : restrict f F ≅ restrict f G) (a : U ⟶ T)
    (ha : a ≫ f = g) : pullIso e.symm a ha = (pullIso e a ha).symm := by
  apply Iso.ext
  apply NatTrans.ext
  ext1 V
  change ((pullIso e.symm a ha).app (op V.unop)).hom =
    ((pullIso e a ha).app (op V.unop)).symm.hom
  apply congrArg Iso.hom
  rw [pullIso_app, pullIso_app]
  rfl

@[simp] theorem pullIso_restrictIso (e : F ≅ G) (a : U ⟶ T) (ha : a ≫ f = g) :
    pullIso (restrictIso f e) a ha = restrictIso g e := by
  apply Iso.ext
  apply NatTrans.ext
  ext1 V
  change ((pullIso (restrictIso f e) a ha).app (op V.unop)).hom =
    e.hom.app (op ((Over.map g).obj V.unop))
  simp only [pullIso_app, isoAtLift, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    restrictIso, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.mapIso_inv, Functor.op_obj]
  have h := e.hom.naturality (overLiftIso (f := f) (V := (Over.map g).obj V.unop)
    (V.unop.hom ≫ a) (by simp [Category.assoc, ha])).op.hom
  erw [reassoc_of% h]
  simp only [← G.map_comp, Iso.hom_inv_id, G.map_id, Category.comp_id]

section Constants

variable {M N : AddCommGrpCat.{u}}

/-- Pullback of a constant-model isomorphism is pullback of its pointwise family. -/
theorem pullIso_constantIsoOfValues (v : LocallyConstant T (M ≃+ N))
    (a : U ⟶ T) (ha : a ≫ f = g) :
    pullIso (F := constant S M) (G := constant S N) (f := f) (g := g)
      (constantIsoOfValues v) a ha =
      constantIsoOfValues (v.comap ⟨a, a.continuous⟩) := by
  apply Iso.ext
  ext V s
  apply (constantSections U N V.unop).injective
  apply LocallyConstant.ext
  intro x
  let b := V.unop.hom ≫ a
  let e := overLiftIso (f := f) (V := (Over.map g).obj V.unop) b (by
    simp [b, Category.assoc, ha])
  change constantSections S N _ ((constant S N).map e.inv.op
    ((constantIsoOfValues v).hom.app (op (Over.mk b)) ((constant S M).map e.hom.op s))) x =
    constantSections U N V.unop ((constantIsoOfValues (v.comap ⟨a, a.continuous⟩)).hom.app
      (op V.unop) s) x
  simp only [constantSections_map, e, overLiftIso_inv_left]
  change constantSections T N (Over.mk b)
    ((constantHomOfValues (v.map AddEquiv.toAddMonoidHom)).app (op (Over.mk b))
      ((constant S M).map e.hom.op s)) x =
    constantSections U N V.unop
      ((constantHomOfValues ((v.comap ⟨a, a.continuous⟩).map AddEquiv.toAddMonoidHom)).app
        (op V.unop) s) x
  rw [constantHomOfValues_app, constantHomOfValues_app]
  change v (b x) (constantSections S M ((Over.map f).obj (Over.mk b))
    ((constant S M).map e.hom.op s) x) = v (a (V.unop.hom x)) (constantSections U M V.unop s x)
  rw [constantSections_map, overLiftIso_hom_left]
  rfl

end Constants

section Gluing

variable {B : Scheme.{u}} (t : B ⟶ S)
  (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) B)
  (e : ∀ i, restrict (𝒰.f i ≫ t) F ≅ restrict (𝒰.f i ≫ t) G)
  (compat : ∀ i j,
    pullIso (e i) (pullback.fst (𝒰.f i) (𝒰.f j)) rfl =
      pullIso (e j) (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.condition_assoc _).symm)

private theorem mapLift_w {A : Scheme.{u}} {f : A ⟶ B} {V : Over B}
    (a : V.left ⟶ A) (ha : a ≫ f = V.hom) :
    a ≫ f ≫ t = ((Over.map t).obj V).hom := by
  change a ≫ f ≫ t = V.hom ≫ t
  rw [← Category.assoc, ha]

include compat in
private theorem isoAtLift_eq_of_overlap {V : Over B} (i j : 𝒰.I₀)
    (a : V.left ⟶ 𝒰.X i) (b : V.left ⟶ 𝒰.X j)
    (ha : a ≫ 𝒰.f i = V.hom) (hb : b ≫ 𝒰.f j = V.hom) :
    isoAtLift (V := (Over.map t).obj V) (e i) a (mapLift_w t a ha) =
      isoAtLift (V := (Over.map t).obj V) (e j) b (mapLift_w t b hb) := by
  let l := pullback.lift a b (ha.trans hb.symm)
  have hl : l ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i ≫ t =
      ((Over.map t).obj V).hom := by
    rw [pullback.lift_fst_assoc]
    exact mapLift_w t a ha
  have h := congrArg (fun z => isoAtLift (V := (Over.map t).obj V) z l hl) (compat i j)
  rw [isoAtLift_pullIso, isoAtLift_pullIso] at h
  exact (isoAtLift_congr (e i) _ _ (pullback.lift_fst _ _ _).symm).trans
    (h.trans (isoAtLift_congr (e j) _ _ (pullback.lift_snd _ _ _)))

/-- Isomorphisms of restricted étale sheaves glue if they agree on each pairwise overlap. -/
theorem nonempty_iso_of_cover (hF : IsEtaleSheaf F) (hG : IsEtaleSheaf G)
    (compat : ∀ i j,
      pullIso (e i) (pullback.fst (𝒰.f i) (𝒰.f j)) rfl =
        pullIso (e j) (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.condition_assoc _).symm) :
    Nonempty (restrict t F ≅ restrict t G) := by
  let V (i : 𝒰.I₀) := Over.mk (𝒰.f i)
  let P : ObjectProperty (Over B) := fun W => ∃ i, Nonempty (W ⟶ V i)
  have hcover : (topology B).CoversTop V := by
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ Over.mkIdTerminal,
      ← Sieve.ofArrows_eq_ofObjects Over.mkIdTerminal V
        (fun i => Over.mkIdTerminal.from (V i)),
      GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    apply Scheme.mem_grothendieckTopology_iff.mpr
    refine ⟨𝒰, ?_⟩
    rintro _ _ ⟨i⟩
    simpa only [Over.mkIdTerminal_from_left, V, Over.mk_left, Over.mk_hom] using
      (Sieve.ofArrows_mk (fun i => (V i).left)
        (fun i => (Over.mkIdTerminal.from (V i)).left) i)
  let : P.ι.IsCoverDense (topology B) := ⟨fun W => by
    refine (topology B).superset_covering ?_ (hcover W)
    intro T a ha
    exact Presieve.in_coverByImage P.ι (Y := ⟨T, ha⟩) a⟩
  let i (W : P.FullSubcategory) : 𝒰.I₀ := W.property.choose
  let a (W : P.FullSubcategory) : W.obj ⟶ V (i W) := W.property.choose_spec.some
  let localIso : P.ι.op ⋙ restrict t F ≅ P.ι.op ⋙ restrict t G := NatIso.ofComponents
    (fun W => isoAtLift (e (i W.unop)) (a W.unop).left
      (mapLift_w t _ (Over.w (a W.unop))))
    (fun {W Z} k => by
      let b := k.unop.hom.left ≫ (a W.unop).left
      have hb : b ≫ 𝒰.f (i W.unop) = Z.unop.obj.hom := Over.w (k.unop.hom ≫ a W.unop)
      let d := (Over.map t).map k.unop.hom
      change F.map d.op ≫
          (isoAtLift (e (i Z.unop)) (a Z.unop).left (mapLift_w t _ (Over.w (a Z.unop)))).hom =
        (isoAtLift (e (i W.unop)) (a W.unop).left (mapLift_w t _ (Over.w (a W.unop)))).hom ≫
          G.map d.op
      rw [isoAtLift_eq_of_overlap t 𝒰 e compat _ _ _ b (Over.w (a Z.unop)) hb]
      exact isoAtLift_naturality (e (i W.unop)) d _ _ (mapLift_w t _ hb)
        (mapLift_w t _ (Over.w (a W.unop))) rfl)
  exact ⟨Functor.IsCoverDense.presheafIso
    (ℱ := ⟨restrict t F, isEtaleSheaf_restrict t hF⟩)
    (ℱ' := ⟨restrict t G, isEtaleSheaf_restrict t hG⟩) localIso⟩

end Gluing

end Langlands.AlgebraicGeometry.EtaleLocalSystem
