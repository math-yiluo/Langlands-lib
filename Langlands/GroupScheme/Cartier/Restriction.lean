import Langlands.GroupScheme.Cartier.Evaluation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.Cartier
universe u
variable {S : Scheme.{u}}

/-- Base change of a commutative group scheme over `S` to a test scheme `T` over `S`. -/
abbrev testBaseChange (T : Over S) (G : CommGroupScheme S) : CommGroupScheme T.left :=
  (CommGroupScheme.baseChange T.hom).obj G

/-! ### The canonical comparison isomorphisms -/

/-- Pullback along `T'.hom` agrees with pullback along `T.hom` followed by `a.left`. -/
def pullbackCompIso {T T' : Over S} (a : T' ⟶ T) :
    Over.pullback T'.hom ≅ Over.pullback T.hom ⋙ Over.pullback a.left :=
  NatIso.ofComponents
    (fun X => Over.isoMk
      (pullback.congrHom rfl (Over.w a).symm ≪≫
        (pullbackLeftPullbackSndIso X.hom T.hom a.left).symm)
      (by
        dsimp
        simp))
    (by
      intro X Y f
      apply Over.OverMorphism.ext
      dsimp
      apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp
        · simp
      · simp)

/-- The canonical comparison `G_{T'} ≅ (G_T)_{T'}` of group schemes over `T'`. -/
def baseChangeCompIso (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    (testBaseChange T' G).toGrp ≅ (GroupScheme.baseChange a.left).obj (testBaseChange T G).toGrp :=
  (Functor.mapGrpNatIso (pullbackCompIso a)).app G.toGrp ≪≫
    Functor.mapGrpCompIso.app G.toGrp

/-- The canonical projection `G_{T'} = G ×_S T' ⟶ G ×_S T = G_T` over `a`. -/
def baseChangeProj (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    (testBaseChange T' G).X.left ⟶ (testBaseChange T G).X.left :=
  pullback.lift (pullback.fst G.X.hom T'.hom) (pullback.snd G.X.hom T'.hom ≫ a.left)
    (by rw [pullback.condition, Category.assoc, Over.w a])

@[reassoc (attr := simp)]
lemma baseChangeProj_fst (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    baseChangeProj G a ≫ pullback.fst G.X.hom T.hom = pullback.fst G.X.hom T'.hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeProj_snd (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    baseChangeProj G a ≫ pullback.snd G.X.hom T.hom = pullback.snd G.X.hom T'.hom ≫ a.left :=
  pullback.lift_snd _ _ _

lemma baseChangeProj_id (G : CommGroupScheme S) (T : Over S) : baseChangeProj G (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

lemma baseChangeProj_comp (G : CommGroupScheme S) {T T' T'' : Over S} (b : T'' ⟶ T') (a : T' ⟶ T) :
    baseChangeProj G (b ≫ a) = baseChangeProj G b ≫ baseChangeProj G a := by
  apply pullback.hom_ext <;> simp

@[reassoc]
lemma baseChangeCompIso_hom_fst (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    (baseChangeCompIso G a).hom.hom.hom.left ≫
      pullback.fst (pullback.snd G.X.hom T.hom) a.left = baseChangeProj G a := by
  apply pullback.hom_ext
  · simp [baseChangeCompIso, pullbackCompIso, Functor.mapGrpNatIso, Functor.mapGrpCompIso]
  · simp [baseChangeCompIso, pullbackCompIso, Functor.mapGrpNatIso, Functor.mapGrpCompIso,
      pullback.condition]

@[reassoc]
lemma baseChangeCompIso_inv_fst (G : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    (baseChangeCompIso G a).inv.hom.hom.left ≫ pullback.fst G.X.hom T'.hom =
      pullback.fst (pullback.snd G.X.hom T.hom) a.left ≫ pullback.fst G.X.hom T.hom := by
  simp [baseChangeCompIso, pullbackCompIso, Functor.mapGrpNatIso, Functor.mapGrpCompIso]
  exact Category.id_comp _

/-! ### Restriction along test-scheme maps -/

/-- Base change of a homomorphism commutes with the first projection. -/
@[reassoc (attr := simp)]
lemma baseChange_map_fst {G G' : CommGroupScheme S} (T : Over S) (φ : G' ⟶ G) :
    CommGroupScheme.hom ((CommGroupScheme.baseChange T.hom).map φ) ≫
      pullback.fst G.X.hom T.hom =
      pullback.fst G'.X.hom T.hom ≫ CommGroupScheme.hom φ := by
  change ((Over.pullback T.hom).map (CommGroupScheme.groupHom φ).hom.hom).left ≫ _ = _
  simp

/-- Base change of a homomorphism commutes with the second projection. -/
@[reassoc (attr := simp)]
lemma baseChange_map_snd {G G' : CommGroupScheme S} (T : Over S) (φ : G' ⟶ G) :
    CommGroupScheme.hom ((CommGroupScheme.baseChange T.hom).map φ) ≫
      pullback.snd G.X.hom T.hom = pullback.snd G'.X.hom T.hom := by
  change ((Over.pullback T.hom).map (CommGroupScheme.groupHom φ).hom.hom).left ≫ _ = _
  simp

/-- Homomorphisms between base changes are determined by their first projections. -/
lemma relativeHom_ext {G H : CommGroupScheme S} {T : Over S} (f g : RelativeHom G H T)
    (h : CommGroupScheme.hom f ≫ pullback.fst H.X.hom T.hom =
      CommGroupScheme.hom g ≫ pullback.fst H.X.hom T.hom) : f = g := by
  have hf : CommGroupScheme.hom f ≫ pullback.snd H.X.hom T.hom =
      pullback.snd G.X.hom T.hom :=
    Over.w (CommGroupScheme.groupHom f).hom.hom
  have hg : CommGroupScheme.hom g ≫ pullback.snd H.X.hom T.hom =
      pullback.snd G.X.hom T.hom :=
    Over.w (CommGroupScheme.groupHom g).hom.hom
  change Additive.ofMul (CommGroupScheme.groupHom f) =
    Additive.ofMul (CommGroupScheme.groupHom g)
  congr 1
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact pullback.hom_ext h (hf.trans hg.symm)

/-- Restriction of a homomorphism `G_T ⟶ H_T` along `a : T' ⟶ T`: base change along `a`,
conjugated by the canonical comparison isomorphisms. -/
def restrictGrp (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : (testBaseChange T G).toGrp ⟶ (testBaseChange T H).toGrp) :
    (testBaseChange T' G).toGrp ⟶ (testBaseChange T' H).toGrp :=
  (baseChangeCompIso G a).hom ≫ (GroupScheme.baseChange a.left).map χ ≫
    (baseChangeCompIso H a).inv

/-- Restriction along `a : T' ⟶ T`, as a homomorphism of Hom groups. -/
def restrict (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T) :
    RelativeHom G H T →+ RelativeHom G H T' where
  toFun χ := Additive.ofMul (restrictGrp G H a (CommGroupScheme.groupHom χ))
  map_zero' := by
    change Additive.ofMul (restrictGrp G H a 1) = Additive.ofMul 1
    congr 1
    apply Grp.hom_ext
    change (baseChangeCompIso G a).hom.hom.hom ≫
        (Over.pullback a.left).map (1 : (testBaseChange T G).X ⟶ (testBaseChange T H).X) ≫
        (baseChangeCompIso H a).inv.hom.hom = 1
    rw [Functor.map_one, MonObj.one_comp, MonObj.comp_one]
  map_add' χ ψ := by
    change Additive.ofMul (restrictGrp G H a
        (CommGroupScheme.groupHom χ * CommGroupScheme.groupHom ψ)) =
      Additive.ofMul (restrictGrp G H a (CommGroupScheme.groupHom χ) *
        restrictGrp G H a (CommGroupScheme.groupHom ψ))
    congr 1
    apply Grp.hom_ext
    change (baseChangeCompIso G a).hom.hom.hom ≫
        (Over.pullback a.left).map ((CommGroupScheme.groupHom χ).hom.hom *
          (CommGroupScheme.groupHom ψ).hom.hom) ≫
        (baseChangeCompIso H a).inv.hom.hom = _
    rw [Functor.map_mul, MonObj.mul_comp, MonObj.comp_mul]
    rfl

/-- Restriction is base change conjugated by the canonical comparison isomorphisms. -/
lemma restrict_toMul (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) :
    Additive.toMul (restrict G H a χ) = restrictGrp G H a (Additive.toMul χ) := rfl

/-- The defining formula of restriction on first projections. -/
@[reassoc]
lemma restrict_fst (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) :
    CommGroupScheme.hom (restrict G H a χ) ≫ pullback.fst H.X.hom T'.hom =
      baseChangeProj G a ≫ CommGroupScheme.hom χ ≫ pullback.fst H.X.hom T.hom := by
  have h1 := baseChangeCompIso_hom_fst G a
  have h2 := baseChangeCompIso_inv_fst H a
  have h3 : ((Over.pullback a.left).map (CommGroupScheme.groupHom χ).hom.hom).left ≫
      pullback.fst (pullback.snd H.X.hom T.hom) a.left =
      pullback.fst (pullback.snd G.X.hom T.hom) a.left ≫ CommGroupScheme.hom χ :=
    pullback.lift_fst _ _ _
  calc CommGroupScheme.hom (restrict G H a χ) ≫ pullback.fst H.X.hom T'.hom
      = (baseChangeCompIso G a).hom.hom.hom.left ≫
          ((Over.pullback a.left).map (CommGroupScheme.groupHom χ).hom.hom).left ≫
          (baseChangeCompIso H a).inv.hom.hom.left ≫ pullback.fst H.X.hom T'.hom := by
        simp only [← Category.assoc]; rfl
    _ = (baseChangeCompIso G a).hom.hom.hom.left ≫
          (((Over.pullback a.left).map (CommGroupScheme.groupHom χ).hom.hom).left ≫
          pullback.fst (pullback.snd H.X.hom T.hom) a.left) ≫ pullback.fst H.X.hom T.hom := by
        rw [h2]; rfl
    _ = ((baseChangeCompIso G a).hom.hom.hom.left ≫
          pullback.fst (pullback.snd G.X.hom T.hom) a.left) ≫ CommGroupScheme.hom χ ≫
          pullback.fst H.X.hom T.hom := by
        rw [h3]; rfl
    _ = baseChangeProj G a ≫ CommGroupScheme.hom χ ≫ pullback.fst H.X.hom T.hom := by
        rw [h1]

lemma restrict_id (G H : CommGroupScheme S) (T : Over S) (χ : RelativeHom G H T) :
    restrict G H (𝟙 T) χ = χ := by
  apply relativeHom_ext
  rw [restrict_fst, baseChangeProj_id, Category.id_comp]

lemma restrict_comp (G H : CommGroupScheme S) {T T' T'' : Over S} (b : T'' ⟶ T')
    (a : T' ⟶ T) (χ : RelativeHom G H T) :
    restrict G H (b ≫ a) χ = restrict G H b (restrict G H a χ) := by
  apply relativeHom_ext
  rw [restrict_fst, restrict_fst, baseChangeProj_comp, Category.assoc]
  exact congrArg (baseChangeProj G b ≫ ·) (restrict_fst G H a χ).symm

/-- The relative Hom functor `T ↦ Hom_T(G_T, H_T)` on schemes over `S`, with restriction by base
change and the canonical comparison isomorphisms. -/
def relativeHomFunctor (G H : CommGroupScheme S) : (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj T := AddCommGrpCat.of (RelativeHom G H T.unop)
  map a := AddCommGrpCat.ofHom (restrict G H a.unop)
  map_id T := by
    ext χ
    exact restrict_id G H T.unop χ
  map_comp a b := by
    ext χ
    exact restrict_comp G H b.unop a.unop χ

@[simp]
lemma relativeHomFunctor_map_apply (G H : CommGroupScheme S) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) : (relativeHomFunctor G H).map a.op χ = restrict G H a χ := rfl

@[simp]
lemma relativeHomFunctor_obj (G H : CommGroupScheme S) (T : (Over S)ᵒᵖ) :
    ((relativeHomFunctor G H).obj T : Type u) = RelativeHom G H T.unop := rfl

/-! ### Naturality of evaluation in the test scheme -/

/-- The section corresponding to a point has the point as its first projection. -/
@[reassoc (attr := simp)]
lemma sectionPointsEquiv_symm_fst (G : CommGroupScheme S) (T : Over S) (x : T ⟶ G.X) :
    ((sectionPointsEquiv G T).symm x).left ≫ pullback.fst G.X.hom T.hom = x.left := by
  have h := sectionPointsEquiv_left G T ((sectionPointsEquiv G T).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-- The section corresponding to a point is a section of the second projection. -/
@[reassoc (attr := simp)]
lemma sectionPointsEquiv_symm_snd (G : CommGroupScheme S) (T : Over S) (x : T ⟶ G.X) :
    ((sectionPointsEquiv G T).symm x).left ≫ pullback.snd G.X.hom T.hom = 𝟙 T.left :=
  Over.w ((sectionPointsEquiv G T).symm x)

/-- The section of a restricted point maps by the canonical projection to the restriction
of the original section. -/
@[reassoc]
lemma sectionPointsEquiv_symm_comp_baseChangeProj (G : CommGroupScheme S) {T T' : Over S}
    (a : T' ⟶ T) (x : T ⟶ G.X) :
    ((sectionPointsEquiv G T').symm (a ≫ x)).left ≫ baseChangeProj G a =
      a.left ≫ ((sectionPointsEquiv G T).symm x).left := by
  apply pullback.hom_ext
  · simp
  · simp

/-- Evaluation is natural in the test scheme: restricting a relative homomorphism and a point
along `a : T' ⟶ T` restricts the evaluated point. -/
lemma evaluation_restrict {G H : CommGroupScheme S} {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    evaluation (restrict G H a χ) (a ≫ x) = a ≫ evaluation χ x := by
  apply Over.OverMorphism.ext
  simp only [evaluation_def, sectionPointsEquiv_left, Over.comp_left, Category.assoc]
  exact (congrArg (((sectionPointsEquiv G T').symm (a ≫ x)).left ≫ ·)
    (restrict_fst G H a χ)).trans
    (sectionPointsEquiv_symm_comp_baseChangeProj_assoc G a x _)

/-- The torsion-valued evaluation is natural in the test scheme. -/
lemma torsionEvaluation_restrict {G H : CommGroupScheme S} (n : ℤ)
    (h : multiplication G.toGrp n = 1) {T T' : Over S} (a : T' ⟶ T)
    (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    torsionEvaluation n h (restrict G H a χ) (a ≫ x) = a ≫ torsionEvaluation n h χ x := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  rw [torsionEvaluation_ι, Category.assoc, torsionEvaluation_ι, evaluation_restrict]

/-! ### Contravariance in the source group scheme -/

/-- Precomposition with the base change of a homomorphism `φ : G' ⟶ G`. -/
def precompose (H : CommGroupScheme S) {G' G : CommGroupScheme S} (φ : G' ⟶ G) (T : Over S) :
    RelativeHom G H T →+ RelativeHom G' H T :=
  Preadditive.leftComp _ ((CommGroupScheme.baseChange T.hom).map φ)

@[simp]
lemma precompose_apply (H : CommGroupScheme S) {G' G : CommGroupScheme S} (φ : G' ⟶ G)
    (T : Over S) (χ : RelativeHom G H T) :
    precompose H φ T χ = (CommGroupScheme.baseChange T.hom).map φ ≫ χ := rfl

lemma precompose_id (H G : CommGroupScheme S) (T : Over S) (χ : RelativeHom G H T) :
    precompose H (𝟙 G) T χ = χ := by
  rw [precompose_apply, CategoryTheory.Functor.map_id, Category.id_comp]

lemma precompose_comp (H : CommGroupScheme S) {G'' G' G : CommGroupScheme S} (ψ : G'' ⟶ G')
    (φ : G' ⟶ G) (T : Over S) (χ : RelativeHom G H T) :
    precompose H (ψ ≫ φ) T χ = precompose H ψ T (precompose H φ T χ) := by
  simp only [precompose_apply, CategoryTheory.Functor.map_comp, Category.assoc]

/-- The canonical projections are compatible with base-changed homomorphisms. -/
@[reassoc]
lemma baseChange_map_baseChangeProj {G' G : CommGroupScheme S} (φ : G' ⟶ G) {T T' : Over S}
    (a : T' ⟶ T) :
    CommGroupScheme.hom ((CommGroupScheme.baseChange T'.hom).map φ) ≫ baseChangeProj G a =
      baseChangeProj G' a ≫ CommGroupScheme.hom ((CommGroupScheme.baseChange T.hom).map φ) := by
  apply pullback.hom_ext
  · simp
  · simp

/-- Precomposition commutes with restriction along test-scheme maps. -/
lemma restrict_precompose (H : CommGroupScheme S) {G' G : CommGroupScheme S} (φ : G' ⟶ G)
    {T T' : Over S} (a : T' ⟶ T) (χ : RelativeHom G H T) :
    restrict G' H a (precompose H φ T χ) = precompose H φ T' (restrict G H a χ) := by
  apply relativeHom_ext
  rw [restrict_fst]
  simp only [precompose_apply, CommGroupScheme.hom_comp, Category.assoc]
  rw [← baseChange_map_baseChangeProj_assoc]
  exact congrArg (_ ≫ ·) (restrict_fst G H a χ).symm

/-- Precomposition with `φ : G' ⟶ G` as a natural transformation of relative Hom functors. -/
def precomposeNatTrans (H : CommGroupScheme S) {G' G : CommGroupScheme S} (φ : G' ⟶ G) :
    relativeHomFunctor G H ⟶ relativeHomFunctor G' H where
  app T := AddCommGrpCat.ofHom (precompose H φ T.unop)
  naturality T T' a := by
    ext χ
    exact (restrict_precompose H φ a.unop χ).symm

@[simp]
lemma precomposeNatTrans_app_apply (H : CommGroupScheme S) {G' G : CommGroupScheme S}
    (φ : G' ⟶ G) (T : Over S) (χ : RelativeHom G H T) :
    (precomposeNatTrans H φ).app (op T) χ = precompose H φ T χ := rfl

lemma precomposeNatTrans_id (H G : CommGroupScheme S) :
    precomposeNatTrans H (𝟙 G) = 𝟙 (relativeHomFunctor G H) := by
  ext T χ
  exact precompose_id H G T.unop χ

lemma precomposeNatTrans_comp (H : CommGroupScheme S) {G'' G' G : CommGroupScheme S}
    (ψ : G'' ⟶ G') (φ : G' ⟶ G) :
    precomposeNatTrans H (ψ ≫ φ) = precomposeNatTrans H φ ≫ precomposeNatTrans H ψ := by
  ext T χ
  exact precompose_comp H ψ φ T.unop χ

/-- The relative Hom functor into `H`, contravariant in the source group scheme and in the
test scheme. -/
def relativeHomBifunctor (H : CommGroupScheme S) :
    (CommGroupScheme S)ᵒᵖ ⥤ (Over S)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj G := relativeHomFunctor G.unop H
  map φ := precomposeNatTrans H φ.unop
  map_id G := precomposeNatTrans_id H G.unop
  map_comp φ ψ := precomposeNatTrans_comp H ψ.unop φ.unop

/-- The torsion-valued evaluation is compatible with precomposition. -/
lemma torsionEvaluation_precompose (H : CommGroupScheme S) {G' G : CommGroupScheme S}
    (φ : G' ⟶ G) (n : ℤ) (h : multiplication G.toGrp n = 1)
    (h' : multiplication G'.toGrp n = 1) {T : Over S} (χ : RelativeHom G H T)
    (x : T ⟶ G'.X) :
    torsionEvaluation n h' (precompose H φ T χ) x =
      torsionEvaluation n h χ (x ≫ φ.toMul.hom.hom) := by
  apply (cancel_mono (torsionι H.toGrp n).hom.hom).mp
  rw [torsionEvaluation_ι, torsionEvaluation_ι]
  exact evaluation_precompose φ χ x

end Langlands.GroupScheme.Cartier
