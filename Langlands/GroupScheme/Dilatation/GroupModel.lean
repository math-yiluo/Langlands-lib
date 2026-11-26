import Langlands.GroupScheme.Dilatation.Affine
import Langlands.GroupScheme.IntegralModelReduction
import Langlands.GroupScheme.UnitSubgroup
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Dilatations of affine integral group models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme.Dilatation

universe u

section Group

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {J : Ideal R} {r : R} (hr : r ≠ 0) (hJ : J = Ideal.span {r})
  {X : GroupScheme (Spec (CommRingCat.of R))} [IsAffine X.X.left] [Flat X.X.hom]
  {Y : GroupScheme (Spec (CommRingCat.of (R ⧸ J)))}
  (j : Y ⟶ (baseChange (quotientBase J)).obj X) [IsClosedImmersion j.hom.hom.left]

local notation "F" => Over.pullback (quotientBase J)
local notation "D" => affineDilatation r j.hom.hom
local notation "d" => affineDilatationHom r j.hom.hom

private instance tensor_flat {S : Scheme.{u}} (T U : Over S) [Flat T.hom] [Flat U.hom] :
    Flat (T ⊗ U).hom := by
  change Flat (pullback.fst T.hom U.hom ≫ T.hom)
  infer_instance

private instance tensor_affine (T U : Over (Spec (CommRingCat.of R)))
    [IsAffine T.left] [IsAffine U.left] : IsAffine (T ⊗ U).left := by
  change IsAffine (pullback T.hom U.hom)
  infer_instance

private instance unit_flat : Flat (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
  change Flat (𝟙 (Spec (CommRingCat.of R)))
  infer_instance

private instance unit_affine : IsAffine (𝟙_ (Over (Spec (CommRingCat.of R)))).left := by
  change IsAffine (Spec (CommRingCat.of R))
  infer_instance

private def lift {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] [Flat T.hom]
    (f : T ⟶ X.X) (hf : ∃ g : (F).obj T ⟶ Y.X, g ≫ j.hom.hom = (F).map f) : T ⟶ D :=
  ((affineDilatation_lift_iff j.hom.hom hr hJ f).mpr hf).exists.choose

omit [Flat X.X.hom] in
@[reassoc (attr := simp)] private theorem lift_fac {T : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [Flat T.hom] (f : T ⟶ X.X)
    (hf : ∃ g : (F).obj T ⟶ Y.X, g ≫ j.hom.hom = (F).map f) : lift hr hJ j f hf ≫ d = f :=
  ((affineDilatation_lift_iff j.hom.hom hr hJ f).mpr hf).exists.choose_spec

include hr hJ in
/-- The reduction of the dilatation map factors through the actual centre. -/
theorem quotient_factors : ∃ g : (F).obj D ⟶ Y.X, g ≫ j.hom.hom = (F).map d := by
  apply (affineDilatation_lift_iff j.hom.hom hr hJ d).mp
  exact ⟨𝟙 D, by simp, fun _ h => affineDilatationHom_injective j.hom.hom hr (by simpa using h)⟩

omit [IsDedekindDomain R] [IsAffine X.X.left] [Flat X.X.hom]
  [IsClosedImmersion j.hom.hom.left] in
private theorem reduce_one (T : Over (Spec (CommRingCat.of R))) :
    ∃ g : (F).obj T ⟶ Y.X, g ≫ j.hom.hom = (F).map (1 : T ⟶ X.X) :=
  ⟨1, by rw [MonObj.one_comp, Functor.map_one]⟩

omit [IsDedekindDomain R] [IsAffine X.X.left] [Flat X.X.hom]
  [IsClosedImmersion j.hom.hom.left] in
private theorem reduce_inv {T : Over (Spec (CommRingCat.of R))} (f : T ⟶ X.X)
    (hf : ∃ g : (F).obj T ⟶ Y.X, g ≫ j.hom.hom = (F).map f) :
    ∃ g : (F).obj T ⟶ Y.X, g ≫ j.hom.hom = (F).map f⁻¹ := by
  obtain ⟨g, hg⟩ := hf
  exact ⟨g⁻¹, by rw [GrpObj.inv_comp, hg, Functor.map_inv']⟩

omit [IsDedekindDomain R] [IsAffine X.X.left] [Flat X.X.hom]
  [IsClosedImmersion j.hom.hom.left] in
private theorem reduce_mul {T : Over (Spec (CommRingCat.of R))} (f g : T ⟶ X.X)
    (hf : ∃ a : (F).obj T ⟶ Y.X, a ≫ j.hom.hom = (F).map f)
    (hg : ∃ a : (F).obj T ⟶ Y.X, a ≫ j.hom.hom = (F).map g) :
    ∃ a : (F).obj T ⟶ Y.X, a ≫ j.hom.hom = (F).map (f * g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a * b, by rw [MonObj.mul_comp, ha, hb, Functor.map_mul]⟩

include hr hJ in
private theorem reduce_comp {T : Over (Spec (CommRingCat.of R))} (f : T ⟶ D) :
    ∃ g : (F).obj T ⟶ Y.X, g ≫ j.hom.hom = (F).map (f ≫ d) := by
  obtain ⟨g, hg⟩ := quotient_factors hr hJ j
  exact ⟨(F).map f ≫ g, by rw [Category.assoc, hg, (F).map_comp]⟩

private def liftedOne : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ D :=
  lift hr hJ j 1 (reduce_one j _)

private def liftedInv : D ⟶ D :=
  lift hr hJ j d⁻¹ (reduce_inv j d (quotient_factors hr hJ j))

private def liftedMul : D ⊗ D ⟶ D :=
  lift hr hJ j ((fst D D ≫ d) * (snd D D ≫ d))
    (reduce_mul j _ _ (reduce_comp hr hJ j (fst D D)) (reduce_comp hr hJ j (snd D D)))

omit [Flat X.X.hom] in
@[simp, reassoc] private theorem liftedOne_fac : liftedOne hr hJ j ≫ d = 1 :=
  lift_fac hr hJ j _ _

@[simp, reassoc] private theorem liftedInv_fac : liftedInv hr hJ j ≫ d = d⁻¹ :=
  lift_fac hr hJ j _ _

@[simp, reassoc] private theorem liftedMul_fac : liftedMul hr hJ j ≫ d =
    (fst D D ≫ d) * (snd D D ≫ d) := lift_fac hr hJ j _ _

set_option maxHeartbeats 800000 in
/-- The group law is the unique lift of the original operations from flat affine products. -/
@[instance_reducible] def dilatationGroupObj : GrpObj D where
  one := liftedOne hr hJ j
  mul := liftedMul hr hJ j
  inv := liftedInv hr hJ j
  one_mul := by
    apply affineDilatationHom_injective j.hom.hom hr
    simp only [Category.assoc, liftedMul_fac, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, liftedOne_fac, MonObj.comp_one, one_mul, leftUnitor_hom]
  mul_one := by
    apply affineDilatationHom_injective j.hom.hom hr
    simp only [Category.assoc, liftedMul_fac, MonObj.comp_mul, whiskerLeft_fst_assoc,
      whiskerLeft_snd_assoc, liftedOne_fac, MonObj.comp_one, mul_one, rightUnitor_hom]
  mul_assoc := by
    apply affineDilatationHom_injective j.hom.hom hr
    simp only [Category.assoc, liftedMul_fac, MonObj.comp_mul, whiskerRight_fst_assoc,
      whiskerRight_snd_assoc, whiskerLeft_fst_assoc, whiskerLeft_snd_assoc,
      associator_hom_fst_assoc, associator_hom_snd_fst_assoc, associator_hom_snd_snd_assoc,
      mul_assoc]
  left_inv := by
    apply affineDilatationHom_injective j.hom.hom hr
    simp only [Category.assoc, liftedMul_fac, MonObj.comp_mul, lift_fst_assoc,
      lift_snd_assoc, Category.id_comp, liftedInv_fac, liftedOne_fac, MonObj.comp_one,
      inv_mul_cancel]
  right_inv := by
    apply affineDilatationHom_injective j.hom.hom hr
    simp only [Category.assoc, liftedMul_fac, MonObj.comp_mul, lift_fst_assoc,
      lift_snd_assoc, Category.id_comp, liftedInv_fac, liftedOne_fac, MonObj.comp_one,
      mul_inv_cancel]

/-- The actual group scheme on the affine dilatation. -/
def dilatationGroup : GroupScheme (Spec (CommRingCat.of R)) :=
  { X := D, grp := dilatationGroupObj hr hJ j }

/-- The dilatation map is a group-scheme homomorphism. -/
def dilatationGroupHom : dilatationGroup hr hJ j ⟶ X := by
  refine Grp.homMk'' d ?_ ?_
  · change liftedOne hr hJ j ≫ d = η[X.X]
    rw [liftedOne_fac, MonObj.one_eq_one]
  · change liftedMul hr hJ j ≫ d = (d ⊗ₘ d) ≫ μ[X.X]
    rw [liftedMul_fac, MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]

variable {T : GroupScheme (Spec (CommRingCat.of R))} [IsAffine T.X.left] [Flat T.X.hom]

/-- A group homomorphism from a flat affine group scheme has a unique homomorphic lift
whenever its reduction factors through the centre as a scheme map. -/
theorem existsUnique_dilatationGroupHom (f : T ⟶ X)
    (hf : ∃ g : (F).obj T.X ⟶ Y.X, g ≫ j.hom.hom = (F).map f.hom.hom) :
    ∃! g : T ⟶ dilatationGroup hr hJ j, g ≫ dilatationGroupHom hr hJ j = f := by
  let l := lift hr hJ j f.hom.hom hf
  have hl : l ≫ d = f.hom.hom := lift_fac hr hJ j _ _
  let g : T ⟶ dilatationGroup hr hJ j := Grp.homMk'' l
    (by
      apply affineDilatationHom_injective j.hom.hom hr
      change (η[T.X] ≫ l) ≫ d = liftedOne hr hJ j ≫ d
      rw [Category.assoc, hl, liftedOne_fac, MonObj.one_eq_one T.X, MonObj.one_comp])
    (by
      apply affineDilatationHom_injective j.hom.hom hr
      change (μ[T.X] ≫ l) ≫ d = ((l ⊗ₘ l) ≫ liftedMul hr hJ j) ≫ d
      simp only [Category.assoc, hl, liftedMul_fac, MonObj.comp_mul, tensorHom_fst_assoc,
        tensorHom_snd_assoc]
      rw [MonObj.mul_eq_mul, MonObj.mul_comp])
  refine ⟨g, Grp.hom_ext _ _ hl, ?_⟩
  intro g' hg'
  apply Grp.hom_ext
  apply affineDilatationHom_injective j.hom.hom hr
  exact (congrArg (fun h : T ⟶ X => h.hom.hom) hg').trans hl.symm

/-- A flat affine group scheme satisfying the same lifting property is uniquely isomorphic
 to the dilatation over the original group. -/
theorem existsUnique_dilatationGroupIso (p : T ⟶ X)
    (hp : ∀ (U : Over (Spec (CommRingCat.of R))) [IsAffine U.left] [Flat U.hom] (f : U ⟶ X.X),
      (∃! g : U ⟶ T.X, g ≫ p.hom.hom = f) ↔
        ∃ q : (F).obj U ⟶ Y.X, q ≫ j.hom.hom = (F).map f)
    (hinj : Function.Injective (fun f : T.X ⟶ T.X => f ≫ p.hom.hom)) :
    ∃! e : T ≅ dilatationGroup hr hJ j, e.hom ≫ dilatationGroupHom hr hJ j = p := by
  have hcentre := (hp T.X p.hom.hom).mp
    ⟨𝟙 T.X, Category.id_comp _, fun _ h => hinj (h.trans (Category.id_comp _).symm)⟩
  obtain ⟨g, hg, huniq⟩ := existsUnique_dilatationGroupHom hr hJ j p hcentre
  obtain ⟨v, hv, -⟩ := (hp D d).mpr (quotient_factors hr hJ j)
  have hleft : g.hom.hom ≫ v = 𝟙 T.X := by
    apply hinj
    change (g.hom.hom ≫ v) ≫ p.hom.hom = 𝟙 T.X ≫ p.hom.hom
    rw [Category.assoc, hv, Category.id_comp]
    exact congrArg (fun h : T ⟶ X => h.hom.hom) hg
  have hright : v ≫ g.hom.hom = 𝟙 D := by
    apply affineDilatationHom_injective j.hom.hom hr
    simp only [Category.assoc, Category.id_comp]
    have h := congrArg (fun h : T ⟶ X => h.hom.hom) hg
    change g.hom.hom ≫ d = p.hom.hom at h
    rw [h, hv]
  let e := Grp.mkIso (G := T) (H := dilatationGroup hr hJ j) ⟨g.hom.hom, v, hleft, hright⟩
    (IsMonHom.one_hom (f := g.hom.hom)) (IsMonHom.mul_hom (f := g.hom.hom))
  have he : e.hom = g := Grp.hom_ext _ _ rfl
  refine ⟨e, ?_, fun e' he' => Iso.ext ((huniq _ he').trans he.symm)⟩
  change e.hom ≫ _ = _
  rw [he, hg]

section Maps

variable {X' : GroupScheme (Spec (CommRingCat.of R))} [IsAffine X'.X.left] [Flat X'.X.hom]
  {Y' : GroupScheme (Spec (CommRingCat.of (R ⧸ J)))}
  (j' : Y' ⟶ (baseChange (quotientBase J)).obj X') [IsClosedImmersion j'.hom.hom.left]
  (f : X ⟶ X') (g : Y ⟶ Y') (h : j ≫ (baseChange (quotientBase J)).map f = g ≫ j')

include h in
/-- Compatible maps of ambient groups and of their centres have a unique lift between
the dilatation groups. -/
theorem existsUnique_dilatationMap :
    ∃! v : dilatationGroup hr hJ j ⟶ dilatationGroup hr hJ j',
      v ≫ dilatationGroupHom hr hJ j' = dilatationGroupHom hr hJ j ≫ f := by
  let : IsAffine (dilatationGroup hr hJ j).X.left :=
    inferInstanceAs (IsAffine (affineDilatation r j.hom.hom).left)
  let : Flat (dilatationGroup hr hJ j).X.hom :=
    inferInstanceAs (Flat (affineDilatation r j.hom.hom).hom)
  apply existsUnique_dilatationGroupHom hr hJ j'
  obtain ⟨t, ht⟩ := quotient_factors hr hJ j
  refine ⟨t ≫ g.hom.hom, ?_⟩
  have h' : j.hom.hom ≫ (F).map f.hom.hom = g.hom.hom ≫ j'.hom.hom :=
    congrArg (fun k : Y ⟶ (baseChange (quotientBase J)).obj X' => k.hom.hom) h
  change (t ≫ g.hom.hom) ≫ j'.hom.hom = (F).map (d ≫ f.hom.hom)
  rw [Category.assoc, ← h', ← Category.assoc, ht, Functor.map_comp]

/-- The functorial map of group-scheme dilatations. -/
def dilatationMap : dilatationGroup hr hJ j ⟶ dilatationGroup hr hJ j' :=
  (existsUnique_dilatationMap hr hJ j j' f g h).exists.choose

@[reassoc] theorem dilatationMap_fac :
    dilatationMap hr hJ j j' f g h ≫ dilatationGroupHom hr hJ j' =
      dilatationGroupHom hr hJ j ≫ f :=
  (existsUnique_dilatationMap hr hJ j j' f g h).exists.choose_spec

/-- Uniqueness identifies the lift of the identity with the identity. -/
theorem dilatationMap_id
    (h : j ≫ (baseChange (quotientBase J)).map (𝟙 X) = (𝟙 Y) ≫ j) :
    dilatationMap hr hJ j j (𝟙 X) (𝟙 Y) h = 𝟙 _ := by
  obtain ⟨v, _, hv⟩ := existsUnique_dilatationMap hr hJ j j (𝟙 X) (𝟙 Y) h
  exact (hv _ (dilatationMap_fac hr hJ j j _ _ h)).trans
    (hv _ (by simp)).symm

variable {X'' : GroupScheme (Spec (CommRingCat.of R))} [IsAffine X''.X.left] [Flat X''.X.hom]
  {Y'' : GroupScheme (Spec (CommRingCat.of (R ⧸ J)))}
  (j'' : Y'' ⟶ (baseChange (quotientBase J)).obj X'') [IsClosedImmersion j''.hom.hom.left]
  (f' : X' ⟶ X'') (g' : Y' ⟶ Y'')
  (h' : j' ≫ (baseChange (quotientBase J)).map f' = g' ≫ j'')

/-- Functorial maps of dilatations compose. -/
theorem dilatationMap_comp
    (h'' : j ≫ (baseChange (quotientBase J)).map (f ≫ f') = (g ≫ g') ≫ j'') :
    dilatationMap hr hJ j j'' (f ≫ f') (g ≫ g') h'' =
      dilatationMap hr hJ j j' f g h ≫ dilatationMap hr hJ j' j'' f' g' h' := by
  obtain ⟨v, _, hv⟩ := existsUnique_dilatationMap hr hJ j j'' (f ≫ f') (g ≫ g') h''
  exact (hv _ (dilatationMap_fac hr hJ j j'' _ _ h'')).trans
    (hv _ (by
      change (_ ≫ _) ≫ dilatationGroupHom hr hJ j'' = _
      rw [Category.assoc, dilatationMap_fac, dilatationMap_fac_assoc])).symm

end Maps

section Sections

variable {S U : Scheme.{u}} (b : U ⟶ S) (P : GroupScheme S) (x : Over.mk (𝟙 S) ⟶ P.X)

private theorem baseChangeSectionHom_eq :
    baseChangeSectionHom b P x =
      Functor.LaxMonoidal.ε (Over.pullback b) ≫ (Over.pullback b).map x := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [baseChangeSectionHom_fst]
    change b ≫ x.left = (Functor.LaxMonoidal.ε (Over.pullback b)).left ≫
      pullback.lift (pullback.fst (𝟙 S) b ≫ x.left) (pullback.snd (𝟙 S) b) _ ≫
        pullback.fst P.X.hom b
    rw [pullback.lift_fst, ← Category.assoc, Over.ε_pullback_left]
    have hc : pullback.fst (𝟙 S) b = pullback.snd (𝟙 S) b ≫ b := by
      simpa only [Category.comp_id] using (pullback.condition (f := 𝟙 S) (g := b))
    rw [hc, IsIso.inv_hom_id_assoc]
  · exact (baseChangeSectionHom b P x).w.trans
      (Functor.LaxMonoidal.ε (Over.pullback b) ≫ (Over.pullback b).map x).w.symm

end Sections

/-- The literal image of sections over the base is the inverse image of centre sections
under the original reduction map. -/
theorem range_dilatationSections :
    (rationalPoints.map (dilatationGroupHom hr hJ j)).range =
      (rationalPoints.map j).range.comap (baseChangeSectionHom (quotientBase J) X) := by
  let : IsAffine (Over.mk (𝟙 (Spec (CommRingCat.of R)))).left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  let : Flat (Over.mk (𝟙 (Spec (CommRingCat.of R)))).hom :=
    inferInstanceAs (Flat (𝟙 (Spec (CommRingCat.of R))))
  ext x
  let ε := Functor.LaxMonoidal.ε (Over.pullback (quotientBase J))
  have hε := baseChangeSectionHom_eq (quotientBase J) X x
  change baseChangeSectionHom (quotientBase J) X x = ε ≫ (F).map x at hε
  change (∃ g : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ D, g ≫ d = x) ↔
    (∃ y : rationalPoints Y, y ≫ j.hom.hom = baseChangeSectionHom (quotientBase J) X x)
  constructor
  · intro hg
    have he := (affineDilatation_lift_iff j.hom.hom hr hJ x).mp
      (by obtain ⟨g, hg⟩ := hg
          exact ⟨g, hg, fun _ h => affineDilatationHom_injective j.hom.hom hr (h.trans hg.symm)⟩)
    obtain ⟨y, hy⟩ := he
    exact ⟨ε ≫ y, by rw [Category.assoc, hy, hε]⟩
  · rintro ⟨y, hy⟩
    have he : ∃ a : (F).obj (𝟙_ _) ⟶ Y.X, a ≫ j.hom.hom = (F).map x := by
      refine ⟨inv ε ≫ y, ?_⟩
      rw [Category.assoc, hy, hε, IsIso.inv_hom_id_assoc]
    exact ((affineDilatation_lift_iff j.hom.hom hr hJ x).mpr he).exists

end Group

end Langlands.GroupScheme.Dilatation

namespace Langlands.GroupScheme.IntegralModel

open Dilatation

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G G' : GroupScheme (Spec (CommRingCat.of K))} (M : IntegralModel R K G)

section Principal

variable {J : Ideal R} {r : R} (hr : r ≠ 0) (hJ : J = Ideal.span {r})
  {Y : GroupScheme (Spec (CommRingCat.of (R ⧸ J)))}
  (j : Y ⟶ (baseChange (quotientBase J)).obj M.group)
  [IsClosedImmersion j.hom.hom.left]

local instance : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom

private def dilatationGenericIso :
    (baseChange (Spec.algebraMap R K)).obj (dilatationGroup hr hJ j) ≅ M.genericFibre := by
  let f := (baseChange (Spec.algebraMap R K)).map (dilatationGroupHom hr hJ j)
  have : IsIso f.hom.hom := isIso_generic_affineDilatationHom j.hom.hom hr
  exact Grp.mkIso (asIso f.hom.hom) (IsMonHom.one_hom (f := f.hom.hom))
    (IsMonHom.mul_hom (f := f.hom.hom))

/-- The actual integral group model obtained by dilating along a subgroup over a
principal quotient of the DVR. -/
def dilatationAtQuotient : IntegralModel R K G where
  group := dilatationGroup hr hJ j
  affine := by
    change IsAffineHom (affineDilatation r j.hom.hom).hom
    exact isAffineHom_of_isAffine _
  flat := inferInstanceAs (Flat (affineDilatation r j.hom.hom).hom)
  finiteType := inferInstanceAs (LocallyOfFiniteType (affineDilatation r j.hom.hom).hom)
  genericIso := dilatationGenericIso M hr hJ j ≪≫ M.genericIso

/-- The structural morphism of the dilatation induces the identity of the supplied generic
group. -/
def dilatationAtQuotientHom : (M.dilatationAtQuotient hr hJ j).Hom M (𝟙 G) where
  hom := dilatationGroupHom hr hJ j
  generic_comm := by
    rw [Category.comp_id]
    apply congrArg (· ≫ M.genericIso.hom)
    apply Grp.hom_ext
    rfl

@[simp] theorem dilatationAtQuotientHom_genericIso :
    (baseChange (Spec.algebraMap R K)).map (M.dilatationAtQuotientHom hr hJ j).hom ≫
        M.genericIso.hom = (M.dilatationAtQuotient hr hJ j).genericIso.hom := by
  simpa only [Category.comp_id] using (M.dilatationAtQuotientHom hr hJ j).generic_comm

/-- On flat affine tests the original group map identifies points of the dilatation
with the reduction preimage of the centre. -/
theorem dilatationAtQuotient_lift_iff {T : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [Flat T.hom] (x : T ⟶ M.group.X) :
    (∃! y : T ⟶ (M.dilatationAtQuotient hr hJ j).group.X,
      y ≫ (M.dilatationAtQuotientHom hr hJ j).hom.hom.hom = x) ↔
      ∃ z : (Over.pullback (quotientBase J)).obj T ⟶ Y.X,
        z ≫ j.hom.hom = (Over.pullback (quotientBase J)).map x :=
  affineDilatation_lift_iff j.hom.hom hr hJ x

/-- The integral sections give the literal reduction preimage inside the original section group. -/
theorem range_dilatationAtQuotientSections :
    (rationalPoints.map (M.dilatationAtQuotientHom hr hJ j).hom).range =
      (rationalPoints.map j).range.comap (baseChangeSectionHom (quotientBase J) M.group) :=
  range_dilatationSections hr hJ j

/-- Inside the supplied generic group the dilatation's integral points are obtained by
applying the original integral-point map to the reduction preimage. -/
theorem integralPoints_dilatationAtQuotient :
    (M.dilatationAtQuotient hr hJ j).integralPoints =
      ((rationalPoints.map j).range.comap (baseChangeSectionHom (quotientBase J) M.group)).map
        M.integralPointMap := by
  rw [← M.range_dilatationAtQuotientSections hr hJ j]
  have hp (x : (M.dilatationAtQuotient hr hJ j).integralSections) :
      M.integralPointMap (rationalPoints.map (M.dilatationAtQuotientHom hr hJ j).hom x) =
        (M.dilatationAtQuotient hr hJ j).integralPointMap x := by
    rw [(M.dilatationAtQuotientHom hr hJ j).integralPointMap_naturality]
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, hp x⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, (hp x).symm⟩

variable {M} {N : IntegralModel R K G'} {f : G ⟶ G'}
  {Y' : GroupScheme (Spec (CommRingCat.of (R ⧸ J)))}
  (j' : Y' ⟶ (baseChange (quotientBase J)).obj N.group)
  [IsClosedImmersion j'.hom.hom.left]

/-- A compatible model homomorphism and a commuting map of centres lift to an actual
model homomorphism inducing the specified generic map. -/
def Hom.dilatationAtQuotientMap (φ : M.Hom N f) (g : Y ⟶ Y')
    (h : j ≫ (baseChange (quotientBase J)).map φ.hom = g ≫ j') :
    (M.dilatationAtQuotient hr hJ j).Hom (N.dilatationAtQuotient hr hJ j') f where
  hom := dilatationMap hr hJ j j' φ.hom g h
  generic_comm := by
    let F := baseChange (Spec.algebraMap R K)
    rw [← M.dilatationAtQuotientHom_genericIso hr hJ j,
      ← N.dilatationAtQuotientHom_genericIso hr hJ j']
    change F.map (dilatationMap hr hJ j j' φ.hom g h) ≫
      F.map (dilatationGroupHom hr hJ j') ≫ N.genericIso.hom =
      (F.map (dilatationGroupHom hr hJ j) ≫ M.genericIso.hom) ≫ f
    rw [← Category.assoc, ← Functor.map_comp, dilatationMap_fac, Functor.map_comp,
      Category.assoc, φ.generic_comm, Category.assoc]

@[reassoc] theorem Hom.dilatationAtQuotientMap_fac (φ : M.Hom N f) (g : Y ⟶ Y')
    (h : j ≫ (baseChange (quotientBase J)).map φ.hom = g ≫ j') :
    (φ.dilatationAtQuotientMap hr hJ j j' g h).hom ≫ (N.dilatationAtQuotientHom hr hJ j').hom =
      (M.dilatationAtQuotientHom hr hJ j).hom ≫ φ.hom :=
  dilatationMap_fac hr hJ j j' φ.hom g h

end Principal

section Special

variable {ϖ : R} (hϖ : Irreducible ϖ)
  {Y : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
  (j : Y ⟶ M.specialFibre) [IsClosedImmersion j.hom.hom.left]

/-- Dilatation along a closed subgroup of the actual residue special fibre. -/
abbrev dilatation : IntegralModel R K G :=
  M.dilatationAtQuotient hϖ.ne_zero hϖ.maximalIdeal_eq j

/-- The residue-centre dilatation map with its generic identity. -/
abbrev dilatationHom : (M.dilatation hϖ j).Hom M (𝟙 G) :=
  M.dilatationAtQuotientHom hϖ.ne_zero hϖ.maximalIdeal_eq j

theorem range_dilatationIntegralSections :
    (rationalPoints.map (M.dilatationHom hϖ j).hom).range =
      (rationalPoints.map j).range.comap M.reduction :=
  M.range_dilatationAtQuotientSections hϖ.ne_zero hϖ.maximalIdeal_eq j

theorem integralPoints_dilatation :
    (M.dilatation hϖ j).integralPoints =
      ((rationalPoints.map j).range.comap M.reduction).map M.integralPointMap :=
  M.integralPoints_dilatationAtQuotient hϖ.ne_zero hϖ.maximalIdeal_eq j

end Special

end Langlands.GroupScheme.IntegralModel
