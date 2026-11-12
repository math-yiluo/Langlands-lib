import Langlands.GroupScheme.RepresentabilityTransfer
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.Descent.Data
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Langlands.GroupScheme.Reductive.Basic

/-!
# The stabilizer group scheme of an action

For an action `b` of a group scheme `G` over `S` on a scheme `Z` over `S`, the stabilizer
scheme is the base change of the action graph `(g, z) ↦ (g.z, z)` along the diagonal of `Z`.
Over `Z`, it is a group scheme: the subgroup scheme of `G_Z = G ×_S Z` whose points over a
`Z`-scheme `T` are the points of `G` fixing the tautological point `T → Z`. Its fibre over a
point of `Z` with values in a scheme with one point (for example the spectrum of a field) is
a closed subgroup of the corresponding base change of `G`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ActionStabilizer

variable {S : Scheme.{u}} {G : GroupScheme S} {Z : Over S} (b : SchemeAction G Z)

/-- The graph `(g, z) ↦ (g.z, z)` of the action. -/
abbrev graph : G.X ⊗ Z ⟶ Z ⊗ Z := lift b.hom (snd G.X Z)

/-- The stabilizer scheme over `S`: the base change of the graph along the diagonal. -/
abbrev stab : Over S := pullback (graph b) (lift (𝟙 Z) (𝟙 Z))

/-- The projection of the stabilizer scheme to `Z`. -/
abbrev stabProj : stab b ⟶ Z := pullback.snd (graph b) (lift (𝟙 Z) (𝟙 Z))

/-- The projection of the stabilizer scheme to `G`. -/
def stabGroup : stab b ⟶ G.X := pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z)) ≫ fst G.X Z

theorem stab_fst :
    pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z)) = lift (stabGroup b) (stabProj b) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [stabGroup]
  · have h := pullback.condition (f := (graph b)) (g := lift (𝟙 Z) (𝟙 Z)) =≫ snd Z Z
    simpa only [Category.assoc, lift_snd, Category.comp_id] using h

/-- The tautological point of the stabilizer is fixed by its tautological group point. -/
theorem act_stabGroup_stabProj : b.act (stabGroup b) (stabProj b) = stabProj b := by
  have h := pullback.condition (f := (graph b)) (g := lift (𝟙 Z) (𝟙 Z)) =≫ fst Z Z
  simp only [Category.assoc, lift_fst, Category.comp_id] at h
  rw [stab_fst] at h
  exact h

/-- A point of `G` fixing a point of `Z` gives a point of the stabilizer scheme. -/
def stabLift {T : Over S} (g : T ⟶ G.X) (t : T ⟶ Z) (h : b.act g t = t) : T ⟶ (stab b) :=
  pullback.lift (lift g t) t (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, Category.comp_id]
      exact h
    · simp only [Category.assoc, lift_snd, Category.comp_id])

@[reassoc (attr := simp)]
theorem stabLift_stabGroup {T : Over S} (g : T ⟶ G.X) (t : T ⟶ Z) (h : b.act g t = t) :
    stabLift b g t h ≫ (stabGroup b) = g := by
  rw [stabLift, stabGroup, pullback.lift_fst_assoc, lift_fst]

@[reassoc (attr := simp)]
theorem stabLift_stabProj {T : Over S} (g : T ⟶ G.X) (t : T ⟶ Z) (h : b.act g t = t) :
    stabLift b g t h ≫ (stabProj b) = t :=
  pullback.lift_snd _ _ _

/-- Points of the stabilizer scheme are determined by their two projections. -/
theorem stab_hom_ext {T : Over S} {y y' : T ⟶ (stab b)}
    (h₁ : y ≫ (stabGroup b) = y' ≫ (stabGroup b)) (h₂ : y ≫ (stabProj b) = y' ≫ (stabProj b)) :
    y = y' := by
  apply pullback.hom_ext
  · rw [stab_fst, comp_lift, comp_lift, h₁, h₂]
  · exact h₂

section OverZ

/-- The tautological point `T → Z` of a scheme `T` over `Z`, regarded over `S`. -/
def basePoint (T : Over Z.left) : (Over.map Z.hom).obj T ⟶ Z :=
  Over.homMk T.hom

theorem map_basePoint {T T' : Over Z.left} (a : T' ⟶ T) :
    (Over.map Z.hom).map a ≫ basePoint T = basePoint T' := by
  ext
  exact Over.w a

/-- The stabilizer subgroup functor of `G_Z = G ×_S Z` over `Z`: a point `x` over a
`Z`-scheme `T` belongs to it when the corresponding point of `G` fixes the tautological point
of `Z`. -/
def stabilizerFunctor : SubgroupFunctor ((GroupScheme.baseChange Z.hom).obj G) where
  carrier T :=
    { carrier := {x | b.act (baseChangePointsEquiv Z.hom G T x) (basePoint T) = basePoint T}
      one_mem' := by
        simp only [Set.mem_ofPred_eq, map_one, SchemeAction.act_one]
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq, map_mul, SchemeAction.act_mul] at hx hy ⊢
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq, map_inv] at hx ⊢
        conv_lhs => rw [← hx]
        rw [← SchemeAction.act_mul, inv_mul_cancel, SchemeAction.act_one] }
  comp_mem a x hx := by
    change b.act (baseChangePointsEquiv Z.hom G _ (a ≫ x)) (basePoint _) = basePoint _
    rw [baseChangePointsEquiv_naturality, ← map_basePoint a, ← SchemeAction.naturality, hx]

/-- The stabilizer scheme, regarded as a scheme over `Z`. -/
abbrev stabOver : Over Z.left := Over.mk (stabProj b).left

/-- The stabilizer scheme maps to `G_Z = G ×_S Z` over `Z`. -/
def stabIncl : (stabOver b) ⟶ ((GroupScheme.baseChange Z.hom).obj G).X :=
  Over.homMk (pullback.lift (stabGroup b).left (stabProj b).left
    (by rw [Over.w (stabGroup b), Over.w (stabProj b)])) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
theorem stabIncl_left_fst :
    (stabIncl b).left ≫ pullback.fst G.X.hom Z.hom = (stabGroup b).left :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem stabIncl_left_snd :
    (stabIncl b).left ≫ pullback.snd G.X.hom Z.hom = (stabProj b).left :=
  pullback.lift_snd _ _ _

/-- A point of the stabilizer scheme over `Z`, regarded as a point over `S`. -/
def toStab {T : Over Z.left} (y : T ⟶ (stabOver b)) : (Over.map Z.hom).obj T ⟶ (stab b) :=
  Over.homMk y.left (by
    change y.left ≫ (stab b).hom = T.hom ≫ Z.hom
    rw [← Over.w (stabProj b), ← Category.assoc]
    congr 1
    exact Over.w y)

theorem toStab_stabProj {T : Over Z.left} (y : T ⟶ (stabOver b)) :
    toStab b y ≫ (stabProj b) = basePoint T := by
  ext
  exact Over.w y

theorem toStab_stabGroup {T : Over Z.left} (y : T ⟶ (stabOver b)) :
    toStab b y ≫ (stabGroup b) = baseChangePointsEquiv Z.hom G T (y ≫ (stabIncl b)) := by
  ext
  rw [baseChangePointsEquiv_left]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (y.left ≫ ·) (stabIncl_left_fst b).symm

/-- The points of `G_Z` in the stabilizer subgroup functor are those factoring through the
stabilizer scheme. -/
theorem mem_stabilizerFunctor_iff (T : Over Z.left)
    (x : T ⟶ ((GroupScheme.baseChange Z.hom).obj G).X) :
    x ∈ (stabilizerFunctor b).carrier T ↔ ∃ y : T ⟶ stabOver b, y ≫ stabIncl b = x := by
  constructor
  · intro hx
    have hx' : b.act (baseChangePointsEquiv Z.hom G T x) (basePoint T) = basePoint T := hx
    have hP := congrArg CommaMorphism.left (stabLift_stabProj b _ _ hx')
    have hG := congrArg CommaMorphism.left (stabLift_stabGroup b _ _ hx')
    simp only [Over.comp_left] at hP hG
    refine ⟨Over.homMk (stabLift b _ _ hx').left hP, ?_⟩
    ext1
    apply pullback.hom_ext
    · change (stabLift b _ _ hx').left ≫ (stabIncl b).left ≫ pullback.fst G.X.hom Z.hom = _
      rw [stabIncl_left_fst, hG]
      rfl
    · change (stabLift b _ _ hx').left ≫ (stabIncl b).left ≫ pullback.snd G.X.hom Z.hom = _
      rw [stabIncl_left_snd, hP]
      exact (Over.w x).symm
  · rintro ⟨y, rfl⟩
    change b.act (baseChangePointsEquiv Z.hom G T (y ≫ (stabIncl b))) (basePoint T) = basePoint T
    rw [← toStab_stabGroup, ← toStab_stabProj, ← SchemeAction.naturality, act_stabGroup_stabProj]

instance : Mono (stabIncl b) :=
  ⟨fun {W} y y' h => by
    have h1 : toStab b y = toStab b y' :=
      stab_hom_ext b (by rw [toStab_stabGroup, toStab_stabGroup, h])
        (by rw [toStab_stabProj, toStab_stabProj])
    have h2 : (toStab b y).left = (toStab b y').left := congrArg CommaMorphism.left h1
    exact Over.OverMorphism.ext h2⟩

/-- The stabilizer group scheme over `Z`, carried by the stabilizer scheme. -/
abbrev stabilizerGroup : GroupScheme Z.left :=
  (stabilizerFunctor b).representingGroupScheme (stabIncl b) (mem_stabilizerFunctor_iff b)

/-- The inclusion of the stabilizer group scheme into `G_Z`. -/
def stabilizerHom : (stabilizerGroup b) ⟶ (GroupScheme.baseChange Z.hom).obj G :=
  (stabilizerFunctor b).representingHom (stabIncl b) (mem_stabilizerFunctor_iff b)

theorem stabilizerHom_hom : (stabilizerHom b).hom.hom = (stabIncl b) :=
  (stabilizerFunctor b).representingHom_hom (stabIncl b) (mem_stabilizerFunctor_iff b)

theorem stabilizerGroup_hom : (stabilizerGroup b).X.hom = (stabProj b).left := rfl

end OverZ

section Schemes

/-- The defining square of the stabilizer scheme, on underlying schemes. -/
theorem isPullback_stab_left :
    IsPullback (pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z))).left (stabProj b).left
      (graph b).left (lift (𝟙 Z) (𝟙 Z)).left :=
  (IsPullback.of_hasPullback (graph b) (lift (𝟙 Z) (𝟙 Z))).map (Over.forget S)

@[reassoc]
theorem stab_fst_left_fst :
    (pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z))).left ≫ pullback.fst G.X.hom Z.hom =
      (stabGroup b).left := by
  rw [stab_fst]
  exact congrArg CommaMorphism.left (lift_fst (stabGroup b) (stabProj b))

@[reassoc]
theorem stab_fst_left_snd :
    (pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z))).left ≫ pullback.snd G.X.hom Z.hom =
      (stabProj b).left := by
  rw [stab_fst]
  exact congrArg CommaMorphism.left (lift_snd (stabGroup b) (stabProj b))

@[reassoc]
theorem stab_fst_left_act :
    (pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z))).left ≫ b.hom.left = (stabProj b).left := by
  rw [stab_fst]
  exact congrArg CommaMorphism.left (act_stabGroup_stabProj b)

omit b in
@[reassoc]
theorem diag_left_fst : (lift (𝟙 Z) (𝟙 Z)).left ≫ pullback.fst Z.hom Z.hom = 𝟙 Z.left :=
  congrArg CommaMorphism.left (lift_fst (𝟙 Z) (𝟙 Z))

omit b in
@[reassoc]
theorem diag_left_snd : (lift (𝟙 Z) (𝟙 Z)).left ≫ pullback.snd Z.hom Z.hom = 𝟙 Z.left :=
  congrArg CommaMorphism.left (lift_snd (𝟙 Z) (𝟙 Z))

@[reassoc]
theorem graph_left_fst : (graph b).left ≫ pullback.fst Z.hom Z.hom = b.hom.left :=
  congrArg CommaMorphism.left (lift_fst b.hom (snd G.X Z))

@[reassoc]
theorem graph_left_snd : (graph b).left ≫ pullback.snd Z.hom Z.hom = pullback.snd G.X.hom Z.hom :=
  congrArg CommaMorphism.left (lift_snd b.hom (snd G.X Z))

/-- The stabilizer scheme is locally of finite type over `Z` when `G` is locally of finite type
over `S`: it is a base change of the diagonal of `Z` followed by a base change of `G → S`. -/
instance [LocallyOfFiniteType G.X.hom] : LocallyOfFiniteType (stabProj b).left := by
  have hΔ : LocallyOfFiniteType (lift (𝟙 Z) (𝟙 Z)).left := by
    have : LocallyOfFiniteType ((lift (𝟙 Z) (𝟙 Z)).left ≫ pullback.fst Z.hom Z.hom) := by
      rw [diag_left_fst]
      infer_instance
    exact locallyOfFiniteType_of_comp _ (pullback.fst Z.hom Z.hom)
  have hτ : LocallyOfFiniteType (pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z))).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (isPullback_stab_left b).flip hΔ
  rw [← stab_fst_left_snd]
  infer_instance

variable {Y : Scheme.{u}} (q : Y ⟶ Z.left)

omit b in
/-- The map `X ×_S Y → X ×_S Z` induced by `q : Y → Z`. -/
abbrev bcMap {X : Scheme.{u}} (p : X ⟶ S) : pullback p (q ≫ Z.hom) ⟶ pullback p Z.hom :=
  pullback.lift (pullback.fst p (q ≫ Z.hom)) (pullback.snd p (q ≫ Z.hom) ≫ q)
    (by rw [pullback.condition, Category.assoc])

omit b in
/-- `X ×_S Y` is the base change of `X ×_S Z` along `q`. -/
theorem isPullback_bcMap {X : Scheme.{u}} (p : X ⟶ S) :
    IsPullback (bcMap q p) (pullback.snd p (q ≫ Z.hom)) (pullback.snd p Z.hom) q := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback p Z.hom)
  rw [pullback.lift_fst]
  exact IsPullback.of_hasPullback p (q ≫ Z.hom)

omit b in
/-- The section `Y → Z ×_S Y`, `y ↦ (q(y), y)`. -/
def pointSection : Y ⟶ pullback Z.hom (q ≫ Z.hom) :=
  pullback.lift q (𝟙 Y) (by rw [Category.id_comp])

/-- The orbit map `G ×_S Y → Z ×_S Y`, `(g, y) ↦ (g.q(y), y)`. -/
def baseChangeOrbitMap : pullback G.X.hom (q ≫ Z.hom) ⟶ pullback Z.hom (q ≫ Z.hom) :=
  pullback.lift (bcMap q G.X.hom ≫ b.hom.left) (pullback.snd _ _) (by
    have e : b.hom.left ≫ Z.hom = pullback.fst G.X.hom Z.hom ≫ G.X.hom := Over.w b.hom
    rw [Category.assoc, e, pullback.lift_fst_assoc, pullback.condition])

/-- The map from the fibre of the stabilizer scheme over `q` to `G ×_S Y`. -/
def fibreIncl : pullback (stabProj b).left q ⟶ pullback G.X.hom (q ≫ Z.hom) :=
  pullback.lift (pullback.fst _ _ ≫ (stabGroup b).left) (pullback.snd _ _) (by
    rw [Category.assoc, Over.w (stabGroup b), ← Over.w (stabProj b), ← Category.assoc,
      pullback.condition, Category.assoc])

/-- The fibre of the stabilizer scheme over `q` is the base change of the section given by
`q` along the orbit map. -/
theorem isPullback_fibreIncl :
    IsPullback (fibreIncl b q) (pullback.snd (stabProj b).left q) (baseChangeOrbitMap b q)
      (pointSection q) := by
  have hR : IsPullback (bcMap q G.X.hom) (baseChangeOrbitMap b q) (graph b).left
      (bcMap q Z.hom) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd Z.hom (q ≫ Z.hom))
      (v₂₂ := pullback.snd Z.hom Z.hom) (h₃₁ := q) ?_ ?_ (isPullback_bcMap q Z.hom)
    · have e1 : baseChangeOrbitMap b q ≫ pullback.snd Z.hom (q ≫ Z.hom) =
          pullback.snd G.X.hom (q ≫ Z.hom) := pullback.lift_snd _ _ _
      rw [e1, graph_left_snd]
      exact isPullback_bcMap q G.X.hom
    · apply pullback.hom_ext
      · rw [Category.assoc, graph_left_fst, baseChangeOrbitMap, Category.assoc, pullback.lift_fst,
          pullback.lift_fst]
      · rw [Category.assoc, graph_left_snd, Category.assoc]
        simp only [bcMap, baseChangeOrbitMap, pullback.lift_snd, pullback.lift_snd_assoc]
  have hC := (IsPullback.of_hasPullback (stabProj b).left q).paste_horiz (isPullback_stab_left b)
  have e1 : fibreIncl b q ≫ bcMap q G.X.hom =
      pullback.fst (stabProj b).left q ≫ (pullback.fst (graph b) (lift (𝟙 Z) (𝟙 Z))).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, fibreIncl, pullback.lift_fst, Category.assoc,
        stab_fst_left_fst]
    · rw [Category.assoc, pullback.lift_snd, fibreIncl, pullback.lift_snd_assoc, Category.assoc,
        stab_fst_left_snd, pullback.condition]
  have e2 : pointSection q ≫ bcMap q Z.hom = q ≫ (lift (𝟙 Z) (𝟙 Z)).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pointSection, pullback.lift_fst, Category.assoc,
        diag_left_fst, Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, pointSection, pullback.lift_snd_assoc,
        Category.id_comp, Category.assoc, diag_left_snd, Category.comp_id]
  refine IsPullback.of_right ?_ ?_ hR
  · rw [e1, e2]
    exact hC
  · apply pullback.hom_ext
    · rw [Category.assoc, baseChangeOrbitMap, pullback.lift_fst, ← Category.assoc, e1,
        Category.assoc, stab_fst_left_act, pullback.condition, Category.assoc, pointSection,
        pullback.lift_fst]
    · rw [Category.assoc, baseChangeOrbitMap, pullback.lift_snd, fibreIncl, pullback.lift_snd,
        Category.assoc, pointSection, pullback.lift_snd, Category.comp_id]

/-- Over a scheme with at most one point, the fibre of the stabilizer scheme is a closed
subscheme of the base change of `G`. -/
theorem isClosedImmersion_fibreIncl [Subsingleton Y] : IsClosedImmersion (fibreIncl b q) := by
  have hs : IsClosedImmersion (pointSection q) :=
    isClosedImmersion_of_comp_eq_id (pullback.snd Z.hom (q ≫ Z.hom)) (pointSection q)
      (pullback.lift_snd _ _ _)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_fibreIncl b q).flip hs

/-- The fibre over `q` of the stabilizer group scheme maps to the base change of `G` along any
`r : Y → S` equal to `q ≫ (Z → S)`. -/
def fibreHom {r : Y ⟶ S} (h : q ≫ Z.hom = r) :
    (GroupScheme.baseChange q).obj (stabilizerGroup b) ⟶ (GroupScheme.baseChange r).obj G :=
  (GroupScheme.baseChange q).map (stabilizerHom b) ≫
    (Descent.pullbackComparison Z.hom q r h G).hom

theorem fibreHom_left : (fibreHom b q rfl).hom.hom.left = fibreIncl b q := by
  have h0 : (fibreHom b q rfl).hom.hom.left =
      ((GroupScheme.baseChange q).map (stabilizerHom b)).hom.hom.left ≫
        (Descent.pullbackComparison Z.hom q _ rfl G).hom.hom.hom.left := rfl
  have h2 : ((GroupScheme.baseChange q).map (stabilizerHom b)).hom.hom.left ≫
      pullback.fst ((GroupScheme.baseChange Z.hom).obj G).X.hom q ≫
        pullback.fst G.X.hom Z.hom =
      pullback.fst (stabilizerGroup b).X.hom q ≫ (stabGroup b).left := by
    erw [pullback.lift_fst_assoc]
    rw [stabilizerHom_hom, Category.assoc, stabIncl_left_fst]
  have h3 : ((GroupScheme.baseChange q).map (stabilizerHom b)).hom.hom.left ≫
      pullback.snd ((GroupScheme.baseChange Z.hom).obj G).X.hom q =
      pullback.snd (stabilizerGroup b).X.hom q :=
    pullback.lift_snd _ _ _
  have hw : (Descent.pullbackComparison Z.hom q _ rfl G).hom.hom.hom.left ≫
      pullback.snd G.X.hom (q ≫ Z.hom) =
      pullback.snd ((GroupScheme.baseChange Z.hom).obj G).X.hom q :=
    Over.w (Descent.pullbackComparison Z.hom q _ rfl G).hom.hom.hom
  rw [h0]
  apply pullback.hom_ext
  · rw [Category.assoc, Descent.pullbackComparison_hom_fst, h2, fibreIncl, pullback.lift_fst]
    rfl
  · rw [Category.assoc, hw, h3, fibreIncl, pullback.lift_snd]
    rfl

/-- Over a scheme with at most one point, the fibre of the stabilizer group scheme is a closed
subgroup of the base change of `G`. -/
theorem isClosedSubgroup_fibreHom [Subsingleton Y] {r : Y ⟶ S} (h : q ≫ Z.hom = r) :
    IsClosedSubgroup (fibreHom b q h) := by
  subst h
  unfold IsClosedSubgroup
  rw [fibreHom_left]
  exact isClosedImmersion_fibreIncl b q

end Schemes

end Langlands.GroupScheme.ActionStabilizer
