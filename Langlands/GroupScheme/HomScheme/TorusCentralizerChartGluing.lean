import Langlands.GroupScheme.HomScheme.TorusCentralizerSheaf
import Mathlib.AlgebraicGeometry.Sites.Representability

/-! # Gluing open charts for torus-centralizer families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- A chart of actual smooth closed subgroups with torus-centralizer fibres.
The open lifting criterion is tested along all morphisms of parameter schemes. -/
structure IsOpenCentralizerChart {U : Over S} {K : GroupScheme U.left}
    (j : K ⟶ (baseChange U.hom).obj G) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType U.hom
  closed : IsClosedSubgroup j
  smooth : Smooth K.X.hom
  connected : GeometricallyConnected K.X.hom
  fibres : HasTorusCentralizerResidueFibres j
  injective : ∀ (T : Over S) (a b : T ⟶ U), evaluate j a = evaluate j b → a = b
  isOpen : ∀ (T : Over S) (L : GroupScheme T.left) (i : L ⟶ (baseChange T.hom).obj G),
    IsClosedSubgroup i → Smooth L.X.hom → GeometricallyConnected L.X.hom →
    HasTorusCentralizerResidueFibres i → ∃ V : T.left.Opens, ∀ (A : Over S) (a : A ⟶ T),
      (∃ b : A ⟶ U, evaluate j b = evaluate i a) ↔ Set.range a.left.base ⊆ V

/-- Local coverage tests every point of every actual centralizer family. -/
def CentralizerChartsCover {ι : Type u} {U : ι → Over S} {K : ∀ k, GroupScheme (U k).left}
    (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj G) : Prop :=
  ∀ (T : Over S) (L : GroupScheme T.left) (i : L ⟶ (baseChange T.hom).obj G),
    IsClosedSubgroup i → Smooth L.X.hom → GeometricallyConnected L.X.hom →
    HasTorusCentralizerResidueFibres i → ∀ t : T.left,
      ∃ (k : ι) (V : T.left.Opens), t ∈ V ∧
        ∃ a : Over.mk (V.ι ≫ T.hom) ⟶ U k,
          evaluate (j k) a = evaluate i (Over.homMk V.ι rfl)

/-- A locally finite-type parameter with its universal actual closed family. -/
def FibrewiseTorusCentralizersRepresentable (G : GroupScheme S) : Prop :=
  ∃ (M : Over S) (H : GroupScheme M.left) (c : H ⟶ (baseChange M.hom).obj G),
    LocallyOfFiniteType M.hom ∧ IsClosedSubgroup c ∧ Smooth H.X.hom ∧
      GeometricallyConnected H.X.hom ∧ HasTorusCentralizerResidueFibres c ∧
      ∀ (T : Over S) (K : GroupScheme T.left) (j : K ⟶ (baseChange T.hom).obj G),
        IsClosedSubgroup j → Smooth K.X.hom → GeometricallyConnected K.X.hom →
        HasTorusCentralizerResidueFibres j → ∃! a : T ⟶ M, evaluate c a = range j

variable (hG : HasAffineResidueFibers G)

private def actualCentralizerSubgroup {T : Scheme.{u}}
    (x : (totalCentralizerPresheaf hG).obj (op T)) : CentralizerSubgroup ((baseChange x.1).obj G) :=
  centralizerEquiv hG (Over.mk x.1) (Functor.OverTotal.toFibre (Over.mk x.1) x rfl)

private theorem actualCentralizerSubgroup_map {T A : Scheme.{u}} (a : A ⟶ T)
    (x : (totalCentralizerPresheaf hG).obj (op T)) :
    actualCentralizerSubgroup hG ((totalCentralizerPresheaf hG).map a.op x) =
      restrictCentralizer hG (Over.homMk a rfl : Over.mk (a ≫ x.1) ⟶ Over.mk x.1)
        (actualCentralizerSubgroup hG x) := by
  let b : Over.mk (a ≫ x.1) ⟶ Over.mk x.1 := Over.homMk a rfl
  change centralizerEquiv hG (Over.mk (a ≫ x.1)) (Functor.OverTotal.toFibre (Over.mk (a ≫ x.1))
    ((totalCentralizerPresheaf hG).map a.op x) rfl) = _
  calc
    _ = centralizerEquiv hG (Over.mk (a ≫ x.1)) ((centralizerPresheaf hG).map b.op
        (Functor.OverTotal.toFibre (Over.mk x.1) x rfl)) :=
      congrArg (centralizerEquiv hG _) (Functor.OverTotal.toFibre_naturality b x rfl rfl)
    _ = _ := centralizerEquiv_map hG b _

variable {U : Over S} {K : GroupScheme U.left}
variable (j : K ⟶ (baseChange U.hom).obj G) (hj : IsOpenCentralizerChart j)

private def centralizerChartSection : (centralizerPresheaf hG).obj (op U) :=
  (centralizerEquiv hG U).symm
    ⟨range j, isCentralizerFamily_range j hj.closed hj.smooth hj.connected hj.fibres⟩

/-- The actual chart family induces a morphism into the centralizer sheaf. -/
def centralizerChartMap : yoneda.obj U.left ⟶ totalCentralizerPresheaf hG :=
  yonedaEquiv.symm (Functor.OverTotal.ofFibre U (centralizerChartSection hG j hj))

@[simp]
theorem centralizerChartMap_app_fst {T : Scheme.{u}} (a : T ⟶ U.left) :
    ((centralizerChartMap hG j hj).app (op T) a).1 = a ≫ U.hom := rfl

private theorem centralizerChartMap_app_toFibre {T : Over S} (a : T ⟶ U)
    (ha : ((centralizerChartMap hG j hj).app (op T.left) a.left).1 = T.hom) :
    (centralizerEquiv hG T (Functor.OverTotal.toFibre T
      ((centralizerChartMap hG j hj).app (op T.left) a.left) ha)).val = evaluate j a := by
  let x := Functor.OverTotal.ofFibre U (centralizerChartSection hG j hj)
  change (centralizerEquiv hG T (Functor.OverTotal.toFibre T
    ((centralizerPresheaf hG).overTotal.map a.left.op x) ha)).val = _
  rw [Functor.OverTotal.toFibre_naturality a x rfl ha, centralizerEquiv_map]
  apply restrictCentralizer_eq_evaluate hG
  rw [Functor.OverTotal.toFibre_ofFibre, centralizerChartSection, Equiv.apply_symm_apply]

/-- A chart value equals a total section precisely when their actual subgroup
functors agree over the given structural map. -/
theorem centralizerChartMap_app_eq_iff {T : Over S} (a : T ⟶ U)
    (x : (totalCentralizerPresheaf hG).obj (op T.left)) (hx : x.1 = T.hom) :
    (centralizerChartMap hG j hj).app (op T.left) a.left = x ↔
      evaluate j a = (centralizerEquiv hG T (Functor.OverTotal.toFibre T x hx)).val := by
  let y := (centralizerChartMap hG j hj).app (op T.left) a.left
  have hy : y.1 = T.hom := a.w
  have he := centralizerChartMap_app_toFibre hG j hj a hy
  change y = x ↔ _
  rw [← he]
  constructor
  · intro h
    rw [Functor.OverTotal.toFibre_congr T h hy hx]
  · intro h
    rw [← Functor.OverTotal.ofFibre_toFibre T y hy, ← Functor.OverTotal.ofFibre_toFibre T x hx]
    exact congrArg (Functor.OverTotal.ofFibre T)
      ((centralizerEquiv hG T).injective (Subtype.ext h))

private theorem centralizerChartMap_app_injective (T : Scheme.{u}) :
    Function.Injective ((centralizerChartMap hG j hj).app (op T)) := by
  intro a b hab
  have hw : a ≫ U.hom = b ≫ U.hom := congrArg Sigma.fst hab
  let A : Over S := Over.mk (b ≫ U.hom)
  let a' : A ⟶ U := Over.homMk a hw
  let b' : A ⟶ U := Over.homMk b rfl
  let y := (centralizerChartMap hG j hj).app (op T) b
  exact congrArg (fun f => f.left) (hj.injective A a' b'
    (((centralizerChartMap_app_eq_iff hG j hj a' y rfl).mp hab).trans
      (centralizerChartMap_app_toFibre hG j hj b' rfl)))

set_option maxHeartbeats 800000 in
private theorem exists_open_centralizerChart_pullback {T : Scheme.{u}}
    (x : (totalCentralizerPresheaf hG).obj (op T)) :
    ∃ V : T.Opens, ∀ (A : Scheme.{u}) (a : A ⟶ T),
      (∃ b : A ⟶ U.left, (centralizerChartMap hG j hj).app (op A) b =
        (totalCentralizerPresheaf hG).map a.op x) ↔ Set.range a.base ⊆ V := by
  let M : Over S := Over.mk x.1
  let F := actualCentralizerSubgroup hG x
  let r := centralizerRepresentative F
  obtain ⟨V, hV⟩ := hj.isOpen M r.group r.hom r.closed r.smooth r.connected r.fibres
  refine ⟨V, fun A a => ?_⟩
  let A' : Over S := Over.mk (a ≫ x.1)
  let a' : A' ⟶ M := Over.homMk a rfl
  let z := (totalCentralizerPresheaf hG).map a.op x
  have he : (actualCentralizerSubgroup hG z).val = evaluate r.hom a' :=
    (congrArg Subtype.val (actualCentralizerSubgroup_map hG a x)).trans
      (restrictCentralizer_eq_evaluate hG a' F r.hom r.represents.2)
  constructor
  · rintro ⟨b, hb⟩
    let b' : A' ⟶ U := Over.homMk b (congrArg Sigma.fst hb)
    exact (hV A' a').mp ⟨b', ((centralizerChartMap_app_eq_iff hG j hj b' z rfl).mp hb).trans he⟩
  · intro ha
    obtain ⟨b, hb⟩ := (hV A' a').mpr ha
    exact ⟨b.left, (centralizerChartMap_app_eq_iff hG j hj b z rfl).mpr (hb.trans he.symm)⟩

private theorem centralizerChartMap_app_comp {T A : Scheme.{u}} (a : A ⟶ T) (b : T ⟶ U.left) :
    (centralizerChartMap hG j hj).app (op A) (a ≫ b) =
      (totalCentralizerPresheaf hG).map a.op ((centralizerChartMap hG j hj).app (op T) b) := by
  change (totalCentralizerPresheaf hG).map (a ≫ b).op _ =
    (totalCentralizerPresheaf hG).map a.op ((totalCentralizerPresheaf hG).map b.op _)
  rw [op_comp, Functor.map_comp_apply]

set_option maxHeartbeats 800000 in
/-- The open lifting condition represents all pullbacks of the chart by open immersions. -/
theorem centralizerChartMap_isOpenImmersion : IsOpenImmersion.presheaf (centralizerChartMap hG j hj) := by
  apply MorphismProperty.relative.of_exists
  intro T g
  let x := yonedaEquiv g
  have hg : ∀ {A : Scheme.{u}} (a : A ⟶ T), g.app (op A) a =
      (totalCentralizerPresheaf hG).map a.op x := fun a => (map_yonedaEquiv g a).symm
  obtain ⟨V, hV⟩ := exists_open_centralizerChart_pullback hG j hj x
  obtain ⟨φ, hφ⟩ := (hV V V.ι).mpr (by rw [Scheme.Opens.range_ι])
  refine ⟨V, yoneda.map φ, V.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨A⟩
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext c
    change (centralizerChartMap hG j hj).app (op A) (c ≫ φ) = g.app (op A) (c ≫ V.ι)
    rw [centralizerChartMap_app_comp, hφ, hg, op_comp, Functor.map_comp_apply]
  · rintro c c' ⟨-, hc⟩
    exact (cancel_mono V.ι).mp hc
  · intro b a ha
    change A ⟶ U.left at b
    change A ⟶ T at a
    change (centralizerChartMap hG j hj).app (op A) b = g.app (op A) a at ha
    have h := (hV A a).mp ⟨b, ha.trans (hg a)⟩
    rw [← Scheme.Opens.range_ι] at h
    refine ⟨IsOpenImmersion.lift V.ι a h, ?_, IsOpenImmersion.lift_fac V.ι a h⟩
    change IsOpenImmersion.lift V.ι a h ≫ φ = b
    apply centralizerChartMap_app_injective hG j hj A
    rw [centralizerChartMap_app_comp, hφ, ← Functor.map_comp_apply, ← op_comp,
      IsOpenImmersion.lift_fac, ← hg]
    exact ha.symm

variable {ι : Type u} {U' : ι → Over S} {K' : ∀ k, GroupScheme (U' k).left}
variable (j' : ∀ k, K' k ⟶ (baseChange (U' k).hom).obj G) (hj' : ∀ k, IsOpenCentralizerChart (j' k))

private theorem isLocallySurjective_of_open_lifts {P : Scheme.{u}ᵒᵖ ⥤ Type u}
    {X : ι → Scheme.{u}} (f : ∀ k, yoneda.obj (X k) ⟶ P)
    (h : ∀ (T : Scheme.{u}) (x : P.obj (op T)) (t : T),
      ∃ (k : ι) (V : T.Opens), t ∈ V ∧ ∃ a : (V : Scheme.{u}) ⟶ X k,
        (f k).app (op (V : Scheme.{u})) a = P.map V.ι.op x) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f) := by
  constructor
  intro T x
  choose k V ht hLift using h T x
  choose a ha using hLift
  let 𝒱 : T.OpenCover := Scheme.Cover.mkOfCovers T (fun t => (V t : Scheme.{u}))
    (fun t => (V t).ι) (fun t => ⟨t, ⟨t, ht t⟩, rfl⟩)
  refine GrothendieckTopology.superset_covering _ ?_ 𝒱.mem_grothendieckTopology
  intro A g hg
  obtain ⟨t, b, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  let b' : A ⟶ (V t : Scheme.{u}) := b
  refine ⟨(Sigma.ι (fun l => yoneda.obj (X l)) (k t)).app (op A) (b' ≫ a t), ?_⟩
  show ((Sigma.ι (fun l => yoneda.obj (X l)) (k t)) ≫ Sigma.desc f).app (op A) (b' ≫ a t) =
    P.map (b' ≫ (V t).ι).op x
  rw [Sigma.ι_comp_desc]
  have hn : (f (k t)).app (op A) (b' ≫ a t) =
      P.map b'.op ((f (k t)).app (op (V t : Scheme.{u})) (a t)) :=
    NatTrans.naturality_apply (f (k t)) b'.op (a t)
  rw [hn, ha, ← Functor.map_comp_apply, ← op_comp]

set_option maxHeartbeats 800000 in
private theorem centralizerChartMap_restrict_eq_iff {T A : Scheme.{u}}
    (x : (totalCentralizerPresheaf hG).obj (op T)) {H : GroupScheme T}
    (i : H ⟶ (baseChange x.1).obj G) (hi : range i = (actualCentralizerSubgroup hG x).val)
    (b : A ⟶ T) (k : ι) (a : Over.mk (b ≫ x.1) ⟶ U' k) :
    (centralizerChartMap hG (j' k) (hj' k)).app (op A) a.left =
      (totalCentralizerPresheaf hG).map b.op x ↔
        evaluate (j' k) a =
          evaluate i (Over.homMk b rfl : Over.mk (b ≫ x.1) ⟶ Over.mk x.1) := by
  let M : Over S := Over.mk x.1
  let F := actualCentralizerSubgroup hG x
  let B : Over S := Over.mk (b ≫ x.1)
  let b' : B ⟶ M := Over.homMk b rfl
  let z := (totalCentralizerPresheaf hG).map b.op x
  have he : (actualCentralizerSubgroup hG z).val = evaluate i b' :=
    (congrArg Subtype.val (actualCentralizerSubgroup_map hG b x)).trans
      (restrictCentralizer_eq_evaluate hG b' F i hi)
  constructor
  · intro ha
    exact ((centralizerChartMap_app_eq_iff hG (j' k) (hj' k) a z rfl).mp ha).trans he
  · intro ha
    exact (centralizerChartMap_app_eq_iff hG (j' k) (hj' k) a z rfl).mpr (ha.trans he.symm)

private theorem exists_centralizerChart_lift (hc : CentralizerChartsCover j')
    (T : Scheme.{u}) (x : (totalCentralizerPresheaf hG).obj (op T)) (t : T) :
    ∃ (k : ι) (V : T.Opens), t ∈ V ∧ ∃ a : (V : Scheme.{u}) ⟶ (U' k).left,
      (centralizerChartMap hG (j' k) (hj' k)).app (op (V : Scheme.{u})) a =
        (totalCentralizerPresheaf hG).map V.ι.op x := by
  let M : Over S := Over.mk x.1
  obtain ⟨H, i, hi, hs, hg, hf, hr⟩ := (actualCentralizerSubgroup hG x).property
  obtain ⟨k, V, ht, a, ha⟩ := hc M H i hi hs hg hf t
  exact ⟨k, V, ht, a.left, (centralizerChartMap_restrict_eq_iff hG j' hj' x i hr.2 V.ι k a).mpr ha⟩

private theorem isLocallySurjective_centralizerChartMap (hc : CentralizerChartsCover j') :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun k => centralizerChartMap hG (j' k) (hj' k))) :=
  isLocallySurjective_of_open_lifts (fun k => centralizerChartMap hG (j' k) (hj' k))
    (exists_centralizerChart_lift hG j' hj' hc)

private theorem universal_of_centralizerRepresentableBy {M : Over S}
    (e : (centralizerPresheaf hG).RepresentableBy M) :
    ∃ (H : GroupScheme M.left) (c : H ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup c ∧ Smooth H.X.hom ∧ GeometricallyConnected H.X.hom ∧
        HasTorusCentralizerResidueFibres c ∧
        ∀ (T : Over S) (L : GroupScheme T.left) (i : L ⟶ (baseChange T.hom).obj G),
          IsClosedSubgroup i → Smooth L.X.hom → GeometricallyConnected L.X.hom →
          HasTorusCentralizerResidueFibres i → ∃! a : T ⟶ M, evaluate c a = range i := by
  let F := centralizerEquiv hG M (e.homEquiv (𝟙 M))
  let r := centralizerRepresentative F
  have he {T : Over S} (a : T ⟶ M) :
      evaluate r.hom a = (centralizerEquiv hG T (e.homEquiv a)).val := by
    rw [e.homEquiv_eq, centralizerEquiv_map]
    exact (restrictCentralizer_eq_evaluate hG a F r.hom r.represents.2).symm
  refine ⟨r.group, r.hom, r.closed, r.smooth, r.connected, r.fibres, ?_⟩
  intro T L i hi hs hc hf
  let y : CentralizerSubgroup ((baseChange T.hom).obj G) := ⟨range i, isCentralizerFamily_range i hi hs hc hf⟩
  let x := (centralizerEquiv hG T).symm y
  have hx : centralizerEquiv hG T x = y := (centralizerEquiv hG T).apply_symm_apply y
  refine ⟨e.homEquiv.symm x, ?_, ?_⟩
  · change evaluate r.hom (e.homEquiv.symm x) = range i
    rw [he, Equiv.apply_symm_apply, hx]
  · intro b hb
    apply e.homEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply (centralizerEquiv hG T).injective
    apply Subtype.ext
    rw [← he, hx]
    exact hb

/-- Open charts that cover locally yield a locally finite-type representer
of the actual centralizer families. -/
def TorusCentralizerChartGluingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), HasAffineResidueFibers G →
    ∀ (ι : Type u) (U : ι → Over S) (K : ∀ k, GroupScheme (U k).left)
      (j : ∀ k, K k ⟶ (baseChange (U k).hom).obj G),
      (∀ k, IsOpenCentralizerChart (j k)) → CentralizerChartsCover j → FibrewiseTorusCentralizersRepresentable G

set_option maxHeartbeats 800000 in
theorem torusCentralizerChartGluing : TorusCentralizerChartGluingStatement.{u} := by
  intro S G hG ι U K j hj hc
  let F := centralizerSheaf hG
  have hOpen : ∀ k, IsOpenImmersion.presheaf
      (show yoneda.obj (U k).left ⟶ F.1 from centralizerChartMap hG (j k) (hj k)) :=
    fun k => centralizerChartMap_isOpenImmersion hG (j k) (hj k)
  have : Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (fun k => (show yoneda.obj (U k).left ⟶ F.1 from centralizerChartMap hG (j k) (hj k)))) :=
    isLocallySurjective_centralizerChartMap hG j hj hc
  let e : (totalCentralizerPresheaf hG).RepresentableBy _ :=
    Scheme.LocalRepresentability.representableBy (F := F) hOpen
  let a (k : ι) := Scheme.LocalRepresentability.toGlued (F := F) hOpen k
  have ha (k : ι) : a k ≫ e.overTotalBase = (U k).hom := by
    have he : e.homEquiv (a k) = yonedaEquiv (centralizerChartMap hG (j k) (hj k)) :=
      Scheme.LocalRepresentability.yonedaGluedToSheaf_app_toGlued (F := F) hOpen
    exact (e.overTotal_homEquiv_fst (a k)).symm.trans (congrArg Sigma.fst he)
  have hM : LocallyOfFiniteType e.overTotalBase := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFiniteType)
      (Scheme.LocalRepresentability.glueData (F := F) hOpen).openCover
    intro k
    change LocallyOfFiniteType (a k ≫ e.overTotalBase)
    rw [ha]
    exact (hj k).locallyOfFiniteType
  obtain ⟨H, i, hi, hs, hg, hf, hu⟩ := universal_of_centralizerRepresentableBy hG e.ofOverTotal
  exact ⟨Over.mk e.overTotalBase, H, i, hM, hi, hs, hg, hf, hu⟩

end Langlands.GroupScheme.TorusSubgroupModuli
