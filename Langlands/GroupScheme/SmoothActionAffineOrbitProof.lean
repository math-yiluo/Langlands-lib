import Langlands.GroupScheme.SmoothActionAffineOrbitStatement
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! # Affine orbits of a smooth action relation: proof -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SchemeAction

section General

variable {S : Scheme.{u}} {G : GroupScheme S} {X : Over S} (a : SchemeAction G X)

/-- The action on the points of a test morphism `t : T ⟶ X`, `(g, s) ↦ g • t s`. -/
def actAlong {T : Over S} (t : T ⟶ X) : G.X ⊗ T ⟶ X :=
  (G.X ◁ t) ≫ a.hom

/-- The base change of the action relation along `t`, `(g, s) ↦ (g • t s, s)`. -/
def relationAlong {T : Over S} (t : T ⟶ X) : G.X ⊗ T ⟶ X ⊗ T :=
  lift (a.actAlong t) (snd G.X T)

theorem comp_actAlong {T W : Over S} (t : T ⟶ X) (f : W ⟶ G.X ⊗ T) :
    f ≫ a.actAlong t = a.act (f ≫ fst G.X T) (f ≫ snd G.X T ≫ t) := by
  rw [actAlong, act, ← Category.assoc]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem relationAlong_fst {T : Over S} (t : T ⟶ X) :
    a.relationAlong t ≫ fst X T = a.actAlong t := by
  simp [relationAlong]

/-- The relation along `t` is the base change of the action relation along `X ◁ t`. -/
theorem isPullback_relationAlong {T : Over S} (t : T ⟶ X) :
    IsPullback (a.relationAlong t) (G.X ◁ t) (X ◁ t) (lift a.hom (snd G.X X)) := by
  have he : a.relationAlong t ≫ (X ◁ t) = (G.X ◁ t) ≫ lift a.hom (snd G.X X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [relationAlong, actAlong]
    · simp [relationAlong]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ he) ?_
  refine PullbackCone.IsLimit.mk he
    (fun s => lift (s.snd ≫ fst G.X X) (s.fst ≫ snd X T)) ?_ ?_ ?_
  · intro s
    have c₁ : s.fst ≫ fst X T = s.snd ≫ a.hom := by
      simpa using congrArg (fun f => f ≫ fst X X) s.condition
    have c₂ : s.fst ≫ snd X T ≫ t = s.snd ≫ snd G.X X := by
      simpa using congrArg (fun f => f ≫ snd X X) s.condition
    have hw : lift (s.snd ≫ fst G.X X) (s.fst ≫ snd X T) ≫ (G.X ◁ t) = s.snd := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using c₂
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, relationAlong_fst, actAlong, ← Category.assoc, hw, c₁]
    · simp [relationAlong]
  · intro s
    have c₂ : s.fst ≫ snd X T ≫ t = s.snd ≫ snd G.X X := by
      simpa using congrArg (fun f => f ≫ snd X X) s.condition
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using c₂
  · intro s m hm₁ hm₂
    apply CartesianMonoidalCategory.hom_ext
    · have hh := congrArg (fun f => f ≫ fst G.X X) hm₂
      simpa using hh
    · have hh := congrArg (fun f => f ≫ snd X T) hm₁
      simpa [relationAlong] using hh

/-- The orbit morphism is the base change of the action relation along the
section `y ↦ (y, x)`. -/
theorem isPullback_orbitMap (x : 𝟙_ (Over S) ⟶ X) :
    IsPullback (a.orbitMap x) (lift (𝟙 G.X) (toUnit G.X ≫ x))
      (lift (𝟙 X) (toUnit X ≫ x)) (lift a.hom (snd G.X X)) := by
  have he : a.orbitMap x ≫ lift (𝟙 X) (toUnit X ≫ x) =
      lift (𝟙 G.X) (toUnit G.X ≫ x) ≫ lift a.hom (snd G.X X) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [orbitMap, act]
    · simp
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ he) ?_
  refine PullbackCone.IsLimit.mk he (fun s => s.snd ≫ fst G.X X) ?_ ?_ ?_
  · intro s
    have c₁ : s.fst = s.snd ≫ a.hom := by
      simpa using congrArg (fun f => f ≫ fst X X) s.condition
    have c₂ : toUnit _ ≫ x = s.snd ≫ snd G.X X := by
      simpa using congrArg (fun f => f ≫ snd X X) s.condition
    rw [a.comp_orbitMap, c₂, c₁, act]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  · intro s
    have c₂ : toUnit _ ≫ x = s.snd ≫ snd G.X X := by
      simpa using congrArg (fun f => f ≫ snd X X) s.condition
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · simpa using c₂
  · intro s m _ hm₂
    have hh := congrArg (fun f => f ≫ fst G.X X) hm₂
    simpa using hh

/-- If the action relation is smooth, so is every rational orbit morphism. -/
theorem smooth_orbitMap (hΨ : Smooth (lift a.hom (snd G.X X)).left)
    (x : 𝟙_ (Over S) ⟶ X) : Smooth (a.orbitMap x).left :=
  MorphismProperty.of_isPullback (P := @Smooth)
    ((a.isPullback_orbitMap x).map (Over.forget S)).flip hΨ

/-- If the action relation is smooth, so is its base change along every test morphism. -/
theorem smooth_relationAlong (hΨ : Smooth (lift a.hom (snd G.X X)).left)
    {T : Over S} (t : T ⟶ X) : Smooth (a.relationAlong t).left :=
  MorphismProperty.of_isPullback (P := @Smooth)
    ((a.isPullback_relationAlong t).map (Over.forget S)).flip hΨ

/-- The orbit of a rational section is stable: if `g • t s` lies in the orbit of `x`,
then so does `t s`. -/
theorem mem_range_orbitMap_of_actAlong {T : Over S} (t : T ⟶ X)
    (x : 𝟙_ (Over S) ⟶ X) (p : (G.X ⊗ T).left)
    (hp : (a.actAlong t).left p ∈ Set.range (a.orbitMap x).left) :
    t.left ((snd G.X T).left p) ∈ Set.range (a.orbitMap x).left := by
  obtain ⟨g, hg⟩ := hp
  obtain ⟨r, hr₁, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := (a.actAlong t).left) (g := (a.orbitMap x).left) p g hg.symm
  let P : Over S := Over.mk (pullback.fst (a.actAlong t).left (a.orbitMap x).left ≫
    (G.X ⊗ T).hom)
  let f₁ : P ⟶ G.X ⊗ T := Over.homMk (pullback.fst _ _) rfl
  let f₂ : P ⟶ G.X := Over.homMk (pullback.snd (a.actAlong t).left (a.orbitMap x).left) (by
    simp only [P, Over.mk_hom]
    rw [← Over.w (a.orbitMap x), ← Category.assoc, ← pullback.condition, Category.assoc,
      Over.w (a.actAlong t)])
  have hcond : f₁ ≫ a.actAlong t = f₂ ≫ a.orbitMap x :=
    Over.OverMorphism.ext pullback.condition
  have key : ((f₁ ≫ fst G.X T)⁻¹ * f₂) ≫ a.orbitMap x = f₁ ≫ snd G.X T ≫ t := by
    rw [a.comp_orbitMap, a.act_mul, ← a.comp_orbitMap, ← hcond, a.comp_actAlong,
      ← a.act_mul, inv_mul_cancel, a.act_one]
  refine ⟨((f₁ ≫ fst G.X T)⁻¹ * f₂).left r, ?_⟩
  have hk := congrArg (fun φ : P ⟶ X => φ.left r) key
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at hk
  rw [hk]
  change t.left ((snd G.X T).left
    ((pullback.fst (a.actAlong t).left (a.orbitMap x).left) r)) = _
  rw [hr₁]

end General

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  {X : Over (Spec (CommRingCat.of k))} (a : SchemeAction G X)

/-- Over a field, the action along any test morphism has open image when the
action relation is smooth. -/
theorem isOpen_range_actAlong (hΨ : Smooth (lift a.hom (snd G.X X)).left)
    {T : Over (Spec (CommRingCat.of k))} (t : T ⟶ X) :
    IsOpen (Set.range (a.actAlong t).left) := by
  have : Smooth (a.relationAlong t).left := a.smooth_relationAlong hΨ t
  have : UniversallyOpen (fst X T).left := by
    change UniversallyOpen (pullback.fst X.hom T.hom)
    infer_instance
  have : UniversallyOpen (a.actAlong t).left := by
    rw [← a.relationAlong_fst, Over.comp_left]
    infer_instance
  exact (a.actAlong t).left.isOpenMap.isOpen_range

/-- Over a field, a smooth action relation makes each rational orbit closed. -/
theorem isClosed_range_orbitMap (hΨ : Smooth (lift a.hom (snd G.X X)).left)
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    IsClosed (Set.range (a.orbitMap x).left) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro y hy
  let T : Over (Spec (CommRingCat.of k)) :=
    Over.mk (X.left.fromSpecResidueField y ≫ X.hom)
  let t : T ⟶ X := Over.homMk (X.left.fromSpecResidueField y) rfl
  refine ⟨Set.range (a.actAlong t).left, ?_, a.isOpen_range_actAlong hΨ t, ?_⟩
  · rintro _ ⟨p, rfl⟩ hpU
    apply hy
    have hm := a.mem_range_orbitMap_of_actAlong t x p hpU
    have ht : ∀ z, t.left z = y := fun z => Scheme.fromSpecResidueField_apply y z
    rwa [ht] at hm
  · have hs : lift (1 : T ⟶ G.X) (𝟙 T) ≫ a.actAlong t = t := by
      rw [a.comp_actAlong]
      simp
    let s : T.left := IsLocalRing.closedPoint (X.left.residueField y)
    refine ⟨(lift (1 : T ⟶ G.X) (𝟙 T)).left s, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hs]
    exact Scheme.fromSpecResidueField_apply _ _

end Field

/-- The affine orbit factorization for a smooth action relation. -/
theorem smoothActionAffineOrbit : SmoothActionAffineOrbitStatement.{u} := by
  intro k _ G _ _ X _ _ a hΨ x
  have hsmooth : Smooth (a.orbitMap x).left := a.smooth_orbitMap hΨ x
  have hopen : IsOpen (Set.range (a.orbitMap x).left) :=
    (a.orbitMap x).left.isOpenMap.isOpen_range
  have hclosed := a.isClosed_range_orbitMap hΨ x
  let U : X.left.Opens := ⟨Set.range (a.orbitMap x).left, hopen⟩
  have : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by simpa [U] using hclosed)
  have : IsAffine X.left := isAffine_of_isAffineHom X.hom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : IsAffine U.toScheme := isAffine_of_isAffineHom U.ι
  let Q : Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ X.hom)
  let j : Q ⟶ X := Over.homMk U.ι rfl
  let qL : G.X.left ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (a.orbitMap x).left (by simp [U])
  have hqL : qL ≫ U.ι = (a.orbitMap x).left := IsOpenImmersion.lift_fac _ _ _
  let q : G.X ⟶ Q := Over.homMk qL (by
    simp only [Q, Over.mk_hom]
    rw [← Category.assoc, hqL, Over.w (a.orbitMap x)])
  refine ⟨Q, q, j, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsAffineHom (U.ι ≫ X.hom)
    infer_instance
  · change LocallyOfFiniteType (U.ι ≫ X.hom)
    infer_instance
  · change QuasiCompact (U.ι ≫ X.hom)
    infer_instance
  · change IsOpenImmersion U.ι
    infer_instance
  · change IsClosedImmersion U.ι
    infer_instance
  · change Smooth qL
    have sq : IsPullback (𝟙 G.X.left) qL (a.orbitMap x).left U.ι :=
      IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, hqL]⟩
    exact MorphismProperty.of_isPullback (P := @Smooth) sq hsmooth
  · change Surjective qL
    refine ⟨fun u => ?_⟩
    have hu : U.ι u ∈ Set.range (a.orbitMap x).left := by
      have : U.ι u ∈ Set.range U.ι := ⟨u, rfl⟩
      simpa [U] using this
    obtain ⟨g, hg⟩ := hu
    refine ⟨g, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hqL, hg]
  · change QuasiCompact qL
    infer_instance
  · exact Over.OverMorphism.ext hqL

end Langlands.GroupScheme.SchemeAction
