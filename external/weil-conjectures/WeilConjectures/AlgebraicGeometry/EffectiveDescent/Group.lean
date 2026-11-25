/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import WeilConjectures.AlgebraicGeometry.EffectiveDescent.Basic

/-!
# Group structures descend

Let `p : X ⟶ Y` be faithfully flat and quasi-compact and let `V` be a group scheme over `X` with
an effective descent datum `D`, with descended scheme `V₀`, such that the group law of `V` is
compatible with `D`. We construct a group structure on `V₀`, and show that it is the only one
for which the projection `V ⟶ V₀` maps products of points to products of points.

For a scheme `T` over `Y`, write `T' = T ×_Y X`. A `T`-point `t` of `V₀` gives a point of `V`
over `T' ⟶ X` (`CategoryTheory.Over.DescentDatum.liftPoint`), and this identifies the
`T`-points of `V₀` with the points of `V` over `T'` which are invariant under `D`
(`CategoryTheory.Over.DescentDatum.PointInvariant`). The invariant points form a subgroup, so
the `T`-points of `V₀` form a group, naturally in `T`, and the Yoneda lemma
(`GrpObj.ofRepresentableBy`) gives the group structure on `V₀`. Uniqueness holds because
`liftPoint` is injective (`CategoryTheory.Over.DescentDatum.mul_eq_of_descendPoint_mul`) and a
group object structure is determined by its multiplication (`CategoryTheory.GrpObj.ext_of_mul_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace CategoryTheory.GrpObj

/-- A group object structure in a cartesian monoidal category is determined by its
multiplication. -/
lemma ext_of_mul_eq {C : Type*} [Category C] [CartesianMonoidalCategory C] {G : C}
    {G₁ G₂ : GrpObj G} (h : G₁.mul = G₂.mul) : G₁ = G₂ := by
  have hg (T : C) : (letI := G₁; (Hom.group : Group (T ⟶ G))) =
      (letI := G₂; (Hom.group : Group (T ⟶ G))) :=
    Group.ext (funext₂ fun a b ↦ congrArg (lift a b ≫ ·) h)
  have e : toUnit (𝟙_ C) = 𝟙 _ := toUnit_unique _ _
  have hη : G₁.one = G₂.one :=
    calc G₁.one = toUnit (𝟙_ C) ≫ G₁.one := by rw [e, Category.id_comp]
      _ = toUnit (𝟙_ C) ≫ G₂.one :=
        congrArg (fun g : Group (𝟙_ C ⟶ G) ↦ (@One.one _ g.toOne)) (hg (𝟙_ C))
      _ = G₂.one := by rw [e, Category.id_comp]
  have hι : G₁.inv = G₂.inv :=
    calc G₁.inv = 𝟙 G ≫ G₁.inv := (Category.id_comp _).symm
      _ = 𝟙 G ≫ G₂.inv := congrArg (fun g : Group (G ⟶ G) ↦ (@Inv.inv _ g.toInv (𝟙 G))) (hg G)
      _ = G₂.inv := Category.id_comp _
  obtain @⟨⟨η₁, μ₁⟩, ι₁⟩ := G₁
  obtain @⟨⟨η₂, μ₂⟩, ι₂⟩ := G₂
  obtain rfl : μ₁ = μ₂ := h
  obtain rfl : η₁ = η₂ := hη
  obtain rfl : ι₁ = ι₂ := hι
  rfl

end CategoryTheory.GrpObj

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {X Y : Scheme.{u}} {p : X ⟶ Y} {V : Over X} {V₀ : Over Y} {qV : V.left ⟶ V₀.left}

/-- The point of `V` over `T ×_Y X ⟶ X` induced by a `T`-point of `V₀`, for a projection
`qV : V ⟶ V₀` exhibiting `V` as the base change of `V₀` along `p`. -/
noncomputable def liftPoint (hqV : IsPullback qV V.hom V₀.hom p) {T : Over Y} (t : T ⟶ V₀) :
    Over.mk (pullback.snd T.hom p) ⟶ V :=
  Over.homMk (hqV.lift (pullback.fst T.hom p ≫ t.left) (pullback.snd T.hom p)
    (by rw [Category.assoc, Over.w t, pullback.condition])) (by simp)

@[reassoc (attr := simp)]
lemma liftPoint_left_qV (hqV : IsPullback qV V.hom V₀.hom p) {T : Over Y} (t : T ⟶ V₀) :
    (liftPoint hqV t).left ≫ qV = pullback.fst T.hom p ≫ t.left := by
  simp [liftPoint]

/-- A point `b` of `V` over `T ×_Y X ⟶ X` is **invariant** under the descent datum `D` if its
two pullbacks to `(T ×_Y X) ×_T (T ×_Y X)` correspond under `D`. -/
def PointInvariant (D : DescentDatum p V) {T : Over Y} (b : Over.mk (pullback.snd T.hom p) ⟶ V) :
    Prop :=
  ∀ ⦃S : Scheme.{u}⦄ (g₁ g₂ : S ⟶ Limits.pullback T.hom p)
    (hg : g₁ ≫ pullback.fst T.hom p = g₂ ≫ pullback.fst T.hom p),
    D.transport (g₁ ≫ pullback.snd T.hom p) (g₂ ≫ pullback.snd T.hom p)
      (by rw [Category.assoc, Category.assoc, ← pullback.condition, reassoc_of% hg])
      (Over.homMkComp g₁ ≫ b) =
      Over.homMkComp g₂ ≫ b

variable (D : DescentDatum p V) (hqV : IsPullback qV V.hom V₀.hom p)
  (hDV : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a : Over.mk f₁ ⟶ V),
    (D.transport f₁ f₂ h a).left ≫ qV = a.left ≫ qV)

include hDV in
lemma pointInvariant_liftPoint {T : Over Y} (t : T ⟶ V₀) : D.PointInvariant (liftPoint hqV t) := by
  intro S g₁ g₂ hg
  refine D.transport_eq_of_isPullback hqV hDV _ _ _ _ _ ?_
  simp [reassoc_of% hg]

lemma liftPoint_injective [Flat p] [Surjective p] [QuasiCompact p] {T : Over Y} :
    Function.Injective (liftPoint hqV (T := T)) := by
  have : Flat (pullback.fst T.hom p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom p).flip inferInstance
  have : Surjective (pullback.fst T.hom p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom p).flip inferInstance
  have : QuasiCompact (pullback.fst T.hom p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom p).flip inferInstance
  intro t₁ t₂ h
  ext
  rw [← cancel_epi (pullback.fst T.hom p), ← liftPoint_left_qV hqV, ← liftPoint_left_qV hqV, h]

include hDV in
lemma exists_liftPoint_eq [Flat p] [Surjective p] [QuasiCompact p] {T : Over Y}
    (b : Over.mk (pullback.snd T.hom p) ⟶ V) (hb : D.PointInvariant b) :
    ∃ t : T ⟶ V₀, liftPoint hqV t = b := by
  have : Flat (pullback.fst T.hom p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom p).flip inferInstance
  have : Surjective (pullback.fst T.hom p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom p).flip inferInstance
  have : QuasiCompact (pullback.fst T.hom p) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom p).flip inferInstance
  have hw (S : Scheme.{u}) (g₁ g₂ : S ⟶ Limits.pullback T.hom p)
      (hg : g₁ ≫ pullback.fst T.hom p = g₂ ≫ pullback.fst T.hom p) :
      g₁ ≫ b.left ≫ qV = g₂ ≫ b.left ≫ qV := by
    have h := congrArg (fun c ↦ c.left ≫ qV) (hb g₁ g₂ hg)
    simp only [hDV] at h
    simpa using h
  let t₀ := EffectiveEpi.desc (pullback.fst T.hom p) (b.left ≫ qV) (fun g₁ g₂ h ↦ hw _ g₁ g₂ h)
  have ht₀ : pullback.fst T.hom p ≫ t₀ = b.left ≫ qV := EffectiveEpi.fac _ _ _
  have ht₀Y : t₀ ≫ V₀.hom = T.hom := by
    rw [← cancel_epi (pullback.fst T.hom p), reassoc_of% ht₀, hqV.w, Over.w_assoc]
    exact pullback.condition.symm
  refine ⟨Over.homMk t₀ ht₀Y, ?_⟩
  ext
  refine hqV.hom_ext ?_ ?_
  · rw [liftPoint_left_qV]
    exact ht₀
  · rw [Over.w b, Over.w (liftPoint hqV _)]

/-- Pulling back the point induced by `t` along `h : T₁ ⟶ T₂` gives the point induced by
`h ≫ t`. -/
lemma liftPoint_comp {T₁ T₂ : Over Y} (h : T₁ ⟶ T₂) (t : T₂ ⟶ V₀) :
    liftPoint hqV (h ≫ t) =
      Over.homMk (pullback.map T₁.hom p T₂.hom p h.left (𝟙 X) (𝟙 Y) (by simp) (by simp))
        (by simp) ≫ liftPoint hqV t := by
  ext
  refine hqV.hom_ext ?_ ?_
  · simp
  · simp [liftPoint]

/-- The point `qV ∘ a` of `V₀` over `Y` induced by a point `a` of `V` over `f`, for a projection
`qV : V ⟶ V₀` exhibiting `V` as the base change of `V₀` along `p`. -/
abbrev descendPoint {T : Scheme.{u}} {f : T ⟶ X} (a : Over.mk f ⟶ V) :
    Over.mk (f ≫ p) ⟶ V₀ :=
  Over.homMk (a.left ≫ qV) (by
    simp only [Over.mk_hom, Category.assoc, hqV.w]
    rw [← Category.assoc, Over.w a]
    rfl)

/-- Restricting the point of `V` induced by `descendPoint hqV a` along the section
`T ⟶ T ×_Y X` given by `f` recovers `a`. -/
lemma homMk_liftPoint_descendPoint {T : Scheme.{u}} {f : T ⟶ X} (a : Over.mk f ⟶ V) :
    (Over.homMk (pullback.lift (𝟙 T) f (by simp)) (by simp) :
      Over.mk f ⟶ Over.mk (pullback.snd (f ≫ p) p)) ≫ liftPoint hqV (descendPoint hqV a) = a := by
  ext
  refine hqV.hom_ext ?_ ?_
  · simp only [Over.mk_left, Over.comp_left, Over.homMk_left, Category.assoc, liftPoint_left_qV,
      Over.mk_hom, limit.lift_π_assoc, cospan_left, PullbackCone.mk_π_app]
    exact Category.id_comp _
  · simp [liftPoint]

/-- The point of `V` induced by a `T`-point `t` of `V₀` descends to the pullback of `t` along
`T ×_Y X ⟶ T`. -/
lemma descendPoint_liftPoint {T : Over Y} (t : T ⟶ V₀) :
    descendPoint hqV (liftPoint hqV t) =
      (Over.homMk (pullback.fst T.hom p) pullback.condition :
        Over.mk (pullback.snd T.hom p ≫ p) ⟶ T) ≫ t := by
  ext
  simp

/-- If `qV` maps products of points of `V` to products of points of `V₀`, for monoid structures
on `V` and `V₀`, then so does `liftPoint`. -/
lemma liftPoint_mul_of_descendPoint_mul [MonObj V] [M₀ : MonObj V₀]
    (hV₀ : ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ μ[V₀])
    {T : Over Y} (x y : T ⟶ V₀) :
    liftPoint hqV (x * y) = liftPoint hqV x * liftPoint hqV y := by
  ext
  refine hqV.hom_ext ?_ ?_
  · have h := congrArg CommaMorphism.left (hV₀ _ (liftPoint hqV x) (liftPoint hqV y))
    rw [descendPoint_liftPoint, descendPoint_liftPoint, ← comp_lift_assoc] at h
    rw [liftPoint_left_qV]
    exact h.symm
  · rw [Over.w, Over.w]

/-- Two monoid structures on `V₀` for which `qV` maps products of points of `V` to products of
points of `V₀` have the same multiplication. -/
lemma mul_eq_of_descendPoint_mul [Flat p] [Surjective p] [QuasiCompact p] [MonObj V]
    (M₁ M₂ : MonObj V₀)
    (h₁ : ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ M₁.mul)
    (h₂ : ∀ {T : Scheme.{u}} (f : T ⟶ X) (a b : Over.mk f ⟶ V),
      descendPoint hqV (lift a b ≫ μ[V]) =
        lift (descendPoint hqV a) (descendPoint hqV b) ≫ M₂.mul) :
    M₁.mul = M₂.mul := by
  have e₁ : liftPoint hqV (lift (fst V₀ V₀) (snd V₀ V₀) ≫ M₁.mul) =
      liftPoint hqV (fst V₀ V₀) * liftPoint hqV (snd V₀ V₀) :=
    liftPoint_mul_of_descendPoint_mul (M₀ := M₁) hqV h₁ (fst V₀ V₀) (snd V₀ V₀)
  have e₂ : liftPoint hqV (lift (fst V₀ V₀) (snd V₀ V₀) ≫ M₂.mul) =
      liftPoint hqV (fst V₀ V₀) * liftPoint hqV (snd V₀ V₀) :=
    liftPoint_mul_of_descendPoint_mul (M₀ := M₂) hqV h₂ (fst V₀ V₀) (snd V₀ V₀)
  rw [lift_fst_snd, Category.id_comp] at e₁ e₂
  exact liftPoint_injective hqV (e₁.trans e₂.symm)

section Group

variable [GrpObj V]
  (hμ : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) (a b : Over.mk f₁ ⟶ V),
    D.transport f₁ f₂ h (lift a b ≫ μ[V]) =
      lift (D.transport f₁ f₂ h a) (D.transport f₁ f₂ h b) ≫ μ[V])
  (hη : ∀ {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p),
    D.transport f₁ f₂ h (toUnit _ ≫ η[V]) = toUnit _ ≫ η[V])

include hμ in
lemma transport_mul {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a b : Over.mk f₁ ⟶ V) :
    D.transport f₁ f₂ h (a * b) = D.transport f₁ f₂ h a * D.transport f₁ f₂ h b :=
  hμ f₁ f₂ h a b

include hη in
lemma transport_one {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p) :
    D.transport f₁ f₂ h 1 = 1 :=
  hη f₁ f₂ h

include hμ hη in
lemma transport_inv {T : Scheme.{u}} (f₁ f₂ : T ⟶ X) (h : f₁ ≫ p = f₂ ≫ p)
    (a : Over.mk f₁ ⟶ V) :
    D.transport f₁ f₂ h a⁻¹ = (D.transport f₁ f₂ h a)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    rw [← D.transport_mul hμ, inv_mul_cancel, D.transport_one hη])

/-- The subgroup of points of `V` over `T ×_Y X ⟶ X` which are invariant under `D`. -/
def invariantSubgroup (T : Over Y) : Subgroup (Over.mk (pullback.snd T.hom p) ⟶ V) where
  carrier := {b | D.PointInvariant b}
  mul_mem' {b c} hb hc S g₁ g₂ hg := by
    rw [MonObj.comp_mul, D.transport_mul hμ, hb g₁ g₂ hg, hc g₁ g₂ hg, MonObj.comp_mul]
  one_mem' S g₁ g₂ hg := by
    rw [MonObj.comp_one, D.transport_one hη, MonObj.comp_one]
  inv_mem' {b} hb S g₁ g₂ hg := by
    rw [GrpObj.comp_inv, D.transport_inv hμ hη, hb g₁ g₂ hg, GrpObj.comp_inv]

variable [Flat p] [Surjective p] [QuasiCompact p]

/-- The `T`-points of `V₀` are the invariant points of `V` over `T ×_Y X ⟶ X`. -/
noncomputable def pointEquiv (T : Over Y) : (T ⟶ V₀) ≃ D.invariantSubgroup hμ hη T :=
  Equiv.ofBijective (fun t ↦ ⟨liftPoint hqV t, D.pointInvariant_liftPoint hqV hDV t⟩)
    ⟨fun _ _ h ↦ liftPoint_injective hqV (congrArg Subtype.val h), fun b ↦
      (D.exists_liftPoint_eq hqV hDV b.1 b.2).imp fun _ h ↦ Subtype.ext h⟩

/-- The group structure on the `T`-points of `V₀`, transported from the invariant points of
`V`. -/
noncomputable abbrev homGroup (T : Over Y) : Group (T ⟶ V₀) :=
  (D.pointEquiv hqV hDV hμ hη T).group

lemma liftPoint_mul {T : Over Y} (x y : T ⟶ V₀) :
    letI := D.homGroup hqV hDV hμ hη T
    liftPoint hqV (x * y) = liftPoint hqV x * liftPoint hqV y :=
  congrArg Subtype.val ((D.pointEquiv hqV hDV hμ hη T).apply_symm_apply _)

lemma liftPoint_one {T : Over Y} :
    letI := D.homGroup hqV hDV hμ hη T
    liftPoint hqV (1 : T ⟶ V₀) = 1 :=
  congrArg Subtype.val ((D.pointEquiv hqV hDV hμ hη T).apply_symm_apply _)

/-- The presheaf of groups of points of `V₀`. -/
@[simps]
noncomputable def descendedPresheaf : (Over Y)ᵒᵖ ⥤ GrpCat.{u} where
  obj T := @GrpCat.of (T.unop ⟶ V₀) (D.homGroup hqV hDV hμ hη T.unop)
  map {T₁ T₂} h :=
    letI := D.homGroup hqV hDV hμ hη T₁.unop
    letI := D.homGroup hqV hDV hμ hη T₂.unop
    GrpCat.ofHom
    { toFun := fun t ↦ h.unop ≫ t
      map_one' := liftPoint_injective hqV (by
        rw [liftPoint_comp, D.liftPoint_one hqV hDV hμ hη, D.liftPoint_one hqV hDV hμ hη,
          MonObj.comp_one])
      map_mul' := fun x y ↦ liftPoint_injective hqV (by
        rw [liftPoint_comp, D.liftPoint_mul hqV hDV hμ hη, D.liftPoint_mul hqV hDV hμ hη,
          liftPoint_comp, liftPoint_comp,
          MonObj.comp_mul]) }

/-- `V₀` represents its presheaf of points. -/
noncomputable def descendedRepresentableBy :
    (D.descendedPresheaf hqV hDV hμ hη ⋙ CategoryTheory.forget _).RepresentableBy V₀ where
  homEquiv := Equiv.refl _
  homEquiv_comp _ _ := rfl

/-- The points of `V₀` induced by points of `V` multiply as the points of `V` do. -/
lemma descendPoint_mul {T : Scheme.{u}} {f : T ⟶ X} (a b : Over.mk f ⟶ V) :
    letI := D.homGroup hqV hDV hμ hη (Over.mk (f ≫ p))
    descendPoint hqV (a * b) = descendPoint hqV a * descendPoint hqV b := by
  let := D.homGroup hqV hDV hμ hη (Over.mk (f ≫ p))
  have hs := congrArg (fun c ↦ c.left ≫ qV) (congrArg
    ((Over.homMk (pullback.lift (𝟙 T) f (by simp)) (by simp) :
      Over.mk f ⟶ Over.mk (pullback.snd (f ≫ p) p)) ≫ ·)
    (D.liftPoint_mul hqV hDV hμ hη (descendPoint hqV a) (descendPoint hqV b)))
  simp only [MonObj.comp_mul, homMk_liftPoint_descendPoint] at hs
  ext
  refine hs.symm.trans ?_
  simp only [Over.mk_left, Over.comp_left, Over.homMk_left, Category.assoc, liftPoint_left_qV,
    Over.mk_hom, limit.lift_π_assoc, cospan_left, PullbackCone.mk_π_app]
  exact Category.id_comp _

end Group

end CategoryTheory.Over.DescentDatum
