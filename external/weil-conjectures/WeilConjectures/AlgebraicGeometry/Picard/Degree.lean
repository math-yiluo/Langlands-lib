/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# The fibrewise degree on the relative Picard functor

Let `f: X ⟶ S` be a proper morphism locally of finite presentation.  For a scheme `T` over `S`
and a class `ℒ ∈ Pic (X_T)` of the Picard presheaf, the *fibrewise degree* of `ℒ` at a point
`t ∈ T` is `deg ℒ_t = χ(ℒ_t) - χ(𝒪_{X_t})`, computed on the fibre `X_t` of `X_T ⟶ T` over the
residue field `κ(t)`.  We show that it is compatible with base change and, for `f` flat, locally
constant; and that it descends to the relative Picard functor `Pic_{X/S}`, the fppf
sheafification of the Picard presheaf, as a locally constant function on `T` attached to every
section of `Pic_{X/S}` over `T`.

## Main definitions

- `AlgebraicGeometry.picardPresheafDegree`: the fibrewise degree `t ↦ deg ℒ_t` of a class
  `ℒ ∈ Pic (X_T)`.
- `AlgebraicGeometry.picardDegree`: the degree of a section of the relative Picard functor, a
  function `T → ℤ`.

## Main statements

- `AlgebraicGeometry.isLocallyConstant_picardPresheafDegree` and
  `AlgebraicGeometry.picardPresheafDegree_map`: the fibrewise degree is locally constant and
  compatible with base change.
- `AlgebraicGeometry.picardPresheafDegree_mul_map_snd`: twisting by a class pulled back from
  the base does not change the fibrewise degree.
- `AlgebraicGeometry.picardPresheafDegree_eq_of_toPicardFunctor_eq`: two classes with the same
  image in `Pic_{X/S}` have the same fibrewise degree.
- `AlgebraicGeometry.Scheme.Modules.degree_pullback_of_isPullback`: the degree of an invertible
  module on a proper scheme over a field is invariant under base change along any cartesian square
  of fields.
- `AlgebraicGeometry.picardDegree_toPicardFunctor`, `AlgebraicGeometry.picardDegree_map` and
  `AlgebraicGeometry.isLocallyConstant_picardDegree`: the degree of a section of `Pic_{X/S}` is
  the fibrewise degree of any local representative, is compatible with base change, and is
  locally constant.

## Implementation details

The fibrewise degree is defined through the fibre Euler characteristics
`AlgebraicGeometry.Scheme.Modules.eulerCharFiber` of `ℒ` and of `𝒪_{X_T}` along the projection
`X_T ⟶ T`, so that the semicontinuity package of
`WeilConjectures/AlgebraicGeometry/Cohomology/DirectImage.lean` applies directly.

Instead of a morphism `Pic_{X/S} ⟶ ℤ` to the constant sheaf, the degree is spelled out as a
function `AlgebraicGeometry.picardDegree` on sections, together with its
naturality `AlgebraicGeometry.picardDegree_map` and its local constancy; the sheaf property of
the target is not needed.  The tensor product on `Pic (X_T)` is the group law of
`WeilConjectures/AlgebraicGeometry/Picard/Group.lean`. For a smooth proper curve, the
additivity of the degree on the fibres over field-valued points is
`AlgebraicGeometry.picardFibreDegree_mul`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {X S : Scheme.{u}}

section PresheafDegree

/-- The **fibrewise degree** of a class of the Picard presheaf.  Let `f: X ⟶ S` be a morphism,
`T` a scheme over `S` and `ℒ ∈ Pic (X_T)`, `X_T = X ×_S T`.  For a point `t ∈ T` the fibre
`X_t` of the projection `X_T ⟶ T` is a scheme over the residue field `κ(t)`, and the fibrewise
degree of `ℒ` at `t` is `deg ℒ_t = χ(X_t, ℒ_t) - χ(X_t, 𝒪_{X_t})`. -/
noncomputable def picardPresheafDegree (f : X ⟶ S) {T : Over S}
    (L : (picardPresheaf f).obj (.op T)) (t : T.left) : ℤ :=
  Modules.eulerCharFiber ((fromSkeleton _).obj (Pic.val (Y := pullback f T.hom) L))
      (pullback.snd f T.hom) t -
    Modules.eulerCharFiber (SheafOfModules.unit (pullback f T.hom).ringCatSheaf)
      (pullback.snd f T.hom) t

variable (f : X ⟶ S)

/-- **The fibrewise degree is compatible with base change.** For `g: T' ⟶ T` and
`ℒ ∈ Pic (X_T)`, the fibrewise degree of the pullback of `ℒ` to `X_{T'}` at `t'` is the
fibrewise degree of `ℒ` at the image of `t'`. -/
theorem picardPresheafDegree_map [IsProper f] [LocallyOfFinitePresentation f] {T T' : Over S}
    (g : T' ⟶ T) (L : (picardPresheaf f).obj (.op T)) (t : T'.left) :
    picardPresheafDegree f ((picardPresheaf f).map g.op L) t =
      picardPresheafDegree f L (g.left t) := by
  have := Modules.isGrothendieckAbelian (pullback f T.hom)
  have := Pic.isInvertible (Y := pullback f T.hom) L
  have : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : SheafOfModules.IsFinitePresentation.{u, u, u}
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have hsq := isPullback_baseChangeMap f g
  simp only [picardPresheafDegree]
  rw [← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ hsq,
    ← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ hsq,
    Modules.eulerCharFiber_congr (Modules.pullbackObjUnitIso _),
    ← Modules.eulerCharFiber_congr (fromSkeletonToSkeletonIso
      ((Modules.pullback (baseChangeMap f g)).obj ((fromSkeleton _).obj (Pic.val L))))]
  rfl

/-- **The fibrewise degree is compatible with cartesian squares of families.** Let `f' : X' ⟶ S'`
be another morphism, `T'` a scheme over `S'` and `e : X'_{T'} ⟶ X_T` a morphism over
`φ : T' ⟶ T` exhibiting `X'_{T'}` as `X_T ×_T T'`. Then the fibrewise degree of the pullback of
`ℒ ∈ Pic (X_T)` along `e` at `t'` is the fibrewise degree of `ℒ` at `φ(t')`. -/
theorem picardPresheafDegree_pic_map_of_isPullback [IsProper f] [LocallyOfFinitePresentation f]
    {X' S' : Scheme.{u}} (f' : X' ⟶ S') {T : Over S} {T' : Over S'} (φ : T'.left ⟶ T.left)
    (e : pullback f' T'.hom ⟶ pullback f T.hom)
    (sq : IsPullback e (pullback.snd f' T'.hom) (pullback.snd f T.hom) φ)
    (L : (picardPresheaf f).obj (.op T)) (t : T'.left) :
    picardPresheafDegree f' (Pic.map e L) t = picardPresheafDegree f L (φ t) := by
  have := Modules.isGrothendieckAbelian (pullback f T.hom)
  have := Pic.isInvertible (Y := pullback f T.hom) L
  have : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : SheafOfModules.IsFinitePresentation.{u, u, u}
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  simp only [picardPresheafDegree]
  rw [← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ sq,
    ← Modules.eulerCharFiber_pullback_of_isPullback _ _ _ _ _ sq,
    Modules.eulerCharFiber_congr (Modules.pullbackObjUnitIso _),
    ← Modules.eulerCharFiber_congr (fromSkeletonToSkeletonIso
      ((Modules.pullback e).obj ((fromSkeleton _).obj (Pic.val L))))]
  rfl

/-- **The fibrewise degree is locally constant** when `f` is proper, flat and locally of finite
presentation. -/
theorem isLocallyConstant_picardPresheafDegree [IsProper f] [LocallyOfFinitePresentation f]
    [Flat f] {T : Over S} (L : (picardPresheaf f).obj (.op T)) :
    IsLocallyConstant (picardPresheafDegree f L) := by
  have := Modules.isGrothendieckAbelian (pullback f T.hom)
  have := Pic.isInvertible (Y := pullback f T.hom) L
  have : SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : SheafOfModules.IsFinitePresentation.{u, u, u}
      (SheafOfModules.unit (pullback f T.hom).ringCatSheaf) :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  exact (Modules.isLocallyConstant_eulerCharFiber _ _
    (Modules.isFlatOver_of_isInvertible _ _)).sub
    (Modules.isLocallyConstant_eulerCharFiber _ _ (Modules.isFlatOver_of_isInvertible _ _))

/-- Twisting a class by the pullback of a class from the base does not change its restriction
to the fibres: on the fibre over `t` the twist is pulled back from `Spec κ(t)`, whose Picard group
is trivial. -/
lemma Scheme.Pic.map_fiberι_mul_map {Y T : Scheme.{u}} (g : Y ⟶ T) (L : Y.Pic) (N : T.Pic)
    (t : T) : Pic.map (g.fiberι t) (L * Pic.map g N) = Pic.map (g.fiberι t) L := by
  rw [Pic.map_mul, ← Pic.map_comp, Scheme.Hom.fiber_fac, Pic.map_comp,
    Subsingleton.elim (h := Pic.subsingleton_spec_field (T.residueField t)) (Pic.map _ N) 1,
    Pic.map_one, mul_one]

/-- The fibre Euler characteristic at `t` of (the representative of) a class of the Picard group
only depends on the restriction of the class to the fibre over `t`. -/
lemma Scheme.Modules.eulerCharFiber_eq_of_pic_map_fiberι_eq {Y T : Scheme.{u}} (g : Y ⟶ T)
    {L L' : Y.Pic} {t : T} (h : Pic.map (g.fiberι t) L = Pic.map (g.fiberι t) L') :
    Modules.eulerCharFiber ((fromSkeleton _).obj L.val) g t =
      Modules.eulerCharFiber ((fromSkeleton _).obj L'.val) g t := by
  obtain ⟨e⟩ := Pic.eq_iff_nonempty_iso.1 h
  let := g.fiberOverSpecResidueField t
  refine finsum_congr fun q ↦ ?_
  exact congrArg (fun n : ℕ ↦ (-1) ^ q * (n : ℤ)) (Modules.finrankH_congr _
    ((fromSkeletonToSkeletonIso _).symm ≪≫ e ≪≫ fromSkeletonToSkeletonIso _) q)

/-- **Twisting by a class from the base does not change the fibrewise degree.** For
`ℒ ∈ Pic (X_T)` and an invertible module `𝒩` on `T`, the fibrewise degree of `ℒ ⊗ f_T^* 𝒩` is
that of `ℒ`, where `f_T: X_T ⟶ T` is the projection. -/
theorem picardPresheafDegree_mul_map_snd {T : Over S} (L : (pullback f T.hom).Pic)
    (N : T.left.Pic) :
    picardPresheafDegree f (T := T) (L * Pic.map (pullback.snd f T.hom) N) =
      picardPresheafDegree f (T := T) L := by
  funext t
  rw [picardPresheafDegree, picardPresheafDegree,
    Modules.eulerCharFiber_eq_of_pic_map_fiberι_eq _ (Pic.map_fiberι_mul_map _ L N t)]

/-- Two classes of the Picard presheaf with the same image in the relative Picard functor have
the same fibrewise degree: they agree after pullback along an fppf covering, every point of `T`
lifts to that covering, and the fibrewise degree is compatible with base change. -/
theorem picardPresheafDegree_eq_of_toPicardFunctor_eq [IsProper f]
    [LocallyOfFinitePresentation f] {T : Over S} {L L' : (picardPresheaf f).obj (.op T)}
    (h : (toPicardFunctor f).app (.op T) L = (toPicardFunctor f).app (.op T) L') :
    picardPresheafDegree f L = picardPresheafDegree f L' := by
  funext t
  obtain ⟨Z, g, hg, -, -, z, rfl⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (Presheaf.equalizerSieve_mem (fppfTopology.over S) (toPicardFunctor f) L L' h) t
  rw [← picardPresheafDegree_map, ← picardPresheafDegree_map]
  exact congrArg (picardPresheafDegree f · z) hg

end PresheafDegree

section Degree

variable (f : X ⟶ S)

/-- Every point of `T` carries a local representative of a section `x` of the relative Picard
functor over `T`: a morphism `g : Z ⟶ T`, flat and locally of finite presentation, whose image
contains the point, and a class `ℒ ∈ Pic (X_Z)` whose image in `Pic_{X/S}(Z)` is the pullback of
`x`.  Recorded together with the fibrewise degree of `ℒ` at a lift of the point. -/
lemma exists_picardPresheafDegree_eq {T : Over S} (x : (picardFunctor f).obj.obj (.op T))
    (t : T.left) :
    ∃ (n : ℤ) (Z : Over S) (g : Z ⟶ T) (L : (picardPresheaf f).obj (.op Z)) (z : Z.left),
      (toPicardFunctor f).app (.op Z) L = (picardFunctor f).obj.map g.op x ∧ g.left z = t ∧
        Flat g.left ∧ LocallyOfFinitePresentation g.left ∧ picardPresheafDegree f L z = n := by
  obtain ⟨Z, g, ⟨L, hL⟩, hg₁, hg₂, z, hz⟩ := exists_flat_mem_of_mem_fppfTopology_over
    (Presheaf.imageSieve_mem (fppfTopology.over S) (toPicardFunctor f) x) t
  exact ⟨_, Z, g, L, z, hL, hz, hg₁, hg₂, rfl⟩

/-- The **degree** of a section `x` of the relative Picard functor `Pic_{X/S}` over `T`: the
function `T → ℤ` whose value at `t` is the fibrewise degree `deg ℒ_z` of any local
representative `ℒ ∈ Pic (X_Z)` of `x` along `g: Z ⟶ T`, at any point `z` over `t`. -/
noncomputable def picardDegree {T : Over S} (x : (picardFunctor f).obj.obj (.op T))
    (t : T.left) : ℤ :=
  (exists_picardPresheafDegree_eq f x t).choose

/-- Local representatives of a section of `Pic_{X/S}` at points with the same image have the same
fibrewise degree. -/
lemma picardPresheafDegree_eq_of_toPicardFunctor_eq_map [IsProper f]
    [LocallyOfFinitePresentation f] {T : Over S} (x : (picardFunctor f).obj.obj (.op T))
    {Z Z' : Over S} (g : Z ⟶ T) (g' : Z' ⟶ T) (L : (picardPresheaf f).obj (.op Z))
    (L' : (picardPresheaf f).obj (.op Z'))
    (hL : (toPicardFunctor f).app (.op Z) L = (picardFunctor f).obj.map g.op x)
    (hL' : (toPicardFunctor f).app (.op Z') L' = (picardFunctor f).obj.map g'.op x)
    (z : Z.left) (z' : Z'.left) (h : g.left z = g'.left z') :
    picardPresheafDegree f L z = picardPresheafDegree f L' z' := by
  let W : Over S := Over.mk (pullback.fst g.left g'.left ≫ Z.hom)
  let p : W ⟶ Z := Over.homMk (pullback.fst g.left g'.left)
  let p' : W ⟶ Z' := Over.homMk (pullback.snd g.left g'.left) (by
    simp only [W, Over.mk_hom, ← Over.w g, ← Over.w g', pullback.condition_assoc])
  have hpp : p ≫ g = p' ≫ g' := by
    ext
    simp [p, p', pullback.condition]
  obtain ⟨w, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback z z' h
  have hw : pullback.fst g.left g'.left w = p.left w := rfl
  have hw' : pullback.snd g.left g'.left w = p'.left w := rfl
  rw [hw, hw', ← picardPresheafDegree_map, ← picardPresheafDegree_map]
  have key : (toPicardFunctor f).app (.op W) ((picardPresheaf f).map p.op L) =
      (toPicardFunctor f).app (.op W) ((picardPresheaf f).map p'.op L') := by
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hL, hL',
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hpp]
  rw [picardPresheafDegree_eq_of_toPicardFunctor_eq f key]

/-- The degree of a section of `Pic_{X/S}` is the fibrewise degree of any local representative. -/
theorem picardDegree_eq [IsProper f] [LocallyOfFinitePresentation f] {T : Over S}
    (x : (picardFunctor f).obj.obj (.op T)) {Z : Over S} (g : Z ⟶ T)
    (L : (picardPresheaf f).obj (.op Z))
    (hL : (toPicardFunctor f).app (.op Z) L = (picardFunctor f).obj.map g.op x) (z : Z.left) :
    picardDegree f x (g.left z) = picardPresheafDegree f L z := by
  obtain ⟨Z', g', L', z', hL', hz', -, -, h⟩ :=
    (exists_picardPresheafDegree_eq f x (g.left z)).choose_spec
  rw [picardDegree, ← h]
  exact picardPresheafDegree_eq_of_toPicardFunctor_eq_map f x g' g L' L hL' hL z' z hz'

/-- The degree of the image of a class `ℒ ∈ Pic (X_T)` in `Pic_{X/S}(T)` is its fibrewise
degree. -/
theorem picardDegree_toPicardFunctor [IsProper f] [LocallyOfFinitePresentation f] {T : Over S}
    (L : (picardPresheaf f).obj (.op T)) :
    picardDegree f ((toPicardFunctor f).app (.op T) L) = picardPresheafDegree f L := by
  funext t
  exact picardDegree_eq f _ (𝟙 T) L (by simp) t

/-- **The degree is natural**: for `g : T' ⟶ T` the degree of the pullback of a section `x` of
`Pic_{X/S}` is the degree of `x` composed with `g`. -/
theorem picardDegree_map [IsProper f] [LocallyOfFinitePresentation f] {T T' : Over S}
    (g : T' ⟶ T) (x : (picardFunctor f).obj.obj (.op T)) (t : T'.left) :
    picardDegree f ((picardFunctor f).obj.map g.op x) t = picardDegree f x (g.left t) := by
  obtain ⟨-, Z, h, L, z, hL, rfl, -, -, -⟩ :=
    exists_picardPresheafDegree_eq f ((picardFunctor f).obj.map g.op x) t
  rw [picardDegree_eq f _ h L hL z, show g.left (h.left z) = (h ≫ g).left z by simp,
    picardDegree_eq f x (h ≫ g) L (by rw [hL, op_comp, Functor.map_comp_apply]) z]

/-- **The degree of a section of `Pic_{X/S}` is locally constant** when `f` is proper, flat and
locally of finite presentation: near a point it is the fibrewise degree of a local
representative along a flat morphism locally of finite presentation, which is open. -/
theorem isLocallyConstant_picardDegree [IsProper f] [LocallyOfFinitePresentation f] [Flat f]
    {T : Over S} (x : (picardFunctor f).obj.obj (.op T)) :
    IsLocallyConstant (picardDegree f x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro t
  obtain ⟨-, Z, g, L, z, hL, rfl, hg₁, hg₂, -⟩ := exists_picardPresheafDegree_eq f x t
  have hV := (isLocallyConstant_picardPresheafDegree f L).isOpen_fiber
    (picardPresheafDegree f L z)
  refine ⟨g.left.base '' (picardPresheafDegree f L ⁻¹' {picardPresheafDegree f L z}),
    g.left.isOpenMap _ hV, ⟨z, rfl, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  rw [picardDegree_eq f x g L hL v, picardDegree_eq f x g L hL z]
  exact hv

end Degree

section BaseChange

/-- **The degree is invariant under base change along a cartesian square.** Let `C` be a proper
scheme over a field `K`, let `C'` over a field `K'` sit in a cartesian square over
`g: Spec K' ⟶ Spec K`, and let `ℒ` be an invertible module on `C`. Then the degree of the pullback
of `ℒ` to `C'` is the degree of `ℒ`. The square need not be the canonical one, and `g` need not
be a `K`-algebra map. -/
theorem Scheme.Modules.degree_pullback_of_isPullback {C C' : Scheme.{u}} {K K' : Type u} [Field K]
    [Field K'] [C.Over (Spec (.of K))] [C'.Over (Spec (.of K'))] [IsProper (C ↘ Spec (.of K))]
    (g : Spec (.of K') ⟶ Spec (.of K)) (g' : C' ⟶ C)
    (sq : IsPullback g' (C' ↘ Spec (.of K')) (C ↘ Spec (.of K)) g) (L : C.Modules)
    [L.IsInvertible] : ((Modules.pullback g').obj L).degree K' = L.degree K := by
  obtain ⟨s'⟩ : Nonempty (Spec (.of K')) := inferInstance
  have := Modules.IsInvertible.sheafOfModules_isInvertible L
  have : L.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have : SheafOfModules.IsInvertible.{u, u, u} (SheafOfModules.unit C.ringCatSheaf) :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : SheafOfModules.IsFinitePresentation.{u, u, u} (SheafOfModules.unit C.ringCatSheaf) :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  have := SheafOfModules.isQuasicoherent_unit (R := C'.ringCatSheaf)
  have h₁ := Modules.eulerCharFiber_eq_eulerChar (C' ↘ Spec (.of K'))
    ((Modules.pullback g').obj L) s'
  have h₂ := Modules.eulerCharFiber_eq_eulerChar (C' ↘ Spec (.of K'))
    (SheafOfModules.unit C'.ringCatSheaf) s'
  have h₃ := Modules.eulerCharFiber_eq_eulerChar (C ↘ Spec (.of K)) L (g.base s')
  have h₄ := Modules.eulerCharFiber_eq_eulerChar (C ↘ Spec (.of K))
    (SheafOfModules.unit C.ringCatSheaf) (g.base s')
  have h₅ := Modules.eulerCharFiber_pullback_of_isPullback (C ↘ Spec (.of K)) L g g' _ sq s'
  have h₆ := Modules.eulerCharFiber_pullback_of_isPullback (C ↘ Spec (.of K))
    (SheafOfModules.unit C.ringCatSheaf) g g' _ sq s'
  rw [Modules.eulerCharFiber_congr (Modules.pullbackObjUnitIso g')] at h₆
  simp only [Modules.degree]
  rw [← h₁, ← h₂, ← h₃, ← h₄, h₅, h₆]

end BaseChange

end AlgebraicGeometry
