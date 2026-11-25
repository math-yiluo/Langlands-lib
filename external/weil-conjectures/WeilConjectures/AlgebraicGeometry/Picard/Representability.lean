/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Sites.Representability
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Representability
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocusOfRank

/-!
# Representability of the Picard functor of a smooth projective curve

Let `k` be a separably closed field, let `f: X ⟶ Spec k` be a smooth projective curve and let
`σ` be a `k`-rational point of `X`.  Write `G = Pic_{X/k,σ}` for the `σ`-normalized Picard
functor (`AlgebraicGeometry.picardFunctorNormalized`).  This file states the steps of the
representability argument:

* the subfunctor `F ⊆ G` cut out by the condition that `Rf_{T,*} ℒ` is an invertible
  `𝒪_T`-module placed in degree `0`;
* `F ⊆ G` is representable by open immersions;
* the general criterion: a Zariski sheaf of groups with a representable open subfunctor that
  generates it under translation is representable by a group scheme.

The resulting representability of `Pic_{X/k}` is
`AlgebraicGeometry.isRepresentable_picardFunctor` in
`WeilConjectures/AlgebraicGeometry/Picard/Scheme.lean`.

## Implementation notes

There is no derived category of `X.Modules` available, so the condition "`Rf_{T,*} ℒ` is an
invertible module in degree `0`" is spelled out concretely by
`AlgebraicGeometry.IsInvertibleDirectImage`: `R⁰f_{T,*} ℒ` is invertible and
`R^q f_{T,*} ℒ = 0` for all `q > 0`.  The higher direct images are the right derived functors
of `AlgebraicGeometry.Scheme.Modules.pushforward f_T`; they are used inline rather than through
`AlgebraicGeometry.Scheme.Modules.higherDirectImage`, to avoid carrying that file's instance
hypotheses.

That the condition is stable under base change is
`AlgebraicGeometry.IsInvertibleDirectImage.map_of_isProper`, for `f` flat, proper and locally of
finite presentation: the locus of `T` over which a class satisfies the condition is open
(`AlgebraicGeometry.exists_opens_isInvertibleDirectImage_map_iff`). The subfunctor
`AlgebraicGeometry.picardFunctorInvertibleDirectImage` is only defined under these hypotheses,
which every smooth projective curve satisfies; for a general `f`, cohomology and base change
(Stacks 08IB) would need at least `f` quasi-compact and quasi-separated.

Every statement here assumes injective resolutions in the fibres, `∀ T,
HasInjectiveResolutions (X ×[k] T).Modules`. This hypothesis always holds, since the category of
`𝒪`-modules on a scheme is Grothendieck abelian
(`AlgebraicGeometry.Scheme.Modules.isGrothendieckAbelian`); it is discharged in this way in
`WeilConjectures/AlgebraicGeometry/Picard/Scheme.lean`.

A class in `Pic` is represented by the canonical sheaf of modules `(fromSkeleton _).obj ℒ.val`
attached to its isomorphism class, so `IsInvertibleDirectImage` is well defined on `Pic`.

Representability by open immersions of a morphism of `Type (u + 1)`-valued presheaves on
`Over (Spec k)` is expressed through `CategoryTheory.MorphismProperty.relative` for
`CategoryTheory.uliftYoneda.{u + 1}` (`CategoryTheory.MorphismProperty.presheaf` only applies to
`Type u`-valued presheaves), with the inverse image of `IsOpenImmersion` under `Over.forget`.

The representability criterion is stated for group-valued presheaves
`(Over (Spec k))ᵒᵖ ⥤ GrpCat`, the shape expected by `CategoryTheory.GrpObj.ofRepresentableBy`.
Its values must be assumed `u`-small: otherwise the statement fails, e.g. for the sheaf of
locally constant functions to a group that is not `u`-small, with `F` the trivial subgroup.

## Main definitions

- `AlgebraicGeometry.IsInvertibleDirectImage`: the condition cutting out `F`.
- `AlgebraicGeometry.picardFunctorInvertibleDirectImage`: the subfunctor `F ⊆ Pic_{X/k,σ}`.

## Main statements

- `AlgebraicGeometry.exists_opens_isInvertibleDirectImage_map_iff`: the open locus of `T` over
  which a class lies in `F`.
- `AlgebraicGeometry.isOpenImmersion_picardFunctorInvertibleDirectImage_ι`: `F` is an open
  subfunctor of `Pic_{X/k,σ}`.
- `AlgebraicGeometry.IsInvertibleDirectImage.map_of_isProper`: cohomology and base change for `F`.
- `AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor`: the representability
  criterion.

## References

* [Stacks, Tag 08IB] (cohomology and base change)
* [Stacks, Tag 0B9V] (`F` is an open subfunctor)
* [Stacks, Tag 0B9Q] (the representability criterion)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

/-- A morphism smooth of relative dimension `1` is smooth. -/
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The condition cutting out the subfunctor `F` of the Picard functor: the class
`ℒ ∈ Pic (X_T)` has `R⁰f_{T,*} ℒ` invertible and `R^q f_{T,*} ℒ = 0` for all `q > 0`, which is
the concrete form of "`Rf_{T,*} ℒ` is an invertible `𝒪_T`-module placed in degree `0`". -/
def IsInvertibleDirectImage (f : X ⟶ Spec (.of k)) (T : Over (Spec (.of k)))
    [HasInjectiveResolutions (Limits.pullback f T.hom).Modules]
    (L : (Limits.pullback f T.hom).Pic) : Prop :=
  SheafOfModules.IsInvertible
      (((Modules.pushforward (Limits.pullback.snd f T.hom)).rightDerived 0).obj
        ((fromSkeleton _).obj L.val)) ∧
    ∀ q : ℕ, 0 < q →
      IsZero (((Modules.pushforward (Limits.pullback.snd f T.hom)).rightDerived q).obj
        ((fromSkeleton _).obj L.val))

/-- **The open locus of `F` for a single class.** Let `f: X ⟶ Spec k` be flat, proper and
locally of finite presentation, and let `ℒ ∈ Pic (X_T)` for a `k`-scheme `T`. There is an open
`U ⊆ T` such that a morphism `a: W ⟶ T` of `k`-schemes factors through `U` if and only if the
pullback `ℒ_W` satisfies `IsInvertibleDirectImage`, i.e. `Rf_{W,*} ℒ_W` is an invertible
`𝒪_W`-module placed in degree `0`. -/
theorem exists_opens_isInvertibleDirectImage_map_iff (f : X ⟶ Spec (.of k)) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f]
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules]
    {T : Over (Spec (.of k))} (L : (Limits.pullback f T.hom).Pic) :
    ∃ U : T.left.Opens, ∀ (W : Over (Spec (.of k))) (a : W ⟶ T),
      IsInvertibleDirectImage f W (Pic.map (baseChangeMap f a) L) ↔ Set.range a.left ⊆ U := by
  let ℒ : (Limits.pullback f T.hom).Modules := (fromSkeleton _).obj L.val
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := L.isInvertible
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℒ :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : ℒ.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  obtain ⟨U, -, hU⟩ := Modules.exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree
    (Limits.pullback.snd f T.hom) ℒ (Modules.isFlatOver_of_isInvertible _ ℒ) 0 1
  refine ⟨U, fun W a ↦ ?_⟩
  rw [hU _ _ _ (isPullback_baseChangeMap f a), Modules.isFiniteLocallyFreeInDegree_zero_one_iff]
  -- the chosen representative of the class `ℒ_W` is isomorphic to the pullback of `ℒ`
  let e (q : ℕ) := ((Modules.pushforward (Limits.pullback.snd f W.hom)).rightDerived q).mapIso
    (fromSkeletonToSkeletonIso ((Modules.pullback (baseChangeMap f a)).obj ℒ))
  exact ⟨fun ⟨h₀, h⟩ ↦ ⟨fun q hq ↦ (h q (Nat.pos_of_ne_zero hq)).of_iso (e q).symm,
      SheafOfModules.IsInvertible.of_iso.{u, u, u} (e 0) (h := h₀)⟩,
    fun ⟨h, h₀⟩ ↦ ⟨SheafOfModules.IsInvertible.of_iso.{u, u, u} (e 0).symm (h := h₀),
      fun q hq ↦ (h q hq.ne').of_iso (e q)⟩⟩

/-- **`F` is a subfunctor.** For `f: X ⟶ Spec k` flat, proper and locally of finite
presentation, the condition `IsInvertibleDirectImage` is stable under pullback along a morphism
`i: V ⟶ U` of `k`-schemes. -/
theorem IsInvertibleDirectImage.map_of_isProper (f : X ⟶ Spec (.of k)) [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f]
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules]
    {U V : Over (Spec (.of k))} (i : V ⟶ U) {L : (Limits.pullback f U.hom).Pic}
    (hL : IsInvertibleDirectImage f U L) :
    IsInvertibleDirectImage f V (Pic.map (baseChangeMap f i) L) := by
  obtain ⟨U', hU'⟩ := exists_opens_isInvertibleDirectImage_map_iff f L
  have hU : Set.range (Over.Hom.left (𝟙 U)) ⊆ U' := by
    refine (hU' U (𝟙 U)).1 ?_
    rwa [baseChangeMap_id, Pic.map_id]
  refine (hU' V i).2 (subset_trans (fun t _ ↦ ?_) hU)
  exact ⟨t, rfl⟩

/-- **The subfunctor `F`.** Let `k` be a field, let `f: X ⟶ Spec k` be flat, proper and locally
of finite presentation, with a `k`-rational point `σ`, and let `G = Pic_{X/k,σ}` be the
`σ`-normalized Picard functor. The subfunctor `F ⊆ G` is
`F(T) = {ℒ ∈ G(T) | Rf_{T,*} ℒ is an invertible 𝒪_T-module placed in degree 0}`,
where `f_T: X_T ⟶ T` is the base change of `f`; concretely (`IsInvertibleDirectImage`),
`R⁰f_{T,*} ℒ` is an invertible `𝒪_T`-module and `R^q f_{T,*} ℒ = 0` for all `q > 0`. -/
noncomputable def picardFunctorInvertibleDirectImage (f : X ⟶ Spec (.of k)) [Flat f]
    [IsProper f] [LocallyOfFinitePresentation f]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules] :
    Subfunctor (picardFunctorNormalized f σ hσ).toFunctor where
  obj T := {L | IsInvertibleDirectImage f T.unop (L : (picardPresheaf f).obj T)}
  map := by
    rintro ⟨U⟩ ⟨V⟩ ⟨i⟩ L hL
    exact IsInvertibleDirectImage.map_of_isProper f i hL

/-- **`F` is an open subfunctor.** The inclusion `F ⊆ G = Pic_{X/k,σ}` is representable by open
immersions. -/
theorem isOpenImmersion_picardFunctorInvertibleDirectImage_ι [IsSepClosed k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 (Spec (.of k)))
    [∀ T : Over (Spec (.of k)), HasInjectiveResolutions (Limits.pullback f T.hom).Modules] :
    (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} (picardFunctorInvertibleDirectImage f σ hσ).ι :=
  relative_isOpenImmersion_of_exists_opens fun _ x ↦
    exists_opens_isInvertibleDirectImage_map_iff f x.1

/-- **The criterion: a functor generated by a representable open subfunctor.** Let
`G: (Sch/k)ᵒᵖ ⥤ Grp` be a presheaf of groups on the category of `k`-schemes such that

1. `G` is a Zariski sheaf, with `u`-small values;
2. there is a subfunctor `F ⊆ G` with
   (a) `F` representable,
   (b) the inclusion `F ⊆ G` representable by open immersions,
   (c) *generation*: for every field extension `K/k` and every `g ∈ G(K)` there is a
       `g' ∈ G(k)` with `g' g ∈ F(K)`.

Then `G` is representable by a group scheme over `k`. -/
theorem isRepresentable_of_representable_open_subfunctor
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1})
    (F : Subfunctor (G ⋙ forget GrpCat.{u + 1}))
    (hsmall : ∀ T, Small.{u} ((G ⋙ forget GrpCat.{u + 1}).obj T))
    (hG : Presheaf.IsSheaf (Scheme.zariskiTopology.over (Spec (.of k)))
      (G ⋙ forget GrpCat.{u + 1}))
    (hFrep : F.toFunctor.IsRepresentable)
    (hFopen : (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} F.ι)
    (hgen : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
      ∃ g' : G.obj (.op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A),
      Nonempty ((G ⋙ forget GrpCat.{u + 1}).RepresentableBy A) := by
  let P := G ⋙ forget GrpCat.{u + 1}
  have : ∀ T, Small.{u} (P.obj T) := hsmall
  obtain ⟨A, ⟨eF⟩⟩ := hFrep.has_representation
  -- restriction of a `k`-point `g ∈ G(k)` to `T`
  let r (T : Over (Spec (.of k))) (g : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
      G.obj (op T) :=
    (G.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom g
  have hr {T W : Over (Spec (.of k))} (a : W ⟶ T) (g) : (G.map a.op).hom (r T g) = r W g := by
    simp only [r, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp]
    congr 4
    ext
    simp
  have hP {T W : Over (Spec (.of k))} (a : W ⟶ T) (x : G.obj (op T)) :
      (G ⋙ forget GrpCat.{u + 1}).map a.op x = (G.map a.op).hom x := rfl
  let ξ₀ : G.obj (op A) := (eF.homEquiv (𝟙 A)).1
  have he {W : Over (Spec (.of k))} (b : W ⟶ A) : (eF.homEquiv b).1 = (G.map b.op).hom ξ₀ := by
    rw [← Category.comp_id b, eF.homEquiv_comp]
    rfl
  have hsymm {W : Over (Spec (.of k))} (z : P.obj (op W)) (hz : z ∈ F.obj (op W)) :
      (G.map (eF.homEquiv.symm (⟨z, hz⟩ : F.toFunctor.obj (op W))).op).hom ξ₀ = z := by
    rw [← he]
    exact congr_arg Subtype.val (eF.homEquiv.apply_symm_apply _)
  have : Small.{u} (G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) := hsmall _
  let ι := Shrink.{u} (G.obj (op (Over.mk (𝟙 (Spec (.of k))))))
  let g (i : ι) : G.obj (op (Over.mk (𝟙 (Spec (.of k))))) := (equivShrink _).symm i
  let ξ (i : ι) : P.obj (op A) := (r A (g i))⁻¹ * ξ₀
  have hξ {W : Over (Spec (.of k))} (i : ι) (b : W ⟶ A) :
      (G.map b.op).hom (ξ i) = (r W (g i))⁻¹ * (G.map b.op).hom ξ₀ := by
    rw [map_mul, map_inv, hr]
  have hinj (i : ι) {T : Over (Spec (.of k))} (a b : T ⟶ A)
      (h : P.map a.op (ξ i) = P.map b.op (ξ i)) : a = b := by
    simp only [P, hP] at h
    rw [hξ, hξ, mul_right_inj, ← he, ← he] at h
    exact eF.homEquiv.injective (Subtype.ext h)
  have hopen (i : ι) (T : Over (Spec (.of k))) (x : G.obj (op T)) : ∃ U : T.left.Opens,
      ∀ (W : Over (Spec (.of k))) (a : W ⟶ T),
        (∃ b : W ⟶ A, P.map a.op x = P.map b.op (ξ i)) ↔ Set.range a.left ⊆ U := by
    obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion hFopen T (r T (g i) * x)
    refine ⟨U, fun W a ↦ ?_⟩
    rw [← hU]
    simp only [P, hP, map_mul, hr]
    constructor
    · rintro ⟨b, hb⟩
      rw [hb, hξ, mul_inv_cancel_left, ← he]
      exact (eF.homEquiv b).2
    · intro h
      refine ⟨eF.homEquiv.symm (⟨_, h⟩ : F.toFunctor.obj (op W)), ?_⟩
      rw [hξ, hsymm, inv_mul_cancel_left]
  have hcov (T : Over (Spec (.of k))) (x : G.obj (op T)) (t : T.left) :
      ∃ (i : ι) (W : Over (Spec (.of k))) (a : W ⟶ T) (b : W ⟶ A),
        t ∈ Set.range a.left ∧ P.map a.op x = P.map b.op (ξ i) := by
    let K := T.left.residueField t
    let φ : CommRingCat.of k ⟶ K := Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
    let : Algebra k K := φ.hom.toAlgebra
    have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
        T.left.fromSpecResidueField t ≫ T.hom := by
      rw [← Spec.map_preimage (T.left.fromSpecResidueField t ≫ T.hom)]
      rfl
    let a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ T :=
      Over.homMk (T.left.fromSpecResidueField t) hK.symm
    obtain ⟨g', hg'⟩ := hgen K (P.map a.op x)
    refine ⟨equivShrink _ g', _, a, eF.homEquiv.symm (⟨_, hg'⟩ : F.toFunctor.obj _), ?_, ?_⟩
    · have h := Scheme.range_fromSpecResidueField t
      exact h.symm ▸ Set.mem_singleton t
    · simp only [P, hP]
      rw [hξ, hsymm]
      simp [g, r]
  obtain ⟨A', ⟨e⟩⟩ := (Scheme.LocalRepresentability.isRepresentable_of_isSheaf_over P hG
    (fun _ : ι ↦ A) ξ hinj hopen hcov).has_representation
  exact ⟨A', GrpObj.ofRepresentableBy A' G e, ⟨e⟩⟩

/-- **The representing scheme is covered by copies of the open subfunctor.** In the situation of
`AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor`, let `A` represent `F` and
let `A'` represent `G`. Then every point of `A'` lies in the image of an open immersion
`A ⟶ A'` of `k`-schemes. -/
theorem exists_isOpenImmersion_of_representable_open_subfunctor
    (G : (Over (Spec (.of k)))ᵒᵖ ⥤ GrpCat.{u + 1})
    (F : Subfunctor (G ⋙ forget GrpCat.{u + 1})) {A : Over (Spec (.of k))}
    (eF : F.toFunctor.RepresentableBy A)
    (hFopen : (IsOpenImmersion.inverseImage (Over.forget (Spec (.of k)))).relative
      uliftYoneda.{u + 1} F.ι)
    (hgen : ∀ (K : Type u) [Field K] [Algebra k K]
      (g : G.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))),
      ∃ g' : G.obj (.op (Over.mk (𝟙 (Spec (.of k))))),
        (G.map (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
          F.obj (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))))
    {A' : Over (Spec (.of k))} (e' : (G ⋙ forget GrpCat.{u + 1}).RepresentableBy A')
    (a : A'.left) :
    ∃ ψ : A ⟶ A', IsOpenImmersion ψ.left ∧ a ∈ Set.range ψ.left.base := by
  let P := G ⋙ forget GrpCat.{u + 1}
  -- restriction of a `k`-point `g ∈ G(k)` to `T`
  let r (T : Over (Spec (.of k))) (g : G.obj (op (Over.mk (𝟙 (Spec (.of k)))))) :
      G.obj (op T) :=
    (G.map (Over.homMk T.hom (by simp) : T ⟶ Over.mk (𝟙 (Spec (.of k)))).op).hom g
  have hr {T W : Over (Spec (.of k))} (c : W ⟶ T) (g) : (G.map c.op).hom (r T g) = r W g := by
    simp only [r, ← GrpCat.comp_apply, ← G.map_comp, ← op_comp]
    congr 4
    ext
    simp
  have hP {T W : Over (Spec (.of k))} (c : W ⟶ T) (y : G.obj (op T)) :
      P.map c.op y = (G.map c.op).hom y := rfl
  let ξ₀ : G.obj (op A) := (eF.homEquiv (𝟙 A)).1
  have he {W : Over (Spec (.of k))} (b : W ⟶ A) : (eF.homEquiv b).1 = (G.map b.op).hom ξ₀ := by
    rw [← Category.comp_id b, eF.homEquiv_comp]
    rfl
  let x : G.obj (op A') := e'.homEquiv (𝟙 A')
  have he' {W : Over (Spec (.of k))} (c : W ⟶ A') : e'.homEquiv c = (G.map c.op).hom x := by
    rw [← Category.comp_id c, e'.homEquiv_comp]
    rfl
  -- the residue field of `a`, and a class `g' ∈ G(k)` translating `x` into `F` at `a`
  let K := A'.left.residueField a
  let φ : CommRingCat.of k ⟶ K := Spec.preimage (A'.left.fromSpecResidueField a ≫ A'.hom)
  let : Algebra k K := φ.hom.toAlgebra
  have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) =
      A'.left.fromSpecResidueField a ≫ A'.hom := by
    rw [← Spec.map_preimage (A'.left.fromSpecResidueField a ≫ A'.hom)]
    rfl
  let pa : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶ A' :=
    Over.homMk (A'.left.fromSpecResidueField a) hK.symm
  obtain ⟨g', hg'⟩ := hgen K (P.map pa.op x)
  -- the open `U ⊆ A'` over which `r g' * x` lies in `F`
  obtain ⟨U, hU⟩ := exists_opens_of_relative_isOpenImmersion hFopen A' (r A' g' * x)
  have hUiff {W : Over (Spec (.of k))} (c : W ⟶ A') :
      r W g' * (G.map c.op).hom x ∈ F.obj (op W) ↔ Set.range c.left ⊆ U := by
    rw [← hU]
    simp only [P, hP, map_mul, hr]
  -- the morphism `ψ: A ⟶ A'` classifying `ξ = r g'⁻¹ * ξ₀`
  let ξ : G.obj (op A) := (r A g')⁻¹ * ξ₀
  let ψ : A ⟶ A' := e'.homEquiv.symm ξ
  have hψ : (G.map ψ.op).hom x = ξ := by
    rw [← he']
    exact e'.homEquiv.apply_symm_apply ξ
  have hξ {W : Over (Spec (.of k))} (b : W ⟶ A) :
      (G.map b.op).hom ξ = (r W g')⁻¹ * (G.map b.op).hom ξ₀ := by
    rw [map_mul, map_inv, hr]
  -- `ψ` is a monomorphism
  have hmono {W : Over (Spec (.of k))} (b₁ b₂ : W ⟶ A) (h : b₁ ≫ ψ = b₂ ≫ ψ) : b₁ = b₂ := by
    have h' := congrArg e'.homEquiv h
    rw [he', he', op_comp, op_comp, Functor.map_comp, Functor.map_comp, GrpCat.comp_apply,
      GrpCat.comp_apply, hψ, hξ, hξ, mul_right_inj, ← he, ← he] at h'
    exact eF.homEquiv.injective (Subtype.ext h')
  -- `ψ` factors through `U`
  have hψU : Set.range ψ.left ⊆ U := by
    rw [← hUiff, hψ, mul_inv_cancel_left]
    exact (eF.homEquiv (𝟙 A)).2
  -- the inclusion of `U` factors through `ψ`
  let Uo : Over (Spec (.of k)) := Over.mk (U.ι ≫ A'.hom)
  let ιU : Uo ⟶ A' := Over.homMk U.ι
  have hιU : r Uo g' * (G.map ιU.op).hom x ∈ F.obj (op Uo) := by
    rw [hUiff]
    change Set.range U.ι ⊆ U
    rw [U.range_ι]
  let b : Uo ⟶ A := eF.homEquiv.symm ⟨_, hιU⟩
  have hb : b ≫ ψ = ιU := by
    refine e'.homEquiv.injective ?_
    rw [he', he', op_comp, Functor.map_comp, GrpCat.comp_apply, hψ, hξ, ← he,
      eF.homEquiv.apply_symm_apply]
    exact inv_mul_cancel_left _ _
  have hψU' : Set.range ψ.left ⊆ Set.range U.ι := by
    rw [U.range_ι]
    exact hψU
  let ψ' : A ⟶ Uo := Over.homMk (IsOpenImmersion.lift U.ι ψ.left hψU') (by
    simp only [Uo, Over.mk_hom]
    rw [IsOpenImmersion.lift_fac_assoc, Over.w])
  have hψ' : ψ' ≫ ιU = ψ := by
    ext
    exact IsOpenImmersion.lift_fac _ _ _
  have h₁ : ψ' ≫ b = 𝟙 A := hmono _ _ (by rw [Category.assoc, hb, hψ', Category.id_comp])
  have h₂ : b ≫ ψ' = 𝟙 Uo := by
    ext1
    rw [← cancel_mono U.ι]
    change (b ≫ ψ' ≫ ιU).left = (𝟙 Uo ≫ ιU).left
    rw [hψ', hb, Category.id_comp]
  have : IsIso ψ' := ⟨b, h₁, h₂⟩
  have : IsIso ψ'.left := (Over.forget _).map_isIso ψ'
  refine ⟨ψ, ?_, ?_⟩
  · rw [← hψ', Over.comp_left]
    change IsOpenImmersion (ψ'.left ≫ U.ι)
    infer_instance
  · -- `a` lies in `U`, the image of `ψ`
    have ha : Set.range pa.left ⊆ U := by
      rw [← hUiff]
      exact hg'
    have : a ∈ Set.range pa.left := by
      have h := Scheme.range_fromSpecResidueField a
      exact h.symm ▸ Set.mem_singleton a
    have haU : a ∈ Set.range U.ι := by
      rw [U.range_ι]
      exact ha this
    obtain ⟨u, hu⟩ := haU
    refine ⟨b.left u, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hb]
    exact hu

end AlgebraicGeometry
