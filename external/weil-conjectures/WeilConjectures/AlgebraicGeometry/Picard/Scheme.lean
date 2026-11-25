/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import WeilConjectures.AlgebraicGeometry.Picard.RationalPoint
public import WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# The Picard scheme of a smooth projective curve

Let `k` be a separably closed field and let `X` be a smooth projective curve over `k`.  We show
that the Picard functor `Pic_{X/k}` is representable by a group scheme over `k`.

The proof follows Stacks: `X` has a `k`-rational point `σ`, so `Pic_{X/k} ≅ Pic_{X/k,σ}`, and the
`σ`-normalized Picard functor is a presheaf of groups to which the representability criterion
`AlgebraicGeometry.isRepresentable_of_representable_open_subfunctor` applies, with `F ⊆ Pic_{X/k,σ}`
the subfunctor of classes `ℒ` with `Rf_{T,*} ℒ` invertible in degree `0`.  The four conditions
of the criterion are:

1. `Pic_{X/k,σ}` is an fppf, hence a Zariski, sheaf
   (`AlgebraicGeometry.isSheaf_zariski_picardFunctorNormalized`);
2. (a) `F` is representable by an open subscheme of `Hilb^g_{X/k}`
   (`AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage`);
   (b) `F ⊆ Pic_{X/k,σ}` is representable by open immersions
   (`AlgebraicGeometry.isOpenImmersion_picardFunctorInvertibleDirectImage_ι`);
   (c) every class over a field `K` is translated into `F(K)` by a class defined over `k`: this is
   the twist lemma `AlgebraicGeometry.Scheme.exists_isInvertible_twist` together with
   `AlgebraicGeometry.isInvertibleDirectImage_of_finrankH_eq`.

## Main statements

- `AlgebraicGeometry.isInvertibleDirectImage_of_finrankH_eq`: an invertible module on `X_K` with
  `h⁰ = 1` and `h¹ = 0` has `Rf_{K,*} ℒ ≅ K[0]`.
- `AlgebraicGeometry.smoothOfRelativeDimension_and_isProper_and_geometricallyIntegral_pullback_snd`:
  the base change of a smooth projective curve to a field extension is again a smooth projective
  curve.
- `AlgebraicGeometry.isRepresentable_picardFunctor`: the Picard functor of a smooth projective
  curve over a separably closed field is representable by a group scheme whose group law is the
  tensor product of invertible modules.
- `AlgebraicGeometry.smoothOfRelativeDimension_of_representableBy_picardFunctor`: the Picard
  scheme is smooth of dimension `g`, being covered by translates of an open subscheme of
  `Hilb^g_{X/k}`.

## References

* [Stacks, Tag 0B9Z]
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry

open Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **Smooth projective curves are stable under extension of the base field.** Let `X` be a
smooth projective curve over `k`, i.e. `X ⟶ Spec k` is smooth of relative dimension `1`, proper
and geometrically integral, and let `K/k` be a field extension.  Then the base change
`X_K ⟶ Spec K` is again smooth of relative dimension `1`, proper and geometrically integral, and
`X_K` is integral. -/
theorem smoothOfRelativeDimension_and_isProper_and_geometricallyIntegral_pullback_snd
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f]
    (K : Type u) [Field K] [Algebra k K] :
    SmoothOfRelativeDimension 1 (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      GeometricallyIntegral (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
      IsIntegral (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := by
  have h := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : GeometricallyIntegral (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) :=
    MorphismProperty.of_isPullback h ‹_›
  exact ⟨(smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback h ‹_›,
    IsProper.isStableUnderBaseChange.of_isPullback h ‹_›, this,
    GeometricallyIntegral.isIntegral_of_subsingleton
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))⟩

section Curve

variable [X.Over (Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]

/-- **A twisted class lies in `F`.** Let `X` be a smooth projective curve over `k`, let `K/k` be a
field extension and let `ℒ` be an invertible module on `X_K` with `h⁰(X_K, ℒ) = 1` and
`h¹(X_K, ℒ) = 0`.  Then `Rf_{K,*} ℒ ≅ H⁰(X_K, ℒ)[0] ≅ K[0]` is an invertible `𝒪_K`-module placed
in degree `0`, i.e. the class of `ℒ` satisfies `AlgebraicGeometry.IsInvertibleDirectImage`. -/
theorem isInvertibleDirectImage_of_finrankH_eq (K : Type u) [Field K] [Algebra k K]
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (L : (pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic)
    (h0 : Modules.finrankH K ((fromSkeleton _).obj L.val) 0 = 1)
    (h1 : Modules.finrankH K ((fromSkeleton _).obj L.val) 1 = 0) :
    IsInvertibleDirectImage (X ↘ Spec (.of k))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L := by
  let XK := pullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let g : XK ⟶ Spec (.of K) := XK ↘ Spec (.of K)
  have hpb :=
    IsPullback.of_hasPullback (X ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  have : IsProper g := IsProper.isStableUnderBaseChange.of_isPullback hpb ‹_›
  have : SmoothOfRelativeDimension 1 g :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hpb ‹_›
  have : IsLocallyNoetherian XK := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian XK := ⟨⟩
  have : HasInjectiveResolutions XK.Modules :=
    inferInstanceAs <| HasInjectiveResolutions (pullback (X ↘ Spec (.of k))
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))).hom).Modules
  let ℒ : XK.Modules := (fromSkeleton _).obj L.val
  have : SheafOfModules.IsInvertible.{u, u, u} ℒ := L.isInvertible
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} ℒ :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : ℒ.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have hK : IsField (CommRingCat.of K) := Field.toIsField K
  -- `H¹(X_K, ℒ)` is finite-dimensional, hence zero, and `H^q(X_K, ℒ) = 0` for `q ≥ 2` since
  -- `X_K` is a curve (`Modules.subsingleton_H_of_two_le`)
  have hH (q : ℕ) (hq : 0 < q) : Subsingleton (ℒ.H q) := by
    obtain rfl | hq := eq_or_lt_of_le (Nat.succ_le_of_lt hq)
    · have := Modules.finiteDimensional_H_of_isProper (k := K) ℒ 1
      exact Module.finrank_zero_iff (R := K).1 h1
    · have := Modules.IsInvertible.of_sheafOfModules ℒ
      exact Modules.subsingleton_H_of_two_le K ℒ (by omega)
  -- `R^q g_* ℒ` lives on `Spec K`, where it is determined by its sections `H^q(X_K, ℒ)`
  refine ⟨show SheafOfModules.IsInvertible.{u, u, u} ((Modules.higherDirectImage g 0).obj ℒ)
    from ?_, fun q hq ↦ show IsZero ((Modules.higherDirectImage g q).obj ℒ) from ?_⟩
  · obtain ⟨e⟩ := Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H ℒ K 0
    have h : Module.finrank K _ = 1 := e.finrank_eq.trans h0
    have : Module.Finite K _ := Module.finite_of_finrank_eq_succ h
    exact (SheafOfModules.isInvertible_iff_isFiniteLocallyFreeOfRank_one
      ((Modules.higherDirectImage g 0).obj ℒ)).2
      ((Modules.isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hK _ 1).2 h)
  · obtain ⟨e⟩ := Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H ℒ K q
    have := hH q hq
    have := e.toEquiv.subsingleton
    exact (Modules.isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hK _).2
      Module.finrank_zero_of_subsingleton

variable [GeometricallyIntegral (X ↘ Spec (.of k))]

/-- **Every class over a field is translated into `F` by a class defined over `k`.** Let `σ` be a
`k`-rational point of the smooth projective curve `X`, let `K/k` be a field extension and let
`g ∈ Pic_{X/k,σ}(K)`. Then there is `g' ∈ Pic_{X/k,σ}(k)` such that `g'|_K * g` lies in the
subfunctor `F` of `AlgebraicGeometry.picardFunctorInvertibleDirectImage`. -/
theorem exists_mul_mem_picardFunctorInvertibleDirectImage [IsSepClosed k]
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 _) (K : Type u) [Field K]
    [Algebra k K] (g : (picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ).obj
      (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))) :
    ∃ g' : (picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ).obj
        (.op (Over.mk (𝟙 (Spec (.of k))))),
      ((picardFunctorNormalizedGrp (X ↘ Spec (.of k)) σ hσ).map
          (Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
            (by simp) : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))) ⟶
              Over.mk (𝟙 (Spec (.of k)))).op).hom g' * g ∈
        (picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).obj
          (.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K))))) := by
  set f := X ↘ Spec (.of k)
  let G := picardFunctorNormalizedGrp f σ hσ
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  let TK := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))
  let T₀ := Over.mk (𝟙 (Spec (.of k)))
  let a : TK ⟶ T₀ :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap k K))) (Category.comp_id _)
  -- the twist `ℒ₀` with `h⁰(ℒ ⊗ ℒ₀|_{X_K}) = 1` and `h¹(ℒ ⊗ ℒ₀|_{X_K}) = 0`
  obtain ⟨ℒ₀, hℒ₀, h0, h1⟩ := exists_isInvertible_twist K ((fromSkeleton _).obj g.1.val)
  -- `ℒ₀` pulled back to `X = X_k` is `σ`-normalized, since `Pic (Spec k)` is trivial
  let x := Pic.ofIsInvertible ((Modules.pullback (pullback.fst f T₀.hom)).obj ℒ₀)
  have hx : Pic.mapHom (sectionBaseChange f σ hσ T₀) x = 1 := by
    have hs : sectionBaseChange f σ hσ T₀ ≫ pullback.fst f T₀.hom = σ :=
      (pullback.lift_fst _ _ _).trans (Category.id_comp σ)
    obtain ⟨eσ⟩ := Modules.IsInvertible.nonempty_iso_unit (X := Spec (.of k)) default
      ((Modules.pullback σ).obj ℒ₀)
    exact Pic.eq_iff_nonempty_iso.2 ⟨fromSkeletonToSkeletonIso _ ≪≫
      (Modules.pullback _).mapIso (Pic.ofIsInvertibleIso _) ≪≫
      (Modules.pullbackComp _ _).app ℒ₀ ≪≫ (Modules.pullbackCongr hs).app ℒ₀ ≪≫ eσ ≪≫
      Pic.oneIso.symm⟩
  refine ⟨⟨x, hx⟩, ?_⟩
  -- the product is the class of `ℒ ⊗ ℒ₀|_{X_K}`
  have hb : baseChangeMap f a ≫ pullback.fst f T₀.hom = pullback.fst f TK.hom :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  let e₁ : (fromSkeleton _).obj (Pic.map (baseChangeMap f a) x).val ≅
      (Modules.pullback (pullback.fst f TK.hom)).obj ℒ₀ :=
    fromSkeletonToSkeletonIso _ ≪≫ (Modules.pullback _).mapIso (Pic.ofIsInvertibleIso _) ≪≫
      (Modules.pullbackComp _ _).app ℒ₀ ≪≫ (Modules.pullbackCongr hb).app ℒ₀
  let e : (fromSkeleton (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Modules).obj
        (Pic.map (baseChangeMap f a) x * g.1).val ≅
      (fromSkeleton _).obj g.1.val ⊗
        (Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj
          ℒ₀ :=
    Pic.mulIso (Pic.map (baseChangeMap f a) x) g.1 ≪≫ (e₁ ⊗ᵢ Iso.refl _) ≪≫ β_ _ _
  exact isInvertibleDirectImage_of_finrankH_eq K _ ((Modules.finrankH_congr K e 0).trans h0)
    ((Modules.finrankH_congr K e 1).trans h1)

/-- **`F` is represented by an open subscheme of a smooth scheme.** For a `k`-rational point `σ` of
`X`, the subfunctor `F ⊆ Pic_{X/k,σ}` is represented by an open subscheme `W` of the Hilbert scheme
`H = Hilb^g_{X/k}`, which is smooth of relative dimension `g` over `k`
(`AlgebraicGeometry.isRepresentable_picardFunctorInvertibleDirectImage`). -/
lemma exists_representableBy_picardFunctorInvertibleDirectImage [IsSepClosed k]
    [∀ T : Over (Spec (.of k)),
      HasInjectiveResolutions (pullback (X ↘ Spec (.of k)) T.hom).Modules]
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 _) :
    ∃ (H : Over (Spec (.of k))) (W : Scheme.{u}) (j : W ⟶ H.left),
      SmoothOfRelativeDimension (arithmeticGenus k X) H.hom ∧ IsOpenImmersion j ∧
      Nonempty ((picardFunctorInvertibleDirectImage (X ↘ Spec (.of k)) σ hσ).toFunctor
        |>.RepresentableBy (Over.mk (j ≫ H.hom))) := by
  obtain ⟨H, q, hq, -, -, eH, -⟩ :=
    hilbertPresheaf_curve_representable (X ↘ Spec (.of k)) (arithmeticGenus k X)
  obtain ⟨W, j, hj, ⟨eF⟩⟩ :=
    isRepresentable_picardFunctorInvertibleDirectImage σ hσ (Over.mk q) eH
  exact ⟨Over.mk q, W, j, hq, hj, ⟨eF⟩⟩

/-- The version of `AlgebraicGeometry.isRepresentable_picardFunctor` for a curve given by an
`AlgebraicGeometry.Scheme.Over` instance. -/
theorem isRepresentable_picardFunctor_aux [IsSepClosed k] :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A),
      Nonempty ((picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy A) := by
  set f := X ↘ Spec (.of k)
  have : ∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback f T.hom).Modules :=
    fun T ↦ have := Modules.isGrothendieckAbelian (pullback f T.hom); inferInstance
  -- a `k`-rational point `σ`
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨p⟩ := Hom.nonempty_fieldPoints (k := k) f
  let σ : Spec (.of k) ⟶ X := p.1
  have hσ : σ ≫ f = 𝟙 _ := by
    rw [p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  -- the criterion, applied to `G = Pic_{X/k,σ}` and `F`
  let G := picardFunctorNormalizedGrp f σ hσ
  let F := picardFunctorInvertibleDirectImage f σ hσ
  have hf := isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral (k := k) (X := X)
  obtain ⟨H, W, j, -, -, ⟨eF⟩⟩ := exists_representableBy_picardFunctorInvertibleDirectImage σ hσ
  obtain ⟨A, _, ⟨e⟩⟩ := isRepresentable_of_representable_open_subfunctor G F
    (fun T ↦ have := Pic.small (pullback f T.unop.hom); small_subtype _ _)
    (isSheaf_zariski_picardFunctorNormalized f σ hσ hf) eF.isRepresentable
    (isOpenImmersion_picardFunctorInvertibleDirectImage_ι f σ hσ)
    (exists_mul_mem_picardFunctorInvertibleDirectImage σ hσ)
  exact ⟨A, inferInstance,
    ⟨e.ofIso (nonempty_picardFunctorNormalized_iso_picardFunctor σ hσ).some⟩⟩

/-- **The Picard scheme is smooth of dimension `g`.** Let `X` be a smooth projective curve of
genus `g` over a separably closed field `k`. Every `k`-scheme `A` representing the Picard functor
`Pic_{X/k}` is smooth of relative dimension `g` over `k`. -/
theorem smoothOfRelativeDimension_of_representableBy_picardFunctor [IsSepClosed k]
    (A : Over (Spec (.of k))) (e : (picardFunctor (X ↘ Spec (.of k))).obj.RepresentableBy A) :
    SmoothOfRelativeDimension (arithmeticGenus k X) A.hom := by
  set f := X ↘ Spec (.of k)
  have : ∀ T : Over (Spec (.of k)), HasInjectiveResolutions (pullback f T.hom).Modules :=
    fun T ↦ have := Modules.isGrothendieckAbelian (pullback f T.hom); inferInstance
  -- a `k`-rational point `σ`
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨p⟩ := Hom.nonempty_fieldPoints (k := k) f
  let σ : Spec (.of k) ⟶ X := p.1
  have hσ : σ ≫ f = 𝟙 _ := by
    rw [p.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨H, W, j, hH, hj, ⟨eF⟩⟩ := exists_representableBy_picardFunctorInvertibleDirectImage σ hσ
  let e' : (picardFunctorNormalizedGrp f σ hσ ⋙ forget GrpCat.{u + 1}).RepresentableBy A :=
    e.ofIso (nonempty_picardFunctorNormalized_iso_picardFunctor σ hσ).some.symm
  refine IsZariskiLocalAtSource.of_forall_exists_isOpenImmersion _ fun a ↦ ?_
  obtain ⟨ψ, hψ, ha⟩ := exists_isOpenImmersion_of_representable_open_subfunctor _ _ eF
    (isOpenImmersion_picardFunctorInvertibleDirectImage_ι f σ hσ)
    (exists_mul_mem_picardFunctorInvertibleDirectImage σ hσ) e' a
  refine ⟨_, ψ.left, hψ, ha, ?_⟩
  rw [Over.w ψ]
  have := smoothOfRelativeDimension_comp (n := 0) (m := arithmeticGenus k X) j H.hom
  rwa [zero_add] at this

end Curve

/-- **The Picard functor of a smooth projective curve over a separably closed field is
representable.** Let `k` be a separably closed field and let `f: X ⟶ Spec k` be a smooth
projective curve.  Then the Picard functor `Pic_{X/k} = AlgebraicGeometry.picardFunctor f` is
represented by a group scheme `A` over `k`, i.e. by an object of `Over (Spec k)` carrying a
`CategoryTheory.GrpObj` structure, and the representation respects the group laws
(`AlgebraicGeometry.IsPicardMul`): the group law of `A` is the tensor product of invertible
modules. -/
theorem isRepresentable_picardFunctor [IsSepClosed k] (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyIntegral f] :
    ∃ (A : Over (Spec (.of k))) (_ : GrpObj A) (e : (picardFunctor f).obj.RepresentableBy A),
      IsPicardMul f e := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : SmoothOfRelativeDimension 1 (X ↘ Spec (.of k)) := ‹SmoothOfRelativeDimension 1 f›
  have : IsProper (X ↘ Spec (.of k)) := ‹IsProper f›
  have : GeometricallyIntegral (X ↘ Spec (.of k)) := ‹GeometricallyIntegral f›
  obtain ⟨A, -, ⟨e⟩⟩ := isRepresentable_picardFunctor_aux (k := k) (X := X)
  obtain ⟨_, he⟩ := exists_commGrpObj_isPicardMul f e
  exact ⟨A, inferInstance, e, he⟩

end AlgebraicGeometry
