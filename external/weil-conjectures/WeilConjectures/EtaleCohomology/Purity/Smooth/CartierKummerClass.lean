/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersion
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionFrame
public import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricPoint
public import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsEtale
public import WeilConjectures.SixFunctors.Etale.Derived.SupportsOpenImmersion
public import WeilConjectures.SixFunctors.Integral.Exact

/-!
# The cycle class of an effective Cartier divisor via Kummer boundaries

Blueprint `lemma-cycle-class-cartier-divisor`. Let `i : D ⟶ T` be an effective Cartier divisor, that
is a regular closed immersion of codimension one (`AlgebraicGeometry.IsRegularImmersion 1 i`): near
every point, `D` is cut out by one non-zero-divisor `f`. On such a chart the Kummer boundary
`∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` (`AlgebraicGeometry.Etale.kummerBoundary`) is a class supported on
`D ∩ U`, and changing `f` by a unit does not change it
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`). The local classes
glue to a class

`c_D ∈ H²_D(T, Λ(1)) = Hom(Λ_T, Ri_! Ri^! (Λ_T(1)[2]))`,

whose adjoint is the supported Kummer map `Λ_D ⟶ Ri^! (Λ_T(1)[2])`
(`AlgebraicGeometry.Etale.supportedClassMap`), equivalently `i_* Λ_D ⟶ Λ_T(1)[2]`.

## The purity hypothesis

Gluing morphisms in a derived category along an open cover is not automatic. It is possible
when the target is a sheaf placed in degree zero
(`AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`). We therefore assume that
`Ri_! Ri^! (Λ_T(c)[2c])` is isomorphic to a sheaf placed in degree zero
(`AlgebraicGeometry.Etale.SupportedTatePure`), which for `c = 1` is the semi-purity
`𝓗⁰_D = 𝓗¹_D = 0` of `Λ(1)` together with the vanishing of the higher local cohomology
sheaves. This hypothesis is stable under étale base change
(`AlgebraicGeometry.Etale.SupportedTatePure.of_etale`), and it holds for a regular closed
immersion of a regular scheme into a scheme smooth over a perfect field, by purity
(`AlgebraicGeometry.Etale.supportedTatePure_of_smooth`, in
`WeilConjectures.EtaleCohomology.Purity.Smooth.CartierKummerClassSmooth`); in that case the
class constructed here is the fundamental class `AlgebraicGeometry.Etale.fundamentalClass`
(`AlgebraicGeometry.Etale.pureFundamentalClass_eq_fundamentalClass`). As there, the independence
of the local classes from the choice of equations uses the rank-one normalisation
`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`.

Everything is done for regular immersions of any codimension `c`, where the local classes are
the cup products `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` of the frames (`AlgebraicGeometry.Etale.frameClass`);
the Cartier case is `c = 1`. The arguments are those of
`WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion`, with the smoothness and
regularity hypotheses replaced by the purity hypothesis. That file is not imported: its import
closure contains the smooth duality of `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality`,
which is not needed here.

*Sign.* Forgetting supports, `∂κ(f)` is `c₁(𝒪(-D))`; the blueprint's class `c_D`, whose image is
`c₁(𝒪(D))`, is `-∂κ(f)` (see `WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineClass`).

## Main definitions

- `AlgebraicGeometry.Etale.SupportedTatePure`: the purity hypothesis.
- `AlgebraicGeometry.Etale.pureFundamentalClass`: the glued class of a regular immersion.
- `AlgebraicGeometry.Etale.cartierKummerClass`: the class `c_D ∈ H²_D(T, Λ(1))` of an effective
  Cartier divisor.
- `AlgebraicGeometry.Etale.cartierKummerMap`: its adjoint `Λ_D ⟶ Ri^! (Λ_T(1)[2])`.

## Main statements

- `AlgebraicGeometry.Etale.existsUnique_pureFundamentalClass`: existence and uniqueness of the
  glued class.
- `AlgebraicGeometry.Etale.frameRestriction_cartierKummerClass`: on every chart `(U, f)` of `D`
  the class `c_D` restricts to the Kummer boundary class `∂κ(f)`.
- `AlgebraicGeometry.Etale.restrictSupportedClass_cartierKummerClass`: base change along any
  `g : T' ⟶ T` for which the pulled-back divisor is again Cartier (with the purity hypothesis).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Z : Scheme.{u}}

section Hypothesis

variable [HasTateTwist Λ]

/-- The *purity hypothesis* for a closed immersion `i : Z ⟶ X` in codimension `c`: the object
`Ri_! Ri^! (Λ_X(c)[2c])` of classes with supports in `Z` is isomorphic to a sheaf placed in
degree zero. Then classes in `H^{2c}_Z(X, Λ(c))` are sections of a sheaf, so they are determined
locally and glue along open covers. It holds for regular immersions into schemes smooth over a
perfect field (`AlgebraicGeometry.Etale.supportedTatePure_of_smooth`). -/
def SupportedTatePure (c : ℕ) (i : Z ⟶ X) [IsClosedImmersion i] [HasInvertibleExponent Λ X] :
    Prop :=
  ∃ G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
    Nonempty ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) ≅
      (DerivedCategory.singleFunctor _ 0).obj G)

variable {Λ} in
/-- The purity hypothesis is stable under étale base change: the restriction of supports along
an étale map is an isomorphism (`AlgebraicGeometry.Etale.isIso_supportedRestriction_of_etale`)
and the pullback of a sheaf placed in degree zero is the sheaf pullback placed in degree zero. -/
theorem SupportedTatePure.of_etale {c : ℕ} {i : Z ⟶ X} [IsClosedImmersion i]
    [HasInvertibleExponent Λ X] (hP : SupportedTatePure Λ c i) {U Z' : Scheme.{u}}
    (e : U ⟶ X) [AlgebraicGeometry.Etale e] [HasInvertibleExponent Λ U] (i' : Z' ⟶ U)
    [IsClosedImmersion i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e) :
    SupportedTatePure Λ c i' := by
  obtain ⟨G, ⟨eM⟩⟩ := hP
  have := isIso_supportedRestriction_of_etale Λ e i i' g hg _ _
    (leftDerivedUpperStarTateShiftIso Λ e c)
  exact ⟨_, ⟨(asIso (supportedRestriction Λ e i i' g hg _ _
    (leftDerivedUpperStarTateShiftIso Λ e c))).symm ≪≫ (L((e)^*[ModuleCat.{u + 1} Λ])).mapIso eM ≪≫
      ((e)^*[ModuleCat.{u + 1} Λ]).singleFunctorCompLeftDerivedFunctorIso.app G⟩⟩

end Hypothesis

section FundamentalClass

attribute [local instance] HasInvertibleExponent.opens

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ X] (c : ℕ)
  (i : Z ⟶ X)

omit [HasKummerClass.IsNormalized Λ] in
/-- *Uniqueness of the fundamental class under the purity hypothesis.* Two classes in
`H^{2c}_Z(X, Λ(c))` are equal if every point of `Z` lies in a Zariski frame on which their
restrictions agree: under `AlgebraicGeometry.Etale.SupportedTatePure` the classes are sections of
a sheaf, so they are determined by their pullbacks to the geometric points of `X`. -/
theorem eq_of_forall_exists_frameRestriction_eq_of_pure [IsClosedImmersion i]
    (hP : SupportedTatePure Λ c i)
    {γ γ' : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))}
    (h : ∀ z : Z, ∃ F : i.EtaleFrame c, IsOpenImmersion F.e ∧ z ∈ Set.range F.toZ ∧
      frameRestriction Λ F γ = frameRestriction Λ F γ') :
    γ = γ' := by
  obtain ⟨G, ⟨eM⟩⟩ := id hP
  refine hom_ext_of_leftDerivedUpperStar_map_eq (constantComplexIsoSingleFunctor Λ X) eM
    fun Ω _ _ x ↦ ?_
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  by_cases hx : Set.range x.base ⊆ Set.range i.openComplement.ι.base
  · -- `x` misses `Z`, where the classes live
    refine (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint
      (ModuleCat.{u + 1} Λ) i i.openComplement.ι ?_ x hx _).eq_of_tgt _ _
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  · -- `x` is a point of `Z`, which lies in a Zariski frame
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := Set.not_subset.mp hx
    rw [← Set.mem_compl_iff, ← i.range_eq_compl_range_openComplement_ι] at hy
    obtain ⟨z, hz⟩ := hy
    obtain ⟨F, hF, ⟨w, rfl⟩, hFγ⟩ := h z
    have hxe : Set.range x.base ⊆ Set.range F.e.base := by
      rintro _ ⟨y', rfl⟩
      refine ⟨(F.U.zeroLocusSubschemeι (Set.range F.f)) w, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← F.isPullback.w, Scheme.Hom.comp_apply, hz,
        Subsingleton.elim y' y]
    have he : (L((F.e)^*[ModuleCat.{u + 1} Λ])).map γ =
        (L((F.e)^*[ModuleCat.{u + 1} Λ])).map γ' := by
      have hψ := isIso_supportedRestriction_of_isOpenImmersion Λ F.e i _ F.toZ
        F.isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ F.e c)
      have := hFγ
      simp only [frameRestriction, restrictSupportedClass] at this
      rwa [cancel_epi, cancel_mono] at this
    have hx' := IsOpenImmersion.lift_fac F.e x hxe
    let comp := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) (IsOpenImmersion.lift F.e x hxe)
      F.e x hx'.symm
    rw [← NatIso.naturality_2 comp γ, ← NatIso.naturality_2 comp γ', Functor.comp_map,
      Functor.comp_map, he]

omit [HasKummerClass.IsNormalized Λ] in
/-- *Uniqueness of the fundamental class under the purity hypothesis.* Two classes in
`H^{2c}_Z(X, Λ(c))` whose restrictions to every Zariski frame agree are equal
(`AlgebraicGeometry.Etale.eq_of_forall_exists_frameRestriction_eq_of_pure`): every point of `Z`
lies in a Zariski frame (`AlgebraicGeometry.Scheme.Hom.exists_etaleFrame_isOpenImmersion`). -/
theorem eq_of_frameRestriction_eq_of_pure [IsRegularImmersion c i]
    (hP : SupportedTatePure Λ c i)
    {γ γ' : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))}
    (h : ∀ F : i.EtaleFrame c, IsOpenImmersion F.e →
      frameRestriction Λ F γ = frameRestriction Λ F γ') :
    γ = γ' :=
  eq_of_forall_exists_frameRestriction_eq_of_pure Λ c i hP fun z ↦
    have ⟨F, hF, hz, _⟩ := i.exists_etaleFrame_isOpenImmersion c z
    ⟨F, hF, hz, h F hF⟩

/-- **Frame classes agree on overlaps.** Two frames `F₁`, `F₂`, with `F₁` given by a weakly
regular sequence on an affine scheme, have the same restriction to any `W` étale over both. -/
theorem restrictSupportedClass_frameClass_eq_of_pure [IsClosedImmersion i]
    (hP : SupportedTatePure Λ c i)
    (F₁ F₂ : i.EtaleFrame c)
    [IsAffine F₁.U] (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(F₁.U, ⊤) (List.ofFn F₁.f))
    {W Z' : Scheme.{u}} [HasInvertibleExponent Λ W] (a : W ⟶ F₁.U) (b : W ⟶ F₂.U)
    [AlgebraicGeometry.Etale a] [AlgebraicGeometry.Etale b] (hab : a ≫ F₁.e = b ≫ F₂.e)
    (i' : Z' ⟶ W) [IsClosedImmersion i']
    (g₁ : Z' ⟶ _) (hg₁ : IsPullback g₁ i' (F₁.U.zeroLocusSubschemeι (Set.range F₁.f)) a)
    (g₂ : Z' ⟶ _) (hg₂ : IsPullback g₂ i' (F₂.U.zeroLocusSubschemeι (Set.range F₂.f)) b) :
    restrictSupportedClass Λ a _ i' g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
        (frameClass Λ F₁) =
      restrictSupportedClass Λ b _ i' g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
        (frameClass Λ F₂) := by
  have hw := hg₁.paste_horiz F₁.isPullback
  refine eq_of_forall_exists_frameRestriction_eq_of_pure Λ c i'
    (hP.of_etale (a ≫ F₁.e) i' (g₁ ≫ F₁.toZ) hw) fun z ↦ ?_
  obtain ⟨D, hD, hzD⟩ : ∃ D : W.Opens, IsAffineOpen D ∧ i' z ∈ D := by
    obtain ⟨_, ⟨D, hD, rfl⟩, hzD, -⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (i' z)) isOpen_univ
    exact ⟨D, hD, hzD⟩
  have : IsAffine D.toScheme := hD
  let v : Fin c → Γ(D.toScheme, ⊤) := fun t ↦ (D.ι ≫ a).appTop (F₁.f t)
  let w : Fin c → Γ(D.toScheme, ⊤) := fun t ↦ (D.ι ≫ b).appTop (F₂.f t)
  have hv : RingTheory.Sequence.IsWeaklyRegular Γ(D.toScheme, ⊤) (List.ofFn v) := by
    have : List.ofFn v = (List.ofFn F₁.f).map (D.ι ≫ a).appTop.hom := by
      rw [List.map_ofFn]; rfl
    rw [this]
    exact hreg.map_of_flat (HasRingHomProperty.appTop @Flat (D.ι ≫ a) inferInstance)
  obtain ⟨gv, hgv⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (D.ι ≫ a) (Set.range F₁.f)
      (Set.range v) (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨gw, hgw⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (D.ι ≫ b) (Set.range F₂.f)
      (Set.range w) (by rw [← Set.range_comp]; rfl)⟩
  have heq : (D.ι ≫ b) ≫ F₂.e = (D.ι ≫ a) ≫ F₁.e := by simp [hab]
  have hspan : Ideal.span (Set.range w) = Ideal.span (Set.range v) :=
    Scheme.span_eq_of_isPullback_zeroLocusSubschemeι (heq ▸ hgw.paste_horiz F₂.isPullback)
      (hgv.paste_horiz F₁.isPullback)
  obtain ⟨M, hM, hdet⟩ := RingTheory.Sequence.IsWeaklyRegular.exists_mulVec_isUnit_det v w hv
    hspan
  -- the point `i' z` of `D` lies in the zero locus of `v`
  obtain ⟨p, hp⟩ : i' z ∈ Set.range D.ι.base := by rw [Scheme.Opens.range_ι]; exact hzD
  have hp0 : p ∈ D.toScheme.zeroLocus (Set.range v) := by
    rw [← Scheme.range_zeroLocusSubschemeι]
    obtain ⟨q, -, hq⟩ := hgv.exists_scheme_point (g₁ z) p (by
      rw [← Scheme.Hom.comp_apply, hg₁.w, Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply])
    exact ⟨q, hq⟩
  -- the frame of `i'` on the basic open of `det M`, given by `v`
  set B := D.toScheme.basicOpen M.det
  obtain ⟨pB, hpB⟩ : p ∈ Set.range B.ι.base := by
    rw [Scheme.Opens.range_ι]; exact Scheme.mem_basicOpen_of_isUnit_mk hdet hp0
  let f : Fin c → Γ(B.toScheme, ⊤) := fun t ↦ B.ι.appTop (v t)
  obtain ⟨gB, hgB⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι B.ι (Set.range v) (Set.range f)
      (by rw [← Set.range_comp]; rfl)⟩
  have hout := hgB.paste_horiz hgv
  let toZ := hg₁.lift (gB ≫ gv) (B.toScheme.zeroLocusSubschemeι (Set.range f) ≫ B.ι ≫ D.ι)
    (by rw [Category.assoc, hgv.w, reassoc_of% hgB.w]; simp)
  have hH : IsPullback toZ (B.toScheme.zeroLocusSubschemeι (Set.range f)) i' (B.ι ≫ D.ι) := by
    refine IsPullback.of_right (h₁₂ := g₁) (v₁₃ := F₁.U.zeroLocusSubschemeι (Set.range F₁.f))
      (h₂₂ := a) ?_ (hg₁.lift_snd _ _ _) hg₁
    rw [hg₁.lift_fst]
    simpa using hout
  let H : i'.EtaleFrame c :=
    { U := B.toScheme
      e := B.ι ≫ D.ι
      etale := inferInstance
      f := f
      toZ := toZ
      isPullback := hH }
  have : HasInvertibleExponent Λ B.toScheme := .of_hom (B.ι ≫ D.ι ≫ a ≫ F₁.e)
  refine ⟨H, inferInstanceAs (IsOpenImmersion (B.ι ≫ D.ι)), ?_, ?_⟩
  · obtain ⟨z', hz', -⟩ := hH.exists_scheme_point z pB (by
      rw [Scheme.Hom.comp_apply, hpB, hp])
    exact ⟨z', hz'⟩
  -- the restriction of the class of `F₁` is the class of `v`
  have h₁ : frameRestriction Λ H (restrictSupportedClass Λ a _ i' g₁ hg₁
      (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
      (frameClass Λ F₁)) = kummerBoundaryProduct Λ f := by
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ H.e a _ rfl _ _ _ g₁ hg₁
      toZ hH (toZ ≫ g₁) (hH.paste_horiz hg₁)]
    exact restrictSupportedClass_kummerBoundaryProduct Λ _ F₁.f f (fun _ ↦ rfl) _ _
  -- the restriction of the class of `F₂` is the class of `M v`, hence of `v`
  let w' : Fin c → Γ(B.toScheme, ⊤) := fun t ↦ B.ι.appTop (w t)
  let M' := M.map B.ι.appTop.hom
  have hw' : w' = M'.mulVec f := by
    funext t
    simp only [w', f, M', hM, RingHom.map_mulVec]
    rfl
  have hdet' : IsUnit M'.det := by
    rw [show M'.det = _ from (RingHom.map_det B.ι.appTop.hom M).symm]
    refine B.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ ↦ ?_
    rw [← B.toScheme.mem_basicOpen_top, ← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨gw', hgw'⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι (H.e ≫ b) (Set.range F₂.f)
      (Set.range w') (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨g₀, hg₀⟩ := Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq
    (U := B.toScheme) (s := Set.range w') (s' := Set.range f)
    (by rw [hw', Ideal.span_range_mulVec_of_isUnit_det _ hdet'])
  have key : ∀ (w'' : Fin c → Γ(B.toScheme, ⊤)) (_ : w'' = M'.mulVec f) (g : _ ⟶ _)
      (hg : IsPullback g (B.toScheme.zeroLocusSubschemeι (Set.range f))
        (B.toScheme.zeroLocusSubschemeι (Set.range w'')) (𝟙 _)),
      restrictSupportedClass Λ (𝟙 _) _ _ g hg
        (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
        (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c) (kummerBoundaryProduct Λ w'') =
      kummerBoundaryProduct Λ f := by
    rintro _ rfl g hg
    exact restrictSupportedClass_kummerBoundaryProduct_mulVec Λ f M' hdet' g hg
  have h₂ : frameRestriction Λ H (restrictSupportedClass Λ b _ i' g₂ hg₂
      (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
      (frameClass Λ F₂)) = kummerBoundaryProduct Λ f := by
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ H.e b _ rfl _ _ _ g₂ hg₂
      toZ hH (toZ ≫ g₂) (hH.paste_horiz hg₂),
      restrictSupportedClass_comp_tateShift Λ (𝟙 _) (H.e ≫ b) _ (Category.id_comp _).symm _ _ _
      gw' hgw'
      g₀ hg₀ (toZ ≫ g₂) (hH.paste_horiz hg₂)]
    rw [frameClass, restrictSupportedClass_kummerBoundaryProduct Λ _ F₂.f w' (fun _ ↦ rfl) _ _]
    exact key w' hw' g₀ hg₀
  rw [h₁, h₂]

/-- **The fundamental class under the purity hypothesis.** Let `i : Z ⟶ X` be a regular closed
immersion of pure codimension `c` such that `Ri_! Ri^! (Λ_X(c)[2c])` is a sheaf placed in degree
zero (`AlgebraicGeometry.Etale.SupportedTatePure`). The frame classes
depend only on `Z_U ⊂ U`, not on the frame, and they glue: there is a unique class
`[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` whose restriction to every frame is the frame class.

Near every point of `Z` there is a frame given by a regular sequence on an affine open, and any
other frame differs from it, near `Z`, by a matrix with invertible determinant
(`RingTheory.Sequence.IsWeaklyRegular.exists_mulVec_isUnit_det`), under which the frame classes
agree (`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`); so frame
classes agree on overlaps
(`AlgebraicGeometry.Etale.restrictSupportedClass_frameClass_eq_of_pure`). By the purity
hypothesis the classes are morphisms into a sheaf placed in degree zero, so the Zariski-local
classes glue (`AlgebraicGeometry.Etale.exists_hom_of_isOpenImmersion_cover`). -/
theorem existsUnique_pureFundamentalClass [IsRegularImmersion c i]
    (hP : SupportedTatePure Λ c i) :
    ∃! γ : constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)),
      ∀ F : i.EtaleFrame c, frameRestriction Λ F γ = frameClass Λ F := by
  obtain ⟨G, ⟨eM⟩⟩ := id hP
  choose F hFo hzF hFa hFr using fun z ↦ i.exists_etaleFrame_isOpenImmersion c z
  have hdisj : Disjoint (Set.range i.base) (Set.range i.openComplement.ι.base) := by
    rw [i.range_eq_compl_range_openComplement_ι]
    exact disjoint_compl_left
  -- the cover of `X` by the Zariski frames and the complement of `Z`
  let V : Option Z → Scheme.{u} := fun j ↦ Option.elim j i.openComplement.toScheme (F · |>.U)
  let e : ∀ j, V j ⟶ X := fun j ↦ match j with
    | none => i.openComplement.ι
    | some z => (F z).e
  have he : ∀ j, IsOpenImmersion (e j) := by
    rintro (_ | z)
    · exact inferInstanceAs (IsOpenImmersion i.openComplement.ι)
    · exact hFo z
  have hΨ : ∀ z, IsIso (supportedRestriction Λ (F z).e i _ (F z).toZ
      (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c)) := fun z ↦
    have := hFo z
    isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _
  let δ : ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ X) ⟶
      (L((e j)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧))) :=
    fun j ↦ match j with
    | none => 0
    | some z => (leftDerivedUpperStarConstantComplexIso Λ (F z).e).hom ≫ frameClass Λ (F z) ≫
        inv (supportedRestriction Λ (F z).e i _ (F z).toZ
          (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c))
  have hδ : ∀ z, δ (some z) ≫ supportedRestriction Λ (F z).e i _ (F z).toZ
      (F z).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (F z).e c) =
        (leftDerivedUpperStarConstantComplexIso Λ (F z).e).hom ≫ frameClass Λ (F z) := by
    intro z
    simp [δ]
  -- the restriction of `Ri_! Ri^! (Λ(c)[2c])` to the complement of `Z` vanishes
  have hzero : ∀ {W : Scheme.{u}} (w : W ⟶ X),
      Set.range w.base ⊆ Set.range i.openComplement.ι.base →
      IsZero ((L((w)^*[ModuleCat.{u + 1} Λ])).obj ((R(i)_![ModuleCat.{u + 1} Λ]).obj
        ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)))) :=
    fun w hw ↦ isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _ i
      i.openComplement.ι hdisj w hw _
  have hcov : ∀ x : X, ∃ j, x ∈ Set.range (e j).base := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨w, hw⟩ := hzF z
      refine ⟨some z, (F z).U.zeroLocusSubschemeι _ w, ?_⟩
      change (F z).e _ = i z
      rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw]
    · refine ⟨none, ?_⟩
      rwa [← Set.mem_compl_iff, i.range_eq_compl_range_openComplement_ι, compl_compl] at hx
  obtain ⟨γ, hγ⟩ := exists_hom_of_isOpenImmersion_cover (constantComplexIsoSingleFunctor Λ X) eM
    e hcov δ (by
    rintro (_ | z) (_ | z') W a b _ _ h
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rw [h]; rintro _ ⟨y, rfl⟩; exact ⟨b y, rfl⟩)).eq_of_tgt _ _
    · -- two Zariski frames: compare the restrictions of the frame classes to `W`
      have := hFo z
      have := hFo z'
      have := hFa z
      change W ⟶ (F z).U at a
      change W ⟶ (F z').U at b
      change a ≫ (F z).e = b ≫ (F z').e at h
      have : HasInvertibleExponent Λ W := .of_hom a
      obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g _ _ _ :=
        ⟨_, isPullback_zeroLocusSubschemeι a (Set.range (F z).f)
          (Set.range fun t ↦ a.appTop ((F z).f t)) (by rw [← Set.range_comp]; rfl)⟩
      have hg' := hg₁.paste_horiz (F z).isPullback
      have hout : IsPullback (g₁ ≫ (F z).toZ)
          (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t))) i (b ≫ (F z').e) :=
        h ▸ hg'
      let g₂ := (F z').isPullback.lift (g₁ ≫ (F z).toZ)
        (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t)) ≫ b)
        (by rw [hout.w, Category.assoc])
      have hg₂ : IsPullback g₂ (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((F z).f t)))
          _ b :=
        IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
          ((F z').isPullback.lift_snd _ _ _)
          (F z').isPullback
      have := isIso_supportedRestriction_of_isOpenImmersion Λ (a ≫ (F z).e) i
        _ _ hg' _ _ (leftDerivedUpperStarTateShiftIso Λ (a ≫ (F z).e) c)
      rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ (a ≫ (F z).e)).inv,
        ← cancel_mono (supportedRestriction Λ (a ≫ (F z).e) i _ _ hg' _ _
          (leftDerivedUpperStarTateShiftIso Λ (a ≫ (F z).e) c))]
      simp only [Category.assoc]
      exact (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
        (F z).e a _ rfl i _ _ (F z).toZ (F z).isPullback g₁ hg₁ _ hg' _ _ (hδ z)).trans
          ((restrictSupportedClass_frameClass_eq_of_pure Λ c i hP (F z) (F z') (hFr z) a b h _ g₁
            hg₁ g₂ hg₂).trans
          (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
            (F z').e b _ h i _ _ (F z').toZ (F z').isPullback g₂ hg₂ _ hg' _ _ (hδ z')).symm))
  have hγz : ∀ z, frameRestriction Λ (F z) γ = frameClass Λ (F z) := by
    intro z
    have h : (L(((F z).e)^*[ModuleCat.{u + 1} Λ])).map γ = δ (some z) := hγ (some z)
    simp only [frameRestriction, restrictSupportedClass, h, δ, Category.assoc, IsIso.inv_hom_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  -- every frame is compared with the Zariski frames near each of its points
  have hall : ∀ F' : i.EtaleFrame c, frameRestriction Λ F' γ = frameClass Λ F' := by
    intro F'
    have : HasInvertibleExponent Λ F'.U := .of_hom F'.e
    refine eq_of_forall_exists_frameRestriction_eq_of_pure Λ c _
      (hP.of_etale F'.e _ F'.toZ F'.isPullback) fun z' ↦ ?_
    set z := F'.toZ z'
    have := hFo z
    have := hFa z
    let W : F'.U.Opens := F'.e ⁻¹ᵁ (F z).e.opensRange
    have hrange : Set.range (W.ι ≫ F'.e).base ⊆ Set.range (F z).e.base := by
      rintro _ ⟨y, rfl⟩
      exact y.2
    let a := IsOpenImmersion.lift (F z).e (W.ι ≫ F'.e) hrange
    have hab : a ≫ (F z).e = W.ι ≫ F'.e := IsOpenImmersion.lift_fac _ _ _
    have : AlgebraicGeometry.Etale (a ≫ (F z).e) := hab ▸ inferInstance
    have : AlgebraicGeometry.Etale a := .of_comp a (F z).e
    let H := Scheme.Hom.EtaleFrame.ofFunctions F'.f W.ι
    have hout : IsPullback (H.toZ ≫ F'.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range H.f)) i
        (a ≫ (F z).e) := hab ▸ H.isPullback.paste_horiz F'.isPullback
    let g₁ := (F z).isPullback.lift (H.toZ ≫ F'.toZ)
      (W.toScheme.zeroLocusSubschemeι (Set.range H.f) ≫ a) (by rw [hout.w, Category.assoc])
    have hg₁ : IsPullback g₁ (W.toScheme.zeroLocusSubschemeι (Set.range H.f)) _ a :=
      IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
        ((F z).isPullback.lift_snd _ _ _) (F z).isPullback
    refine ⟨H, inferInstanceAs (IsOpenImmersion W.ι), ?_, ?_⟩
    · obtain ⟨w₀, hw₀⟩ := hzF z
      obtain ⟨p, hp⟩ : (F'.U.zeroLocusSubschemeι (Set.range F'.f)) z' ∈ Set.range W.ι.base := by
        rw [Scheme.Opens.range_ι]
        refine ⟨(F z).U.zeroLocusSubschemeι _ w₀, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (F z).isPullback.w, Scheme.Hom.comp_apply, hw₀,
          ← Scheme.Hom.comp_apply, F'.isPullback.w, Scheme.Hom.comp_apply]
      obtain ⟨q, hq, -⟩ := H.isPullback.exists_scheme_point z' p hp.symm
      exact ⟨q, hq⟩
    · have e₁ := restrictSupportedClass_comp_tateShift Λ W.ι F'.e (W.ι ≫ F'.e) rfl _ _ _ F'.toZ
        F'.isPullback H.toZ H.isPullback _ (H.isPullback.paste_horiz F'.isPullback) γ
      have e₂ := restrictSupportedClass_comp_tateShift Λ a (F z).e (W.ι ≫ F'.e) hab.symm _ _ _
        (F z).toZ (F z).isPullback g₁ hg₁ _ (H.isPullback.paste_horiz F'.isPullback) γ
      have e₃ := restrictSupportedClass_frameClass_eq_of_pure Λ c i hP (F z) F' (hFr z) a W.ι hab _
        g₁ hg₁ H.toZ H.isPullback
      exact e₁.symm.trans (e₂.trans ((congrArg (restrictSupportedClass _ a _ _ g₁ hg₁ _ _)
        (hγz z)).trans e₃))
  exact ⟨γ, hall, fun γ' hγ' ↦ eq_of_frameRestriction_eq_of_pure Λ c i hP fun F _ ↦ by
    rw [hγ' F, hall F]⟩


variable [IsRegularImmersion c i]

/-- The *fundamental class* `[Z ⊂ X] ∈ H^{2c}_Z(X, Λ(c))` of a regular closed immersion
`i : Z ⟶ X` of pure codimension `c` satisfying the purity hypothesis
(`AlgebraicGeometry.Etale.SupportedTatePure`): the unique class restricting to the frame class
`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_c)` on every frame (`AlgebraicGeometry.Etale.existsUnique_pureFundamentalClass`).
-/
noncomputable def pureFundamentalClass (hP : SupportedTatePure Λ c i) :
    constantComplex Λ X ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ X c)⟦2 * (c : ℤ)⟧)) :=
  (existsUnique_pureFundamentalClass Λ c i hP).exists.choose

/-- The fundamental class restricts to the frame class on every frame. -/
theorem frameRestriction_pureFundamentalClass (hP : SupportedTatePure Λ c i)
    (F : i.EtaleFrame c) :
    frameRestriction Λ F (pureFundamentalClass Λ c i hP) = frameClass Λ F :=
  (existsUnique_pureFundamentalClass Λ c i hP).exists.choose_spec F

/-- **Base change of the fundamental class.** For any `e : X' ⟶ X` such that the base change
`i' : Z' ⟶ X'` of `i` is again a regular immersion of codimension `c` satisfying the purity
hypothesis, the restriction of supports along `e` carries `[Z ⊂ X]` to `[Z' ⊂ X']`: Zariski
frames of `i` pull back to Zariski frames of `i'`, and Kummer boundary products are compatible
with pullback along any morphism
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct`). -/
theorem restrictSupportedClass_pureFundamentalClass (hP : SupportedTatePure Λ c i)
    {X' Z' : Scheme.{u}} [HasInvertibleExponent Λ X'] (e : X' ⟶ X) (i' : Z' ⟶ X')
    [IsRegularImmersion c i'] (g : Z' ⟶ Z) (hg : IsPullback g i' i e)
    (hP' : SupportedTatePure Λ c i') :
    restrictSupportedClass Λ e i i' g hg
        (leftDerivedUpperStarConstantComplexIso Λ e).inv (leftDerivedUpperStarTateShiftIso Λ e c)
        (pureFundamentalClass Λ c i hP) = pureFundamentalClass Λ c i' hP' := by
  refine eq_of_forall_exists_frameRestriction_eq_of_pure Λ c i' hP' fun z' ↦ ?_
  obtain ⟨F, hFo, ⟨w₀, hw₀⟩, -, -⟩ := i.exists_etaleFrame_isOpenImmersion c (g z')
  have := hFo
  -- the preimage of the frame `F` in `X'`
  let W : X'.Opens := e ⁻¹ᵁ F.e.opensRange
  have hrange : Set.range (W.ι ≫ e).base ⊆ Set.range F.e.base := by
    rintro _ ⟨y, rfl⟩
    exact y.2
  let a := IsOpenImmersion.lift F.e (W.ι ≫ e) hrange
  have hab : a ≫ F.e = W.ι ≫ e := IsOpenImmersion.lift_fac _ _ _
  let f' : Fin c → Γ(W.toScheme, ⊤) := fun t ↦ a.appTop (F.f t)
  obtain ⟨m, hm⟩ : ∃ m, IsPullback m (W.toScheme.zeroLocusSubschemeι (Set.range f'))
      (F.U.zeroLocusSubschemeι (Set.range F.f)) a :=
    ⟨_, isPullback_zeroLocusSubschemeι a (Set.range F.f) (Set.range f')
      (by rw [← Set.range_comp]; rfl)⟩
  have hout : IsPullback (m ≫ F.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range f')) i
      (W.ι ≫ e) := hab ▸ hm.paste_horiz F.isPullback
  let toZ := hg.lift (m ≫ F.toZ) (W.toScheme.zeroLocusSubschemeι (Set.range f') ≫ W.ι)
    (by rw [hout.w, Category.assoc])
  have hH : IsPullback toZ (W.toScheme.zeroLocusSubschemeι (Set.range f')) i' W.ι :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout) (hg.lift_snd _ _ _) hg
  -- the pulled back frame of `i'`
  let H : i'.EtaleFrame c :=
    { U := W.toScheme
      e := W.ι
      etale := inferInstance
      f := f'
      toZ := toZ
      isPullback := hH }
  refine ⟨H, inferInstanceAs (IsOpenImmersion W.ι), ?_, ?_⟩
  · obtain ⟨p, hp⟩ : i' z' ∈ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      refine ⟨F.U.zeroLocusSubschemeι _ w₀, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← F.isPullback.w, Scheme.Hom.comp_apply, hw₀,
        ← Scheme.Hom.comp_apply, hg.w, Scheme.Hom.comp_apply]
    obtain ⟨q, hq, -⟩ := hH.exists_scheme_point z' p hp.symm
    exact ⟨q, hq⟩
  · rw [frameRestriction_pureFundamentalClass]
    have hF := frameRestriction_pureFundamentalClass Λ c i hP F
    rw [frameRestriction] at hF
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ W.ι e (W.ι ≫ e) rfl i i' _ g
      hg toZ hH (m ≫ F.toZ) hout, restrictSupportedClass_comp_tateShift Λ a F.e (W.ι ≫ e)
      hab.symm i _ _ F.toZ F.isPullback m hm (m ≫ F.toZ) hout, hF]
    exact restrictSupportedClass_kummerBoundaryProduct Λ a F.f f' (fun _ ↦ rfl) m hm

end FundamentalClass

section Cartier

attribute [local instance] HasInvertibleExponent.opens

variable [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] {T D : Scheme.{u}}
  [HasInvertibleExponent Λ T] (i : D ⟶ T) [IsRegularImmersion 1 i]

/-- Blueprint `lemma-cycle-class-cartier-divisor`: A Cartier divisor gives a supported Kummer map

The *class of an effective Cartier divisor* `i : D ⟶ T` (a regular closed immersion of
codimension one), `c_D ∈ H²_D(T, Λ(1)) = Hom(Λ_T, Ri_! Ri^! (Λ_T(1)[2]))`: the Kummer boundaries
`∂κ(f)` of the local equations `f` of `D`, glued under the purity hypothesis
(`AlgebraicGeometry.Etale.pureFundamentalClass` with `c = 1`). With the conventions of
`AlgebraicGeometry.Etale.kummerBoundary` it forgets supports to `c₁(𝒪_T(-D))`, so it is the
negative of the blueprint's `c_D`. -/
noncomputable def cartierKummerClass (hP : SupportedTatePure Λ 1 i) :
    constantComplex Λ T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ T 1)⟦2 * ((1 : ℕ) : ℤ)⟧)) :=
  pureFundamentalClass Λ 1 i hP

/-- Blueprint `lemma-cycle-class-cartier-divisor`: A Cartier divisor gives a supported Kummer map

The *supported Kummer map* `Λ_D ⟶ Ri^! (Λ_T(1)[2])` of an effective Cartier divisor
`i : D ⟶ T`, the adjoint (`AlgebraicGeometry.Etale.supportedClassMap`) of its class
`AlgebraicGeometry.Etale.cartierKummerClass`; by `Ri_! ⊣ Ri^!` and `Ri_! ≅ i_*` it is equivalently
a map `i_* Λ_D ⟶ Λ_T(1)[2]`. -/
noncomputable def cartierKummerMap (hP : SupportedTatePure Λ 1 i) :
    constantComplex Λ D ⟶ (R(i)^![Λ]).obj ((tateObject Λ T 1)⟦2 * ((1 : ℕ) : ℤ)⟧) :=
  supportedClassMap Λ i (cartierKummerClass Λ i hP)

/-- Blueprint `lemma-cycle-class-cartier-divisor`, local description: on every chart
`(e : U ⟶ T, f)` of `D`, an étale `e` with a function `f` on `U` cutting out `D ×_T U`, the class
`c_D` restricts to the Kummer boundary class `∂κ(f) ∪ 1` of `f`
(`AlgebraicGeometry.Etale.kummerBoundaryProduct` of the one-element tuple). -/
theorem frameRestriction_cartierKummerClass (hP : SupportedTatePure Λ 1 i)
    (F : i.EtaleFrame 1) :
    frameRestriction Λ F (cartierKummerClass Λ i hP) = kummerBoundaryProduct Λ F.f :=
  frameRestriction_pureFundamentalClass Λ 1 i hP F

/-- The class `c_D` is the unique class with supports in `D` restricting to the Kummer boundary
class of the local equation on every chart of `D`. -/
theorem eq_cartierKummerClass (hP : SupportedTatePure Λ 1 i)
    (γ : constantComplex Λ T ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ T 1)⟦2 * ((1 : ℕ) : ℤ)⟧)))
    (hγ : ∀ F : i.EtaleFrame 1, frameRestriction Λ F γ = kummerBoundaryProduct Λ F.f) :
    γ = cartierKummerClass Λ i hP :=
  (existsUnique_pureFundamentalClass Λ 1 i hP).unique hγ
    (frameRestriction_pureFundamentalClass Λ 1 i hP)

/-- Blueprint `lemma-cycle-class-cartier-divisor`, base change: for any `g : T' ⟶ T` along which the
pulled-back divisor `i' : D' ⟶ T'` is again an effective Cartier divisor satisfying the purity
hypothesis, the restriction of `c_D` along `g` is `c_{D'}`. -/
theorem restrictSupportedClass_cartierKummerClass (hP : SupportedTatePure Λ 1 i)
    {T' D' : Scheme.{u}} [HasInvertibleExponent Λ T'] (g : T' ⟶ T) (i' : D' ⟶ T')
    [IsRegularImmersion 1 i'] (gD : D' ⟶ D) (hg : IsPullback gD i' i g)
    (hP' : SupportedTatePure Λ 1 i') :
    restrictSupportedClass Λ g i i' gD hg
        (leftDerivedUpperStarConstantComplexIso Λ g).inv (leftDerivedUpperStarTateShiftIso Λ g 1)
        (cartierKummerClass Λ i hP) = cartierKummerClass Λ i' hP' :=
  restrictSupportedClass_pureFundamentalClass Λ 1 i hP g i' gD hg hP'

end Cartier

end Etale

end AlgebraicGeometry
