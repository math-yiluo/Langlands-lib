/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import Mathlib.CategoryTheory.Simple
public import WeilConjectures.DeligneLaumon.AffineLine.Defs
public import WeilConjectures.WeilSheaf.FourierInversion
public import WeilConjectures.DeligneLaumon.AffineLine.DirectImageUnit
public import WeilConjectures.Mathlib.CategoryTheory.Simple
public import WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport

/-!
# The curve perverse t-structure and Fourier exactness

On a smooth curve the two classes of the perverse t-structure are described purely in terms of
the ordinary cohomology sheaves of a complex: the *upper* class consists of the complexes `K`
with `𝓗ᵃK = 0` for `a > 0` and `𝓗⁰K` of finite support, the *lower* class of those with
`𝓗ᵃK = 0` for `a < -1` and `𝓗⁻¹K` without a nonzero finite-support subsheaf. Their
intersection is the perverse heart. The Fourier–Deligne transform of the affine line is an
exact equivalence between the perverse hearts of the two dual lines.

The three classes below are stated for an arbitrary `k₀`-scheme, but they agree with the
perverse t-structure only on a smooth curve — whence the names. On a scheme of dimension at
least two the perverse t-structure is not described by these two conditions, and the names
`IsCurvePerverse*` keep the description distinct from the genuine t-structure that
`chap-The-six-operations-on-Dbctf` will build.

That the Fourier transform is an equivalence at all is Fourier inversion, which belongs to the
block `chap-The-Fourier-transform`: it is `AlgebraicGeometry.isEquivalence_fourierTransform`. What
this subsection adds is that the equivalence is exact for the perverse t-structures.

## Main declarations

- `AlgebraicGeometry.WeilComplex.IsCurvePerverseUpper`,
  `AlgebraicGeometry.WeilComplex.IsCurvePerverseLower`,
  `AlgebraicGeometry.WeilComplex.IsCurvePerverse`: the two truncation classes on a curve and
  the perverse heart.
- `AlgebraicGeometry.WeilComplex.IsCurvePerverseLE`: the shifted upper classes `ᵖD^{≤n}`.
- `AlgebraicGeometry.WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero`: on a smooth
  curve the lower class is the right orthogonal of `ᵖD^{≤-1}`, the t-structure axiom of
  `lemma-perverse-sheaves-curve`.
- `AlgebraicGeometry.WeilComplex.simple_iff`: the simple curve perverse sheaves on the affine
  line (`lemma-simple-objects--1`), and
  `AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.simple_middleExtension`: the middle extension of
  an irreducible lisse sheaf is simple.
- `AlgebraicGeometry.isCurvePerverseLE_fourierTransform_obj`,
  `AlgebraicGeometry.isCurvePerverseLE_fourierTransform_inv_obj`: `FT_ψ` and its inverse
  preserve the upper classes (`proposition-fourier-transform-perverse-heart--1`).
- `AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`: `FT_ψ` preserves and reflects
  perversity.
- `AlgebraicGeometry.simple_fourierTransform_obj`: `FT_ψ` preserves simple perverse objects.

## Implementation notes

The blueprint defines `ᵖD^{≤0}` and `ᵖD^{≥0}` by the support and cosupport conditions, and
proves in `lemma-perverse-sheaves-curve` that on a smooth curve they are the upper and lower
classes above. The support and cosupport conditions are formalised on the étale site, in
`WeilConjectures.SixFunctors.Etale.Perverse.Basic`; for Weil complexes, which have no Verdier
dual yet, the curve classes are taken as the definition, and parts (1) and (3) of the theorem
hold by definition. Part (5), on short exact sequences in the heart, is not stated: the
provisional `AlgebraicGeometry.WeilComplex` is not triangulated, so its curve perverse heart
carries no abelian structure.

Following the blueprint, the lower class is reached through orthogonality: `FT_ψ` and its
inverse preserve the upper classes, hence `FT_ψ` preserves their right orthogonals.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The upper truncation class of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for
`a > 0`, and `𝓗⁰K` has finite support. (blueprint:
`proposition-fourier-transform-perverse-heart`) -/
def IsCurvePerverseUpper (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, 0 < a → IsZero ((homologySheaf a).obj K)) ∧
    (WeilSheaf.support ((homologySheaf (0 : ℤ)).obj K)).Finite

/-- The lower truncation class of the perverse t-structure on a smooth curve: `𝓗ᵃK = 0` for
`a < -1`, and `𝓗⁻¹K` has no nonzero subsheaf of finite support.
(blueprint: `proposition-fourier-transform-perverse-heart`) -/
def IsCurvePerverseLower (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, a < -1 → IsZero ((homologySheaf a).obj K)) ∧
    ∀ (G : WeilSheaf k₀ l X) (i : G ⟶ (homologySheaf (-1 : ℤ)).obj K), Mono i →
      (WeilSheaf.support G).Finite → IsZero G

/-- A Weil complex on a smooth curve is *curve perverse* if it lies in both truncation classes.
(blueprint: `proposition-fourier-transform-perverse-heart`) -/
def IsCurvePerverse (K : WeilComplex k₀ l X) : Prop :=
  K.IsCurvePerverseUpper ∧ K.IsCurvePerverseLower

/-- The shifted upper class `ᵖD^{≤n} = ᵖD^{≤0}[-n]` of the perverse t-structure on a smooth
curve: `𝓗ᵃK = 0` for `a > n`, and `𝓗ⁿK` has finite support.
(blueprint: `lemma-perverse-sheaves-curve`) -/
def IsCurvePerverseLE (n : ℤ) (K : WeilComplex k₀ l X) : Prop :=
  (∀ a : ℤ, n < a → IsZero ((homologySheaf a).obj K)) ∧
    (WeilSheaf.support ((homologySheaf n).obj K)).Finite

theorem isCurvePerverseUpper_iff_isCurvePerverseLE_zero (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseUpper ↔ K.IsCurvePerverseLE 0 :=
  Iff.rfl

/-- Curve perversity is invariant under isomorphism: the cohomology sheaves of isomorphic
complexes are isomorphic, hence have the same support. -/
instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X)) where
  of_iso {K K'} e h := by
    refine ⟨⟨fun a ha ↦ (h.1.1 a ha).of_iso ((homologySheaf a).mapIso e).symm, ?_⟩,
      ⟨fun a ha ↦ (h.2.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
        fun G i _ hG ↦ h.2.2 G (i ≫ (homologySheaf (-1 : ℤ)).map e.inv)
          (have : Mono ((homologySheaf (-1 : ℤ)).map e.inv) :=
            @IsIso.mono_of_iso _ _ _ _ _ (Functor.map_isIso _ _)
          mono_comp _ _) hG⟩⟩
    rw [← WeilSheaf.support_congr ((homologySheaf (0 : ℤ)).mapIso e)]
    exact h.1.2

theorem IsCurvePerverseLE.of_iso {n : ℤ} {K L : WeilComplex k₀ l X} (e : K ≅ L)
    (hK : K.IsCurvePerverseLE n) : L.IsCurvePerverseLE n :=
  ⟨fun a ha ↦ (hK.1 a ha).of_iso ((homologySheaf a).mapIso e).symm,
    WeilSheaf.support_congr ((homologySheaf n).mapIso e) ▸ hK.2⟩

section Curve

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

omit [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- **The perverse t-structure on a smooth curve**, orthogonality: on a smooth curve
`C` of finite type over `k₀`, a Weil complex lies in the lower class `ᵖD^{≥0}` exactly when it
receives no nonzero morphism from an object of `ᵖD^{≤-1}`. Together with the truncation
triangles this is the statement that the two curve classes form a t-structure.
(blueprint: `lemma-perverse-sheaves-curve`) -/
theorem isCurvePerverseLower_iff_forall_hom_eq_zero (K : WeilComplex k₀ l X) :
    K.IsCurvePerverseLower ↔
      ∀ M : WeilComplex k₀ l X, M.IsCurvePerverseLE (-1) → ∀ f : M ⟶ K, f = 0 := by
  have : Smooth (X ↘ Spec (CommRingCat.of k₀)) := SmoothOfRelativeDimension.smooth 1 _
  constructor
  · rintro ⟨h1, h2⟩ M ⟨hM1, hM2⟩ f
    have : K.obj.IsGE (-1) := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦
      (isZero_homologySheaf_obj_iff i K).1 (h1 i hi)
    have : M.obj.IsLE (-1) := (_root_.DerivedCategory.isLE_iff _ _).2 fun i hi ↦
      (isZero_homologySheaf_obj_iff i M).1 (hM1 i hi)
    have hg : (homologySheaf (-1)).map f = 0 := by
      set g := (homologySheaf (-1)).map f
      have hI := h2 (Limits.image g) (Limits.image.ι g) inferInstance
        (hM2.subset (WeilSheaf.support_subset_of_epi (Limits.factorThruImage g)))
      rw [← Limits.image.fac g, hI.eq_of_src (Limits.image.ι g) 0, Limits.comp_zero]
    apply ObjectProperty.hom_ext
    apply (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE (-1)).1
    exact (congrArg (fun φ ↦ φ.hom) hg).trans (Functor.map_zero _ _ _).symm
  · intro H
    have key (a : ℤ) [K.obj.IsGE a] (G : WeilSheaf k₀ l X)
        (hG : (singleComplex a G).IsCurvePerverseLE (-1)) (i : G ⟶ (homologySheaf a).obj K) :
        i = 0 := by
      have : (singleComplex a G).obj.IsLE a :=
        inferInstanceAs (_root_.DerivedCategory.IsLE
          ((_root_.DerivedCategory.singleFunctor _ a).obj G.obj) a)
      obtain ⟨f, hf⟩ := (_root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
        (X := (singleComplex a G).obj) (Y := K.obj) a).2
        ((homologySheafSingleComplexIso a G).hom.hom ≫ i.hom)
      have hf0 : f = 0 := congrArg (fun φ ↦ φ.hom) (H _ hG (ObjectProperty.homMk f))
      simp only [hf0, Functor.map_zero] at hf
      apply ObjectProperty.hom_ext
      rw [← cancel_epi (homologySheafSingleComplexIso a G).hom.hom, ← hf]
      exact (Limits.comp_zero).symm
    have hLE (a : ℤ) (ha : a < -1) (G : WeilSheaf k₀ l X) :
        (singleComplex a G).IsCurvePerverseLE (-1) :=
      ⟨fun b hb ↦ isZero_homologySheaf_singleComplex (by omega) G, by
        rw [WeilSheaf.support_eq_empty_of_isZero
          (isZero_homologySheaf_singleComplex (by omega) G)]
        exact Set.finite_empty⟩
    have h1 : ∀ a : ℤ, a < -1 → IsZero ((homologySheaf a).obj K) := by
      by_contra! hcon
      obtain ⟨⟨m, hm⟩, -⟩ := K.property.1
      obtain ⟨a, ⟨ha, hza⟩, hmin⟩ := Int.exists_least_of_bdd
        (P := fun a ↦ a < -1 ∧ ¬ IsZero ((homologySheaf a).obj K))
        ⟨m, fun z ⟨_, hz⟩ ↦ by
          by_contra! hzm
          exact hz ((isZero_homologySheaf_obj_iff z K).2
            ((_root_.DerivedCategory.isGE_iff _ m).1 hm z hzm))⟩ hcon
      have : K.obj.IsGE a := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦ by
        by_contra hi'
        have := hmin i ⟨by omega, fun h ↦ hi' ((isZero_homologySheaf_obj_iff i K).1 h)⟩
        omega
      apply hza
      rw [IsZero.iff_id_eq_zero]
      exact key a _ (hLE a ha _) (𝟙 _)
    refine ⟨h1, fun G i _ hG ↦ ?_⟩
    have : K.obj.IsGE (-1) := (_root_.DerivedCategory.isGE_iff _ _).2 fun i hi ↦
      (isZero_homologySheaf_obj_iff i K).1 (h1 i hi)
    have hM : (singleComplex (-1) G).IsCurvePerverseLE (-1) :=
      ⟨fun b hb ↦ isZero_homologySheaf_singleComplex (by omega) G, by
        rw [WeilSheaf.support_congr (homologySheafSingleComplexIso (-1) G)]
        exact hG⟩
    obtain rfl := key (-1) G hM i
    exact IsZero.of_mono_zero G ((homologySheaf (-1)).obj K)

omit [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] in
/-- **Basic objects of the curve perverse heart**: a Weil sheaf of finite support, placed in
degree zero, is curve perverse; these are the objects `i_{x*}E` of the blueprint and their
finite sums. (blueprint: `lemma-perverse-sheaves-curve`) -/
theorem isCurvePerverse_toComplex_obj (G : WeilSheaf k₀ l X) (hG : G.support.Finite) :
    (WeilSheaf.toComplex.obj G).IsCurvePerverse := by
  have hz (a : ℤ) (ha : a ≠ 0) : IsZero ((homologySheaf a).obj (WeilSheaf.toComplex.obj G)) := by
    refine IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ ?_
    change IsZero ((_root_.DerivedCategory.homologyFunctor _ a).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G.obj))
    obtain ha | ha := ha.lt_or_gt
    · exact (_root_.DerivedCategory.isGE_iff _ 0).1 inferInstance a ha
    · exact (_root_.DerivedCategory.isLE_iff _ 0).1 inferInstance a ha
  refine ⟨⟨fun a ha ↦ hz a ha.ne', ?_⟩,
    ⟨fun a ha ↦ hz a (by omega), fun G' i _ _ ↦ IsZero.of_mono i (hz (-1) (by norm_num))⟩⟩
  have e : (homologySheaf 0).obj (WeilSheaf.toComplex.obj G) ≅ G :=
    WeilSheaf.toComplexCompHomologySheafIso.app G
  rw [WeilSheaf.support_congr e]
  exact hG

end Curve

section Heart

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- For `K` in degrees `≤ n` and `L` in degrees `≥ n`, a morphism `K ⟶ L` is determined by the
map it induces on `𝓗ⁿ`, and every morphism `𝓗ⁿK ⟶ 𝓗ⁿL` arises in this way. -/
theorem homologySheaf_map_bijective {K L : WeilComplex k₀ l X} (n : ℤ)
    (hK : ∀ a, n < a → IsZero ((homologySheaf a).obj K))
    (hL : ∀ a, a < n → IsZero ((homologySheaf a).obj L)) :
    Function.Bijective (fun f : K ⟶ L ↦ (homologySheaf n).map f) := by
  have : K.obj.IsLE n := (_root_.DerivedCategory.isLE_iff _ _).2 fun a ha ↦
    (isZero_homologySheaf_obj_iff a K).1 (hK a ha)
  have : L.obj.IsGE n := (_root_.DerivedCategory.isGE_iff _ _).2 fun a ha ↦
    (isZero_homologySheaf_obj_iff a L).1 (hL a ha)
  have h := _root_.DerivedCategory.homologyFunctor_map_bijective_of_isLE_of_isGE
    (X := K.obj) (Y := L.obj) n
  refine ⟨fun f g hfg ↦ ObjectProperty.hom_ext _ (h.1 (congrArg (fun φ ↦ φ.hom) hfg)),
    fun g ↦ ?_⟩
  obtain ⟨f, hf⟩ := h.2 g.hom
  exact ⟨ObjectProperty.homMk f, ObjectProperty.hom_ext _ hf⟩

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil complex all of whose cohomology sheaves vanish is zero. -/
theorem isZero_of_forall_isZero_homologySheaf {K : WeilComplex k₀ l X}
    (h : ∀ a, IsZero ((homologySheaf a).obj K)) : IsZero K := by
  have : K.obj.IsLE 0 := (_root_.DerivedCategory.isLE_iff _ _).2 fun a _ ↦
    (isZero_homologySheaf_obj_iff a K).1 (h a)
  have : K.obj.IsGE 1 := (_root_.DerivedCategory.isGE_iff _ _).2 fun a _ ↦
    (isZero_homologySheaf_obj_iff a K).1 (h a)
  exact IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) K
    (_root_.DerivedCategory.TStructure.t.isZero K.obj 0 1)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- Two Weil complexes concentrated in degree `n` with isomorphic cohomology sheaves `𝓗ⁿ` are
isomorphic. -/
theorem nonempty_iso_of_homologySheaf_iso {K L : WeilComplex k₀ l X} (n : ℤ)
    (hK : ∀ a, a ≠ n → IsZero ((homologySheaf a).obj K))
    (hL : ∀ a, a ≠ n → IsZero ((homologySheaf a).obj L))
    (e : (homologySheaf n).obj K ≅ (homologySheaf n).obj L) : Nonempty (K ≅ L) := by
  obtain ⟨f, hf⟩ := (homologySheaf_map_bijective n (fun a ha ↦ hK a ha.ne')
    (fun a ha ↦ hL a ha.ne)).2 e.hom
  have : IsIso ((ObjectProperty.ι _).map f) := by
    rw [_root_.DerivedCategory.isIso_iff]
    intro a
    by_cases ha : a = n
    · subst ha
      have : IsIso ((homologySheaf a).map f) := by
        simp only at hf
        rw [hf]
        infer_instance
      exact (inferInstance : IsIso ((ObjectProperty.ι _).map ((homologySheaf a).map f)))
    · exact ⟨⟨0, ((isZero_homologySheaf_obj_iff a K).1 (hK a ha)).eq_of_src _ _,
        ((isZero_homologySheaf_obj_iff a L).1 (hL a ha)).eq_of_src _ _⟩⟩
  have := isIso_of_fully_faithful (ObjectProperty.ι _) f
  exact ⟨asIso f⟩

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- The shifted classes `ᵖD^{≤n}` are compatible with the shift: `K[m] ∈ ᵖD^{≤n'}` for
`K ∈ ᵖD^{≤n}` and `m + n' = n`. -/
theorem IsCurvePerverseLE.shift {n : ℤ} {K : WeilComplex k₀ l X} (hK : K.IsCurvePerverseLE n)
    (m n' : ℤ) (h : m + n' = n) : (K⟦m⟧).IsCurvePerverseLE n' := by
  refine ⟨fun a ha ↦ (hK.1 (m + a) (by omega)).of_iso (homologySheafShiftIso K m a (m + a) rfl),
    ?_⟩
  rw [WeilSheaf.support_congr (homologySheafShiftIso K m n' n h)]
  exact hK.2

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil sheaf `G` placed in degree `-1` has `𝓗ᵃ = 0` for `a ≠ -1`. -/
theorem isZero_homologySheaf_shift_one_toComplex (G : WeilSheaf k₀ l X) {a : ℤ} (ha : a ≠ -1) :
    IsZero ((homologySheaf a).obj ((WeilSheaf.toComplex.obj G)⟦(1 : ℤ)⟧)) :=
  isZero_homologySheaf_shift_toComplex G (by omega)

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil sheaf `G` of finite support placed in degree `-1` lies in `ᵖD^{≤-1}`. -/
theorem isCurvePerverseLE_shift_one_toComplex (G : WeilSheaf k₀ l X) (hG : G.support.Finite) :
    ((WeilSheaf.toComplex.obj G)⟦(1 : ℤ)⟧).IsCurvePerverseLE (-1) := by
  refine ⟨fun a ha ↦ isZero_homologySheaf_shift_one_toComplex G (by omega), ?_⟩
  rw [WeilSheaf.support_congr (homologySheafShiftToComplexIso G 1 (-1) (by norm_num))]
  exact hG

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
/-- A Weil sheaf `G` without nonzero subsheaf of finite support, placed in degree `-1`, is curve
perverse. -/
theorem isCurvePerverse_shift_one_toComplex (G : WeilSheaf k₀ l X)
    (hG : ∀ (G' : WeilSheaf k₀ l X) (i : G' ⟶ G), Mono i → G'.support.Finite → IsZero G') :
    ((WeilSheaf.toComplex.obj G)⟦(1 : ℤ)⟧).IsCurvePerverse := by
  refine ⟨⟨fun a ha ↦ isZero_homologySheaf_shift_one_toComplex G (by omega), ?_⟩,
    ⟨fun a ha ↦ isZero_homologySheaf_shift_one_toComplex G (by omega),
      fun G' i _ hG' ↦ hG G' (i ≫ (homologySheafShiftToComplexIso G 1 (-1) (by norm_num)).hom)
        inferInstance hG'⟩⟩
  rw [WeilSheaf.support_eq_empty_of_isZero
    (isZero_homologySheaf_shift_one_toComplex G (by norm_num))]
  exact Set.finite_empty

variable [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))]

/-- Morphisms from the upper class `ᵖD^{≤0}` to the shift `R[-1]` of an object `R` of the lower
class `ᵖD^{≥0}` vanish: `R[-1]` lies in `ᵖD^{≥1}`. -/
theorem hom_shift_neg_one_eq_zero {M R : WeilComplex k₀ l X} (hM : M.IsCurvePerverseUpper)
    (hR : R.IsCurvePerverseLower) (g : M ⟶ R⟦(-1 : ℤ)⟧) : g = 0 := by
  apply (shiftFunctor (WeilComplex k₀ l X) (1 : ℤ)).map_injective
  rw [Functor.map_zero, ← cancel_mono ((shiftFunctorCompIsoId (WeilComplex k₀ l X) (-1 : ℤ) 1
    (by norm_num)).hom.app R), zero_comp]
  exact (isCurvePerverseLower_iff_forall_hom_eq_zero R).1 hR _
    (IsCurvePerverseLE.shift (n := 0) hM 1 (-1) (by norm_num)) _

/-- In a distinguished triangle `T₁ ⟶ T₂ ⟶ T₃ ⟶ T₁[1]` with `T₃` in the lower class, a morphism
`u : M ⟶ T₁` from the upper class with `u ≫ T.mor₁ = 0` vanishes. -/
theorem eq_zero_of_comp_mor₁_eq_zero (T : Pretriangulated.Triangle (WeilComplex k₀ l X))
    (hT : T ∈ distTriang _) (hR : T.obj₃.IsCurvePerverseLower) {M : WeilComplex k₀ l X}
    (hM : M.IsCurvePerverseUpper) (u : M ⟶ T.obj₁) (hu : u ≫ T.mor₁ = 0) : u = 0 := by
  obtain ⟨g, rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₂ _
    (Pretriangulated.inv_rot_of_distTriang _ hT) u hu
  rw [hom_shift_neg_one_eq_zero hM hR g, zero_comp]

/-- **Short exact sequences of the heart** (`lemma-perverse-sheaves-curve`, part (5)): if
`Q ⟶ P ⟶ R ⟶ Q[1]` is a distinguished triangle with `Q` and `P` curve perverse and `R` in the
lower class, then `Q ⟶ P` is a monomorphism of the curve perverse heart. -/
theorem mono_homMk_of_distinguished
    {Q P : ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))}
    {R : WeilComplex k₀ l X} (f : Q.obj ⟶ P.obj) (g : P.obj ⟶ R) (h : R ⟶ Q.obj⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk f g h ∈ distTriang _) (hR : R.IsCurvePerverseLower) :
    Mono (ObjectProperty.homMk f : Q ⟶ P) :=
  Preadditive.mono_of_cancel_zero _ fun {M} u hu ↦ ObjectProperty.hom_ext _
    (eq_zero_of_comp_mor₁_eq_zero _ hT hR M.property.1 u.hom (congrArg (fun φ ↦ φ.hom) hu))

omit [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (CommRingCat.of k₀))] in
/-- A monomorphism `f : Q ⟶ P` of the curve perverse heart is left cancellable against morphisms
`u : M ⟶ Q` of Weil complexes from a curve perverse `M`. -/
theorem eq_zero_of_comp_hom_eq_zero
    {Q P : ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))}
    (f : Q ⟶ P) [Mono f] {M : WeilComplex k₀ l X} (hM : M.IsCurvePerverse) (u : M ⟶ Q.obj)
    (hu : u ≫ f.hom = 0) : u = 0 := by
  have : (ObjectProperty.homMk u : (⟨M, hM⟩ : ObjectProperty.FullSubcategory
      (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))) ⟶ Q) = 0 :=
    (cancel_mono f).1 (ObjectProperty.hom_ext _ (by simpa using hu))
  exact congrArg (fun φ ↦ φ.hom) this


/-- **Cokernels in the heart** (`lemma-perverse-sheaves-curve`, part (5)): the cone `C` of a
monomorphism `f : Q ⟶ P` of the curve perverse heart is curve perverse, so that
`0 ⟶ Q ⟶ P ⟶ C ⟶ 0` is a short exact sequence of the heart. The long exact sequence of
cohomology sheaves shows that `C` lies in the upper class and in degrees `≥ -2`; a nonzero
`𝓗⁻²C ⊆ ker(𝓗⁻¹Q ⟶ 𝓗⁻¹P)`, or a nonzero punctual subsheaf of `𝓗⁻¹C`, would give a nonzero
morphism to `Q` from a curve perverse object killed by `f`. -/
theorem isCurvePerverse_of_mono
    {Q P : ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))}
    (f : Q ⟶ P) [Mono f] {C : WeilComplex k₀ l X} (g : P.obj ⟶ C) (h : C ⟶ Q.obj⟦(1 : ℤ)⟧)
    (hT : Pretriangulated.Triangle.mk f.hom g h ∈ distTriang _) : C.IsCurvePerverse := by
  set T := Pretriangulated.Triangle.mk f.hom g h
  have hQ := Q.property
  have hP := P.property
  have hC₀ (a : ℤ) (h₁ : IsZero ((homologySheaf a).obj P.obj))
      (h₂ : IsZero ((homologySheaf (a + 1)).obj Q.obj)) : IsZero ((homologySheaf a).obj C) :=
    (homologySheaf_exact₃ T a (a + 1) hT rfl).isZero_X₂ (h₁.eq_of_src _ _) (h₂.eq_of_tgt _ _)
  have hup : C.IsCurvePerverseUpper := by
    refine ⟨fun a ha ↦ hC₀ a (hP.1.1 a ha) (hQ.1.1 (a + 1) (by omega)), ?_⟩
    have : Epi ((homologySheaf (0 : ℤ)).map g) :=
      (homologySheaf_exact₃ T 0 1 hT rfl).epi_f ((hQ.1.1 1 one_pos).eq_of_tgt _ _)
    exact hP.1.2.subset (WeilSheaf.support_subset_of_epi ((homologySheaf (0 : ℤ)).map g))
  -- `𝓗⁻²C` embeds into the kernel of `𝓗⁻¹Q ⟶ 𝓗⁻¹P`, which vanishes as `f` is a monomorphism
  have hm2 : IsZero ((homologySheaf (-2)).obj C) := by
    set K := (homologySheaf (-2)).obj C
    let δ := homologySheafδ T (-2) (-1) (by norm_num)
    have : Mono δ := (homologySheaf_exact₃ T (-2) (-1) hT (by norm_num)).mono_g
      ((hP.2.1 (-2) (by norm_num)).eq_of_src _ _)
    have hδ0 : δ ≫ (homologySheaf (-1)).map f.hom = 0 :=
      homologySheafδ_comp_map_mor₁ T (-2) (-1) hT (by norm_num)
    let K' := (WeilSheaf.toComplex.obj K)⟦(1 : ℤ)⟧
    let eK : (homologySheaf (-1)).obj K' ≅ K :=
      homologySheafShiftToComplexIso K 1 (-1) (by norm_num)
    have hK' : K'.IsCurvePerverse := isCurvePerverse_shift_one_toComplex K
      fun G i _ hG ↦ hQ.2.2 G (i ≫ δ) inferInstance hG
    obtain ⟨u, hu⟩ := (homologySheaf_map_bijective (-1) (K := K') (L := Q.obj)
      (fun a ha ↦ isZero_homologySheaf_shift_one_toComplex K (by omega))
      (fun a ha ↦ hQ.2.1 a ha)).2 (eK.hom ≫ δ)
    simp only at hu
    have hu' : u ≫ f.hom = 0 := (homologySheaf_map_bijective (-1) (K := K') (L := P.obj)
      (fun a ha ↦ isZero_homologySheaf_shift_one_toComplex K (by omega))
      (fun a ha ↦ hP.2.1 a ha)).1 (by simp [hu, hδ0])
    have hu0 := eq_zero_of_comp_hom_eq_zero f hK' u hu'
    rw [hu0, Functor.map_zero] at hu
    exact IsZero.of_mono_eq_zero δ ((cancel_epi eK.hom).1 (by rw [← hu, comp_zero]))
  have hge (a : ℤ) (ha : a < -1) : IsZero ((homologySheaf a).obj C) := by
    obtain ha' | rfl := lt_or_eq_of_le (show a ≤ -2 by omega)
    · exact hC₀ a (hP.2.1 a (by omega)) (hQ.2.1 (a + 1) (by omega))
    · exact hm2
  -- a punctual subsheaf of `𝓗⁻¹C` gives a morphism from a punctual sheaf to `Q` killed by `f`
  refine ⟨hup, hge, fun G i _ hG ↦ ?_⟩
  let G1 := (WeilSheaf.toComplex.obj G)⟦(1 : ℤ)⟧
  let eG : (homologySheaf (-1)).obj G1 ≅ G := homologySheafShiftToComplexIso G 1 (-1) (by norm_num)
  obtain ⟨v, hv⟩ := (homologySheaf_map_bijective (-1) (K := G1) (L := C)
    (fun a ha ↦ isZero_homologySheaf_shift_one_toComplex G (by omega)) hge).2 (eG.hom ≫ i)
  simp only at hv
  obtain ⟨w, hw⟩ : ∃ w : WeilSheaf.toComplex.obj G ⟶ Q.obj,
      (shiftFunctor (WeilComplex k₀ l X) (1 : ℤ)).map w = v ≫ h :=
    ⟨_, Functor.map_preimage _ _⟩
  have hwf : w ≫ f.hom = 0 := (shiftFunctor (WeilComplex k₀ l X) (1 : ℤ)).map_injective (by
    rw [Functor.map_comp, Functor.map_zero, hw, Category.assoc]
    erw [Pretriangulated.comp_distTriang_mor_zero₃₁ _ hT]
    rw [comp_zero])
  rw [eq_zero_of_comp_hom_eq_zero f (isCurvePerverse_toComplex_obj G hG) w hwf,
    Functor.map_zero] at hw
  obtain ⟨v', rfl⟩ := Pretriangulated.Triangle.coyoneda_exact₃ T hT v hw.symm
  rw [(isCurvePerverseLower_iff_forall_hom_eq_zero P.obj).1 hP.2 G1
    (isCurvePerverseLE_shift_one_toComplex G hG) v', zero_comp, Functor.map_zero] at hv
  exact IsZero.of_mono_eq_zero i ((cancel_epi eG.hom).1 (by rw [← hv, comp_zero]))

/-- A Weil sheaf `G` of finite support placed in degree zero, as an object of the curve perverse
heart. -/
noncomputable abbrev punctualObj (G : WeilSheaf k₀ l X) (hG : G.support.Finite) :
    ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X)) :=
  ⟨WeilSheaf.toComplex.obj G, isCurvePerverse_toComplex_obj G hG⟩

-- the reflection of isomorphisms by the inclusion of the heart is found slowly
/-- **Punctual simple objects** (`lemma-simple-objects--1`): a Weil sheaf `G` of finite
support placed in degree zero is simple in the curve perverse heart exactly when it is a simple
Weil sheaf. A subsheaf `G' ⊆ G` gives a short exact sequence `0 ⟶ G' ⟶ G ⟶ G/G' ⟶ 0` of the
heart; conversely, the long exact sequence of a subobject `Q ⊆ G[0]` of the heart shows that
`Q = 𝓗⁰Q[0]` with `𝓗⁰Q ⊆ G`. -/
theorem simple_punctualObj_iff (G : WeilSheaf k₀ l X) (hG : G.support.Finite) :
    Simple (punctualObj G hG) ↔ Simple G := by
  constructor
  · intro hS
    refine ⟨fun {G'} i _ ↦ ?_⟩
    have hG' : G'.support.Finite := hG.subset (WeilSheaf.support_subset_of_mono i)
    have hc : (cokernel i).support.Finite :=
      hG.subset (WeilSheaf.support_subset_of_epi (cokernel.π i))
    have hSe : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
      { exact := ShortComplex.exact_cokernel i }
    have hm := mono_homMk_of_distinguished (Q := punctualObj G' hG') (P := punctualObj G hG) _ _ _
      (WeilSheaf.singleTriangle_distinguished hSe) (isCurvePerverse_toComplex_obj _ hc).2
    have h1 : IsIso (ObjectProperty.homMk (WeilSheaf.toComplex.map i) :
        punctualObj G' hG' ⟶ punctualObj G hG) ↔ IsIso i := by
      have : (ObjectProperty.ι
          (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))).ReflectsIsomorphisms :=
        reflectsIsomorphisms_of_full_and_faithful _
      rw [← isIso_iff_of_reflects_iso _ (ObjectProperty.ι _),
        ← isIso_iff_of_reflects_iso i WeilSheaf.toComplex]
      exact Iff.rfl
    have h2 : (ObjectProperty.homMk (WeilSheaf.toComplex.map i) :
        punctualObj G' hG' ⟶ punctualObj G hG) ≠ 0 ↔ i ≠ 0 := by
      rw [not_iff_not, ← Functor.map_eq_zero_iff WeilSheaf.toComplex]
      exact ⟨fun h ↦ congrArg (fun φ ↦ φ.hom) h, fun h ↦ ObjectProperty.hom_ext _ h⟩
    rw [← h1, ← h2]
    exact Simple.mono_isIso_iff_nonzero _
  · intro hS
    have hG0 : ¬ IsZero G := Simple.not_isZero G
    refine simple_of_forall_mono (fun hz ↦ hG0 ?_) fun {Q} f _ ↦ ?_
    · exact ((homologySheaf (0 : ℤ)).map_isZero ((ObjectProperty.ι _).map_isZero hz)).of_iso
        (WeilSheaf.toComplexCompHomologySheafIso.app G).symm
    obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f.hom
    have hC := isCurvePerverse_of_mono f g h hT
    set T := Pretriangulated.Triangle.mk f.hom g h
    have hQ := Q.property
    have hPm1 : IsZero ((homologySheaf (-1)).obj (WeilSheaf.toComplex.obj G)) :=
      isZero_homologySheaf_singleComplex (by norm_num) G
    have hQm1 : IsZero ((homologySheaf (-1)).obj Q.obj) := by
      have : Mono ((homologySheaf (-1)).map f.hom) :=
        (homologySheaf_exact₁ T (-2) (-1) hT (by norm_num)).mono_g
          ((hC.2.1 (-2) (by norm_num)).eq_of_src _ _)
      exact IsZero.of_mono ((homologySheaf (-1)).map f.hom) hPm1
    have : Mono (homologySheafδ T (-1) 0 (by norm_num)) :=
      (homologySheaf_exact₃ T (-1) 0 hT (by norm_num)).mono_g (hPm1.eq_of_src _ _)
    have hCm1 : IsZero ((homologySheaf (-1)).obj C) :=
      hC.2.2 _ (𝟙 _) inferInstance (hQ.1.2.subset
        (WeilSheaf.support_subset_of_mono (homologySheafδ T (-1) 0 _)))
    have : Mono ((homologySheaf (0 : ℤ)).map f.hom) :=
      (homologySheaf_exact₁ T (-1) 0 hT (by norm_num)).mono_g (hCm1.eq_of_src _ _)
    let e0 := WeilSheaf.toComplexCompHomologySheafIso.app G
    by_cases hφ : (homologySheaf (0 : ℤ)).map f.hom ≫ e0.hom = 0
    · left
      have h0 := IsZero.of_mono_eq_zero _ hφ
      refine ObjectProperty.hom_ext _ (IsZero.eq_of_src ?_ _ _)
      refine isZero_of_forall_isZero_homologySheaf fun a ↦ ?_
      obtain ha | rfl | ha := lt_trichotomy a 0
      · obtain ha' | rfl := lt_or_eq_of_le (show a ≤ -1 by omega)
        · exact hQ.2.1 a (by omega)
        · exact hQm1
      · exact h0
      · exact hQ.1.1 a ha
    · right
      have := (Simple.mono_isIso_iff_nonzero (X := G) _).2 hφ
      have : IsIso ((homologySheaf (0 : ℤ)).map f.hom) := IsIso.of_isIso_comp_right _ e0.hom
      have : Epi ((homologySheaf (0 : ℤ)).map g) :=
        (homologySheaf_exact₃ T 0 1 hT rfl).epi_f ((hQ.1.1 1 one_pos).eq_of_tgt _ _)
      have h0 : IsZero ((homologySheaf (0 : ℤ)).obj C) :=
        IsZero.of_epi_eq_zero ((homologySheaf (0 : ℤ)).map g)
        ((homologySheaf_exact₂ T 0 hT).epi_f_iff.1 (inferInstanceAs (Epi
          ((homologySheaf (0 : ℤ)).map f.hom))))
      have hCz : IsZero C := isZero_of_forall_isZero_homologySheaf fun a ↦ by
        obtain ha | rfl | ha := lt_trichotomy a 0
        · obtain ha' | rfl := lt_or_eq_of_le (show a ≤ -1 by omega)
          · exact hC.2.1 a (by omega)
          · exact hCm1
        · exact h0
        · exact hC.1.1 a ha
      have : IsIso ((ObjectProperty.ι _).map f) :=
        (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).1 hCz
      exact isIso_of_fully_faithful (ObjectProperty.ι _) f

/-- **Simple objects of the heart are pure** (`lemma-simple-objects--1`): a simple curve
perverse object `P` has `𝓗⁻¹P = 0` or `𝓗⁰P = 0`. The truncation triangle
`(𝓗⁻¹P)[1] ⟶ P ⟶ (𝓗⁰P)[0] ⟶` is a short exact sequence of the heart
(`lemma-perverse-sheaves-curve`, part (5)), and the subobject `(𝓗⁻¹P)[1]` of the simple `P` is
zero or all of `P`. -/
theorem isZero_homologySheaf_neg_one_or_zero_of_simple
    (P : ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X)))
    [Simple P] :
    IsZero ((homologySheaf (-1 : ℤ)).obj P.obj) ∨ IsZero ((homologySheaf (0 : ℤ)).obj P.obj) := by
  have hP := P.property
  have hle : P.obj.obj.IsLE 0 := (_root_.DerivedCategory.isLE_iff _ _).2 fun a ha ↦
    (isZero_homologySheaf_obj_iff a P.obj).1 (hP.1.1 a ha)
  obtain ⟨K₁, K₃, f, g, h, hT, h₁, h₃le, h₃ge, ⟨e₃⟩⟩ := exists_distTriang_of_isLE P.obj 0 hle
  set T := Pretriangulated.Triangle.mk f g h
  have hK₃ (a : ℤ) (ha : a ≠ 0) : IsZero ((homologySheaf a).obj K₃) := by
    rw [isZero_homologySheaf_obj_iff]
    obtain ha | ha := ha.lt_or_gt
    · exact (_root_.DerivedCategory.isGE_iff _ 0).1 h₃ge a ha
    · exact (_root_.DerivedCategory.isLE_iff _ 0).1 h₃le a ha
  have hK₁ (a : ℤ) (ha : -1 < a) : IsZero ((homologySheaf a).obj K₁) := by
    rw [isZero_homologySheaf_obj_iff]
    exact (_root_.DerivedCategory.isLE_iff _ (0 - 1)).1 h₁ a (by omega)
  have hiso (a : ℤ) (ha : a ≤ -1) : IsIso ((homologySheaf a).map f) := by
    have : Mono ((homologySheaf a).map f) :=
      (homologySheaf_exact₁ T (a - 1) a hT (by omega)).mono_g
        ((hK₃ (a - 1) (by omega)).eq_of_src _ _)
    have : Epi ((homologySheaf a).map f) :=
      (homologySheaf_exact₂ T a hT).epi_f ((hK₃ a (by omega)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  have hK₁P : K₁.IsCurvePerverse := by
    have hz (a : ℤ) (ha : a ≠ -1) : IsZero ((homologySheaf a).obj K₁) := by
      obtain ha | ha := ha.lt_or_gt
      · have := hiso a ha.le
        exact (hP.2.1 a ha).of_iso (asIso ((homologySheaf a).map f))
      · exact hK₁ a ha
    refine ⟨⟨fun a ha ↦ hz a (by omega), ?_⟩, ⟨fun a ha ↦ hz a (by omega), fun G i _ hG ↦ ?_⟩⟩
    · rw [WeilSheaf.support_eq_empty_of_isZero (hz 0 (by norm_num))]
      exact Set.finite_empty
    · have := hiso (-1) le_rfl
      exact hP.2.2 G (i ≫ (homologySheaf (-1 : ℤ)).map f) inferInstance hG
  have hK₃L : K₃.IsCurvePerverseLower :=
    ⟨fun a ha ↦ hK₃ a (by omega), fun G i _ _ ↦ IsZero.of_mono i (hK₃ (-1) (by norm_num))⟩
  let f' : (⟨K₁, hK₁P⟩ : ObjectProperty.FullSubcategory
      (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X))) ⟶ P := ObjectProperty.homMk f
  have : Mono f' := mono_homMk_of_distinguished (Q := ⟨K₁, hK₁P⟩) f g h hT hK₃L
  by_cases hf : f' = 0
  · left
    have := hiso (-1) le_rfl
    have hf0 : f = 0 := congrArg (fun φ ↦ φ.hom) hf
    exact IsZero.of_epi_eq_zero ((homologySheaf (-1 : ℤ)).map f) (by rw [hf0, Functor.map_zero])
  · right
    have : IsIso f' := (Simple.mono_isIso_iff_nonzero f').2 hf
    have : IsIso f := inferInstanceAs (IsIso ((ObjectProperty.ι _).map f'))
    have hz : IsZero K₃ := (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).2 this
    exact ((homologySheaf (0 : ℤ)).map_isZero hz).of_iso e₃.symm

/-- A simple curve perverse object with `𝓗⁻¹P = 0` is a simple Weil sheaf of finite support,
`𝓗⁰P`, placed in degree zero (`lemma-simple-objects--1`). -/
theorem exists_simple_of_simple_of_isZero_homologySheaf_neg_one
    (P : ObjectProperty.FullSubcategory (IsCurvePerverse : ObjectProperty (WeilComplex k₀ l X)))
    [Simple P] (h : IsZero ((homologySheaf (-1 : ℤ)).obj P.obj)) :
    ∃ G : WeilSheaf k₀ l X, Simple G ∧ G.support.Finite ∧
      Nonempty (P.obj ≅ WeilSheaf.toComplex.obj G) := by
  have hP := P.property
  set G := (homologySheaf (0 : ℤ)).obj P.obj
  have hz (a : ℤ) (ha : a ≠ 0) : IsZero ((homologySheaf a).obj P.obj) := by
    obtain ha | ha := ha.lt_or_gt
    · obtain ha' | rfl := lt_or_eq_of_le (show a ≤ -1 by omega)
      · exact hP.2.1 a ha'
      · exact h
    · exact hP.1.1 a ha
  obtain ⟨e⟩ := nonempty_iso_of_homologySheaf_iso 0 hz
    (fun a ha ↦ isZero_homologySheaf_singleComplex ha G)
    (WeilSheaf.toComplexCompHomologySheafIso.app G).symm
  have hG : G.support.Finite := hP.1.2
  have : Simple (punctualObj G hG) := Simple.of_iso (ObjectProperty.isoMk _ e).symm
  exact ⟨G, (simple_punctualObj_iff G hG).1 this, hG, ⟨e⟩⟩
end Heart

end WeilComplex

namespace WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Basic objects of the curve perverse heart**: the middle extension `(j_*M)[1]` of a lisse
Weil sheaf on a dense open of the affine line is curve perverse. Its only cohomology sheaf is
`𝓗⁻¹ = j_*M`, which has no nonzero punctual subsheaf
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.eq_zero_of_support_finite`).
(blueprint: `lemma-perverse-sheaves-curve`) -/
theorem LisseOnDenseOpen.isCurvePerverse_middleExtension (D : LisseOnDenseOpen k₀ l) :
    D.middleExtension.IsCurvePerverse := by
  have hz (a : ℤ) (ha : a ≠ -1) :
      IsZero ((WeilComplex.homologySheaf a).obj D.middleExtension) :=
    WeilComplex.isZero_homologySheaf_shift_toComplex _ (by omega)
  let e : (WeilComplex.homologySheaf (-1 : ℤ)).obj D.middleExtension ≅ D.directImage :=
    WeilComplex.homologySheafShiftToComplexIso _ 1 (-1) (by norm_num)
  refine ⟨⟨fun a ha ↦ hz a (by omega), ?_⟩, ⟨fun a ha ↦ hz a (by omega), fun G i _ hG ↦ ?_⟩⟩
  · rw [WeilSheaf.support_eq_empty_of_isZero (hz 0 (by norm_num))]
    exact Set.finite_empty
  · have h1 : i = 0 :=
      (cancel_mono e.hom).1 ((D.eq_zero_of_support_finite hG _).trans zero_comp.symm)
    subst h1
    exact IsZero.of_mono_zero G ((WeilComplex.homologySheaf (-1 : ℤ)).obj D.middleExtension)

end WeilSheaf

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The curve perverse Weil complexes on the affine line, as a full subcategory: the heart
`Perv(A₀)` of the perverse t-structure. -/
abbrev curvePerverse : ObjectProperty (WeilComplex k₀ l (affineLine k₀)) :=
  IsCurvePerverse

/-- A curve perverse object `X` maps to a simple `P` either by an isomorphism or from zero, when
the map is a monomorphism. -/
theorem isZero_or_isIso_of_mono_of_simple
    {X P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory} [Simple P] (f : X ⟶ P) [Mono f] :
    IsZero X ∨ IsIso f := by
  by_cases h0 : f = 0
  · exact .inl (IsZero.of_mono_eq_zero f h0)
  · exact .inr ((Simple.mono_isIso_iff_nonzero f).2 h0)

/-- A morphism of curve perverse objects which is an isomorphism of the heart is an isomorphism of
Weil complexes. -/
theorem isIso_hom_of_isIso {X P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory}
    (f : X ⟶ P) [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((ObjectProperty.ι _).map f))

/-- A subobject `f : Q ⟶ P` of the middle extension `P ≅ (j_*N)[1]` of an irreducible lisse `N`
is `0` or all of `P`. The long exact sequence of the triangle `Q ⟶ P ⟶ R ⟶` of the heart is
`0 ⟶ 𝓗⁻¹Q ⟶ j_*N ⟶ 𝓗⁻¹R ⟶ 𝓗⁰Q ⟶ 0`, to which
`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_or_isZero_of_exact` applies: either
`𝓗⁻¹Q = 𝓗⁰Q = 0` and `Q = 0`, or `𝓗⁻¹R = 0` and `R = 0`.
(blueprint: `lemma-simple-objects--1`) -/
theorem eq_zero_or_isIso_of_mono_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) {Q P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory}
    (eP : P.obj ≅ D.middleExtension) (f : Q ⟶ P) [Mono f] :
    f = 0 ∨ IsIso f := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  obtain ⟨R, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle f.hom
  have hR := isCurvePerverse_of_mono f g h hT
  set T := Pretriangulated.Triangle.mk f.hom g h
  have hQ := Q.property
  let eP' : P.obj ≅ (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧ :=
    eP ≪≫ (Iso.refl D.middleExtension :
      D.middleExtension ≅ (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧)
  have hP0 : IsZero ((homologySheaf (0 : ℤ)).obj P.obj) :=
    (isZero_homologySheaf_shift_one_toComplex D.directImage (by norm_num)).of_iso
      ((homologySheaf (0 : ℤ)).mapIso eP')
  let eM : (homologySheaf (-1 : ℤ)).obj P.obj ≅ D.directImage :=
    (homologySheaf (-1 : ℤ)).mapIso eP' ≪≫
      homologySheafShiftToComplexIso D.directImage 1 (-1) (by norm_num)
  have : Mono ((homologySheaf (-1 : ℤ)).map T.mor₁) :=
    (homologySheaf_exact₁ T (-2) (-1) hT (by norm_num)).mono_g
      ((hR.2.1 (-2) (by norm_num)).eq_of_src _ _)
  have : Epi (homologySheafδ T (-1) 0 (by norm_num)) :=
    (homologySheaf_exact₁ T (-1) 0 hT (by norm_num)).epi_f (hP0.eq_of_tgt _ _)
  obtain ⟨hA0, hC0⟩ | hB0 := D.isZero_or_isZero_of_exact hD eM _ _ _ _ _
    (homologySheaf_exact₂ T (-1) hT) (homologySheaf_exact₃ T (-1) 0 hT (neg_add_cancel 1))
    hQ.1.2 hR.2.2
  · left
    refine ObjectProperty.hom_ext _ (IsZero.eq_of_src ?_ _ _)
    refine isZero_of_forall_isZero_homologySheaf fun a ↦ ?_
    obtain ha | rfl | ha := lt_trichotomy a 0
    · obtain ha' | rfl := lt_or_eq_of_le (show a ≤ -1 by omega)
      · exact hQ.2.1 a ha'
      · exact hA0
    · exact hC0
    · exact hQ.1.1 a ha
  · right
    have hRz : IsZero R := isZero_of_forall_isZero_homologySheaf fun a ↦ by
      obtain ha | rfl | ha := lt_trichotomy a 0
      · obtain ha' | rfl := lt_or_eq_of_le (show a ≤ -1 by omega)
        · exact hR.2.1 a ha'
        · exact hB0
      · exact (homologySheaf_exact₃ T 0 1 hT rfl).isZero_X₂ (hP0.eq_of_src _ _)
          ((hQ.1.1 1 one_pos).eq_of_tgt _ _)
      · exact hR.1.1 a ha
    have : IsIso ((ObjectProperty.ι _).map f) :=
      (Pretriangulated.Triangle.isZero₃_iff_isIso₁ T hT).1 hRz
    exact isIso_of_fully_faithful (ObjectProperty.ι _) f

/-- **Middle extensions are simple** (`lemma-simple-objects--1`): a curve perverse object
isomorphic to the middle extension `(j_*N)[1]` of an irreducible lisse `N` is simple
(`AlgebraicGeometry.WeilComplex.eq_zero_or_isIso_of_mono_middleExtension`); it is nonzero since
`N = j^* j_* N` is. -/
theorem simple_of_iso_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) (P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory)
    (eP : P.obj ≅ D.middleExtension) : Simple P := by
  refine simple_of_forall_mono (fun hz ↦ hD.2.1 (D.isZero_of_isZero_lowerStar ?_))
    fun {Q} f _ ↦ eq_zero_or_isIso_of_mono_middleExtension D hD eP f
  let eP' : P.obj ≅ (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧ :=
    eP ≪≫ (Iso.refl D.middleExtension :
      D.middleExtension ≅ (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧)
  have h1 : IsZero D.directImage :=
    ((homologySheaf (-1 : ℤ)).map_isZero ((ObjectProperty.ι _).map_isZero hz)).of_iso
      ((homologySheaf (-1 : ℤ)).mapIso eP' ≪≫
        homologySheafShiftToComplexIso D.directImage 1 (-1) (by norm_num)).symm
  exact h1.of_iso (Iso.refl _ : (WeilSheaf.lowerStar D.j).obj D.sheaf ≅ D.directImage)

/-- A Weil sheaf `G` placed in degree `-1` vanishes if and only if `G` does. -/
theorem isZero_of_isZero_shift_one_toComplex {G : WeilSheaf k₀ l (affineLine k₀)}
    (h : IsZero ((WeilSheaf.toComplex.obj G)⟦(1 : ℤ)⟧)) : IsZero G :=
  ((homologySheaf (-1 : ℤ)).map_isZero h).of_iso
    (homologySheafShiftToComplexIso G 1 (-1) (by norm_num)).symm

/-- **Simple objects without `𝓗⁰` are middle extensions** (`lemma-simple-objects--1`). Let
`P` be simple with `𝓗⁰P = 0`, so `P ≅ F[1]` for `F = 𝓗⁻¹P` without punctual subsheaf. On a
dense open `j : U₀ ↪ 𝔸¹` where `F` is lisse, the unit `F ⟶ j_*j^*F` is injective with punctual
cokernel `Q` (`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.exists_mono_directImage`), and the
triangle `Q[0] ⟶ F[1] ⟶ (j_*j^*F)[1] ⟶` exhibits `Q[0]` as a subobject of `P`, so `Q = 0` and
`P ≅ (j_*N)[1]`, `N = j^*F`. A lisse subsheaf `N' ⊆ N` gives the subobject `(j_*N')[1]` of `P`,
with quotient `C[1]`, `C = coker(j_*N' ⟶ j_*N)` having no punctual subsheaf
(`AlgebraicGeometry.WeilSheaf.LisseOnDenseOpen.isZero_of_mono_cokernel_lowerStar_map`); so
`N' = 0` or `N' = N`. -/
theorem exists_middleExtension_of_simple
    (P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory) [Simple P]
    (h : IsZero ((homologySheaf (0 : ℤ)).obj P.obj)) :
    ∃ D : WeilSheaf.LisseOnDenseOpen k₀ l, D.sheaf.IsIrreducibleLisse ∧
      Nonempty (P.obj ≅ D.middleExtension) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  have hP := P.property
  set F := (homologySheaf (-1 : ℤ)).obj P.obj
  have hF : ∀ (G : WeilSheaf k₀ l (affineLine k₀)) (i : G ⟶ F), Mono i → G.support.Finite →
      IsZero G := hP.2.2
  obtain ⟨eF⟩ := nonempty_iso_of_homologySheaf_iso (-1) (K := P.obj)
    (L := (WeilSheaf.toComplex.obj F)⟦(1 : ℤ)⟧)
    (fun a ha ↦ by
      obtain ha | rfl | ha := lt_trichotomy a 0
      · exact hP.2.1 a (by omega)
      · exact h
      · exact hP.1.1 a ha)
    (fun a ha ↦ isZero_homologySheaf_shift_one_toComplex F ha)
    (homologySheafShiftToComplexIso F 1 (-1) (by norm_num)).symm
  let P' : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory :=
    ⟨(WeilSheaf.toComplex.obj F)⟦(1 : ℤ)⟧, isCurvePerverse_shift_one_toComplex F hF⟩
  have : Simple P' := Simple.of_iso (ObjectProperty.isoMk _ eF).symm
  have hF0 : ¬ IsZero F := fun hz ↦ Simple.not_isZero P'
    (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) P'
      ((shiftFunctor _ (1 : ℤ)).map_isZero (WeilSheaf.toComplex.map_isZero hz)))
  -- the unit `F ⟶ j_* j^* F`
  obtain ⟨D, η, hη, hc⟩ := WeilSheaf.LisseOnDenseOpen.exists_mono_directImage hF
  have hS : (ShortComplex.mk η (cokernel.π η) (cokernel.condition η)).ShortExact :=
    { exact := ShortComplex.exact_cokernel η }
  have hT := Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _
    (WeilSheaf.singleTriangle_distinguished hS))
  have hm := mono_homMk_of_distinguished (Q := punctualObj _ hc) (P := P') _ _ _ hT
    D.isCurvePerverse_middleExtension.2
  obtain hz | hiso := @isZero_or_isIso_of_mono_of_simple _ _ _ _ _ _ _ _ _ _ hm
  swap
  · -- the cokernel of `F ⟶ j_*N` vanishes, else `j_*N = 0`
    have h3 := (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT).2
      (@isIso_hom_of_isIso _ _ _ _ _ _ _ _ _ hiso)
    exact absurd (IsZero.of_mono η (isZero_of_isZero_shift_one_toComplex h3)) hF0
  have hcz : IsZero (cokernel η) :=
    ((homologySheaf (0 : ℤ)).map_isZero ((ObjectProperty.ι _).map_isZero hz)).of_iso
      (WeilSheaf.toComplexCompHomologySheafIso.app _).symm
  have : Epi η := Preadditive.epi_of_isZero_cokernel η hcz
  have : IsIso η := isIso_of_mono_of_epi η
  let e : P.obj ≅ (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧ :=
    eF ≪≫ (shiftFunctor _ (1 : ℤ)).mapIso (WeilSheaf.toComplex.mapIso (asIso η))
  refine ⟨D, ⟨D.lisse, fun hN ↦ hF0 (IsZero.of_mono η ?_), fun N' i _ hN' ↦ ?_⟩,
    ⟨e ≪≫ (Iso.refl _ : (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧ ≅ D.middleExtension)⟩⟩
  · exact ((WeilSheaf.lowerStar D.j).map_isZero hN).of_iso
      (Iso.refl _ : D.directImage ≅ (WeilSheaf.lowerStar D.j).obj D.sheaf)
  -- a lisse subsheaf `N' ⊆ N` gives the subobject `(j_*N')[1]` of `P`
  let ji := (WeilSheaf.lowerStar D.j).map i
  have : Mono ji := (WeilSheaf.lowerStar D.j).map_mono i
  have hS₂ : (ShortComplex.mk ji (cokernel.π ji) (cokernel.condition ji)).ShortExact :=
    { exact := ShortComplex.exact_cokernel ji }
  have hT₂ := Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _
    (Pretriangulated.rot_of_distTriang _
    (WeilSheaf.singleTriangle_distinguished hS₂)))
  let Q₂ : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory :=
    ⟨(WeilSheaf.toComplex.obj ((WeilSheaf.lowerStar D.j).obj N'))⟦(1 : ℤ)⟧,
      isCurvePerverse_shift_one_toComplex _ fun G g _ hG ↦
        IsZero.of_mono_eq_zero g (WeilSheaf.eq_zero_of_support_finite_lowerStar D.j hN' hG g)⟩
  let P₂ : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory :=
    ⟨(WeilSheaf.toComplex.obj ((WeilSheaf.lowerStar D.j).obj D.sheaf))⟦(1 : ℤ)⟧,
      isCurvePerverse_shift_one_toComplex _ fun G g _ hG ↦
        IsZero.of_mono_eq_zero g (WeilSheaf.eq_zero_of_support_finite_lowerStar D.j D.lisse hG g)⟩
  have : Simple P₂ := Simple.of_iso (ObjectProperty.isoMk _ (e ≪≫ (Iso.refl _ :
    (WeilSheaf.toComplex.obj D.directImage)⟦(1 : ℤ)⟧ ≅ P₂.obj))).symm
  have hm₂ := mono_homMk_of_distinguished (Q := Q₂) (P := P₂) _ _ _ hT₂
    (isCurvePerverse_shift_one_toComplex _ fun G g _ hG ↦
      D.isZero_of_mono_cokernel_lowerStar_map i hN' G g hG).2
  obtain hz₂ | hiso₂ := @isZero_or_isIso_of_mono_of_simple _ _ _ _ _ _ _ _ _ _ hm₂
  · exact .inl (D.isZero_of_isZero_lowerStar (isZero_of_isZero_shift_one_toComplex
      ((ObjectProperty.ι _).map_isZero hz₂)))
  · have h3 := (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hT₂).2
      (@isIso_hom_of_isIso _ _ _ _ _ _ _ _ _ hiso₂)
    have : Epi ji := Preadditive.epi_of_isZero_cokernel ji
      (isZero_of_isZero_shift_one_toComplex h3)
    exact .inr (D.isIso_of_isIso_lowerStar_map i (isIso_of_mono_of_epi ji))

/-- **Simple perverse sheaves on the affine line**: a curve perverse Weil complex is simple in
`Perv(A₀)` exactly when it is either a simple Weil sheaf of finite support placed in degree
zero — a punctual object `i_{x*}E` with `E` irreducible — or the middle extension `(j_*N)[1]`
of an irreducible lisse sheaf `N` on a dense open. (blueprint: `lemma-simple-objects--1`)
-/
theorem simple_iff (P : (curvePerverse (k₀ := k₀) (l := l)).FullSubcategory) :
    Simple P ↔
      (∃ G : WeilSheaf k₀ l (affineLine k₀), Simple G ∧ G.support.Finite ∧
        Nonempty (P.obj ≅ WeilSheaf.toComplex.obj G)) ∨
      ∃ D : WeilSheaf.LisseOnDenseOpen k₀ l, D.sheaf.IsIrreducibleLisse ∧
        Nonempty (P.obj ≅ D.middleExtension) := by
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  constructor
  · intro
    obtain h | h := isZero_homologySheaf_neg_one_or_zero_of_simple P
    · exact .inl (exists_simple_of_simple_of_isZero_homologySheaf_neg_one P h)
    · exact .inr (exists_middleExtension_of_simple P h)
  · rintro (⟨G, hG, hGf, ⟨e⟩⟩ | ⟨D, hD, ⟨e⟩⟩)
    · have := (simple_punctualObj_iff G hGf).2 hG
      exact Simple.of_iso (ObjectProperty.isoMk _ e : P ≅ punctualObj G hGf)
    · exact simple_of_iso_middleExtension D hD P e

end WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- The middle extension `(j_*M)[1]` of an irreducible lisse sheaf is a simple object of the
curve perverse heart. (blueprint: `lemma-simple-objects--1`) -/
theorem WeilSheaf.LisseOnDenseOpen.simple_middleExtension (D : WeilSheaf.LisseOnDenseOpen k₀ l)
    (hD : D.sheaf.IsIrreducibleLisse) :
    Simple (⟨D.middleExtension, D.isCurvePerverse_middleExtension⟩ :
      WeilComplex.curvePerverse.FullSubcategory) :=
  (WeilComplex.simple_iff _).2 (.inr ⟨D, hD, ⟨Iso.refl _⟩⟩)

/-- The Tate twist does not change the curve perverse upper classes: it changes neither the
vanishing nor the support of a cohomology sheaf. -/
theorem WeilComplex.isCurvePerverseLE_tateTwist_iff (m n : ℤ)
    (K : WeilComplex k₀ l (affineLine k₀)) :
    ((WeilComplex.tateTwist k₀ l (affineLine k₀) m).obj K).IsCurvePerverseLE n ↔
      K.IsCurvePerverseLE n := by
  simp only [WeilComplex.IsCurvePerverseLE, WeilComplex.isZero_homologySheaf_tateTwist_iff,
    WeilComplex.support_homologySheaf_tateTwist]

/-- **The Fourier transform is perverse t-exact on the line**, upper classes: for a nontrivial
`ψ`, the transform `FT_ψ` carries `ᵖD^{≤n}(A₀)` into `ᵖD^{≤n}(A'₀)`. The truncation triangle
`τ_{<n}K ⟶ K ⟶ 𝓗ⁿK[-n] ⟶` reduces this to two facts: `FT_ψ` carries `D^{≤n-1}` into
`D^{≤n}` with top cohomology sheaf of finite support
(`AlgebraicGeometry.isLE_fourierTransform_obj`,
`AlgebraicGeometry.support_homologySheaf_fourierTransform_finite`), and a sheaf of finite
support transforms into a complex `≤ -1`
(`AlgebraicGeometry.isLE_fourierTransform_of_isGE_of_isLE`).
(blueprint: `proposition-fourier-transform-perverse-heart--1`) -/
theorem isCurvePerverseLE_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {n : ℤ} {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.IsCurvePerverseLE n) :
    ((fourierTransform ψ).obj K).IsCurvePerverseLE n := by
  obtain ⟨hK₁, hK₂⟩ := hK
  obtain ⟨K₁, K₃, f, g, h, hT, h₁, h₃le, h₃ge, ⟨e₃⟩⟩ := WeilComplex.exists_distTriang_of_isLE K n
    ((WeilComplex.isLE_iff_isZero_homologySheaf K n).2 hK₁)
  have hT' := (fourierTransform ψ).map_distinguished _ hT
  have hF₁ := isLE_fourierTransform_obj ψ hψ h₁
  rw [sub_add_cancel] at hF₁
  have hF₁' := support_homologySheaf_fourierTransform_finite ψ hψ h₁
  rw [sub_add_cancel] at hF₁'
  have hF₃ := isLE_fourierTransform_of_isGE_of_isLE ψ h₃ge h₃le
    ((WeilSheaf.support_congr e₃).symm ▸ hK₂)
  -- `𝓗ᵃ FT_ψ(K₁) ⟶ 𝓗ᵃ FT_ψ(K)` is an epimorphism for `a ≥ n`
  have hepi (a : ℤ) (ha : n ≤ a) :
      Epi ((WeilComplex.homologySheaf a).map ((fourierTransform ψ).map f)) :=
    (WeilComplex.homologySheaf_exact₂ _ a hT').epi_f
      (((WeilComplex.isLE_iff_isZero_homologySheaf _ _).1 hF₃ a (by lia)).eq_of_tgt _ _)
  refine ⟨fun a ha ↦ ?_, ?_⟩
  · have := hepi a ha.le
    exact IsZero.of_epi ((WeilComplex.homologySheaf a).map ((fourierTransform ψ).map f))
      ((WeilComplex.isLE_iff_isZero_homologySheaf _ _).1 hF₁ a ha)
  · have := hepi n le_rfl
    exact hF₁'.subset (WeilSheaf.support_subset_of_epi
      ((WeilComplex.homologySheaf n).map ((fourierTransform ψ).map f)))

/-- **The Fourier transform is perverse t-exact on the line**, upper classes for the inverse:
the inverse of the equivalence `FT_ψ`, which is `FT_{ψ⁻¹}(-)(1)` by Fourier inversion
(`AlgebraicGeometry.nonempty_fourierTransform_comp_fourierTransform_inv_iso`), carries
`ᵖD^{≤n}(A'₀)` into `ᵖD^{≤n}(A₀)`, by the argument for `FT_{ψ⁻¹}` and the twist not changing the
upper classes. (blueprint: `proposition-fourier-transform-perverse-heart--1`) -/
theorem isCurvePerverseLE_fourierTransform_inv_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    {n : ℤ} {K : WeilComplex k₀ l (affineLine k₀)} (hK : K.IsCurvePerverseLE n) :
    haveI := isEquivalence_fourierTransform (l := l) ψ hψ
    ((fourierTransform ψ).inv.obj K).IsCurvePerverseLE n := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  obtain ⟨e⟩ := nonempty_fourierTransform_comp_fourierTransform_inv_iso (l := l) ψ hψ
  have h := isCurvePerverseLE_fourierTransform_obj ψ⁻¹ (inv_ne_one.2 hψ) hK
  rw [← WeilComplex.isCurvePerverseLE_tateTwist_iff (-1)]
  exact h.of_iso ((fourierTransform ψ⁻¹).mapIso
    ((fourierTransform ψ).asEquivalence.counitIso.app K).symm ≪≫
      e.app ((fourierTransform ψ).inv.obj K))

/--
The Fourier–Deligne transform along a nontrivial additive character is exact for the curve
perverse t-structures of the two dual affine lines: a Weil complex is curve perverse exactly
when its transform is.

```
  Dᵇ(A₀) ──────FT_ψ──────▶ Dᵇ(A'₀)
     ∪                        ∪
  Perv(A₀) ────≃ exact───▶ Perv(A'₀)
```
(blueprint: `proposition-fourier-transform-perverse-heart`)
-/
theorem isCurvePerverse_fourierTransform_obj_iff (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (K : WeilComplex k₀ l (affineLine k₀)) :
    ((fourierTransform ψ).obj K).IsCurvePerverse ↔ K.IsCurvePerverse := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  have : SmoothOfRelativeDimension 1 (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) := by
    simpa using AffineSpace.smoothOfRelativeDimension_over PUnit.{u + 1} (Spec (.of k₀))
  constructor
  · rintro ⟨hU, hL⟩
    refine ⟨(isCurvePerverseLE_fourierTransform_inv_obj ψ hψ hU).of_iso
      ((fourierTransform ψ).asEquivalence.unitIso.app K).symm, ?_⟩
    rw [WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero] at hL ⊢
    intro M hM f
    apply (fourierTransform ψ).map_injective
    rw [hL _ (isCurvePerverseLE_fourierTransform_obj ψ hψ hM) ((fourierTransform ψ).map f),
      Functor.map_zero]
  · rintro ⟨hU, hL⟩
    refine ⟨isCurvePerverseLE_fourierTransform_obj ψ hψ hU, ?_⟩
    rw [WeilComplex.isCurvePerverseLower_iff_forall_hom_eq_zero] at hL ⊢
    intro M hM f
    let e := (fourierTransform ψ).asEquivalence.counitIso.app M
    obtain ⟨g, hg⟩ := (fourierTransform ψ).map_surjective (e.hom ≫ f)
    rw [← cancel_epi e.hom, comp_zero]
    exact hg.symm.trans ((congrArg (fourierTransform ψ).map
      (hL _ (isCurvePerverseLE_fourierTransform_inv_obj ψ hψ hM) g)).trans (Functor.map_zero _ _ _))

/-- `FT_ψ` preserves simple objects of the curve perverse heart: by Fourier inversion
(`AlgebraicGeometry.isEquivalence_fourierTransform`) and perversity
(`AlgebraicGeometry.isCurvePerverse_fourierTransform_obj_iff`) it restricts to an
autoequivalence of the heart, and equivalences preserve simple objects.
(blueprint: `proposition-fourier-transform-middle-extension--1`, Step 1) -/
theorem simple_fourierTransform_obj (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1)
    (K : (WeilComplex.curvePerverse (k₀ := k₀) (l := l)).FullSubcategory) [Simple K] :
    Simple (⟨(fourierTransform ψ).obj K.obj,
      (isCurvePerverse_fourierTransform_obj_iff ψ hψ K.obj).2 K.property⟩ :
        WeilComplex.curvePerverse.FullSubcategory) := by
  have := isEquivalence_fourierTransform (l := l) ψ hψ
  have hP : WeilComplex.curvePerverse.inverseImage (fourierTransform ψ).asEquivalence.functor =
      WeilComplex.curvePerverse :=
    funext fun K ↦ propext (isCurvePerverse_fourierTransform_obj_iff ψ hψ K)
  exact simple_obj ((fourierTransform ψ).asEquivalence.congrFullSubcategory hP).functor K

end AlgebraicGeometry
