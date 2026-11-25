/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.Separable
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# An integral étale scheme embeds in its finite generic normalization

An integral separated étale scheme `E` over a normal integral Noetherian scheme `X` embeds as an
open subscheme of the normalization of `X` in the finite separable generic-fibre field `L`,
provided that normalization is finite. No quasi-compactness of `E` or `f` is assumed. The
generic-fibre equation in the statement records the specified identification with `Spec L`
using the canonical map from `Spec L` to the normalization.

Source: Stacks Project, more-morphisms.tex, Tag 05K0
(lemma-quasi-finite-separated-pass-through-finite), applied on affine source and target
neighbourhoods; morphisms.tex, Tag 0AB1 (lemma-finite-birational-over-normal); separated
uniqueness as in Tag 01RH (blueprint: lem-sf-integral-etale-normalization-open).

## Main statements

* `AlgebraicGeometry.integral_etale_normalization_open`
-/


@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing

namespace AlgebraicGeometry

private theorem normalization_source_iso
    {P Q Y : Scheme.{u}} (a : P ⟶ Y) (b : Q ⟶ Y)
    [QuasiCompact a] [QuasiSeparated a] [QuasiCompact b] [QuasiSeparated b]
    (e : P ≅ Q) (he : e.hom ≫ b = a) :
    ∃ en : a.normalization ≅ b.normalization,
      en.hom ≫ b.fromNormalization = a.fromNormalization := by
  have h₁ : a = (e.hom ≫ b.toNormalization) ≫ b.fromNormalization := by simp [he]
  have h₂ : b = (e.inv ≫ a.toNormalization) ≫ a.fromNormalization := by
    simp [← he]
  let m := a.normalizationDesc (e.hom ≫ b.toNormalization) b.fromNormalization h₁
  let n := b.normalizationDesc (e.inv ≫ a.toNormalization) a.fromNormalization h₂
  have hm : m ≫ b.fromNormalization = a.fromNormalization := a.normalizationDesc_comp ..
  have hn : n ≫ a.fromNormalization = b.fromNormalization := b.normalizationDesc_comp ..
  have hmn : m ≫ n = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext a _ _ a.fromNormalization
    · simp [m, n, Category.assoc]
    · simp [Category.assoc, hn, hm]
    · simp
  have hnm : n ≫ m = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext b _ _ b.fromNormalization
    · simp [m, n, Category.assoc]
    · simp [Category.assoc, hm, hn]
    · simp
  exact ⟨⟨m, n, hmn, hnm⟩, hm⟩

private theorem field_dominant_generic
    {Y : Scheme.{u}} [IsIntegral Y] {L : Type u} [Field L]
    (q : Spec (.of L) ⟶ Y) [IsDominant q] (z : Spec (.of L)) :
    q z = genericPoint Y := by
  apply (show IsGenericPoint (q z) ⊤ from ?_).eq (genericPoint_spec Y)
  change closure {q z} = Set.univ
  rw [← q.denseRange.closure_range]
  congr 1
  ext y
  exact ⟨fun h ↦ ⟨z, h.symm⟩,
    fun ⟨x, hx⟩ ↦ by rw [← hx, Subsingleton.elim x z]; rfl⟩

private theorem generic_normalization_isIso
    {Y : Scheme.{u}} [IsIntegral Y]
    (hn : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
    {L : Type u} [Field L] (q : Spec (.of L) ⟶ Y)
    [IsDominant q] [IsPreimmersion q] : IsIso q.fromNormalization := by
  have hq : q (closedPoint L) = genericPoint Y := field_dominant_generic q _
  have hf : IsField (Y.presheaf.stalk (q (closedPoint L))) := by
    rw [hq]
    exact Field.toIsField Y.functionField
  let := hf.toField
  have hi : IsIso (Scheme.stalkClosedPointTo q) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨(Scheme.stalkClosedPointTo q).hom.injective,
      (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of L)).hom).2.comp
        (q.stalkMap_surjective _)⟩
  have key (y : Y) (hy : y = genericPoint Y)
      (ψ : Y.presheaf.stalk y ⟶ .of L) [IsIso ψ]
      (hψ : Spec.map ψ ≫ Y.fromSpecStalk y = q) :
      ∃ e : Spec (.of L) ≅ Spec Y.functionField,
        e.hom ≫ Y.fromSpecFunctionField = q := by
    subst y
    exact ⟨asIso (Spec.map ψ), hψ⟩
  obtain ⟨e, he⟩ := key _ hq (Scheme.stalkClosedPointTo q)
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk q)
  obtain ⟨en, hen⟩ := normalization_source_iso q Y.fromSpecFunctionField e he
  have hnormal := Y.isIso_fromNormalization_restrict ⊤ (fun y _ ↦ hn y)
  have : IsIso Y.fromNormalization := by
    have := hnormal
    have : IsIso (⊤ : Y.Opens).ι := Y.topIso.isIso_hom
    have hi : IsIso ((Y.fromNormalization ⁻¹ᵁ ⊤).ι ≫ Y.fromNormalization) := by
      rw [← morphismRestrict_ι]
      infer_instance
    have : IsIso ((⊤ : Y.normalization.Opens).ι ≫ Y.fromNormalization) := by
      simpa using hi
    have : IsIso (⊤ : Y.normalization.Opens).ι := Y.normalization.topIso.isIso_hom
    exact IsIso.of_isIso_comp_left (⊤ : Y.normalization.Opens).ι _
  rw [← hen]
  infer_instance

private theorem extend_generic_to_integral
    {P Y X N : Scheme.{u}} (q : P ⟶ Y) [QuasiCompact q] [QuasiSeparated q]
    [IsIso q.fromNormalization] (f : Y ⟶ X) (n : N ⟶ X) [IsIntegralHom n]
    (a : P ⟶ N) (ha : a ≫ n = q ≫ f) :
    ∃ j : Y ⟶ N, j ≫ n = f ∧ q ≫ j = a := by
  let b := pullback.lift a q ha
  let p := pullback.snd n f
  have hb : q = b ≫ p := by simp [b, p]
  let d := q.normalizationDesc b p hb
  let s := inv q.fromNormalization ≫ d
  have hs : s ≫ p = 𝟙 Y := by
    simp [s, d, p]
  have hq : q ≫ inv q.fromNormalization = q.toNormalization := by
    apply (cancel_mono q.fromNormalization).mp
    simp
  refine ⟨s ≫ pullback.fst n f, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · simp only [s, ← Category.assoc, hq]
    rw [Scheme.Hom.toNormalization_normalizationDesc]
    simp [b]

private theorem normalization_chart_open
    {P V E X : Scheme.{u}} [IsReduced V]
    (f : E ⟶ X) (q : P ⟶ E) (φ : P ⟶ X)
    [QuasiCompact φ] [QuasiSeparated φ] (hqf : q ≫ f = φ)
    (j : E ⟶ φ.normalization) (hj : j ≫ φ.fromNormalization = f)
    (hqj : q ≫ j = φ.toNormalization)
    (i : V ⟶ E) (v : P ⟶ V) [IsDominant v] (hvi : v ≫ i = q)
    [QuasiCompact (i ≫ f)] [IsSeparated (i ≫ f)]
    [LocallyOfFiniteType (i ≫ f)] [LocallyQuasiFinite (i ≫ f)] :
    IsOpenImmersion (i ≫ j) := by
  let h := i ≫ f
  have hh : h = (i ≫ j) ≫ φ.fromNormalization := by simp [h, hj]
  have hv : φ = (v ≫ h.toNormalization) ≫ h.fromNormalization := by
    simp [h, ← hvi, ← hqf]
  let a := h.normalizationDesc (i ≫ j) φ.fromNormalization hh
  let b := φ.normalizationDesc (v ≫ h.toNormalization) h.fromNormalization hv
  have ha : a ≫ φ.fromNormalization = h.fromNormalization := h.normalizationDesc_comp ..
  have hb : b ≫ h.fromNormalization = φ.fromNormalization := φ.normalizationDesc_comp ..
  have hva : v ≫ i ≫ j = φ.toNormalization := by rw [← Category.assoc, hvi, hqj]
  have hab : a ≫ b = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext h _ _ h.fromNormalization
    · change h.toNormalization ≫ a ≫ b = h.toNormalization
      rw [← Category.assoc, h.toNormalization_normalizationDesc]
      refine ext_of_isDominant_of_isSeparated h.fromNormalization ?_ v ?_
      · simp [Category.assoc, hb, hj, h]
      · rw [← Category.assoc, ← Category.assoc, hvi, hqj]
        exact φ.toNormalization_normalizationDesc ..
    · simp [Category.assoc, hb, ha]
    · simp
  have hba : b ≫ a = 𝟙 _ := by
    apply Scheme.Hom.normalization.hom_ext φ _ _ φ.fromNormalization
    · change φ.toNormalization ≫ b ≫ a = φ.toNormalization
      rw [← Category.assoc, φ.toNormalization_normalizationDesc,
        Category.assoc, h.toNormalization_normalizationDesc]
      exact hva
    · simp [Category.assoc, ha, hb]
    · simp
  have : IsIso a := ⟨⟨b, hab, hba⟩⟩
  have heq : i ≫ j = h.toNormalization ≫ a := by simp [a]
  rw [heq]
  infer_instance

private theorem injective_of_normalization_charts
    {P E X N : Scheme.{u}} (f : E ⟶ X) [IsSeparated f]
    (q : P ⟶ E) [IsDominant q]
    (n : N ⟶ X) (j : E ⟶ N) (hj : j ≫ n = f)
    (H : ∀ (U : E.Opens) (_ : IsAffineOpen U) (_ : Nonempty U),
      IsOpenImmersion (U.ι ≫ j))
    (hq : ∀ (U : E.Opens) (_ : Nonempty U), Set.range q ⊆ Set.range U.ι)
    [IsIntegral E] : Function.Injective j := by
  intro x y hxy
  let U : E.Opens := (E.affineCover.f (E.affineCover.idx x)).opensRange
  let V : E.Opens := (E.affineCover.f (E.affineCover.idx y)).opensRange
  have hx : x ∈ U := E.affineCover.covers x
  have hy : y ∈ V := E.affineCover.covers y
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : Nonempty V := ⟨⟨y, hy⟩⟩
  have := H U (isAffineOpen_opensRange _) inferInstance
  have := H V (isAffineOpen_opensRange _) inferInstance
  let u := IsOpenImmersion.lift U.ι q (hq U inferInstance)
  let v := IsOpenImmersion.lift V.ι q (hq V inferInstance)
  have hu : u ≫ U.ι = q := IsOpenImmersion.lift_fac ..
  have hv : v ≫ V.ι = q := IsOpenImmersion.lift_fac ..
  have : IsDominant u := by
    have : IsDominant (u ≫ U.ι) := by rw [hu]; infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion u U.ι
  let t : P ⟶ pullback (U.ι ≫ j) (V.ι ≫ j) :=
    pullback.lift u v (by simp [← Category.assoc, hu, hv])
  have ht : t ≫ pullback.fst (U.ι ≫ j) (V.ι ≫ j) = u := by simp [t]
  have : IsDominant t := by
    have : IsDominant (t ≫ pullback.fst (U.ι ≫ j) (V.ι ≫ j)) := by
      rw [ht]
      infer_instance
    exact IsDominant.of_comp_of_isOpenImmersion t
      (pullback.fst (U.ι ≫ j) (V.ι ≫ j))
  have : IsReduced (pullback (U.ι ≫ j) (V.ι ≫ j)) :=
    isReduced_of_isOpenImmersion (pullback.fst (U.ι ≫ j) (V.ι ≫ j))
  have heq : pullback.fst (U.ι ≫ j) (V.ι ≫ j) ≫ U.ι =
      pullback.snd (U.ι ≫ j) (V.ι ≫ j) ≫ V.ι := by
    refine ext_of_isDominant_of_isSeparated f ?_ t ?_
    · rw [← hj]
      simpa only [Category.assoc] using congrArg (· ≫ n)
        (pullback.condition (f := U.ι ≫ j) (g := V.ι ≫ j))
    · simp [t, hu, hv]
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := U.ι ≫ j) (g := V.ι ≫ j) ⟨x, hx⟩ ⟨y, hy⟩ hxy
  have hz := congrArg (fun a : pullback (U.ι ≫ j) (V.ι ≫ j) ⟶ E ↦ a z) heq
  simpa only [Scheme.Hom.comp_apply, hz₁, hz₂, Scheme.Opens.ι_apply] using hz

/-- **An integral étale scheme embeds in its finite generic normalization.** Let `X` be a
normal integral Noetherian scheme with function field `K`, `f : E ⟶ X` separated étale with
`E` normal integral, `L / K` finite separable with `e : E ×_X Spec K ≅ Spec L` over `K`, and
assume `ν : X^L ⟶ X` finite. Then there is an open immersion `j : E ⟶ X^L` with `j ≫ ν = f`
whose generic-fibre map is `e` followed by the canonical map `Spec L ⟶ X^L ×_X Spec K`.

Source: Stacks Project, Tags 05K0, 0AB1 and 01RH
(blueprint: lem-sf-integral-etale-normalization-open).

Proof:
1. The given fibre identification gives a dominant preimmersion `q : Spec L ⟶ E`.
   Dominance follows by flat base change of the schematically dominant generic point of `X`.
   Its one point is the generic point of `E`, and the surjective map on stalks identifies
   `L` with `k(E)` (a homomorphism of fields is injective).
2. Normality of `E` makes `q.fromNormalization` an isomorphism. Apply the universal property
   of relative normalization to the integral pullback of `X^L ⟶ X` along `f`, obtaining
   `j : E ⟶ X^L` with `j ≫ ν = f` and the specified restriction on `Spec L`.
3. On every nonempty affine open `U` of `E`, the map `U ⟶ X` is quasi-compact, separated,
   locally of finite type, and locally quasi-finite. Zariski main makes its canonical map
   into its relative normalization an open immersion.
4. Compare this chart normalization with `X^L` using `normalizationDesc` in both directions.
   The normalization universal property and separated uniqueness along the dominant
   `Spec L ⟶ U` prove that the comparisons are inverse. Thus `U ⟶ X^L` is open.
5. On the pullback of any two such chart maps, the two maps to `E` agree on `Spec L`.
   This pullback is reduced, and the map from `Spec L` is dominant. Separated uniqueness
   over `X` gives equality of the two maps, proving that `j` is injective.
6. The affine cover and injectivity imply that `j` is an open immersion. The required
   generic-fibre equation follows by equality of its two pullback projections.
-/
theorem integral_etale_normalization_open
    {X E : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    (hX : ∀ x : X,
      IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    (f : E ⟶ X) [IsSeparated f] [Etale f] [IsIntegral E]
    (hE : ∀ x : E,
      IsDomain (E.presheaf.stalk x) ∧ IsIntegrallyClosed (E.presheaf.stalk x))
    (L : Type u) [Field L] [Algebra X.functionField L]
    [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L]
    (e : pullback f X.fromSpecFunctionField ≅ Spec (.of L))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) =
      pullback.snd f X.fromSpecFunctionField)
    [IsFinite (X.fromNormalizationIn L)] :
    ∃ (j : E ⟶ X.normalizationIn L) (hj : j ≫ X.fromNormalizationIn L = f),
      IsOpenImmersion j ∧
      (pullback.map f X.fromSpecFunctionField (X.fromNormalizationIn L)
        X.fromSpecFunctionField j (𝟙 _) (𝟙 _) (by simp [hj]) (by simp)) =
        e.hom ≫ pullback.lift
          ((X.fromSpecOfAlgebraFunctionField L).toNormalization)
          (Spec.map (CommRingCat.ofHom (algebraMap X.functionField L))) (by
            rw [Scheme.Hom.toNormalization_fromNormalization]) := by
  classical
  let q := e.inv ≫ pullback.fst f X.fromSpecFunctionField
  let φ := X.fromSpecOfAlgebraFunctionField L
  have hqf : q ≫ f = φ := by
    dsimp [q, φ, Scheme.fromSpecOfAlgebraFunctionField]
    rw [Category.assoc, pullback.condition]
    rw [← he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have (x : X) : IsDomain (X.presheaf.stalk x) := (hX x).1
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IsSchemeTheoreticallyDominant X.fromSpecFunctionField :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsDominant q := by dsimp [q]; infer_instance
  have : IsPreimmersion q := by dsimp [q]; infer_instance
  have : IsIso q.fromNormalization := generic_normalization_isIso (fun x ↦ (hE x).2) q
  obtain ⟨j, hj, hqj⟩ := extend_generic_to_integral q f φ.fromNormalization
    φ.toNormalization (φ.toNormalization_fromNormalization.trans hqf.symm)
  have hqU (U : E.Opens) (hU : Nonempty U) :
      Set.range q ⊆ Set.range U.ι := by
    have : Nonempty U := hU
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, field_dominant_generic q z]
    exact Scheme.genericPoint_mem_of_nonempty U
  have : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian f
  have hcharts (U : E.Opens) (haff : IsAffineOpen U) (hU : Nonempty U) :
      IsOpenImmersion (U.ι ≫ j) := by
    have : Nonempty U := hU
    have : IsNoetherianRing Γ(E, U) := IsLocallyNoetherian.component_noetherian ⟨U, haff⟩
    have : NoetherianSpace U := noetherianSpace_of_isAffineOpen U haff
    let v := IsOpenImmersion.lift U.ι q (hqU U hU)
    have hv : v ≫ U.ι = q := IsOpenImmersion.lift_fac ..
    have : IsDominant v := by
      have : IsDominant (v ≫ U.ι) := by rw [hv]; infer_instance
      exact IsDominant.of_comp_of_isOpenImmersion v U.ι
    exact normalization_chart_open f q φ hqf j hj hqj U.ι v hv
  refine ⟨j, hj, ?_, ?_⟩
  · apply IsOpenImmersion.of_forall_source_exists j
      (injective_of_normalization_charts f q φ.fromNormalization j hj hcharts hqU)
    intro x
    let U : E.Opens := (E.affineCover.f (E.affineCover.idx x)).opensRange
    have hx : x ∈ U := E.affineCover.covers x
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    exact ⟨U.toScheme, U.ι, inferInstance, by simpa using hx,
      hcharts U (isAffineOpen_opensRange _) inferInstance⟩
  · apply pullback.hom_ext
    · simp only [pullback.map, pullback.lift_fst, Category.assoc,
        Category.comp_id]
      rw [← cancel_epi e.inv]
      simpa [q] using hqj
    · simp [pullback.map, he]

end AlgebraicGeometry
