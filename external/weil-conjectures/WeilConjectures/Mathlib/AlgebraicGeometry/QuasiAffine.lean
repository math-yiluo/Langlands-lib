/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Quasi-affine morphisms and quasi-affineness from Zariski's Main Theorem

A morphism of schemes is quasi-affine if the preimage of every affine open of the target is a
quasi-affine scheme. This is the relative form of `AlgebraicGeometry.Scheme.IsQuasiAffine`, and
it sits beside `AlgebraicGeometry.IsAffineHom` exactly as the absolute notion sits beside
`AlgebraicGeometry.IsAffine`.

We also record the two consequences of Zariski's Main Theorem that the Nagata compactification
argument uses. Zariski's Main Theorem says that a separated, quasi-compact, locally quasi-finite
morphism of finite type `f : X ⟶ Y` factors as an open immersion into the relative normalization
of `Y` in `X` followed by an integral (in particular affine) morphism.

## Main results

* `AlgebraicGeometry.IsQuasiAffineHom`: the class of quasi-affine morphisms.
* `AlgebraicGeometry.Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite`:
  a separated, quasi-compact, locally quasi-finite morphism of finite type factors as an open
  immersion followed by an affine morphism.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_locallyQuasiFinite`:
  the source of such an `f` is quasi-affine as soon as the target is.
* `AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite`:
  such an `f` is quasi-affine as a morphism, with no hypothesis on `Y`.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom`: over an affine base, the relative
  notion recovers the absolute one.
* `AlgebraicGeometry.IsQuasiAffineHom.of_isPullback`: quasi-affine morphisms are stable under
  base change.

None of the three Zariski's Main Theorem statements is an instance: the hypothesis list is long
and `LocallyQuasiFinite` is not something typeclass inference should be asked to discharge.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Quasi-affineness only depends on the isomorphism class of a scheme. -/
lemma Scheme.IsQuasiAffine.of_isIso (e : X ⟶ Y) [IsIso e] [Y.IsQuasiAffine] : X.IsQuasiAffine :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace e
  .of_isImmersion e

/-- **Zariski's Main Theorem**, in factorization form: a separated, quasi-compact, locally
quasi-finite morphism of finite type factors as an open immersion followed by an affine
morphism. The factorization is through the relative normalization `f.normalization`. -/
theorem Scheme.Hom.exists_isOpenImmersion_isAffineHom_of_locallyQuasiFinite
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ (W : Scheme.{u}) (j : X ⟶ W) (g : W ⟶ Y), IsOpenImmersion j ∧ IsAffineHom g ∧ j ≫ g = f :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization, inferInstance, inferInstance,
    f.toNormalization_fromNormalization⟩


/-- If `f : X ⟶ Y` is separated, quasi-compact and locally quasi-finite of finite type and `Y` is
quasi-affine, then `X` is quasi-affine. Indeed, by Zariski's Main Theorem `f` factors as an open
immersion `X ⟶ f.normalization` followed by an affine morphism onto `Y`, so `f.normalization` is
quasi-affine, and `X` is a quasi-compact locally closed subscheme of it. -/
theorem Scheme.IsQuasiAffine.of_locallyQuasiFinite [Y.IsQuasiAffine]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    X.IsQuasiAffine :=
  have : f.normalization.IsQuasiAffine := .of_isAffineHom f.fromNormalization
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  .of_isImmersion f.toNormalization

/-- A morphism of schemes is quasi-affine if the preimage of every affine open of the target is a
quasi-affine scheme. -/
@[mk_iff]
class IsQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- The preimage of an affine open of the target is a quasi-affine scheme. -/
  isQuasiAffine_preimage (U : Y.Opens) (hU : IsAffineOpen U) : (f ⁻¹ᵁ U).toScheme.IsQuasiAffine

lemma IsAffineOpen.isQuasiAffine_preimage {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsQuasiAffineHom f] : (f ⁻¹ᵁ U).toScheme.IsQuasiAffine :=
  IsQuasiAffineHom.isQuasiAffine_preimage _ hU

instance (priority := 900) [IsAffineHom f] : IsQuasiAffineHom f where
  isQuasiAffine_preimage U hU :=
    have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
    inferInstance

/-- A quasi-compact morphism out of a quasi-affine scheme is quasi-affine: the preimage of an
affine open is a quasi-compact open subscheme of a quasi-affine scheme. -/
instance (priority := 900) [X.IsQuasiAffine] [QuasiCompact f] : IsQuasiAffineHom f where
  isQuasiAffine_preimage U hU :=
    have : CompactSpace (f ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
    .of_isImmersion (f ⁻¹ᵁ U).ι

/-- If `f : X ⟶ Y` is separated, quasi-compact and locally quasi-finite of finite type, then it is
quasi-affine as a morphism. This is Zariski's Main Theorem applied over each affine open of `Y`;
note that no hypothesis on `Y` is needed. -/
theorem IsQuasiAffineHom.of_locallyQuasiFinite
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsQuasiAffineHom f where
  isQuasiAffine_preimage U hU :=
    have : IsAffine U.toScheme := hU
    .of_locallyQuasiFinite (f ∣_ U)

/-- Precomposing a quasi-affine morphism with an immersion again gives a quasi-affine morphism,
provided the composite is quasi-compact. -/
instance {Z : Scheme.{u}} (g : Z ⟶ X) [IsImmersion g] [IsQuasiAffineHom f]
    [QuasiCompact (g ≫ f)] : IsQuasiAffineHom (g ≫ f) where
  isQuasiAffine_preimage U hU := by
    have hcpt : CompactSpace ((g ≫ f) ⁻¹ᵁ U).toScheme :=
      isCompact_iff_compactSpace.mp ((g ≫ f).isCompact_preimage hU.isCompact)
    have he : (g ≫ f) ⁻¹ᵁ U = g ⁻¹ᵁ (f ⁻¹ᵁ U) := by
      rw [Scheme.Hom.comp_base, Opens.map_comp_obj]
    rw [he] at hcpt ⊢
    have := hU.isQuasiAffine_preimage f
    exact .of_isImmersion (g ∣_ (f ⁻¹ᵁ U))

/-- Quasi-affine morphisms are stable under restricting the base to an open subscheme. -/
instance (V : Y.Opens) [IsQuasiAffineHom f] : IsQuasiAffineHom (f ∣_ V) where
  isQuasiAffine_preimage W hW :=
    have : (f ⁻¹ᵁ (V.ι ''ᵁ W)).toScheme.IsQuasiAffine :=
      (hW.image_of_isOpenImmersion V.ι).isQuasiAffine_preimage f
    .of_isIso ((f ⁻¹ᵁ V).ι.isoImage ((f ∣_ V) ⁻¹ᵁ W) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage f V W)).hom

/-- Over an affine base, a quasi-affine morphism has quasi-affine source: the relative notion
recovers the absolute one. -/
lemma Scheme.IsQuasiAffine.of_isQuasiAffineHom [IsQuasiAffineHom f] [IsAffine Y] :
    X.IsQuasiAffine :=
  have : (⊤ : X.Opens).toScheme.IsQuasiAffine := (isAffineOpen_top Y).isQuasiAffine_preimage f
  .of_isIso X.topIso.inv


/-- A qcqs scheme covered by quasi-affine basic opens of global sections is quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), (X.basicOpen r).toScheme.IsQuasiAffine ∧ x ∈ X.basicOpen r) :
    X.IsQuasiAffine := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  obtain ⟨r, hr, hxr⟩ := H x
  refine ⟨PrimeSpectrum.basicOpen r, (X.toSpecΓ_preimage_basicOpen r).ge hxr, ?_⟩
  suffices IsOpenImmersion ((X.basicOpen r).ι ≫ X.toSpecΓ) by
    convert! this <;> rw [Scheme.toSpecΓ_preimage_basicOpen]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  have := isLocalization_basicOpen_of_qcqs (X := X) isCompact_univ isQuasiSeparated_univ r
  have : IsOpenImmersion (X.basicOpen r).toSpecΓ := by
    delta Scheme.Opens.toSpecΓ
    infer_instance
  exact MorphismProperty.comp_mem _ _ _ inferInstance (.of_isLocalization r)

/-- The fibre product of a quasi-affine scheme and an affine scheme over an affine scheme is
quasi-affine. -/
lemma Scheme.IsQuasiAffine.pullback_of_isAffine {A B C : Scheme.{u}}
    [A.IsQuasiAffine] [IsAffine B] [IsAffine C] (α : A ⟶ B) (β : C ⟶ B) :
    (pullback α β).IsQuasiAffine := by
  -- `α` factors through the affine hull of `A`, by an affine morphism
  obtain ⟨γ, hγ, rfl⟩ : ∃ γ : Spec Γ(A, ⊤) ⟶ B, IsAffineHom γ ∧ A.toSpecΓ ≫ γ = α :=
    ⟨Spec.map α.appTop ≫ (Scheme.isoSpec B).inv, inferInstance, by
      rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
        show B.toSpecΓ = (Scheme.isoSpec B).hom from rfl, Iso.hom_inv_id, Category.comp_id]⟩
  have : IsAffine (pullback γ β) := isAffine_of_isAffineHom (pullback.snd γ β)
  have : QuasiCompact (A.toSpecΓ ≫ γ) := quasiCompact_of_compactSpace _
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd (A.toSpecΓ ≫ γ) β)
  have : IsOpenImmersion (pullback.map (A.toSpecΓ ≫ γ) β γ β A.toSpecΓ (𝟙 C) (𝟙 B)
      (by simp) (by simp)) :=
    MorphismProperty.of_isPullback (isPullback_pullback_map_left A.toSpecΓ γ β) inferInstance
  exact .of_isImmersion (pullback.map (A.toSpecΓ ≫ γ) β γ β A.toSpecΓ (𝟙 C) (𝟙 B)
    (by simp) (by simp))

/-- The base change of a quasi-affine morphism along a morphism from an affine scheme has
quasi-affine source. -/
theorem Scheme.IsQuasiAffine.of_isPullback_of_isAffine {S Y W T : Scheme.{u}} {p : Y ⟶ S}
    [IsQuasiAffineHom p] [QuasiCompact p] [QuasiSeparated p] [IsAffine W]
    {h : W ⟶ S} {u : T ⟶ Y} {q : T ⟶ W} (H : IsPullback u q p h) : T.IsQuasiAffine := by
  have : QuasiCompact q := MorphismProperty.of_isPullback H ‹QuasiCompact p›
  have : QuasiSeparated q := MorphismProperty.of_isPullback H ‹QuasiSeparated p›
  have := QuasiCompact.compactSpace_of_compactSpace q
  have := quasiSeparatedSpace_of_quasiSeparated q
  refine .of_forall_exists_isQuasiAffine_basicOpen _ fun t ↦ ?_
  -- an affine open `V` of `S` around the image of `t`
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := p (u t)) (U := ⊤) trivial
  -- a basic open `O` of the affine `W` around the image of `t`, inside `h ⁻¹ V`
  have hb : h.base (q.base t) = p.base (u.base t) := by
    have hw : (q ≫ h).base t = (u ≫ p).base t := by rw [H.w]
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] using hw
  have htV : q t ∈ h ⁻¹ᵁ V := by
    change h.base (q.base t) ∈ V
    rw [hb]
    exact hxV
  obtain ⟨_, ⟨r₀, rfl⟩, htr, hrV⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_basicOpen W) htV
  refine ⟨q.appTop r₀, ?_, by rwa [← Scheme.preimage_basicOpen_top]⟩
  rw [← Scheme.preimage_basicOpen_top]
  -- the preimage of `O` in `T` is the fibre product of `p ⁻¹ V` and `O` over `V`
  have : IsAffine (W.basicOpen r₀).toScheme := (isAffineOpen_top W).basicOpen r₀
  have : IsAffine V.toScheme := hV
  have : (p ⁻¹ᵁ V).toScheme.IsQuasiAffine := hV.isQuasiAffine_preimage p
  set O : W.Opens := W.basicOpen r₀ with hO
  set k : O.toScheme ⟶ V.toScheme := W.homOfLE hrV ≫ (h ∣_ V) with hk
  have hkV : k ≫ V.ι = O.ι ≫ h := by
    rw [hk, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hbig : IsPullback (q ∣_ O) ((q ⁻¹ᵁ O).ι ≫ u) (O.ι ≫ h) p :=
    (isPullback_morphismRestrict q O).paste_vert H.flip
  have hmr := isPullback_morphismRestrict p V
  have hw : (q ∣_ O ≫ k) ≫ V.ι = ((q ⁻¹ᵁ O).ι ≫ u) ≫ p := by
    rw [Category.assoc, hkV, ← Category.assoc, morphismRestrict_ι, Category.assoc,
      Category.assoc, H.w]
  set a : (q ⁻¹ᵁ O).toScheme ⟶ (p ⁻¹ᵁ V).toScheme := hmr.lift (q ∣_ O ≫ k) ((q ⁻¹ᵁ O).ι ≫ u) hw
    with ha
  have hsq : IsPullback (q ∣_ O) a k (p ∣_ V) := by
    refine IsPullback.of_bot ?_ ?_ hmr
    · rw [ha, hmr.lift_snd, hkV]
      exact hbig
    · rw [ha, hmr.lift_fst]
  have : (pullback (p ∣_ V) k).IsQuasiAffine :=
    Scheme.IsQuasiAffine.pullback_of_isAffine (p ∣_ V) k
  exact .of_isIso hsq.flip.isoPullback.hom


/-- Quasi-affine morphisms are stable under base change. -/
theorem IsQuasiAffineHom.of_isPullback {S Y Z T : Scheme.{u}} {p : Y ⟶ S} {g : Z ⟶ S}
    [IsQuasiAffineHom p] [QuasiCompact p] [QuasiSeparated p]
    {u : T ⟶ Y} {q : T ⟶ Z} (H : IsPullback u q p g) : IsQuasiAffineHom q where
  isQuasiAffine_preimage W hW := by
    have : IsAffine W.toScheme := hW
    exact Scheme.IsQuasiAffine.of_isPullback_of_isAffine
      ((isPullback_morphismRestrict q W).paste_vert H.flip).flip

instance {S Y Z : Scheme.{u}} (p : Y ⟶ S) (g : Z ⟶ S)
    [IsQuasiAffineHom p] [QuasiCompact p] [QuasiSeparated p] :
    IsQuasiAffineHom (pullback.snd p g) :=
  .of_isPullback (IsPullback.of_hasPullback p g)


end AlgebraicGeometry
