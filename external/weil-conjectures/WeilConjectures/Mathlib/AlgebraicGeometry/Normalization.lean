/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Complements on the relative normalization

For a quasi-compact open immersion `f : X ⟶ Y`, the relative normalization `f.normalization`
of `Y` in `X` contains `X` as an open subscheme: the morphism `f.toNormalization` is an open
immersion. If `X` is integral with integrally closed local rings, then so is `f.normalization`,
and if `Y` is locally of finite type over a field then `f.fromNormalization` is finite.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isOpenImmersion_toNormalization`: for a quasi-compact open
  immersion `f`, the morphism `f.toNormalization` is an open immersion.
- `AlgebraicGeometry.Scheme.Hom.isIntegrallyClosed_stalk_normalization`: the normalization of
  `Y` in an integral scheme with integrally closed local rings has integrally closed local
  rings.
- `AlgebraicGeometry.Scheme.Hom.isFinite_fromNormalization`: the normalization of a scheme
  locally of finite type over a field in a quasi-compact integral open subscheme is finite.
- `AlgebraicGeometry.Scheme.normalizationIn`: the normalization of an integral scheme in a field
  extension of its function field, and `AlgebraicGeometry.Scheme.isFinite_fromNormalizationIn`:
  it is finite over a scheme locally of finite type over a field if the extension is finite.
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

section OpenImmersion

variable [IsOpenImmersion f] [QuasiCompact f]

/-- For a quasi-compact open immersion `f : X ⟶ Y`, the morphism `X ⟶ f.normalization` is an
open immersion: normalization commutes with the smooth base change `f` itself, and the
normalization of the isomorphism `X ×_Y X ⟶ X` is trivial. -/
instance isOpenImmersion_toNormalization : IsOpenImmersion f.toNormalization := by
  have h := f.toNormalization_normalizationPullback_fst f
  have : f.toNormalization = inv (pullback.fst f f) ≫ (pullback.snd f f).toNormalization ≫
      f.normalizationPullback f ≫ pullback.fst _ _ := by
    rw [h, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

end OpenImmersion

/-- The relative normalization of `Y` in an integral scheme `X` with integrally closed local
rings has integrally closed local rings. Over an affine open `V` of `Y` it is the spectrum of
the integral closure of `Γ(Y, V)` in the integrally closed domain `Γ(X, f⁻¹ V)`, which is
again an integrally closed domain. (blueprint: `lem-weil-pbc-normalization-normal-stalks`) -/
theorem isIntegrallyClosed_stalk_normalization [QuasiCompact f] [QuasiSeparated f]
    [IsIntegral X] (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (y : f.normalization) : IsIntegrallyClosed (f.normalization.presheaf.stalk y) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.fromNormalization y)) isOpen_univ
  let := (f.app U).hom.toAlgebra
  have hV : IsAffineOpen (f.fromNormalization ⁻¹ᵁ U) := hU.preimage f.fromNormalization
  have : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨y, hyU⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := by
    by_contra h
    have : Subsingleton Γ(X, f ⁻¹ᵁ U) := CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp
        fun ⟨x, hx⟩ ↦ h ⟨⟨x, hx⟩⟩))
    exact not_subsingleton Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)
      (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.subsingleton
  have := isIntegrallyClosed_of_isIntegrallyClosed_stalk hX (f ⁻¹ᵁ U)
  have : IsIntegrallyClosed (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
    .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ Γ(X, f ⁻¹ᵁ U)
  have : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    .of_equiv (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm
  let := TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf
    (⟨y, hyU⟩ : f.fromNormalization ⁻¹ᵁ U)
  have := hV.isLocalization_stalk ⟨y, hyU⟩
  exact isIntegrallyClosed_of_isLocalization _ _
    (hV.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- The relative normalization `f.fromNormalization` is finite as soon as, over every nonempty
affine open `U` of `Y`, the integral closure of `Γ(Y, U)` in `Γ(X, f⁻¹ U)` is a finite
`Γ(Y, U)`-module. -/
theorem isFinite_fromNormalization_of_finite [QuasiCompact f] [QuasiSeparated f]
    (H : ∀ U : Y.Opens, IsAffineOpen U → (U : Set Y).Nonempty →
      let := (f.app U).hom.toAlgebra
      Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U))) :
    IsFinite f.fromNormalization := by
  rw [isFinite_iff]
  refine ⟨inferInstance, fun U hU ↦ ?_⟩
  rw [f.fromNormalization_app hU, CommRingCat.hom_comp]
  let := (f.app U).hom.toAlgebra
  refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
    (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.symm.surjective) ?_
  by_cases hne : (U : Set Y).Nonempty
  · exact H U hU hne
  · have : Subsingleton Γ(Y, U) := CommRingCat.subsingleton_of_isTerminal
      (Y.sheaf.isTerminalOfEqEmpty (by simpa [Set.not_nonempty_iff_eq_empty] using hne))
    have : Subsingleton (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := Module.subsingleton Γ(Y, U) _
    exact RingHom.finite_algebraMap.mpr inferInstance

/-- The normalization of a scheme `Y` locally of finite type over a field `K` in a
quasi-compact integral open subscheme `X` is finite over `Y`.

Over an affine open `Spec A` of `Y` meeting `X`, the ring of the normalization is the integral
closure of `A` in `Γ(X ∩ Spec A)`, which lies in the integral closure of the finitely generated
`K`-domain `A ⧸ 𝔭` in its fraction field, `𝔭` the generic point of the closure of `X`; the
latter is a finite `A`-module by E. Noether's finiteness theorem. -/
theorem isFinite_fromNormalization {K : Type u} [Field K] [IsOpenImmersion f] [QuasiCompact f]
    [IsIntegral X] (q : Y ⟶ Spec (.of K)) [LocallyOfFiniteType q] :
    IsFinite f.fromNormalization := by
  refine f.isFinite_fromNormalization_of_finite fun U hU _ ↦ ?_
  let := (f.app U).hom.toAlgebra
  let := ((q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).toAlgebra
  have : Algebra.FiniteType K Γ(Y, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.FiniteType.isNoetherianRing K Γ(Y, U)
  by_cases hV : (f ⁻¹ᵁ U : Set X).Nonempty
  swap
  · have : Subsingleton Γ(X, f ⁻¹ᵁ U) := CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hV))
    infer_instance
  have : Nonempty (f ⁻¹ᵁ U) := hV.to_subtype
  have hη : genericPoint X ∈ f ⁻¹ᵁ U :=
    ((genericPoint_spec X).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr (by simpa using hV)
  let : Algebra Γ(Y, U) X.functionField :=
    (f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U)).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) Γ(X, f ⁻¹ᵁ U) X.functionField := .of_algebraMap_eq' rfl
  have halg (a : Γ(Y, U)) : algebraMap Γ(Y, U) X.functionField a =
      f.stalkMap (genericPoint X) (Y.presheaf.germ U _ hη a) := by
    rw [Scheme.Hom.germ_stalkMap_apply]; rfl
  have hdiv (z : X.functionField) :
      ∃ a b, z = algebraMap Γ(Y, U) _ a / algebraMap Γ(Y, U) _ b := by
    let := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨_, hη⟩ : U)
    have := hU.isLocalization_stalk ⟨_, hη⟩
    obtain ⟨⟨a, s⟩, hw⟩ := IsLocalization.surj (hU.primeIdealOf ⟨_, hη⟩).asIdeal.primeCompl
      (inv (f.stalkMap (genericPoint X)) z)
    have hs := IsLocalization.map_units (Y.presheaf.stalk (f (genericPoint X))) s
    refine ⟨a, s, eq_div_of_mul_eq ?_ ?_⟩
    · rw [halg]
      exact ((hs.map (f.stalkMap (genericPoint X)).hom)).ne_zero
    · have := congr(f.stalkMap (genericPoint X) $hw)
      rw [map_mul, ← CommRingCat.comp_apply, IsIso.inv_hom_id, CommRingCat.id_apply] at this
      rw [halg, halg]
      exact this
  have := Algebra.FiniteType.finite_integralClosure_of_forall_eq_div K hdiv
  let e : Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, U)] X.functionField :=
    { (X.germToFunctionField (f ⁻¹ᵁ U)).hom with commutes' _ := rfl }
  let ψ : integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) →ₗ[Γ(Y, U)]
      integralClosure Γ(Y, U) X.functionField :=
    { toFun x := ⟨e x, x.2.map e⟩
      map_add' x y := Subtype.ext (map_add e x.1 y.1)
      map_smul' a x := Subtype.ext (map_smul e a x.1) }
  refine Module.Finite.of_injective ψ fun x y h ↦ ?_
  exact Subtype.ext (X.germToFunctionField_injective (f ⁻¹ᵁ U) congr($h.1))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The *normalization* `X^ν` of an integral scheme `X` in its function field `K = k(X)`: the
relative normalization `Spec_X(𝒪̃_X)` of `X` in the generic point `Spec K ⟶ X`, where `𝒪̃_X` is
the integral closure of `𝒪_X` in the constant sheaf `K`. Finiteness of `X^ν ⟶ X` is a separate
property, `AlgebraicGeometry.Scheme.isFinite_fromNormalization_of_locallyOfFiniteType`.
(blueprint: `lemma-proper-smooth-model--1`) -/
noncomputable abbrev normalization : Scheme.{u} :=
  X.fromSpecFunctionField.normalization

/-- The canonical morphism `ν : X^ν ⟶ X` from the normalization of an integral scheme `X` in its
function field. (blueprint: `lemma-proper-smooth-model--1`) -/
noncomputable abbrev fromNormalization : X.normalization ⟶ X :=
  X.fromSpecFunctionField.fromNormalization

instance isDominant_fromNormalization : IsDominant X.fromNormalization :=
  have : IsDominant (X.fromSpecFunctionField.toNormalization ≫ X.fromNormalization) := by
    rw [Hom.toNormalization_fromNormalization]; infer_instance
  .of_comp X.fromSpecFunctionField.toNormalization _

/-- The normalization `ν : X^ν ⟶ X` of an integral scheme in its function field is surjective:
it is integral, hence closed, and dominant. (blueprint: `lemma-proper-smooth-model--1`) -/
instance surjective_fromNormalization : Surjective X.fromNormalization :=
  have : UniversallyClosed X.fromNormalization :=
    (IsIntegralHom.iff_universallyClosed_and_isAffineHom.mp inferInstance).1
  inferInstance

/-- Over a nonempty affine open `V` of an integral scheme `X` with `Γ(X, V)` integrally closed,
the normalization `ν : X^ν ⟶ X` in the function field induces an isomorphism on sections:
`Γ(X^ν, ν⁻¹ V)` is the integral closure of `Γ(X, V)` in its fraction field `k(X)`. -/
theorem isIso_fromNormalization_app {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V]
    [IsIntegrallyClosed Γ(X, V)] : IsIso (X.fromNormalization.app V) := by
  let f := X.fromSpecFunctionField
  let := (f.app V).hom.toAlgebra
  have hx : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  -- `Γ(Spec k(X), f⁻¹ V)` is the fraction field of `Γ(X, V)`
  have htop : f ⁻¹ᵁ V = ⊤ := by
    refine top_unique fun p _ ↦ ?_
    have : f p ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨p, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact (show f p ⤳ genericPoint X from this).mem_open V.isOpen hx
  let e : X.functionField ≃+* Γ(Spec X.functionField, f ⁻¹ᵁ V) :=
    ((ΓSpecIso X.functionField).symm ≪≫ (Spec X.functionField).presheaf.mapIso
      (eqToIso htop).op).commRingCatIsoToRingEquiv
  have he (a : Γ(X, V)) : e (X.germToFunctionField V a) = algebraMap Γ(X, V) _ a := by
    change _ = (f.app V) a
    rw [Scheme.fromSpecStalk_app hx, Subsingleton.elim (homOfLE le_top) (eqToHom htop)]
    rfl
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have : IsFractionRing Γ(X, V) Γ(Spec X.functionField, f ⁻¹ᵁ V) :=
    IsLocalization.isLocalization_of_algEquiv _
      { e with commutes' := he }
  rw [Hom.fromNormalization_app f hV]
  have hbij : Function.Bijective
      (algebraMap Γ(X, V) (integralClosure Γ(X, V) Γ(Spec X.functionField, f ⁻¹ᵁ V))) := by
    refine ⟨fun a b h ↦ IsFractionRing.injective Γ(X, V) Γ(Spec X.functionField, f ⁻¹ᵁ V)
      (congrArg Subtype.val h), fun x ↦ ?_⟩
    have hx : x.1 ∈ (⊥ : Subalgebra Γ(X, V) _) := by
      rw [← IsIntegrallyClosed.integralClosure_eq_bot_iff
        (K := Γ(Spec X.functionField, f ⁻¹ᵁ V)) |>.mpr inferInstance]
      exact x.2
    obtain ⟨a, ha⟩ := Algebra.mem_bot.mp hx
    exact ⟨a, Subtype.ext ha⟩
  have : IsIso (CommRingCat.ofHom (algebraMap Γ(X, V)
      (integralClosure Γ(X, V) Γ(Spec X.functionField, f ⁻¹ᵁ V)))) :=
    (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
  infer_instance

/-- **The normalization over the normal locus.** For every open `U` of an integral scheme `X`
whose local rings are integrally closed, the normalization `ν : X^ν ⟶ X` restricts to an
isomorphism `ν⁻¹ U ⟶ U`: over an affine open `Spec A ⊆ U` the ring `A` is an integrally closed
domain, hence equal to its integral closure in `k(X)`.
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem isIso_fromNormalization_restrict (U : X.Opens)
    (hU : ∀ x ∈ U, IsIntegrallyClosed (X.presheaf.stalk x)) :
    IsIso (X.fromNormalization ∣_ U) := by
  -- the case of a nonempty affine open
  have key (V : X.affineOpens) (hVU : (V : X.Opens) ≤ U) (hne : (V : Set X).Nonempty) :
      IsIso (X.fromNormalization ∣_ V) := by
    have : Nonempty V.1 := hne.to_subtype
    have hV' : IsAffineOpen (V.1.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]; exact V.2
    have : Nonempty (V.1.ι ''ᵁ ⊤) := by rw [Scheme.Opens.ι_image_top]; infer_instance
    have : IsIntegrallyClosed Γ(X, V.1.ι ''ᵁ ⊤) := by
      rw [Scheme.Opens.ι_image_top]
      exact isIntegrallyClosed_of_isIntegrallyClosed_stalk_of_mem V fun x hx ↦ hU x (hVU hx)
    have := X.isIso_fromNormalization_app hV'
    have : IsAffine V.1 := V.2
    rw [← MorphismProperty.isomorphisms.iff,
      HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)]
    refine ⟨V.2.preimage X.fromNormalization, ?_⟩
    rw [morphismRestrict_appTop]
    infer_instance
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme)
    (fun V : {V : X.affineOpens // (V : X.Opens) ≤ U ∧ (V : Set X).Nonempty} ↦ U.ι ⁻¹ᵁ V.1.1) ?_]
  · rintro ⟨V, hVU, hne⟩
    refine (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (morphismRestrictRestrict _ _ _)).mpr ?_
    have : U.ι ''ᵁ U.ι ⁻¹ᵁ V.1 = V.1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr hVU]
    rw [this]
    exact key V hVU hne
  · refine top_unique fun x _ ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU, ⟨x.1, hxV⟩⟩, by simpa using hxV⟩

section FiniteExtension

variable (L : Type u) [Field L] [Algebra X.functionField L]

/-- The morphism `Spec L ⟶ X` through the generic point of an integral scheme `X`, for a field
extension `L` of its function field `K = k(X)`: the composite of `Spec L ⟶ Spec K` with
`Spec K ⟶ X`. -/
noncomputable abbrev fromSpecOfAlgebraFunctionField : Spec (.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫ X.fromSpecFunctionField

/-- The *normalization* `X^L` of an integral scheme `X` in a field extension `L` of its function
field `K`: the relative normalization of `X` in `Spec L ⟶ X`, that is the relative spectrum of
the integral closure of `𝒪_X` in `L`. Over an affine open `Spec B` of `X` it is
`Spec B'` with `B'` the integral closure of `B` in `L`. For `L = K` this is
`AlgebraicGeometry.Scheme.normalization`. Finiteness of `X^L ⟶ X` is not part of the
definition; it is `AlgebraicGeometry.Scheme.isFinite_fromNormalizationIn`.
(blueprint: `def-fin-normalization-extension`) -/
noncomputable abbrev normalizationIn : Scheme.{u} :=
  (X.fromSpecOfAlgebraFunctionField L).normalization

/-- The canonical morphism `X^L ⟶ X` from the normalization of an integral scheme `X` in a field
extension `L` of its function field. (blueprint: `def-fin-normalization-extension`) -/
noncomputable abbrev fromNormalizationIn : X.normalizationIn L ⟶ X :=
  (X.fromSpecOfAlgebraFunctionField L).fromNormalization

/-- **Finiteness of the normalization in a finite extension.** Let `X` be an integral scheme
locally of finite type over a field `k` and `L` a finite extension of its function field `K`.
Then the normalization `X^L ⟶ X` of `X` in `L` is finite: over an affine open `Spec B`, the
integral closure of the finitely generated `k`-domain `B` in `L` is a finite `B`-module
(E. Noether's finiteness theorem, Stacks `0359`; `L / K` need not be separable).
(blueprint: `lem-fin-normalization-extension-finite`) -/
theorem isFinite_fromNormalizationIn {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] [FiniteDimensional X.functionField L] :
    IsFinite (X.fromNormalizationIn L) := by
  set φ := X.fromSpecOfAlgebraFunctionField L
  refine φ.isFinite_fromNormalization_of_finite fun U hU hne ↦ ?_
  let := (φ.app U).hom.toAlgebra
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hxU : φ (closedPoint L) ∈ U := by
    rw [Hom.comp_apply, Spec_closedPoint]
    convert hηU
    exact fromSpecStalk_closedPoint
  have hφU : φ ⁻¹ᵁ U = ⊤ := preimage_eq_top_of_closedPoint_mem φ hxU
  let θ : Γ(Spec (.of L), φ ⁻¹ᵁ U) ≅ .of L :=
    (Spec (.of L)).presheaf.mapIso (eqToIso hφU.symm).op ≪≫ ΓSpecIso (.of L)
  have hθφ : φ.app U ≫ θ.hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
    have h1 := germ_stalkClosedPointTo φ U hxU
    have h2 := germ_stalkClosedPointTo_Spec_fromSpecStalk
      (CommRingCat.ofHom (algebraMap X.functionField L)) U hxU
    exact h1.symm.trans h2
  let : Algebra Γ(X, U) L := (φ.app U ≫ θ.hom).hom.toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq' <| by
    change (φ.app U ≫ θ.hom).hom = _
    rw [hθφ]
    rfl
  let := ((q.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have := Algebra.FiniteType.finite_integralClosure k (A := Γ(X, U)) X.functionField L
  let e : Γ(Spec (.of L), φ ⁻¹ᵁ U) →ₐ[Γ(X, U)] L :=
    { θ.hom.hom with commutes' _ := rfl }
  let ψ : integralClosure Γ(X, U) Γ(Spec (.of L), φ ⁻¹ᵁ U) →ₗ[Γ(X, U)]
      integralClosure Γ(X, U) L :=
    { toFun x := ⟨e x, x.2.map e⟩
      map_add' x y := Subtype.ext (map_add e x.1 y.1)
      map_smul' a x := Subtype.ext (map_smul e a x.1) }
  have := Algebra.FiniteType.isNoetherianRing k Γ(X, U)
  refine Module.Finite.of_injective ψ fun x y h ↦ ?_
  exact Subtype.ext ((ConcreteCategory.bijective_of_isIso θ.hom).1 congr($h.1))

/-- **The function field of the normalization in `L` is `L`.** For an integral scheme `X` and
an algebraic extension `L` of its function field, the morphism `Spec L ⟶ X^L` is the generic
point of the normalization `X^L` of `X` in `L`, and it identifies `L` with the function field of
`X^L`: over an affine open `Spec B` of `X`, every element of `L` is a quotient of an element of
the integral closure `B'` of `B` in `L` by a nonzero element of `B`, so `Frac(B') = L`. -/
theorem exists_iso_toNormalization_normalizationIn
    [Algebra.IsAlgebraic X.functionField L] :
    ∃ e : Spec (.of L) ≅ Spec (X.normalizationIn L).functionField,
      e.hom ≫ (X.normalizationIn L).fromSpecFunctionField =
        (X.fromSpecOfAlgebraFunctionField L).toNormalization := by
  set φ := X.fromSpecOfAlgebraFunctionField L
  set Y := X.normalizationIn L
  set g := φ.toNormalization
  set pt := closedPoint L
  -- `g` maps the point of `Spec L` to the generic point of `Y`
  have hq : g pt = genericPoint Y := by
    have hd : DenseRange g := g.denseRange
    have : closure ({g pt} : Set Y) = Set.univ := by
      rw [← hd.closure_range]
      congr 1
      ext y
      exact ⟨fun h ↦ ⟨pt, h.symm⟩, fun ⟨x, hx⟩ ↦ by rw [← hx, Subsingleton.elim x pt]; rfl⟩
    exact (show IsGenericPoint (g pt) ⊤ from this).eq (genericPoint_spec Y)
  -- the stalk of `Y` at `g pt` is a field
  have hfield : IsField (Y.presheaf.stalk (g pt)) := by
    rw [hq]; exact Field.toIsField Y.functionField
  set ψ := stalkClosedPointTo g
  -- an affine open of `X` containing the image of the point
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (φ pt)) isOpen_univ
  have hU' : g pt ∈ φ.fromNormalization ⁻¹ᵁ U := by
    change (g ≫ φ.fromNormalization) pt ∈ U
    rwa [Hom.toNormalization_fromNormalization]
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).specializes (Set.mem_univ (φ pt))).mem_open U.isOpen hxU
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  -- the identification `θ : Γ(Spec L, φ⁻¹ U) ≅ L`
  have hφU : φ ⁻¹ᵁ U = ⊤ := preimage_eq_top_of_closedPoint_mem φ hxU
  let θ : Γ(Spec (.of L), φ ⁻¹ᵁ U) ≅ .of L :=
    (Spec (.of L)).presheaf.mapIso (eqToIso hφU.symm).op ≪≫ ΓSpecIso (.of L)
  -- `θ ∘ φ^*` is the inclusion `Γ(X, U) → k(X) → L`
  have hθφ : φ.app U ≫ θ.hom =
      X.germToFunctionField U ≫ CommRingCat.ofHom (algebraMap X.functionField L) := by
    have h1 := germ_stalkClosedPointTo φ U hxU
    have h2 := germ_stalkClosedPointTo_Spec_fromSpecStalk
      (CommRingCat.ofHom (algebraMap X.functionField L)) U hxU
    exact h1.symm.trans h2
  let : Algebra Γ(X, U) L := (φ.app U ≫ θ.hom).hom.toAlgebra
  -- every element of `L` integral over `Γ(X, U)` lies in the image of `ψ`
  have hint (m : L) (hm : _root_.IsIntegral Γ(X, U) m) : m ∈ Set.range ψ.hom := by
    let : Algebra Γ(X, U) Γ(Spec (.of L), φ ⁻¹ᵁ U) := (φ.app U).hom.toAlgebra
    have ht : _root_.IsIntegral Γ(X, U) (θ.inv m) := by
      refine IsIntegral.map_of_comp_eq (RingHom.id _) θ.inv.hom ?_ hm
      ext b
      change φ.app U b = θ.inv ((φ.app U ≫ θ.hom) b)
      rw [← ConcreteCategory.comp_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    set s := (φ.normalizationObjIso hU).inv ⟨θ.inv m, ht⟩
    have hs := congr($(φ.normalizationObjIso_hom_val hU) s)
    simp only [s, CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hs
    have h1 := congr($(germ_stalkClosedPointTo g _ hU') s)
    refine ⟨(Y.presheaf.germ _ _ hU') s, h1.trans ?_⟩
    have key : g.app (φ.fromNormalization ⁻¹ᵁ U) ≫
        ((Spec (.of L)).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem g hU').symm).op
          ≪≫ ΓSpecIso (.of L)).hom =
        g.appLE (φ.fromNormalization ⁻¹ᵁ U) (φ ⁻¹ᵁ U)
          (le_top.trans (preimage_eq_top_of_closedPoint_mem g hU').ge) ≫ θ.hom := by
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Hom.appLE, θ,
        Category.assoc, ← Functor.map_comp_assoc]
      rfl
    rw [key, CommRingCat.comp_apply, ← hs]
    exact θ.inv_hom_id_apply m
  -- `ψ` is surjective
  have hfrac := functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower Γ(X, U) X.functionField L := IsScalarTower.of_algebraMap_eq' <| by
    change (φ.app U ≫ θ.hom).hom = _
    rw [hθφ]
    rfl
  let := hfield.toField
  have hsurj : Function.Surjective ψ.hom := by
    intro l
    have hl : IsAlgebraic Γ(X, U) l := (IsFractionRing.isAlgebraic_iff Γ(X, U) X.functionField L).2
      (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨y, hy0, hyint⟩ := hl.exists_integral_multiple
    obtain ⟨a, ha⟩ := hint _ hyint
    obtain ⟨b, hb⟩ := hint (algebraMap Γ(X, U) L y) isIntegral_algebraMap
    have hy : algebraMap Γ(X, U) L y ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply Γ(X, U) X.functionField L, map_ne_zero]
      exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero hy0))
    refine ⟨a * b⁻¹, ?_⟩
    rw [map_mul, map_inv₀, ha, hb, Algebra.smul_def, mul_comm]
    exact inv_mul_cancel_left₀ hy l
  have hiso : IsIso ψ := (ConcreteCategory.isIso_iff_bijective ψ).2 ⟨ψ.hom.injective, hsurj⟩
  have hgψ : Spec.map ψ ≫ Y.fromSpecStalk (g pt) = g := Spec_stalkClosedPointTo_fromSpecStalk g
  clear_value ψ
  clear hsurj hint
  revert ψ hiso hgψ
  rw [hq]
  intro ψ _ hgψ
  exact ⟨asIso (Spec.map ψ), hgψ⟩

end FiniteExtension

/-- **Finiteness of the normalization.** For an integral scheme `X` locally of finite type over a
field `k`, the normalization `ν : X^ν ⟶ X` in the function field is finite: over an affine open
`Spec A`, the integral closure of the finitely generated `k`-domain `A` in its fraction field is a
finite `A`-module by E. Noether's finiteness theorem. In particular `X^ν` is proper over `k` if
`X` is. (blueprint: `lemma-proper-smooth-model--1`) -/
theorem isFinite_fromNormalization_of_locallyOfFiniteType {k : Type u} [Field k]
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] : IsFinite X.fromNormalization := by
  have h : X.fromSpecOfAlgebraFunctionField X.functionField = X.fromSpecFunctionField := by
    simp [fromSpecOfAlgebraFunctionField]
  have key {T : Scheme.{u}} (φ ψ : T ⟶ X) [QuasiCompact φ] [QuasiSeparated φ] [QuasiCompact ψ]
      [QuasiSeparated ψ] (h : φ = ψ) (hφ : IsFinite φ.fromNormalization) :
      IsFinite ψ.fromNormalization := by
    subst h; exact hφ
  exact key _ _ h (X.isFinite_fromNormalizationIn X.functionField q)

/-- **The normalization is birational.** For an integral scheme `X` locally of finite type over
a field `k`, the normalization `ν : X^ν ⟶ X` is an isomorphism over a nonempty, hence dense,
open subscheme of `X`. (blueprint: `lemma-proper-smooth-model--1`) -/
theorem exists_isIso_fromNormalization_restrict {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] :
    ∃ U : X.Opens, (U : Set X).Nonempty ∧ IsIso (X.fromNormalization ∣_ U) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  let := ((q.appLE ⊤ V le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, V) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top) (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm.surjective)
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  have := Algebra.FiniteType.finite_integralClosure k (A := Γ(X, V)) X.functionField
    X.functionField
  obtain ⟨b, hb, hbint⟩ := exists_isInteger_smul_of_finite_integralClosure (A := Γ(X, V))
    (K := X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hηV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using ‹Nonempty V›)
  have hηW : genericPoint X ∈ X.basicOpen b := by
    rw [X.mem_basicOpen b _ hηV]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr hb0)
  have hW : IsAffineOpen (X.basicOpen b) := hV.basicOpen b
  have : Nonempty (X.basicOpen b) := ⟨⟨_, hηW⟩⟩
  have := hV.isLocalization_basicOpen b
  have := functionField_isFractionRing_of_isAffineOpen X _ hW
  have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen b) X.functionField :=
    .of_algebraMap_eq fun a ↦ (X.presheaf.germ_res_apply _ _ _ a).symm
  have : IsIntegrallyClosed Γ(X, X.basicOpen b) :=
    isIntegrallyClosed_of_isLocalization_away hb0 hbint
  refine ⟨X.basicOpen b, ⟨_, hηW⟩, X.isIso_fromNormalization_restrict _ fun y hy ↦ ?_⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hy⟩ : X.basicOpen b)
  have := hW.isLocalization_stalk ⟨y, hy⟩
  exact isIntegrallyClosed_of_isLocalization _ _
    (hW.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl_le_nonZeroDivisors

/-- **The normalization preserves dimension.** For an integral scheme `X` locally of finite type
over a field `k`, `dim X^ν = dim X`: the finite surjective morphism `ν` lifts chains of
specializations, and identifies no two distinct points one of which specializes to the other.
(blueprint: `lemma-proper-smooth-model--1`) -/
theorem topologicalKrullDim_normalization {k : Type u} [Field k] (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] : topologicalKrullDim X.normalization = topologicalKrullDim X := by
  have := X.isFinite_fromNormalization_of_locallyOfFiniteType q
  exact le_antisymm (topologicalKrullDim_le_of_continuous X.fromNormalization.continuous
      fun _ _ h e ↦ X.fromNormalization.eq_of_specializes_of_apply_eq h e)
    (topologicalKrullDim_le_of_specializingMap X.fromNormalization.isClosedMap.specializingMap
      X.fromNormalization.surjective)

namespace Hom

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-- Normalization commutes with base change along `g : Y ⟶ S` for affine `f`, as soon as
`Y` is covered by affine opens `V ⊆ g⁻¹ U` (with `U ⊆ S` affine) such that forming the integral
closure of `Γ(S, U)` in `Γ(X, f⁻¹ U)` commutes with the base change to `Γ(Y, V)`. -/
lemma isIso_normalizationPullback_of_isAffineHom [IsAffineHom f]
    (H : ∀ y : Y, ∃ (U : S.Opens) (_ : IsAffineOpen U) (V : Y.Opens) (_ : IsAffineOpen V)
      (hVU : V ≤ g ⁻¹ᵁ U), y ∈ V ∧
      letI := (f.app U).hom.toAlgebra
      letI := (g.appLE U V hVU).hom.toAlgebra
      Function.Bijective (TensorProduct.toIntegralClosure Γ(S, U) Γ(Y, V) Γ(X, f ⁻¹ᵁ U))) :
    IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := .isomorphisms _) fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, hbij⟩ := H (pullback.snd _ g x)
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutSection_of_isAffineOpen
    (.of_hasPullback f.fromNormalization g) hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (hU.preimage f.fromNormalization)
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutSection_of_isAffineOpen
    (.of_hasPullback f g) hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) hU hV (hU.preimage f)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this :)
  let e : Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp hbij
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert! show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

set_option backward.isDefEq.respectTransparency false in
/-- The relative normalization `f.normalization ⟶ S` is étale over an affine open `U ⊆ S` as
soon as the integral closure of `Γ(S, U)` in `Γ(X, f⁻¹ U)` is étale over `Γ(S, U)`. -/
lemma etale_fromNormalization_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U)
    (h : letI := (f.app U).hom.toAlgebra
      Algebra.Etale Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))) :
    Etale ((f.fromNormalization ⁻¹ᵁ U).ι ≫ f.fromNormalization) := by
  have : IsAffine U := hU
  have : IsAffine (f.fromNormalization ⁻¹ᵁ U) := hU.preimage _
  rw [← Scheme.Hom.resLE_comp_ι f.fromNormalization (e := le_rfl)]
  suffices Etale (f.fromNormalization.resLE U _ le_rfl) by infer_instance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
  have : (RingHom.toMorphismProperty RingHom.Etale).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
  refine (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.Etale)
    (arrowResLEAppIso f.fromNormalization U _ le_rfl)).mpr ?_
  change RingHom.Etale (f.fromNormalization.appLE U _ le_rfl).hom
  rw [← Scheme.Hom.app_eq_appLE, fromNormalization_app _ hU]
  let := (f.app U).hom.toAlgebra
  exact RingHom.Etale.respectsIso.1 _ (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
    (RingHom.etale_algebraMap.mpr h)

set_option backward.isDefEq.respectTransparency false in
/-- Conversely to `AlgebraicGeometry.Scheme.Hom.etale_fromNormalization_of_isAffineOpen`, if the
relative normalization `f.normalization ⟶ S` is étale over an affine open `U ⊆ S`, then the
integral closure of `Γ(S, U)` in `Γ(X, f⁻¹ U)` is étale over `Γ(S, U)`. -/
lemma etale_integralClosure_of_etale_fromNormalization {U : S.Opens} (hU : IsAffineOpen U)
    (h : Etale ((f.fromNormalization ⁻¹ᵁ U).ι ≫ f.fromNormalization)) :
    letI := (f.app U).hom.toAlgebra
    Algebra.Etale Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)) := by
  have : IsAffine U := hU
  have : IsAffine (f.fromNormalization ⁻¹ᵁ U) := hU.preimage _
  rw [← Scheme.Hom.resLE_comp_ι f.fromNormalization (e := le_rfl)] at h
  have h' : Etale (f.fromNormalization.resLE U _ le_rfl) := Etale.of_comp _ U.ι
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)] at h'
  have : (RingHom.toMorphismProperty RingHom.Etale).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
  replace h' := (MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.Etale)
    (arrowResLEAppIso f.fromNormalization U _ le_rfl)).mp h'
  change RingHom.Etale (f.fromNormalization.appLE U _ le_rfl).hom at h'
  rw [← Scheme.Hom.app_eq_appLE, fromNormalization_app _ hU] at h'
  let := (f.app U).hom.toAlgebra
  have := RingHom.Etale.respectsIso.1 _ (f.normalizationObjIso hU).commRingCatIsoToRingEquiv h'
  have e : (f.normalizationObjIso hU).commRingCatIsoToRingEquiv.toRingHom.comp
      (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))) ≫
        (f.normalizationObjIso hU).inv).hom =
      algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)) := by
    refine RingHom.ext fun x ↦ ?_
    change (f.normalizationObjIso hU).hom ((f.normalizationObjIso hU).inv _) = _
    exact CommRingCat.hom_inv_apply _ _
  rw [e] at this
  exact RingHom.etale_algebraMap.mp this


end Hom

end AlgebraicGeometry.Scheme
