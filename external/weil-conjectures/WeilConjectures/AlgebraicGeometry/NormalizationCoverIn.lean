/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.NormalizationCover

/-!
# The normalization in a normal integral scheme is the normalization in its function field

Let `f : P ⟶ X` be a quasi-compact quasi-separated morphism of integral schemes mapping the
generic point of `P` to that of `X`, and let `L = k(P)`, an extension of `k(X)`. If `P` is
normal, the relative normalization `f.normalization` of `X` in `P` (the relative spectrum of the
integral closure of `𝒪_X` in `f_* 𝒪_P`) is the normalization `X.normalizationIn L` of `X` in the
field `L` (`AlgebraicGeometry.Scheme.Hom.exists_iso_normalizationIn`): over an affine open
`Spec B ⊆ X`, the integral closure of `B` in `Γ(P, f⁻¹ Spec B)` is the integral closure of `B`
in `L`, because `Γ(P, f⁻¹ Spec B) ⊆ L` is integrally closed in `L`.

Consequently the extension of a connected finite étale cover over a normal open, blueprint
`lem-fin-normalization-extends-cover`, holds with the normalization `X^{k(P)}` of
`def-fin-normalization-extension` (`AlgebraicGeometry.Scheme.normalizationIn_extends_cover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {P X : Scheme.{u}}

/-- `appLE` along equal morphisms. -/
lemma Scheme.Hom.appLE_of_eq {f g : P ⟶ X} (h : f = g) (U : X.Opens) (V : P.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

namespace Scheme.Hom

variable [IsIntegral P] [IsIntegral X] (f : P ⟶ X) (hf : f (genericPoint P) = genericPoint X)

/-- The `k(X)`-algebra structure on `k(P)` induced by a morphism of integral schemes `f : P ⟶ X`
mapping the generic point to the generic point. -/
noncomputable abbrev functionFieldAlgebra : Algebra X.functionField P.functionField :=
  (X.presheaf.stalkSpecializes (specializes_of_eq hf) ≫ f.stalkMap (genericPoint P)).hom.toAlgebra

/-- The morphism `Spec k(P) ⟶ X` through `Spec k(X)` is the generic point of `P` followed by
`f`. -/
lemma fromSpecOfAlgebraFunctionField_eq :
    letI := f.functionFieldAlgebra hf
    X.fromSpecOfAlgebraFunctionField P.functionField = P.fromSpecFunctionField ≫ f := by
  let := f.functionFieldAlgebra hf
  simp only [Scheme.fromSpecOfAlgebraFunctionField, Scheme.fromSpecFunctionField,
    RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]

variable [QuasiCompact f] [QuasiSeparated f]

/-- The comparison morphism `X^{k(P)} ⟶ f.normalization` from the normalization of `X` in the
field `k(P)` to the relative normalization of `X` in `P`, induced by the universal property of
the former and the generic point `Spec k(P) ⟶ P`. -/
noncomputable def normalizationInToNormalization :
    letI := f.functionFieldAlgebra hf
    X.normalizationIn P.functionField ⟶ f.normalization :=
  letI := f.functionFieldAlgebra hf
  (X.fromSpecOfAlgebraFunctionField P.functionField).normalizationDesc
    (P.fromSpecFunctionField ≫ f.toNormalization) f.fromNormalization (by
      rw [fromSpecOfAlgebraFunctionField_eq f hf, Category.assoc,
        toNormalization_fromNormalization])

@[reassoc (attr := simp)]
lemma normalizationInToNormalization_fromNormalization :
    letI := f.functionFieldAlgebra hf
    f.normalizationInToNormalization hf ≫ f.fromNormalization =
      X.fromNormalizationIn P.functionField := by
  let := f.functionFieldAlgebra hf
  exact normalizationDesc_comp ..

@[reassoc (attr := simp)]
lemma toNormalization_normalizationInToNormalization :
    letI := f.functionFieldAlgebra hf
    (X.fromSpecOfAlgebraFunctionField P.functionField).toNormalization ≫
      f.normalizationInToNormalization hf = P.fromSpecFunctionField ≫ f.toNormalization := by
  let := f.functionFieldAlgebra hf
  exact toNormalization_normalizationDesc ..

/-- Over an affine open `U = Spec B` of `X`, the comparison morphism induces an isomorphism on
sections over the preimage of `U`, provided `P` is normal: both sides are integral closures of
`B`, in `Γ(P, f⁻¹ U)` and in `k(P)` respectively, and an element of `k(P)` integral over `B` lies
in `Γ(P, f⁻¹ U)`, which is integrally closed in `k(P)`. -/
lemma isIso_normalizationInToNormalization_app
    (hP : ∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x)) (U : X.affineOpens) :
    IsIso ((f.normalizationInToNormalization hf).app (f.fromNormalization ⁻¹ᵁ U.1)) := by
  let := f.functionFieldAlgebra hf
  set L := P.functionField
  set φ := X.fromSpecOfAlgebraFunctionField L
  set d := f.normalizationInToNormalization hf
  set g := f.fromNormalization
  have hφ : φ = P.fromSpecFunctionField ≫ f := fromSpecOfAlgebraFunctionField_eq f hf
  -- the algebra structures over `B = Γ(X, U)`
  let := (f.app U.1).hom.toAlgebra
  let := (φ.app U.1).hom.toAlgebra
  -- the restriction `ρ : Γ(P, f⁻¹ U) ⟶ Γ(Spec L, φ⁻¹ U)`, a `B`-algebra map
  have hle : φ ⁻¹ᵁ U.1 ≤ P.fromSpecFunctionField ⁻¹ᵁ f ⁻¹ᵁ U.1 := by
    rw [← Scheme.Hom.comp_preimage, ← hφ]
  let ρ := P.fromSpecFunctionField.appLE (f ⁻¹ᵁ U.1) (φ ⁻¹ᵁ U.1) hle
  have hρB : f.app U.1 ≫ ρ = φ.app U.1 := by
    simp only [ρ, Scheme.Hom.appLE, ← Category.assoc, ← Scheme.Hom.comp_app]
    rw [Scheme.Hom.congr_app hφ U.1]
    congr 2
  let ρA : Γ(P, f ⁻¹ᵁ U.1) →ₐ[Γ(X, U.1)] Γ(Spec (.of L), φ ⁻¹ᵁ U.1) :=
    { ρ.hom with commutes' b := congr($hρB b) }
  -- the induced map `θ` of integral closures
  let θ : integralClosure Γ(X, U.1) Γ(P, f ⁻¹ᵁ U.1) →+*
      integralClosure Γ(X, U.1) Γ(Spec (.of L), φ ⁻¹ᵁ U.1) :=
    (ρ.hom.comp (integralClosure Γ(X, U.1) Γ(P, f ⁻¹ᵁ U.1)).val.toRingHom).codRestrict _
      fun x ↦ x.2.map ρA
  -- `d` on sections is `θ`, read through the identifications with integral closures
  have hpre : φ.fromNormalization ⁻¹ᵁ U.1 = d ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
    rw [← Scheme.Hom.comp_preimage, normalizationInToNormalization_fromNormalization]
  have key : d.app (g ⁻¹ᵁ U.1) ≫ (X.normalizationIn L).presheaf.map (eqToHom hpre).op ≫
      (φ.normalizationObjIso U.2).hom =
        (f.normalizationObjIso U.2).hom ≫ CommRingCat.ofHom θ := by
    have e₁ := φ.normalizationObjIso_hom_val U.2
    have e₂ := f.normalizationObjIso_hom_val U.2
    refine CommRingCat.hom_ext (RingHom.ext fun x ↦ Subtype.ext ?_)
    have h₁ : d.app (g ⁻¹ᵁ U.1) ≫ (X.normalizationIn L).presheaf.map (eqToHom hpre).op ≫
        (φ.normalizationObjIso U.2).hom ≫
          CommRingCat.ofHom (integralClosure Γ(X, U.1) _).val.toRingHom =
        (P.fromSpecFunctionField ≫ f.toNormalization).appLE (g ⁻¹ᵁ U.1) (φ ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, Category.assoc,
            toNormalization_fromNormalization, ← hφ]) := by
      rw [e₁, map_appLE, app_eq_appLE, appLE_comp_appLE]
      exact appLE_of_eq (toNormalization_normalizationInToNormalization f hf) _ _ _
    have h₂ : (f.normalizationObjIso U.2).hom ≫ CommRingCat.ofHom θ ≫
          CommRingCat.ofHom (integralClosure Γ(X, U.1) _).val.toRingHom =
        (P.fromSpecFunctionField ≫ f.toNormalization).appLE (g ⁻¹ᵁ U.1) (φ ⁻¹ᵁ U.1)
          (by rw [← Scheme.Hom.comp_preimage, Category.assoc,
            toNormalization_fromNormalization, ← hφ]) := by
      have : CommRingCat.ofHom θ ≫
          CommRingCat.ofHom (integralClosure Γ(X, U.1) _).val.toRingHom =
          CommRingCat.ofHom (integralClosure Γ(X, U.1) _).val.toRingHom ≫ ρ := rfl
      rw [this, reassoc_of% e₂, appLE_comp_appLE]
    exact ConcreteCategory.congr_hom (h₁.trans h₂.symm) x
  -- `θ` is bijective
  have hθ : Function.Bijective θ := by
    by_cases hU : genericPoint X ∈ (U.1 : Set X)
    · -- `f⁻¹ U` is nonempty, and `φ⁻¹ U` is all of `Spec L`
      have hη : genericPoint P ∈ f ⁻¹ᵁ U.1 := by simpa [hf] using hU
      have : Nonempty (f ⁻¹ᵁ U.1) := ⟨⟨genericPoint P, hη⟩⟩
      have hcl : P.fromSpecFunctionField (IsLocalRing.closedPoint P.functionField) =
          genericPoint P := Scheme.fromSpecStalk_closedPoint
      have hmem : P.fromSpecFunctionField (IsLocalRing.closedPoint P.functionField) ∈
          f ⁻¹ᵁ U.1 := by rw [hcl]; exact hη
      have hφU : φ ⁻¹ᵁ U.1 = ⊤ := preimage_eq_top_of_closedPoint_mem φ (by
        rw [hφ]
        exact hmem)
      let τ : Γ(Spec P.functionField, φ ⁻¹ᵁ U.1) ≅ P.functionField :=
        (Spec P.functionField).presheaf.mapIso (eqToIso hφU.symm).op ≪≫
          Scheme.ΓSpecIso P.functionField
      -- `ρ` followed by `τ` is the restriction to the generic point
      have hρτ : ρ ≫ τ.hom = P.germToFunctionField (f ⁻¹ᵁ U.1) := by
        have h1 := Scheme.germ_stalkClosedPointTo P.fromSpecFunctionField (f ⁻¹ᵁ U.1) hmem
        rw [Scheme.stalkClosedPointTo_fromSpecStalk, TopCat.Presheaf.stalkCongr_hom,
          TopCat.Presheaf.germ_stalkSpecializes] at h1
        refine Eq.trans ?_ h1.symm
        simp only [ρ, τ, Scheme.Hom.appLE, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
          eqToIso.hom, Category.assoc, ← Functor.map_comp_assoc]
        rfl
      have hinj : Function.Injective ρ := by
        intro a b h
        apply P.germToFunctionField_injective (f ⁻¹ᵁ U.1)
        rw [← hρτ, CommRingCat.comp_apply, CommRingCat.comp_apply, h]
      refine ⟨fun a b h ↦ Subtype.ext (hinj congr($h.1)), fun y ↦ ?_⟩
      -- an element of `L` integral over `B` is a section over `f⁻¹ U`
      obtain ⟨s, hs⟩ := Scheme.exists_germToFunctionField_eq (f ⁻¹ᵁ U.1) (τ.hom y.1)
        fun z hz ↦ by
          have := hP z
          refine (IsIntegrallyClosed.isIntegral_iff (R := P.presheaf.stalk z)).mp ?_
          refine IsIntegral.map_of_comp_eq (f.app U.1 ≫ P.presheaf.germ _ z hz).hom
            τ.hom.hom ?_ y.2
          ext a
          rw [RingHom.comp_apply, RingHom.comp_apply, CommRingCat.hom_comp, RingHom.comp_apply,
            Scheme.algebraMap_germ_eq_germToFunctionField, ← hρτ]
          have h3 := ConcreteCategory.congr_hom
            (show f.app U.1 ≫ ρ ≫ τ.hom = φ.app U.1 ≫ τ.hom by rw [← Category.assoc, hρB]) a
          simp only [CommRingCat.comp_apply] at h3 ⊢
          exact h3
      have hsy : ρ s = y.1 := by
        apply (ConcreteCategory.bijective_of_isIso τ.hom).1
        rw [← CommRingCat.comp_apply, hρτ, hs]
      have hsi : _root_.IsIntegral Γ(X, U.1) s :=
        (isIntegral_algHom_iff ρA hinj).mp (by
          change _root_.IsIntegral Γ(X, U.1) (ρ s)
          rw [hsy]
          exact y.2)
      exact ⟨⟨s, hsi⟩, Subtype.ext hsy⟩
    · -- both sides are zero rings
      have hfU : f ⁻¹ᵁ U.1 = ⊥ := by
        refine eq_bot_iff.mpr fun z hz ↦ hU ?_
        have hη : genericPoint P ∈ f ⁻¹ᵁ U.1 :=
          ((genericPoint_spec P).mem_open_set_iff (f ⁻¹ᵁ U.1).isOpen).mpr ⟨z, trivial, hz⟩
        simpa [hf] using hη
      have hφU : φ ⁻¹ᵁ U.1 = ⊥ := by
        rw [hφ, Scheme.Hom.comp_preimage, hfU]
        exact Scheme.Hom.preimage_bot _
      have : Subsingleton Γ(P, f ⁻¹ᵁ U.1) := by rw [hfU]; infer_instance
      have : Subsingleton Γ(Spec (.of L), φ ⁻¹ᵁ U.1) := by rw [hφU]; infer_instance
      exact ⟨fun a b _ ↦ Subsingleton.elim a b, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  have : IsIso (CommRingCat.ofHom θ) :=
    (RingEquiv.ofBijective θ hθ).toCommRingCatIso.isIso_hom
  have : IsIso (d.app (g ⁻¹ᵁ U.1) ≫ (X.normalizationIn L).presheaf.map (eqToHom hpre).op ≫
      (φ.normalizationObjIso U.2).hom) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((X.normalizationIn L).presheaf.map (eqToHom hpre).op ≫ (φ.normalizationObjIso U.2).hom)

/-- **The relative normalization in a normal integral scheme is the normalization in its
function field.** Let `f : P ⟶ X` be a quasi-compact quasi-separated morphism of integral
schemes sending the generic point of `P` to that of `X`, with `P` normal. Then the comparison
morphism `X^{k(P)} ⟶ f.normalization` is an isomorphism over `X`. -/
theorem isIso_normalizationInToNormalization
    (hP : ∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x)) :
    IsIso (f.normalizationInToNormalization hf) := by
  let := f.functionFieldAlgebra hf
  set d := f.normalizationInToNormalization hf
  set g := f.fromNormalization
  have key (U : X.affineOpens) (W : f.normalization.Opens) (hW : W = g ⁻¹ᵁ U.1) :
      IsIso (d.app W) := by
    subst hW
    exact f.isIso_normalizationInToNormalization_app hf hP U
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := MorphismProperty.isomorphisms Scheme) (fun U : X.affineOpens ↦ g ⁻¹ᵁ U.1) ?_]
  · intro U
    have hV : IsAffineOpen (g ⁻¹ᵁ U.1) := U.2.preimage g
    have : IsAffine (g ⁻¹ᵁ U.1) := hV
    rw [HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)]
    refine ⟨?_, ?_⟩
    · have h : d ⁻¹ᵁ g ⁻¹ᵁ U.1 = (X.fromNormalizationIn P.functionField) ⁻¹ᵁ U.1 := by
        rw [← Scheme.Hom.comp_preimage, normalizationInToNormalization_fromNormalization]
      change IsAffine (d ⁻¹ᵁ g ⁻¹ᵁ U.1)
      rw [h]
      exact U.2.preimage _
    · rw [morphismRestrict_appTop]
      have := key U ((g ⁻¹ᵁ U.1).ι ''ᵁ ⊤) (by rw [Scheme.Opens.ι_image_top])
      infer_instance
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

/-- **The relative normalization in a normal integral scheme is the normalization in its
function field.** Let `f : P ⟶ X` be a quasi-compact quasi-separated morphism of integral
schemes sending the generic point of `P` to that of `X`, with `P` normal, and let
`L = k(P)` (a `k(X)`-algebra through `f`). Then the relative normalization `f.normalization` of
`X` in `P` is isomorphic over `X` to the normalization `X^L` of `X` in `L`
(`AlgebraicGeometry.Scheme.normalizationIn`, blueprint `def-fin-normalization-extension`). -/
theorem exists_iso_normalizationIn (hP : ∀ x : P, IsIntegrallyClosed (P.presheaf.stalk x)) :
    letI := f.functionFieldAlgebra hf
    ∃ e : f.normalization ≅ X.normalizationIn P.functionField,
      e.hom ≫ X.fromNormalizationIn P.functionField = f.fromNormalization := by
  let := f.functionFieldAlgebra hf
  have := f.isIso_normalizationInToNormalization hf hP
  refine ⟨(asIso (f.normalizationInToNormalization hf)).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq,
    normalizationInToNormalization_fromNormalization]
end Scheme.Hom

/-- Blueprint `lem-fin-normalization-extends-cover`: Extending a finite cover by normalization,
with the normalization in the function field.

Let `X` be an integral scheme of finite type over a field `k`, `kV : V ⟶ X` a nonempty open
subscheme with integrally closed local rings, and `p : P ⟶ V` a connected finite étale cover.
Then `P` is integral and dominates `X`, its function field `L = k(P)` is a finite extension of
`k(X)`, and the normalization `X^L ⟶ X` of `X` in `L` (`AlgebraicGeometry.Scheme.normalizationIn`,
blueprint `def-fin-normalization-extension`) is finite, with `X^L` normal integral, and restricts
over `V` to the given cover: there is an open immersion `P ⟶ X^L` over `X` whose image is the
preimage of `V`.

This is `AlgebraicGeometry.Scheme.normalization_comp_of_finite_etale` for the relative
normalization of `X` in `P`, which is `X^L` by
`AlgebraicGeometry.Scheme.Hom.exists_iso_normalizationIn`, `P` being normal. -/
theorem Scheme.normalizationIn_extends_cover {k : Type u} [Field k] {P V X : Scheme.{u}}
    (q : X ⟶ Spec (.of k)) [LocallyOfFiniteType q] [IsIntegral X]
    (kV : V ⟶ X) [IsOpenImmersion kV] [QuasiCompact kV] [Nonempty V]
    (hV : ∀ v : V, IsIntegrallyClosed (V.presheaf.stalk v))
    (p : P ⟶ V) [IsFinite p] [Etale p] [ConnectedSpace P] :
    ∃ (_ : IsIntegral P) (hgen : (p ≫ kV) (genericPoint P) = genericPoint X),
      letI := (p ≫ kV).functionFieldAlgebra hgen
      FiniteDimensional X.functionField P.functionField ∧
      IsFinite (X.fromNormalizationIn P.functionField) ∧
      IsIntegral (X.normalizationIn P.functionField) ∧
      (∀ y : X.normalizationIn P.functionField,
        IsIntegrallyClosed ((X.normalizationIn P.functionField).presheaf.stalk y)) ∧
      ∃ ι : P ⟶ X.normalizationIn P.functionField, IsOpenImmersion ι ∧
        ι ≫ X.fromNormalizationIn P.functionField = p ≫ kV ∧
        Set.range ι.base = (X.fromNormalizationIn P.functionField).base ⁻¹' Set.range kV.base := by
  obtain ⟨hP, hPst, hι, -, -, hYn, hrange⟩ := Scheme.normalization_comp_of_finite_etale q kV hV p
  have hgen : (p ≫ kV) (genericPoint P) = genericPoint X := by
    obtain ⟨x, hx, hfx⟩ := Flat.generalizingMap (p ≫ kV)
      (genericPoint_specializes ((p ≫ kV) (genericPoint P)))
    obtain rfl : x = genericPoint P := (hx.antisymm (genericPoint_specializes x)).eq
    exact hfx
  refine ⟨hP, hgen, ?_⟩
  let := (p ≫ kV).functionFieldAlgebra hgen
  have hfd : FiniteDimensional X.functionField P.functionField :=
    (p ≫ kV).finiteDimensional_functionField hgen
  obtain ⟨e, he⟩ := (p ≫ kV).exists_iso_normalizationIn hgen hPst
  refine ⟨hfd, X.isFinite_fromNormalizationIn _ q, inferInstance, fun y ↦ ?_,
    (p ≫ kV).toNormalization ≫ e.hom, inferInstance, ?_, ?_⟩
  · have := hYn (e.inv y)
    exact IsIntegrallyClosed.of_equiv (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  · rw [Category.assoc, he, Scheme.Hom.toNormalization_fromNormalization]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange, ← he,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
    exact Set.image_preimage_eq _ (ConcreteCategory.bijective_of_isIso e.hom.base).2

end AlgebraicGeometry
