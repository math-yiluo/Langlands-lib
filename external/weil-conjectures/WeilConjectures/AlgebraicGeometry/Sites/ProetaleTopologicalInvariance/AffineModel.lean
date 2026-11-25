/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ProetaleTopologicalInvariance.Covers
public import WeilConjectures.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.IndWeaklyEtale

/-!
# Affine models in the small pro-étale site

For an affine open `U` of a scheme `S` and a weakly étale `Γ(S, U)`-algebra `D`, the composite
`Spec D ⟶ Spec Γ(S, U) ≅ U ⊆ S` is an object `ofAlgebra hU D` of the small pro-étale site of
`S`. Morphisms between such objects are exactly the `Γ(S, U)`-algebra maps.

## Main definitions and results

- `AlgebraicGeometry.Scheme.ProEt.ofAlgebra`: the object `Spec D ⟶ S` of `S.ProEt`.
- `AlgebraicGeometry.Scheme.ProEt.ofAlgebraMap`: the morphism `ofAlgebra hU D₂ ⟶ ofAlgebra hU D₁`
  induced by a `Γ(S, U)`-algebra map `D₁ →ₐ D₂`.
- `AlgebraicGeometry.Scheme.ProEt.ofAlgebraMapEquiv`: this is a bijection.
- `AlgebraicGeometry.Scheme.ProEt.generate_singleton_ofAlgebraMap_mem_topology`: a faithfully
  flat algebra map gives a single-arrow pro-étale covering.
- `AlgebraicGeometry.Scheme.ProEt.ofAlgebraIsoOfLE`: for affine opens `U'' ≤ U`, a weakly étale
  `Γ(S, U'')`-algebra gives the same object over `U''` and over `U`; ind-étaleness over
  `Γ(S, U'')` implies ind-étaleness over `Γ(S, U)` (`Algebra.IndEtale.of_isAffineOpen_le`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U)

/-- The affine model `Spec D ⟶ Spec Γ(S, U) ≅ U ⊆ S` of a weakly étale `Γ(S, U)`-algebra `D`,
as an object of the small pro-étale site of `S`. -/
noncomputable def ofAlgebra (D : Type u) [CommRing D] [Algebra Γ(S, U) D]
    [Algebra.WeaklyEtale Γ(S, U) D] : S.ProEt :=
  ProEt.mk (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) ≫ hU.fromSpec)

variable {D₁ D₂ D₃ : Type u} [CommRing D₁] [CommRing D₂] [CommRing D₃]
  [Algebra Γ(S, U) D₁] [Algebra Γ(S, U) D₂] [Algebra Γ(S, U) D₃]
  [Algebra.WeaklyEtale Γ(S, U) D₁] [Algebra.WeaklyEtale Γ(S, U) D₂]
  [Algebra.WeaklyEtale Γ(S, U) D₃]

@[simp]
lemma ofAlgebra_left (D : Type u) [CommRing D] [Algebra Γ(S, U) D]
    [Algebra.WeaklyEtale Γ(S, U) D] : (ofAlgebra hU D).left = Spec (.of D) := rfl

@[simp]
lemma ofAlgebra_hom (D : Type u) [CommRing D] [Algebra Γ(S, U) D]
    [Algebra.WeaklyEtale Γ(S, U) D] :
    (ofAlgebra hU D).hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, U) D)) ≫ hU.fromSpec :=
  rfl

/-- The morphism of affine models `Spec D₂ ⟶ Spec D₁` induced by a `Γ(S, U)`-algebra map
`f : D₁ →ₐ D₂`. -/
noncomputable def ofAlgebraMap (f : D₁ →ₐ[Γ(S, U)] D₂) : ofAlgebra hU D₂ ⟶ ofAlgebra hU D₁ :=
  MorphismProperty.Over.homMk (Spec.map (CommRingCat.ofHom f.toRingHom)) (by
    simp only [ofAlgebra_hom, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap])

@[simp]
lemma ofAlgebraMap_left (f : D₁ →ₐ[Γ(S, U)] D₂) :
    (ofAlgebraMap hU f).left = Spec.map (CommRingCat.ofHom f.toRingHom) := rfl

@[simp]
lemma ofAlgebraMap_id : ofAlgebraMap hU (AlgHom.id Γ(S, U) D₁) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  simp
  rfl

@[simp]
lemma ofAlgebraMap_comp (f : D₁ →ₐ[Γ(S, U)] D₂) (g : D₂ →ₐ[Γ(S, U)] D₃) :
    ofAlgebraMap hU (g.comp f) = ofAlgebraMap hU g ≫ ofAlgebraMap hU f := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, ofAlgebraMap_left, ofAlgebraMap_left, ofAlgebraMap_left,
    ← Spec.map_comp]
  rfl

/-- Morphisms of affine models are exactly algebra maps. -/
lemma ofAlgebraMap_bijective :
    Function.Bijective (ofAlgebraMap hU : (D₁ →ₐ[Γ(S, U)] D₂) → _) := by
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · have := Spec.map_injective congr($(hfg).left)
    ext x
    exact congr($(this) x)
  · obtain ⟨g, hg⟩ := Spec.map_surjective φ.left
    have hw := MorphismProperty.Over.w φ
    simp only [ofAlgebra_hom, ← hg, ← Spec.map_comp_assoc, cancel_mono] at hw
    have hw' := Spec.map_injective hw
    refine ⟨{ g.hom with commutes' := fun a ↦ congr($(hw').hom a) }, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    simp [← hg]

/-- The bijection between `Γ(S, U)`-algebra maps `D₁ →ₐ D₂` and morphisms of affine models
`ofAlgebra hU D₂ ⟶ ofAlgebra hU D₁`. -/
noncomputable def ofAlgebraMapEquiv :
    (D₁ →ₐ[Γ(S, U)] D₂) ≃ (ofAlgebra hU D₂ ⟶ ofAlgebra hU D₁) :=
  Equiv.ofBijective _ (ofAlgebraMap_bijective hU)

@[simp]
lemma ofAlgebraMapEquiv_apply (f : D₁ →ₐ[Γ(S, U)] D₂) :
    ofAlgebraMapEquiv hU f = ofAlgebraMap hU f := rfl

/-- The morphism of affine models induced by a faithfully flat algebra map spans a pro-étale
covering sieve. -/
lemma generate_singleton_ofAlgebraMap_mem_topology (f : D₁ →ₐ[Γ(S, U)] D₂)
    (hf : f.toRingHom.FaithfullyFlat) :
    Sieve.generate (Presieve.singleton (ofAlgebraMap hU f)) ∈ topology S _ := by
  rw [mem_topology_iff]
  refine ⟨_, ?_, Sieve.le_generate _⟩
  rw [mem_precoverage_iff, Presieve.map_singleton]
  have hfs := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f.toRingHom)).mpr hf
  have : Surjective ((ProEt.forget S ⋙ Over.forget S).map (ofAlgebraMap hU f)) := hfs.2
  have : QuasiCompact ((ProEt.forget S ⋙ Over.forget S).map (ofAlgebraMap hU f)) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom f.toRingHom)))
  exact Hom.singleton_mem_propQCPrecoverage (weaklyEtale_left (ofAlgebraMap hU f))

/-! ### Changing the affine open -/

section ChangeOfOpen

variable {U'' : S.Opens} (hU'' : IsAffineOpen U'') (hle : U'' ≤ U)

include hU hU'' in
/-- The restriction map `Γ(S, U) ⟶ Γ(S, U'')` between affine opens `U'' ≤ U` is étale:
on spectra it is an open immersion. -/
lemma etale_presheafMap_homOfLE : (S.presheaf.map (homOfLE hle).op).hom.Etale := by
  have h := hU.map_fromSpec hU'' (homOfLE hle).op
  have : IsOpenImmersion (Spec.map (S.presheaf.map (homOfLE hle).op) ≫ hU.fromSpec) := by
    rw [h]
    infer_instance
  have : IsOpenImmersion (Spec.map (S.presheaf.map (homOfLE hle).op)) :=
    .of_comp _ hU.fromSpec
  exact HasRingHomProperty.Spec_iff (P := @Etale).mp inferInstance

variable (D : Type u) [CommRing D] [Algebra Γ(S, U'') D] [Algebra Γ(S, U) D]
  (hD : algebraMap Γ(S, U) D =
    (algebraMap Γ(S, U'') D).comp (S.presheaf.map (homOfLE hle).op).hom)

include hU hU'' hD in
/-- For affine opens `U'' ≤ U`, an ind-étale `Γ(S, U'')`-algebra is ind-étale over `Γ(S, U)`
(through the restriction map, which is étale). -/
lemma indEtale_of_le [Algebra.IndEtale Γ(S, U'') D] : Algebra.IndEtale Γ(S, U) D := by
  have h := etale_presheafMap_homOfLE hU hU'' hle
  algebraize [(S.presheaf.map (homOfLE hle).op).hom]
  have : Algebra.IndEtale Γ(S, U) Γ(S, U'') := by
    rw [Algebra.IndEtale.iff_ind_etale]
    exact ObjectProperty.le_ind _ _ h
  rw [← RingHom.IndEtale.algebraMap_iff, hD]
  exact RingHom.IndEtale.comp ((RingHom.IndEtale.algebraMap_iff _ _).mpr ‹_›)
    ((RingHom.IndEtale.algebraMap_iff _ _).mpr this)


include hU hU'' hD in
/-- For affine opens `U'' ≤ U`, a weakly étale `Γ(S, U'')`-algebra is weakly étale over
`Γ(S, U)` (through the restriction map, which is étale). -/
lemma weaklyEtale_of_le [Algebra.WeaklyEtale Γ(S, U'') D] : Algebra.WeaklyEtale Γ(S, U) D := by
  have h := etale_presheafMap_homOfLE hU hU'' hle
  rw [← RingHom.weaklyEtale_algebraMap_iff, hD]
  refine RingHom.WeaklyEtale.comp ?_ (RingHom.weaklyEtale_algebraMap_iff.mpr ‹_›)
  algebraize [(S.presheaf.map (homOfLE hle).op).hom]
  exact RingHom.weaklyEtale_algebraMap_iff.mpr inferInstance

/-- For affine opens `U'' ≤ U` and a `Γ(S, U'')`-algebra `D` viewed as a `Γ(S, U)`-algebra
through restriction, the affine models of `D` over `U` and over `U''` agree. -/
noncomputable def ofAlgebraIsoOfLE [Algebra.WeaklyEtale Γ(S, U'') D]
    [Algebra.WeaklyEtale Γ(S, U) D] : ofAlgebra hU D ≅ ofAlgebra hU'' D :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    simp [hD, CommRingCat.ofHom_comp, hU.map_fromSpec hU''])

@[simp]
lemma ofAlgebraIsoOfLE_hom_left [Algebra.WeaklyEtale Γ(S, U'') D]
    [Algebra.WeaklyEtale Γ(S, U) D] : (ofAlgebraIsoOfLE hU hU'' hle D hD).hom.left = 𝟙 _ := rfl

@[simp]
lemma ofAlgebraIsoOfLE_inv_left [Algebra.WeaklyEtale Γ(S, U'') D]
    [Algebra.WeaklyEtale Γ(S, U) D] : (ofAlgebraIsoOfLE hU hU'' hle D hD).inv.left = 𝟙 _ := rfl

end ChangeOfOpen

end AlgebraicGeometry.Scheme.ProEt
