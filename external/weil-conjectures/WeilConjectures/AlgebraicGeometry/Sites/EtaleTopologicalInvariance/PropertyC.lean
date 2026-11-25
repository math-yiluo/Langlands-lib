/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Smooth.NoetherianDescent
public import WeilConjectures.Mathlib.RingTheory.Etale.PropertyC
public import WeilConjectures.Mathlib.RingTheory.RingHom.PurelyInseparable
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.Reduction

/-!
# Property (C) for universal homeomorphisms

Let `f : X ⟶ Y` be a universal homeomorphism and `g : U ⟶ X` étale. For every point `u : U`
there is an affine étale `W ⟶ Y` and an `X`-morphism `W ×_Y X ⟶ U` whose image contains `u`.
This is property (C) of [Stacks 04DW], and it is the scheme-theoretic form of
`Algebra.Etale.exists_etale_algHom_comap_eq`.

The proof reduces to the case where `X`, `Y` and `U` are affine, and then, using
`Algebra.Etale.exists_subalgebra_fg`, to the case where `X` is finite over `Y`, which is the
ring-theoretic statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

section ResidueField

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : Spec S)

set_option backward.isDefEq.respectTransparency.types false in
/-- The residue field map of `Spec φ` is identified with `Ideal.ResidueField.map` under the
isomorphisms `Scheme.Spec.residueFieldIso`. -/
lemma Spec.residueFieldMap_residueFieldIso_hom :
    (Spec.map φ).residueFieldMap x ≫ (Scheme.Spec.residueFieldIso S x).hom =
      (Scheme.Spec.residueFieldIso R ((Spec.map φ) x)).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map _ x.asIdeal φ.hom rfl) := by
  rw [← cancel_epi ((Spec R).residue _), Scheme.residue_residueFieldMap_assoc,
    Scheme.Spec.residue_residueFieldIso_hom, Scheme.Spec.residue_residueFieldIso_hom_assoc,
    ← Scheme.localRingHom_comp_stalkIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1

/-- For a universal homeomorphism of rings, the residue field extensions are purely
inseparable. -/
theorem Algebra.IsUniversalHomeomorphism.isPurelyInseparable_residueField_map
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsUniversalHomeomorphism A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    (Ideal.ResidueField.map (𝔮.under A) 𝔮 (algebraMap A B) rfl).IsPurelyInseparable := by
  let φ : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let x : Spec (CommRingCat.of B) := ⟨𝔮, inferInstance⟩
  have h : ((Spec.map φ).residueFieldMap x).hom.IsPurelyInseparable := by
    have H := (tfae_universallyInjective (Spec.map φ)).out 1 3
    exact (H.mp inferInstance).2 x
  change (Ideal.ResidueField.map ((Spec.map φ) x).asIdeal x.asIdeal φ.hom rfl).IsPurelyInseparable
  have hsq := (Iso.inv_comp_eq _).mpr (Spec.residueFieldMap_residueFieldIso_hom φ x)
  have := congr(($hsq).hom)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at this
  rw [← this]
  exact RingHom.IsPurelyInseparable.comp_of_bijective
    (Scheme.Spec.residueFieldIso _ _).commRingCatIsoToRingEquiv.symm.bijective h
    (Scheme.Spec.residueFieldIso _ _).commRingCatIsoToRingEquiv.bijective

end ResidueField

section Spec

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra A C] [IsScalarTower A B C] [Algebra.IsUniversalHomeomorphism A B] [Module.Finite A B]
  [Algebra.Etale B C]

/-- Property (C) for `Spec C ⟶ Spec B ⟶ Spec A` with `B` finite over `A`: the scheme-theoretic
form of `Algebra.Etale.exists_etale_algHom_comap_eq`. -/
theorem exists_etale_hom_mem_range_SpecMap (q : PrimeSpectrum C) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (p : W ⟶ Spec (.of A)) (_ : Etale p)
      (h : pullback p (Spec.map (CommRingCat.ofHom (algebraMap A B))) ⟶ Spec (.of C)),
      h ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) = pullback.snd _ _ ∧
        q ∈ Set.range h := by
  obtain ⟨A', _, _, _, h, hh, q', _, hq⟩ := Algebra.Etale.exists_etale_algHom_comap_eq
    (A := A) (B := B) (C := C)
    (fun A'' _ _ ↦ Algebra.IsUniversalHomeomorphism.comap_injective A'' (A'' ⊗[A] B))
    (fun 𝔮 _ ↦ Algebra.IsUniversalHomeomorphism.isPurelyInseparable_residueField_map 𝔮)
    q.asIdeal
  refine ⟨Spec (.of A'), inferInstance, Spec.map (CommRingCat.ofHom (algebraMap A A')),
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›),
    (pullbackSpecIso A A' B).hom ≫ Spec.map (CommRingCat.ofHom h.toRingHom), ?_, ?_⟩
  · rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : h.toRingHom.comp (algebraMap B C) = Algebra.TensorProduct.includeRight.toRingHom := by
      ext b
      exact congr($hh b)
    rw [show CommRingCat.ofHom (h.toRingHom.comp (algebraMap B C)) =
      CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom from congrArg _ this]
    exact pullbackSpecIso_hom_snd A A' B
  · refine ⟨(pullbackSpecIso A A' B).inv ⟨q', ‹_›⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id_assoc]
    exact PrimeSpectrum.ext hq.symm


end Spec

section Transport

/-- Property (C) for `f : X ⟶ Y` and `g : U ⟶ X` at a point `u`. -/
def PropertyC {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ X) (u : U) : Prop :=
  ∃ (W : Scheme.{u}) (_ : IsAffine W) (p : W ⟶ Y) (_ : Etale p) (h : pullback p f ⟶ U),
    h ≫ g = pullback.snd p f ∧ u ∈ Set.range h

variable {X Y U : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ X}

/-- Property (C) is stable under base change: if it holds for `g₀ : U₀ ⟶ X₀` over `Y` and `g` is
the base change of `g₀` along `ρ : X ⟶ X₀`, then it holds for `g`. -/
lemma PropertyC.of_isPullback {X₀ U₀ : Scheme.{u}} {f₀ : X₀ ⟶ Y} {ρ : X ⟶ X₀} (hρ : ρ ≫ f₀ = f)
    {g₀ : U₀ ⟶ X₀} {σ : U ⟶ U₀} (H : IsPullback σ g g₀ ρ) (u : U) (h : PropertyC f₀ g₀ (σ u)) :
    PropertyC f g u := by
  obtain ⟨W, _, p, _, h₀, hh₀, hu⟩ := h
  let m : pullback p f ⟶ pullback p f₀ :=
    pullback.map p f p f₀ (𝟙 W) ρ (𝟙 Y) (by simp) (by simp [hρ])
  -- `pullback p f` is the base change of `pullback p f₀` along `ρ`.
  have hm : IsPullback m (pullback.snd p f) (pullback.snd p f₀) ρ := by
    refine IsPullback.of_right ?_ (by simp [m]) (IsPullback.of_hasPullback p f₀)
    have : m ≫ pullback.fst p f₀ = pullback.fst p f := by simp [m]
    rw [this, hρ]
    exact IsPullback.of_hasPullback p f
  -- hence `pullback p f ⟶ U` is the base change of `h₀` along `σ`.
  let h : pullback p f ⟶ U := H.lift (m ≫ h₀) (pullback.snd p f) (by
    rw [Category.assoc, hh₀, hm.w])
  have hh : IsPullback h m σ h₀ := by
    refine IsPullback.of_right ?_ (H.lift_fst _ _ _) H.flip
    rw [show h ≫ g = pullback.snd p f from H.lift_snd _ _ _, hh₀]
    exact hm.flip
  refine ⟨W, inferInstance, p, inferInstance, h, H.lift_snd _ _ _, ?_⟩
  obtain ⟨w, hw⟩ := hu
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := σ) (g := h₀) u w hw.symm
  refine ⟨hh.isoPullback.inv z, ?_⟩
  rw [← Scheme.Hom.comp_apply, hh.isoPullback_inv_fst, hz]

/-- Property (C) is stable under isomorphisms of the base. -/
lemma PropertyC.of_iso_base {Y' : Scheme.{u}} (e : Y ≅ Y') (u : U) (h : PropertyC (f ≫ e.hom) g u) :
    PropertyC f g u := by
  obtain ⟨W, _, p, _, h, hh, hu⟩ := h
  let m : pullback (p ≫ e.inv) f ⟶ pullback p (f ≫ e.hom) :=
    pullback.map _ _ _ _ (𝟙 W) (𝟙 X) e.hom (by simp) (by simp)
  refine ⟨W, inferInstance, p ≫ e.inv, inferInstance, m ≫ h, by simp [m, hh], ?_⟩
  obtain ⟨w, rfl⟩ := hu
  exact ⟨inv m w, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]⟩

end Transport

section SpecIntegral

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
  [Algebra.IsUniversalHomeomorphism A B] [Algebra.Etale B C]

/-- Property (C) for `Spec C ⟶ Spec B ⟶ Spec A` with `B` a universal homeomorphism over `A`,
obtained from the finite case by writing `C` as the base change of an étale algebra over a
finite `A`-subalgebra of `B`. -/
theorem propertyC_SpecMap (q : PrimeSpectrum C) :
    PropertyC (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap B C))) q := by
  obtain ⟨B₀, C₀, _, _, hB₀, _, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg (R := A) (A := B) (B := C)
  let _ : Algebra A C₀ := ((algebraMap B₀ C₀).comp (algebraMap A B₀)).toAlgebra
  have : IsScalarTower A B₀ C₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsUniversalHomeomorphism A B₀ :=
    Algebra.IsUniversalHomeomorphism.of_subalgebra B₀
  have : Module.Finite A B₀ := by
    have : Algebra.FiniteType A B₀ := (Subalgebra.fg_iff_finiteType B₀).mp hB₀
    exact Algebra.IsIntegral.finite
  let ρ : Spec (.of B) ⟶ Spec (.of B₀) := Spec.map (CommRingCat.ofHom (algebraMap B₀ B))
  let f₀ : Spec (.of B₀) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B₀))
  have hρ : ρ ≫ f₀ = Spec.map (CommRingCat.ofHom (algebraMap A B)) := by
    simp only [ρ, f₀, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let g₀ : Spec (.of C₀) ⟶ Spec (.of B₀) := Spec.map (CommRingCat.ofHom (algebraMap B₀ C₀))
  let ι : C₀ →+* C := e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  let σ : Spec (.of C) ⟶ Spec (.of C₀) := Spec.map (CommRingCat.ofHom ι)
  have H : IsPullback σ (Spec.map (CommRingCat.ofHom (algebraMap B C))) g₀ ρ := by
    have h1 := (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct B₀ B C₀)).flip
    have h2 : IsPullback (Spec.map (CommRingCat.ofHom e.symm.toRingHom))
        (Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (Spec.map (CommRingCat.ofHom (S := B ⊗[B₀] C₀) Algebra.TensorProduct.includeLeftRingHom))
        (𝟙 _) := by
      have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
        inferInstanceAs (IsIso e.symm.toRingEquiv.toCommRingCatIso.hom)
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      have hcomp : e.symm.toRingHom.comp
          (Algebra.TensorProduct.includeLeftRingHom (A := B) (B := C₀)) = algebraMap B C := by
        ext b
        exact e.symm.commutes b
      rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    have := h2.paste_horiz h1
    rw [Category.id_comp] at this
    convert this using 1
    simp only [σ, ι, Spec.map_comp, CommRingCat.ofHom_comp]
  have hq := exists_etale_hom_mem_range_SpecMap (A := A) (B := B₀) (C := C₀) (σ q)
  exact PropertyC.of_isPullback hρ H q hq

end SpecIntegral

section Affine

variable {X Y U : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine U] (f : X ⟶ Y)
  [IsUniversalHomeomorphism f] (g : U ⟶ X) [Etale g]

/-- Property (C) for affine schemes. -/
theorem propertyC_of_isAffine (u : U) : PropertyC f g u := by
  refine PropertyC.of_iso_base Y.isoSpec u ?_
  refine PropertyC.of_isPullback (f₀ := Spec.map f.appTop) (ρ := X.isoSpec.hom)
    (Scheme.isoSpec_hom_naturality f) (g₀ := Spec.map g.appTop) (σ := U.isoSpec.hom)
    (IsPullback.of_horiz_isIso ⟨Scheme.isoSpec_hom_naturality g⟩) u ?_
  let _ : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let _ : Algebra Γ(X, ⊤) Γ(U, ⊤) := g.appTop.hom.toAlgebra
  have h1 : Spec.map f.appTop = X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom := by
    rw [← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]
  have : Algebra.IsUniversalHomeomorphism Γ(Y, ⊤) Γ(X, ⊤) :=
    ⟨by
      rw [show CommRingCat.ofHom (algebraMap Γ(Y, ⊤) Γ(X, ⊤)) = f.appTop from rfl, h1]
      infer_instance⟩
  have : Algebra.Etale Γ(X, ⊤) Γ(U, ⊤) :=
    RingHom.etale_algebraMap.mp ((HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp ‹_›)
  exact propertyC_SpecMap (A := Γ(Y, ⊤)) (B := Γ(X, ⊤)) (C := Γ(U, ⊤)) (U.isoSpec.hom u)

end Affine

section General

/-- **Property (C)** of [Stacks 04DW]: for a universal homeomorphism `f : X ⟶ Y`, an étale
`g : U ⟶ X` and a point `u : U`, there is an affine étale `W ⟶ Y` and an `X`-morphism
`W ×_Y X ⟶ U` whose image contains `u`. -/
@[stacks 04DW]
theorem Scheme.Hom.exists_etale_hom_mem_range {X Y U : Scheme.{u}} (f : X ⟶ Y)
    [IsUniversalHomeomorphism f] (g : U ⟶ X) [AlgebraicGeometry.Etale g] (u : U) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (p : W ⟶ Y) (_ : AlgebraicGeometry.Etale p)
      (h : pullback p f ⟶ U), h ≫ g = pullback.snd p f ∧ u ∈ Set.range h := by
  obtain ⟨_, ⟨(Y₀ : Y.Opens), hY₀, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g u))) isOpen_univ
  have hX₀ : IsAffineOpen (f ⁻¹ᵁ Y₀) := hY₀.preimage f
  obtain ⟨_, ⟨(U₀ : U.Opens), hU₀, rfl⟩, hu, hle⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (show u ∈ g ⁻¹ᵁ (f ⁻¹ᵁ Y₀) from hy)
      (g ⁻¹ᵁ (f ⁻¹ᵁ Y₀)).isOpen
  have : IsAffine (↑(f ⁻¹ᵁ Y₀) : Scheme.{u}) := hX₀
  have : IsAffine (↑Y₀ : Scheme.{u}) := hY₀
  have : IsAffine (↑U₀ : Scheme.{u}) := hU₀
  obtain ⟨W, _, p₀, _, h₀, hh₀, ⟨w₀, hw₀⟩⟩ :=
    propertyC_of_isAffine (f ∣_ Y₀) (g.resLE (f ⁻¹ᵁ Y₀) U₀ hle) ⟨u, hu⟩
  have H := (IsPullback.of_hasPullback p₀ (f ∣_ Y₀)).paste_vert (isPullback_morphismRestrict f Y₀)
  refine ⟨W, inferInstance, p₀ ≫ Y₀.ι, inferInstance, H.isoPullback.inv ≫ h₀ ≫ U₀.ι, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← Scheme.Hom.resLE_comp_ι g hle, ← Category.assoc h₀,
      hh₀, ← Category.assoc, Category.assoc, H.isoPullback_inv_snd]
  · refine ⟨H.isoPullback.hom w₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id_assoc, Scheme.Hom.comp_apply, hw₀]
    rfl

end General

end AlgebraicGeometry
