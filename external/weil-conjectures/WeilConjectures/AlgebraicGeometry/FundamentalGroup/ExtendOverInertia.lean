/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DecompositionGroup
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FrobeniusRestriction
public import WeilConjectures.Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Covers on which inertia acts trivially extend over the point

Let `j : U ⟶ C` be an open immersion into an integral scheme, `z` a closed point of `C` outside
`U`, and `W` an affine open neighbourhood of `z` with `W ∩ U = D(π)` for some `π ∈ Γ(C, W)`. A
finite étale `U`-scheme `Z` on whose generic geometric fibre the inertia group at `z` acts
trivially extends to a finite étale scheme over `U ∪ W`
(`AlgebraicGeometry.Scheme.FiniteEtale.exists_pullback_iso_of_forall_inertia`): the
normalization `N` of `C` in `Z` restricts to `Z` over `U`, and over `W` it is the spectrum of the
integral closure of `Γ(C, W)` in `Γ(Z, f⁻¹ W)`, which is finite étale by
`Ideal.etale_integralClosure_of_forall_inertia`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X U C : Scheme.{u}} (g : X ⟶ U) (j : U ⟶ C) [IsOpenImmersion j] [IsIntegralHom g]
  [QuasiCompact (g ≫ j)] [QuasiSeparated (g ≫ j)]

instance : IsIntegralHom (pullback.snd (g ≫ j) j) := by
  have h : pullback.snd (g ≫ j) j = pullback.fst (g ≫ j) j ≫ g := by
    rw [← cancel_mono j, Category.assoc, ← pullback.condition]
  rw [h]
  infer_instance

/-- The normalization of `C` in an integral `U`-scheme `X`, restricted to the open `U`, is `X`. -/
noncomputable def pullbackFromNormalizationIso : pullback (g ≫ j).fromNormalization j ≅ X :=
  (asIso ((g ≫ j).normalizationPullback j)).symm ≪≫
    (asIso (pullback.snd (g ≫ j) j).toNormalization).symm ≪≫ asIso (pullback.fst (g ≫ j) j)

@[reassoc (attr := simp)]
lemma pullbackFromNormalizationIso_hom_comp :
    (pullbackFromNormalizationIso g j).hom ≫ g = pullback.snd _ _ := by
  have h : pullback.fst (g ≫ j) j ≫ g = pullback.snd (g ≫ j) j := by
    rw [← cancel_mono j, Category.assoc, pullback.condition]
  simp only [pullbackFromNormalizationIso, Iso.trans_hom, Iso.symm_hom, asIso_hom,
    Category.assoc, asIso_inv, h, IsIso.inv_comp_eq]
  rw [normalizationPullback_snd, toNormalization_fromNormalization]

end Scheme.Hom

/-- A ring-hom property of `f ∣_ U`, for `U` affine with affine preimage, is that of `f.app U`. -/
lemma morphismRestrict_appTop_iff {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hQ : RingHom.RespectsIso Q) {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    Q (f ∣_ U).appTop.hom ↔ Q (f.app U).hom := by
  rw [morphismRestrict_appTop]
  refine (hQ.cancel_right_isIso (f.app (U.ι ''ᵁ ⊤)) _).trans ?_
  have h : U.ι ''ᵁ ⊤ = U := Scheme.Opens.ι_image_top U
  have : ∀ V : Y.Opens, V = U → (Q (f.app V).hom ↔ Q (f.app U).hom) := by
    rintro V rfl
    rfl
  exact this _ h

/-- A point `Spec Ω ⟶ X` landing in an affine open `V` comes from a ring map `Γ(X, V) ⟶ Ω`. -/
lemma IsAffineOpen.exists_specMap_comp_fromSpec {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {Ω : Type u} [CommRing Ω] (t : Spec (.of Ω) ⟶ X)
    (ht : Set.range t.base ⊆ V) :
    ∃ ψ : Γ(X, V) ⟶ CommRingCat.of Ω, Spec.map ψ ≫ hV.fromSpec = t := by
  let t' := IsOpenImmersion.lift V.ι t (by rwa [Scheme.Opens.range_ι])
  refine ⟨Spec.preimage (t' ≫ hV.isoSpec.hom), ?_⟩
  rw [Spec.map_preimage, ← hV.isoSpec_inv_ι, Category.assoc, hV.isoSpec.hom_inv_id_assoc]
  exact IsOpenImmersion.lift_fac _ _ _

/-- The generic point of an integral scheme factors through every nonempty affine open. -/
lemma IsAffineOpen.fromSpecFunctionField_eq {X : Scheme.{u}} [IsIntegral X] {W : X.Opens}
    (hW : IsAffineOpen W) [Nonempty W] :
    X.fromSpecFunctionField = Spec.map (X.germToFunctionField W) ≫ hW.fromSpec := by
  have hgen : genericPoint X ∈ W := by
    obtain ⟨⟨w, hw⟩⟩ := (inferInstance : Nonempty W)
    exact ((genericPoint_spec X).specializes (Set.mem_univ w)).mem_open W.isOpen hw
  change X.fromSpecStalk (genericPoint X) = _
  rw [← hW.fromSpecStalk_eq_fromSpecStalk hgen]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Over an affine open `W`, the normalization of `C` in `X` is finite étale as soon as the integral
closure of `Γ(C, W)` in `Γ(X, f⁻¹ W)` is finite étale over `Γ(C, W)`. -/
lemma isFinite_and_etale_fromNormalization_restrict {X C : Scheme.{u}} (f : X ⟶ C)
    [QuasiCompact f] [QuasiSeparated f] {W : C.Opens} (hW : IsAffineOpen W)
    (hfin : letI := (f.app W).hom.toAlgebra
      Module.Finite Γ(C, W) (integralClosure Γ(C, W) Γ(X, f ⁻¹ᵁ W)))
    (het : letI := (f.app W).hom.toAlgebra
      Algebra.Etale Γ(C, W) (integralClosure Γ(C, W) Γ(X, f ⁻¹ᵁ W))) :
    IsFinite (f.fromNormalization ∣_ W) ∧ Etale (f.fromNormalization ∣_ W) := by
  let := (f.app W).hom.toAlgebra
  have : IsAffine W := hW
  have : IsAffine (f.fromNormalization ⁻¹ᵁ W) := hW.preimage f.fromNormalization
  have happ := Scheme.Hom.fromNormalization_app f hW
  constructor
  · rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
    refine ⟨inferInstance, ?_⟩
    rw [morphismRestrict_appTop_iff RingHom.finite_respectsIso, happ]
    exact (RingHom.finite_respectsIso.cancel_right_isIso (CommRingCat.ofHom (algebraMap _ _))
      (Scheme.Hom.normalizationObjIso f hW).inv).2 (RingHom.finite_algebraMap.2 hfin)
  · rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    rw [morphismRestrict_appTop_iff RingHom.Etale.respectsIso, happ]
    exact (RingHom.Etale.respectsIso.cancel_right_isIso (CommRingCat.ofHom (algebraMap _ _))
      (Scheme.Hom.normalizationObjIso f hW).inv).2 (RingHom.etale_algebraMap.2 het)

namespace Scheme.FiniteEtale

variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] {W : C.Opens}

/-- **Extension of a cover over an open containing the points where the normalization is finite
étale.** If the normalization `N ⟶ C` of `C` in a finite étale `U`-scheme `Z` is finite and étale
over an open `W`, then `Z` extends to a finite étale scheme over `V = U ∪ W`. -/
instance (Z : U.FiniteEtale) : QuasiCompact (Z.obj.hom ≫ j) :=
  have : IsFinite Z.obj.hom := Z.property
  inferInstance

instance (Z : U.FiniteEtale) : QuasiSeparated (Z.obj.hom ≫ j) :=
  have : IsFinite Z.obj.hom := Z.property
  inferInstance

instance (Z : U.FiniteEtale) : IsIntegralHom Z.obj.hom :=
  have : IsFinite Z.obj.hom := Z.property
  inferInstance

set_option backward.isDefEq.respectTransparency.types false in
theorem exists_pullback_iso_of_fromNormalization (Z : U.FiniteEtale)
    (hW : IsFinite ((Z.obj.hom ≫ j).fromNormalization ∣_ W) ∧
      Etale ((Z.obj.hom ≫ j).fromNormalization ∣_ W))
    (V : C.Opens) (hjV : j.opensRange ≤ V) (hWV : W ≤ V) (hV : V ≤ j.opensRange ⊔ W) :
    ∃ Z' : V.toScheme.FiniteEtale, Nonempty ((pullback (IsOpenImmersion.lift V.ι j (by
      rw [Scheme.Opens.range_ι]; exact hjV))).obj Z' ≅ Z) := by
  have : IsFinite Z.obj.hom := Z.property
  have : Etale Z.obj.hom := Z.obj.prop
  set pN := (Z.obj.hom ≫ j).fromNormalization
  let e := Scheme.Hom.pullbackFromNormalizationIso Z.obj.hom j
  -- over `U` the normalization is `Z`
  have earr : Arrow.mk (pN ∣_ j.opensRange) ≅ Arrow.mk Z.obj.hom :=
    morphismRestrictOpensRange pN j ≪≫ Arrow.isoMk e (Iso.refl _) (by
      simp [e, pN])
  have hU : IsFinite (pN ∣_ j.opensRange) ∧ Etale (pN ∣_ j.opensRange) :=
    ⟨(MorphismProperty.arrow_mk_iso_iff _ earr).2 inferInstance,
      (MorphismProperty.arrow_mk_iso_iff _ earr).2 inferInstance⟩
  -- over `V`
  have hres (O : C.Opens) (hO : O ≤ V) :
      Arrow.mk ((pN ∣_ V) ∣_ V.ι ⁻¹ᵁ O) ≅ Arrow.mk (pN ∣_ O) := by
    refine morphismRestrictRestrict pN V (V.ι ⁻¹ᵁ O) ≪≫ morphismRestrictEq pN ?_
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hO]
  have hcov : ⨆ i : Bool, (if i then V.ι ⁻¹ᵁ j.opensRange else V.ι ⁻¹ᵁ W) = ⊤ := by
    rw [iSup_bool_eq]
    refine top_le_iff.1 fun x _ ↦ ?_
    have hx : V.ι x ∈ j.opensRange ⊔ W := hV (by simp)
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr hx
  have hVP : IsFinite (pN ∣_ V) ∧ Etale (pN ∣_ V) := by
    constructor <;>
    · refine IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov fun i ↦ ?_
      cases i
      · exact (MorphismProperty.arrow_mk_iso_iff _ (hres W hWV)).2
          (by first | exact hW.1 | exact hW.2)
      · exact (MorphismProperty.arrow_mk_iso_iff _ (hres _ hjV)).2
          (by first | exact hU.1 | exact hU.2)
  -- the extension
  have earrV : Arrow.mk (pN ∣_ V) ≅ Arrow.mk (pullback.snd pN V.ι) :=
    morphismRestrictEq pN (Scheme.Opens.opensRange_ι V).symm ≪≫ morphismRestrictOpensRange pN V.ι
  have hP : IsFinite (pullback.snd pN V.ι) ∧ Etale (pullback.snd pN V.ι) :=
    ⟨(MorphismProperty.arrow_mk_iso_iff _ earrV).1 hVP.1,
      (MorphismProperty.arrow_mk_iso_iff _ earrV).1 hVP.2⟩
  let Z' : V.toScheme.FiniteEtale :=
    ⟨MorphismProperty.Over.mk ⊤ (pullback.snd pN V.ι) hP.2, hP.1⟩
  set jV := IsOpenImmersion.lift V.ι j (by rw [Scheme.Opens.range_ι]; exact hjV)
  have hjV' : jV ≫ V.ι = j := IsOpenImmersion.lift_fac _ _ _
  let eL : ((pullback jV).obj Z').obj.left ≅ Z.obj.left :=
    pullbackLeftPullbackSndIso pN V.ι jV ≪≫ pullback.congrHom rfl hjV' ≪≫ e
  refine ⟨Z', ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk eL ?_)⟩⟩
  change eL.hom ≫ Z.obj.hom = pullback.snd (pullback.snd pN V.ι) jV
  simp only [eL, e, Iso.trans_hom, Category.assoc,
    Scheme.Hom.pullbackFromNormalizationIso_hom_comp, pullback.congrHom_hom]
  rw [pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd pN V.ι jV

section Inertia

variable [IsIntegral C] [Nonempty U]

omit [QuasiCompact j] in
lemma range_fromSpecFunctionField_subset :
    Set.range C.fromSpecFunctionField.base ⊆ Set.range j.base := by
  rintro _ ⟨y, rfl⟩
  have hy : C.fromSpecFunctionField y = genericPoint C := by
    have : C.fromSpecFunctionField y ⤳ genericPoint C := by
      have := Scheme.range_fromSpecStalk (X := C) (x := genericPoint C)
      have hmem : C.fromSpecFunctionField y ∈ Set.range (C.fromSpecStalk (genericPoint C)).base :=
        ⟨y, rfl⟩
      rw [this] at hmem
      exact hmem
    exact (this.antisymm ((genericPoint_spec C).specializes (Set.mem_univ _))).eq
  rw [hy]
  obtain ⟨u⟩ := (inferInstance : Nonempty U)
  exact ((genericPoint_spec C).specializes (Set.mem_univ (j u))).mem_open
    j.isOpenEmbedding.isOpen_range ⟨u, rfl⟩

omit [QuasiCompact j] in
/-- The generic point `Spec k(C) ⟶ U` of a nonempty open `U` of an integral scheme `C`. -/
noncomputable def genericPointLift : Spec (.of C.functionField) ⟶ U :=
  IsOpenImmersion.lift j C.fromSpecFunctionField (range_fromSpecFunctionField_subset j)

omit [QuasiCompact j] in
@[reassoc (attr := simp)]
lemma genericPointLift_comp : genericPointLift j ≫ j = C.fromSpecFunctionField :=
  IsOpenImmersion.lift_fac _ _ _

variable (hW : IsAffineOpen W) [Nonempty W] [IsDedekindDomain Γ(C, W)]
  (ϖ : Γ(C, W)) (hϖ : ϖ ≠ 0) (hWU : j.opensRange ⊓ W = C.basicOpen ϖ)
  (m : Ideal Γ(C, W)) [m.IsMaximal] [PerfectField m.ResidueField]
  (hϖm : ∀ p : Ideal Γ(C, W), p.IsPrime → ϖ ∈ p → p = m)
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [Algebra Γ(C, W) Ω]
  [IsScalarTower Γ(C, W) C.functionField Ω] [IsGalois C.functionField Ω] [IsSepClosed Ω]
  (Q : Ideal (integralClosure Γ(C, W) Ω)) [Q.IsMaximal] [Q.LiesOver m]

include hW ϖ hϖ hWU m hϖm in
/-- **The normalization of a cover with trivial inertia is finite étale at the point.** -/
theorem isFinite_and_etale_restrict_of_forall_inertia (Z : U.FiniteEtale)
    [IsIntegral Z.obj.left] [ConnectedSpace U]
    (hZ : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω),
      ∀ t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj Z,
        (galoisToAut (genericPointLift j) σ).asIso.hom.app Z t = t) :
    IsFinite ((Z.obj.hom ≫ j).fromNormalization ∣_ W) ∧
      Etale ((Z.obj.hom ≫ j).fromNormalization ∣_ W) := by
  have : IsFinite Z.obj.hom := Z.property
  have : Etale Z.obj.hom := Z.obj.prop
  let f := Z.obj.hom ≫ j
  let A := Γ(Z.obj.left, f ⁻¹ᵁ W)
  let _ : Algebra Γ(C, W) A := (f.app W).hom.toAlgebra
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  -- the open `f⁻¹ W = f⁻¹ D(ϖ)` is affine
  have hDϖ : C.basicOpen ϖ ≤ j.opensRange := by
    rw [← hWU]
    exact inf_le_left
  have hfW : f ⁻¹ᵁ W = f ⁻¹ᵁ C.basicOpen ϖ := by
    ext x
    change f x ∈ W ↔ f x ∈ C.basicOpen ϖ
    rw [← hWU]
    have hx : f x ∈ j.opensRange := ⟨Z.obj.hom x, rfl⟩
    exact ⟨fun h ↦ ⟨hx, h⟩, fun h ↦ h.2⟩
  have hjD : IsAffineOpen (j ⁻¹ᵁ C.basicOpen ϖ) :=
    (hW.basicOpen ϖ).preimage_of_isOpenImmersion j hDϖ
  have hV : IsAffineOpen (f ⁻¹ᵁ W) := by
    rw [hfW]
    exact hjD.preimage Z.obj.hom
  -- `R' = Γ(C, D(ϖ))`, over which `A` is finite étale
  let R' := Γ(C, C.basicOpen ϖ)
  let _ : Algebra Γ(C, W) R' :=
    (C.presheaf.map (homOfLE (C.basicOpen_le ϖ)).op).hom.toAlgebra
  have : IsLocalization.Away ϖ R' :=
    hW.isLocalization_of_eq_basicOpen ϖ (homOfLE (C.basicOpen_le ϖ)) rfl
  let _ : Algebra R' A := (f.appLE (C.basicOpen ϖ) (f ⁻¹ᵁ W) hfW.le).hom.toAlgebra
  have : IsScalarTower Γ(C, W) R' A := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change (f.app W) r = (f.appLE _ _ hfW.le) ((C.presheaf.map _) r)
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.app_eq_appLE]
  have : Algebra.Etale R' A := by
    rw [← RingHom.etale_algebraMap]
    exact HasRingHomProperty.appLE (P := @Etale) f inferInstance ⟨_, hW.basicOpen ϖ⟩ ⟨_, hV⟩
      hfW.le
  have : Module.Finite R' A := by
    rw [← RingHom.finite_algebraMap]
    change (f.appLE (C.basicOpen ϖ) (f ⁻¹ᵁ W) hfW.le).hom.Finite
    have : IsIso (j.app (C.basicOpen ϖ)) := Scheme.Hom.isIso_app j _ hDϖ
    rw [Scheme.Hom.comp_appLE, CommRingCat.hom_comp]
    refine RingHom.Finite.comp ?_ (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (j.app (C.basicOpen ϖ))).2)
    have hi : Z.obj.hom ⁻¹ᵁ (j ⁻¹ᵁ C.basicOpen ϖ) = f ⁻¹ᵁ W := by
      rw [hfW]
      rfl
    have h2 : Z.obj.hom.appLE (j ⁻¹ᵁ C.basicOpen ϖ) (f ⁻¹ᵁ W) hi.ge =
        Z.obj.hom.app _ ≫ Z.obj.left.presheaf.map (eqToHom hi.symm).op := by
      change Z.obj.hom.app _ ≫ Z.obj.left.presheaf.map _ = _
      congr 2
    rw [h2, CommRingCat.hom_comp]
    refine RingHom.Finite.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Z.obj.left.presheaf.map (eqToHom hi.symm).op)).2) ?_
    exact IsFinite.finite_app Z.obj.hom _ hjD
  -- the generic geometric point factors through `W`
  have hgen : pointOfAlgebra Ω (genericPointLift j) ≫ j =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) Ω)) ≫ hW.fromSpec := by
    rw [Category.assoc, genericPointLift_comp, hW.fromSpecFunctionField_eq, ← Category.assoc,
      ← Spec.map_comp]
    congr 2
    ext r
    exact (IsScalarTower.algebraMap_apply Γ(C, W) C.functionField Ω r).symm
  -- `Γ(C, W)`-algebra maps `A → Ω` give points of `Z` over the generic geometric point
  have hpt (ψ : A →ₐ[Γ(C, W)] Ω) :
      (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ≫ Z.obj.hom =
        pointOfAlgebra Ω (genericPointLift j) := by
    rw [← cancel_mono j, hgen, Category.assoc, Category.assoc]
    change Spec.map _ ≫ hV.fromSpec ≫ f = _
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hW hV le_rfl, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext a
    change ψ ((f.appLE W (f ⁻¹ᵁ W) le_rfl) a) = _
    rw [Scheme.Hom.appLE_eq_app]
    exact ψ.commutes a
  obtain ⟨t₀⟩ := nonempty_fiber_of_nonempty (pointOfAlgebra Ω (genericPointLift j)) Z
    inferInstance
  have ht₀ : t₀.left ≫ f = Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) Ω)) ≫ hW.fromSpec := by
    rw [← hgen]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ j) (fiber_left_comp _ t₀))
  have hrange (y : Spec (.of Ω)) : t₀.left y ∈ f ⁻¹ᵁ W := by
    change (t₀.left ≫ f) y ∈ W
    rw [ht₀, Scheme.Hom.comp_apply, ← SetLike.mem_coe, ← hW.range_fromSpec]
    exact Set.mem_range_self _
  obtain ⟨y₀⟩ := (inferInstance : Nonempty (Spec (.of Ω)))
  have : Nonempty (f ⁻¹ᵁ W) := ⟨⟨t₀.left y₀, hrange y₀⟩⟩
  obtain ⟨φ₀, hφ₀⟩ := hV.exists_specMap_comp_fromSpec t₀.left (by rintro _ ⟨y, rfl⟩; exact hrange y)
  have hφ₀R : f.app W ≫ φ₀ = CommRingCat.ofHom (algebraMap Γ(C, W) Ω) := by
    apply Spec.map_injective
    rw [← cancel_mono hW.fromSpec, ← ht₀, ← hφ₀, Spec.map_comp, Category.assoc,
      Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec f hW hV le_rfl]
    exact (Category.assoc _ _ _).symm
  let ψ₀ : A →ₐ[Γ(C, W)] Ω :=
    { φ₀.hom with commutes' := fun r ↦ RingHom.congr_fun (congrArg CommRingCat.Hom.hom hφ₀R) r }
  -- inertia fixes the ring maps `A → Ω`
  have hI : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω), ∀ (ψ : A →ₐ[Γ(C, W)] Ω) (x : A),
      σ (ψ x) = ψ x := by
    intro σ hσ ψ x
    let t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj Z :=
      Over.homMk (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) (hpt ψ)
    have h := congrArg Over.Hom.left (hZ σ hσ t)
    rw [galoisToAut_hom_app_left] at h
    change Spec.map _ ≫ Spec.map _ ≫ hV.fromSpec = Spec.map _ ≫ hV.fromSpec at h
    rw [← Category.assoc, ← Spec.map_comp, cancel_mono] at h
    have := Spec.map_injective h
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) x
  obtain ⟨het, hfin⟩ := Ideal.etale_integralClosure_of_forall_inertia (K := C.functionField) m Q ϖ
    (R' := R') hϖ hϖm ψ₀ hI
  exact isFinite_and_etale_fromNormalization_restrict f hW hfin het

section Open

variable (V : C.Opens) (hjV : j.opensRange ≤ V) (hWV : W ≤ V)

/-- The open immersion `U ⟶ V` into an open containing `U`. -/
noncomputable abbrev toOpen : U ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι j (by rw [Scheme.Opens.range_ι]; exact hjV)

/-- The open immersion `Spec Γ(C, W) ⟶ V` of an affine open contained in `V`. -/
noncomputable abbrev affineToOpen : Spec Γ(C, W) ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι hW.fromSpec (by rw [Scheme.Opens.range_ι, hW.range_fromSpec]; exact hWV)

include hW hjV hWV in
omit [QuasiCompact j] [Algebra Γ(C, W) Ω] [IsScalarTower Γ(C, W) C.functionField Ω] [IsSepClosed Ω]
  [IsDedekindDomain Γ(C, W)] [IsGalois C.functionField Ω] in
/-- The generic geometric point of `U`, mapped to `V`, is the generic geometric point through
`Spec Γ(C, W)`. -/
lemma pointOfAlgebra_genericPointLift_comp_toOpen :
    pointOfAlgebra Ω (genericPointLift j) ≫ toOpen j V hjV =
      pointOfAlgebra Ω (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, W) C.functionField)) ≫
        affineToOpen hW V hWV) := by
  rw [← cancel_mono V.ι]
  simp only [Category.assoc, IsOpenImmersion.lift_fac]
  rw [genericPointLift_comp, hW.fromSpecFunctionField_eq, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  rfl

include hW hjV hWV in
omit [QuasiCompact j] [IsDedekindDomain Γ(C, W)] in
/-- **Inertia acts trivially on covers coming from `V`.** -/
lemma galoisToAut_hom_app_pullback_eq_of_mem_inertia [ConnectedSpace V]
    {σ : Ω ≃ₐ[C.functionField] Ω} (hσ : σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω))
    (P : V.toScheme.FiniteEtale)
    (t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj ((pullback (toOpen j V hjV)).obj P)) :
    (galoisToAut (genericPointLift j) σ).asIso.hom.app _ t = t := by
  have : IsFractionRing Γ(C, W) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C W hW
  have h := pointOfAlgebra_genericPointLift_comp_toOpen j hW V hjV hWV (Ω := Ω)
  let e := pullbackFiberIso (toOpen j V hjV) (pointOfAlgebra Ω (genericPointLift j)) ≪≫
    fiberIsoOfIso (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp, h])
  apply ((ConcreteCategory.isIso_iff_bijective (e.hom.app P)).1 inferInstance).1
  have key := galoisToAut_hom_app_eq_of_mem_inertia (K := C.functionField) (Ω := Ω)
    (affineToOpen hW V hWV) Q hσ P (e.hom.app P t)
  rw [← key]
  apply fiber_ext
  simp only [e, Iso.trans_hom, NatTrans.comp_app, ConcreteCategory.comp_apply]
  simp only [fiberIsoOfIso_hom_app_left, pullbackFiberIso_hom_app_left, galoisToAut_hom_app_left]
  rfl

include hW ϖ hϖ hWU m hϖm hjV hWV in
/-- **Covers with trivial inertia extend over the point.** -/
theorem exists_pullback_toOpen_iso_of_forall_inertia (Z : U.FiniteEtale)
    [IsIntegral Z.obj.left] [ConnectedSpace U] (hV : V ≤ j.opensRange ⊔ W)
    (hZ : ∀ σ ∈ Q.inertia (Ω ≃ₐ[C.functionField] Ω),
      ∀ t : (fiber (pointOfAlgebra Ω (genericPointLift j))).obj Z,
        (galoisToAut (genericPointLift j) σ).asIso.hom.app Z t = t) :
    ∃ Z' : V.toScheme.FiniteEtale, Nonempty ((pullback (toOpen j V hjV)).obj Z' ≅ Z) :=
  exists_pullback_iso_of_fromNormalization j Z
    (isFinite_and_etale_restrict_of_forall_inertia j hW ϖ hϖ hWU m hϖm Q Z hZ) V hjV hWV hV

end Open

end Inertia

end Scheme.FiniteEtale

namespace Etale

variable {C U : Scheme.{u}} (j : U ⟶ C) [IsOpenImmersion j] [IsIntegral C] [Nonempty U]
  {Ω : Type u} [Field Ω] [Algebra C.functionField Ω] [IsSepClosed Ω]

/-- The generic geometric point `η : Spec Ω ⟶ U` of a nonempty open `U` of an integral scheme
`C`, for a separably closed extension `Ω` of the function field of `C`. -/
noncomputable abbrev genericGeometricPoint : Spec (.of Ω) ⟶ U :=
  Scheme.FiniteEtale.pointOfAlgebra Ω (Scheme.FiniteEtale.genericPointLift j)

end Etale

end AlgebraicGeometry
