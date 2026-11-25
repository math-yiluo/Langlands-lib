/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# The deformation to the normal cone of the zero section of affine space

For the standard pair `(𝔸^n_B ⟶ B, 0)`, the deformation space of the zero section is
`𝔸^n_{𝔸¹_B} = 𝔸^n_B ×_B 𝔸¹_B`, with coordinates `u_k = x_k / t`, so that `x_k = t u_k`. This is
blueprint `prose-09-12` (4).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.deformationSpaceToAffineSpace`: the morphism
  `D_0 𝔸^n_B ⟶ 𝔸^n_{𝔸¹_B}` given by the coordinates `u_k = x_k t⁻¹`, with `x_k = t u_k`;
- `AlgebraicGeometry.Scheme.Hom.isIso_deformationSpaceToAffineSpace`: it is an isomorphism;
- `AlgebraicGeometry.Scheme.Hom.isPullback_deformationSpaceMap`: the deformation space of the
  standard pair commutes with base change in `B` (blueprint `prose-09-12` (5)).
-/

@[expose] public section

universe u

open CategoryTheory Limits LaurentPolynomial

namespace AlgebraicGeometry.AffineSpace

variable (m : Type u) (S : Scheme.{u})

/-- The coordinate `x_k` of `𝔸^m_S` restricted to an open. -/
noncomputable def coordRes' (O : (𝔸(m; S)).Opens) (k : m) : Γ(𝔸(m; S), O) :=
  (𝔸(m; S)).presheaf.map (homOfLE le_top).op (coord S k)

lemma opensRange_map_ι (W : S.Opens) :
    (map m W.ι).opensRange = (𝔸(m; S) ↘ S) ⁻¹ᵁ W := by
  ext x
  have := Scheme.Pullback.range_fst (𝔸(m; S) ↘ S) W.ι
  have h : Set.range (map m W.ι) = Set.range (pullback.fst (𝔸(m; S) ↘ S) W.ι) := by
    rw [← (isPullback_map (n := m) W.ι).isoPullback_hom_fst, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso
        (isPullback_map (n := m) W.ι).isoPullback.hom.base).2, Set.image_univ]
  change x ∈ Set.range _ ↔ _
  rw [h, this, Scheme.Opens.range_ι]
  rfl

lemma opensRange_map {X : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] :
    (map m f).opensRange = (𝔸(m; S) ↘ S) ⁻¹ᵁ f.opensRange := by
  ext x
  have := Scheme.Pullback.range_fst (𝔸(m; S) ↘ S) f
  have h : Set.range (map m f) = Set.range (pullback.fst (𝔸(m; S) ↘ S) f) := by
    rw [← (isPullback_map (n := m) f).isoPullback_hom_fst, Scheme.Hom.comp_base,
      TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso
        (isPullback_map (n := m) f).isoPullback.hom.base).2, Set.image_univ]
  change x ∈ Set.range _ ↔ _
  rw [h, this]
  rfl

lemma preimage_preimage_map_ι (W : S.Opens) :
    map m W.ι ⁻¹ᵁ ((𝔸(m; S) ↘ S) ⁻¹ᵁ W) = ⊤ := by
  rw [← opensRange_map_ι, Scheme.Hom.preimage_opensRange]

lemma bijective_appLE_map_ι (W : S.Opens) :
    Function.Bijective ((map m W.ι).appLE ((𝔸(m; S) ↘ S) ⁻¹ᵁ W) ⊤
      (preimage_preimage_map_ι m S W).ge) := by
  have : IsIso ((map m W.ι).app ((𝔸(m; S) ↘ S) ⁻¹ᵁ W)) :=
    Scheme.Hom.isIso_app _ _ (opensRange_map_ι m S W).ge
  have : IsIso ((𝔸(m; W)).presheaf.map
      (homOfLE (preimage_preimage_map_ι m S W).ge : (⊤ : (𝔸(m; W)).Opens) ⟶ _).op) := by
    rw [show (homOfLE (preimage_preimage_map_ι m S W).ge : (⊤ : (𝔸(m; W)).Opens) ⟶ _) =
      eqToHom (preimage_preimage_map_ι m S W).symm from rfl]
    infer_instance
  rw [Scheme.Hom.appLE]
  exact ConcreteCategory.bijective_of_isIso _

/-- **Sections of affine space over an affine open of the base.** For an affine open `W ⊆ S`,
`Γ(𝔸^m_S, p⁻¹ W) = Γ(S, W)[x_1, …, x_m]`. -/
theorem bijective_eval₂Hom_app_preimage {W : S.Opens} (hW : IsAffineOpen W) :
    Function.Bijective (MvPolynomial.eval₂Hom ((𝔸(m; S) ↘ S).app W).hom
      (coordRes' m S ((𝔸(m; S) ↘ S) ⁻¹ᵁ W))) := by
  have : IsAffine W.toScheme := hW
  set A := (map m W.ι).appLE ((𝔸(m; S) ↘ S) ⁻¹ᵁ W) ⊤ (preimage_preimage_map_ι m S W).ge
  set θ := W.ι.appLE W ⊤ W.ι_preimage_self.ge
  have hθ : Function.Bijective θ.hom := ConcreteCategory.bijective_of_isIso _
  have hE : Function.Bijective (MvPolynomial.eval₂Hom (𝔸(m; W) ↘ W).appTop.hom (coord W)) := by
    have h := isoOfIsAffine_hom_appTop (n := m) (S := W.toScheme)
    have : MvPolynomial.eval₂Hom (𝔸(m; W) ↘ W).appTop.hom (coord W) =
        ((Scheme.ΓSpecIso _).inv ≫ (isoOfIsAffine m W.toScheme).hom.appTop).hom := by
      rw [h, Iso.inv_hom_id_assoc, CommRingCat.hom_ofHom]
    rw [this]
    exact ConcreteCategory.bijective_of_isIso _
  have hmap : Function.Bijective (MvPolynomial.map (σ := m) θ.hom) :=
    ⟨MvPolynomial.map_injective _ hθ.1, MvPolynomial.map_surjective _ hθ.2⟩
  have key : A.hom.comp (MvPolynomial.eval₂Hom ((𝔸(m; S) ↘ S).app W).hom
      (coordRes' m S ((𝔸(m; S) ↘ S) ⁻¹ᵁ W))) =
      (MvPolynomial.eval₂Hom (𝔸(m; W) ↘ W).appTop.hom (coord W)).comp
        (MvPolynomial.map θ.hom) := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun k ↦ ?_
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE,
        Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_congr_hom (map_over (n := m) W.ι) _ _ _
          (by simp), ← Scheme.Hom.appLE_comp_appLE (𝔸(m; W.toScheme) ↘ W.toScheme) W.ι W ⊤ ⊤
          W.ι_preimage_self.ge le_top, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X, coordRes']
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
      have := map_appTop_coord (n := m) W.ι k
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at this
      exact this
  have hA : Function.Bijective A.hom := bijective_appLE_map_ι m S W
  rw [← Function.Bijective.of_comp_iff' hA, ← RingHom.coe_comp, key, RingHom.coe_comp]
  exact hE.comp hmap
end AlgebraicGeometry.AffineSpace

namespace AlgebraicGeometry.Scheme.Hom

open AffineZariskiSite

section

variable {V B' : Scheme.{u}} (g : V ⟶ B') (s : B' ⟶ V)

/-- `g̃ : D_s V ⟶ 𝔸¹_B` lies over `D_s V ⟶ V ⟶ B`. -/
@[reassoc]
lemma deformationSpaceProj_over :
    deformationSpaceProj g s ≫ 𝔸(ULift.{u} (Fin 1); B') ↘ B' =
      (relativeGluingData s.ker.coequifibered_toReesPresheaf).toBase ≫ g := by
  rw [deformationSpaceProj, Category.assoc, Category.assoc, AffineSpace.map_over,
    polynomialSpecToAffineSpace_over_assoc, IdealSheafData.deformationSpaceToPolynomialSpec,
    relativeGluingMap_toBase_assoc _ _ _ s.ker.toPolynomialPresheaf_comp_polynomialToRees]

lemma opensRange_affineLineChart {W : B'.Opens} (hW : IsAffineOpen W) :
    (affineLineChart hW).opensRange = (𝔸(ULift.{u} (Fin 1); B') ↘ B') ⁻¹ᵁ W := by
  have := isIso_homOfVector_specPolynomial Γ(B', W)
  have e : affineLineChart hW = AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom Polynomial.C))
      (fun _ ↦ (ΓSpecIso (.of (Polynomial Γ(B', W)))).inv Polynomial.X) ≫
        AffineSpace.map _ hW.fromSpec := by
    rw [affineLineChart, ← AffineSpace.homOfVector_map]
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_opensRange, e, ← Scheme.Hom.coe_opensRange, opensRange_comp_of_isIso,
    AffineSpace.opensRange_map, hW.opensRange_fromSpec]

end

variable (n : Type u) (B : Scheme.{u})

/-- The coordinate `x_k` of `𝔸^n_B`, restricted to an affine open. -/
noncomputable def coordRes (U : (𝔸(n; B)).AffineZariskiSite) (k : n) : Γ(𝔸(n; B), U.1) :=
  (𝔸(n; B)).presheaf.map (homOfLE le_top).op (AffineSpace.coord B k)

lemma coordRes_mem (U : (𝔸(n; B)).AffineZariskiSite) (k : n) :
    coordRes n B U k ∈ (AffineSpace.zeroSection n B).ker.siteIdeal U := by
  rw [IdealSheafData.siteIdeal, Scheme.Hom.ker_apply, RingHom.mem_ker, coordRes,
    ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
  change (B.presheaf.map _).hom ((AffineSpace.zeroSection n B).appTop _) = 0
  rw [AffineSpace.zeroSection_appTop_coord, map_zero]

/-- The coordinate `u_k = x_k t⁻¹` on the chart of the deformation space over `U`. -/
noncomputable def uCoord (U : (𝔸(n; B)).AffineZariskiSite) (k : n) :
    (AffineSpace.zeroSection n B).ker.reesPresheaf.obj (.op U) :=
  ⟨LaurentPolynomial.C (coordRes n B U k) * T (-1),
    Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (coordRes_mem n B U k)⟩

lemma map_uCoord {U U' : (𝔸(n; B)).AffineZariskiSite} (i : U ⟶ U') (k : n) :
    ((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op).hom (uCoord n B U' k) =
      uCoord n B U k := by
  apply Subtype.ext
  change LaurentPolynomial.mapRingHom _ (LaurentPolynomial.C (coordRes n B U' k) * T (-1)) =
    LaurentPolynomial.C (coordRes n B U k) * T (-1)
  rw [map_mul, LaurentPolynomial.mapRingHom_C, LaurentPolynomial.mapRingHom_T]
  congr 2
  change ((𝔸(n; B)).presheaf.map _ ≫ (𝔸(n; B)).presheaf.map _).hom _ = _
  rw [← Functor.map_comp]
  rfl

/-- The chart `Spec Γ(U)[t, I t⁻¹] ⟶ 𝔸^n_{𝔸¹_B}` of the coordinates `u_k = x_k t⁻¹`. -/
noncomputable def deformationSpaceToAffineSpaceChart (U : (𝔸(n; B)).AffineZariskiSite) :
    (relativeGluingData (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor.obj
      U ⟶ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) :=
  AffineSpace.homOfVector
    (colimit.ι (relativeGluingData
      (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
    fun k ↦ (ΓSpecIso _).inv (uCoord n B U k)

set_option backward.isDefEq.respectTransparency false in
lemma map_comp_deformationSpaceToAffineSpaceChart {U U' : (𝔸(n; B)).AffineZariskiSite}
    (i : U ⟶ U') :
    (relativeGluingData (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor.map
      i ≫ deformationSpaceToAffineSpaceChart n B U' = deformationSpaceToAffineSpaceChart n B U := by
  rw [deformationSpaceToAffineSpaceChart, deformationSpaceToAffineSpaceChart,
    AffineSpace.comp_homOfVector, ← Category.assoc, colimit.w]
  congr 1
  funext k
  have h := congr($(Scheme.ΓSpecIso_inv_naturality
    ((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op)) (uCoord n B U' k))
  refine h.symm.trans ?_
  change (ΓSpecIso _).inv (((AffineSpace.zeroSection n B).ker.reesPresheaf.map i.op).hom
    (uCoord n B U' k)) = _
  rw [map_uCoord]
  rfl

/-- **The standard pair.** The morphism `D_0 𝔸^n_B ⟶ 𝔸^n_{𝔸¹_B}` from the deformation space of
the zero section, given by the coordinates `u_k = x_k t⁻¹` over `𝔸¹_B`. -/
noncomputable def deformationSpaceToAffineSpace :
    (AffineSpace.zeroSection n B).ker.deformationSpace ⟶ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) :=
  colimit.desc _
    { pt := _
      ι := { app U := deformationSpaceToAffineSpaceChart n B U
             naturality _ _ i := (map_comp_deformationSpaceToAffineSpaceChart n B i).trans
              (Category.comp_id _).symm } }

@[reassoc (attr := simp)]
lemma ι_deformationSpaceToAffineSpace (U : (𝔸(n; B)).AffineZariskiSite) :
    colimit.ι (relativeGluingData
      (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor U ≫
      deformationSpaceToAffineSpace n B = deformationSpaceToAffineSpaceChart n B U :=
  colimit.ι_desc _ _

@[reassoc (attr := simp)]
lemma deformationSpaceToAffineSpace_over :
    deformationSpaceToAffineSpace n B ≫ 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _ =
      deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B) :=
  colimit.hom_ext fun U ↦ by
    rw [ι_deformationSpaceToAffineSpace_assoc, deformationSpaceToAffineSpaceChart,
      AffineSpace.homOfVector_over]

set_option backward.isDefEq.respectTransparency false in
lemma reesToQuotientPolynomial_comp_deformationSpaceToAffineSpace :
    relativeGluingMap (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf
      (AffineSpace.zeroSection n B).ker.coequifibered_toQuotientPolynomialAlgebra
      (AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial ≫
        deformationSpaceToAffineSpace n B =
      (relativeGluingMap (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf
        (AffineSpace.zeroSection n B).ker.coequifibered_toQuotientPolynomialAlgebra
        (AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial ≫
          deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B)) ≫
        AffineSpace.zeroSection n _ := by
  refine colimit.hom_ext fun U ↦ AffineSpace.hom_ext ?_ fun k ↦ ?_
  · simp only [Category.assoc, deformationSpaceToAffineSpace_over, AffineSpace.zeroSection_over,
      Category.comp_id]
  · conv_rhs => simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.zeroSection_appTop_coord, map_zero]
    rw [ι_relativeGluingMap_assoc, ι_deformationSpaceToAffineSpace,
      deformationSpaceToAffineSpaceChart, AffineSpace.comp_homOfVector,
      AffineSpace.homOfVector_appTop_coord, Function.comp_apply]
    have h := congr($(Scheme.ΓSpecIso_inv_naturality
      ((AffineSpace.zeroSection n B).ker.reesToQuotientPolynomial.app (.op U))) (uCoord n B U k))
    refine h.symm.trans ?_
    change (ΓSpecIso ((AffineSpace.zeroSection n B).ker.quotientPolynomialAlgebra.obj (.op U))).inv
      (Ideal.extendedReesAlgebraToPolynomial _ _ Ideal.mk_ker.ge
      ⟨_, Ideal.C_mul_T_neg_one_mem_extendedReesAlgebra (coordRes_mem n B U k)⟩) = 0
    exact (congrArg _ (Ideal.extendedReesAlgebraToPolynomial_C_mul_T_neg_one
      (I := (AffineSpace.zeroSection n B).ker.siteIdeal U) _ Ideal.mk_ker.ge
      (coordRes_mem n B U k))).trans (map_zero _)

/-- The section `s̃` of the deformation space of the zero section is the zero section of
`𝔸^n_{𝔸¹_B}` in the coordinates `u_k`. -/
lemma deformationSpaceSection_comp_deformationSpaceToAffineSpace :
    (AffineSpace.zeroSection n B).deformationSpaceSection ≫ deformationSpaceToAffineSpace n B =
      AffineSpace.zeroSection n _ := by
  rw [deformationSpaceSection, Category.assoc,
    reesToQuotientPolynomial_comp_deformationSpaceToAffineSpace, ← Category.assoc,
    ← Category.assoc, ← deformationSpaceSection,
    deformationSpaceSection_deformationSpaceProj (AffineSpace.zeroSection_over n B),
    Category.id_comp]

lemma constantCoeff_eq_zero_iff {σ R : Type*} [CommRing R] (p : MvPolynomial σ R) :
    MvPolynomial.constantCoeff p = 0 ↔ p ∈ Ideal.mvPolynomialOrigin R σ := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Ideal.mvPolynomialOrigin, ← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra! h'
    have hm0 : m = 0 := Finsupp.ext fun i ↦ h' i (Set.mem_univ i)
    subst hm0
    rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq, h] at hm
    exact hm rfl
  · have : Ideal.mvPolynomialOrigin R σ ≤ RingHom.ker (MvPolynomial.constantCoeff (σ := σ)) := by
      rw [Ideal.mvPolynomialOrigin, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      simp
    exact this h

variable {n B} in
/-- The affine open `𝔸^n_W = p⁻¹ W` of `𝔸^n_B` over an affine open `W ⊆ B`. -/
noncomputable def affineOpenOver {W : B.Opens} (hW : IsAffineOpen W) :
    (𝔸(n; B)).AffineZariskiSite :=
  ⟨(𝔸(n; B) ↘ B) ⁻¹ᵁ W, hW.preimage _⟩

variable {n B} in
/-- `Γ(B, W)[x_1, …, x_n] ≅ Γ(𝔸^n_B, p⁻¹ W)`. -/
noncomputable abbrev polyToSections {W : B.Opens} (_hW : IsAffineOpen W) :
    MvPolynomial n Γ(B, W) →+* Γ(𝔸(n; B), (𝔸(n; B) ↘ B) ⁻¹ᵁ W) :=
  MvPolynomial.eval₂Hom ((𝔸(n; B) ↘ B).app W).hom
    (AffineSpace.coordRes' n B ((𝔸(n; B) ↘ B) ⁻¹ᵁ W))

set_option backward.isDefEq.respectTransparency false in
/-- Over `p⁻¹ W`, the ideal of the zero section is generated by the coordinates. -/
lemma siteIdeal_affineOpenOver {W : B.Opens} (hW : IsAffineOpen W) :
    (AffineSpace.zeroSection n B).ker.siteIdeal (affineOpenOver hW) =
      (Ideal.mvPolynomialOrigin Γ(B, W) n).map (polyToSections (n := n) hW) := by
  have hbij := AffineSpace.bijective_eval₂Hom_app_preimage n B hW
  set s := AffineSpace.zeroSection n B
  have hsW : s ⁻¹ᵁ ((𝔸(n; B) ↘ B) ⁻¹ᵁ W) = W := by
    rw [← Scheme.Hom.comp_preimage, AffineSpace.zeroSection_over, Scheme.Hom.id_preimage]
  have hkey : (s.app ((𝔸(n; B) ↘ B) ⁻¹ᵁ W)).hom.comp (polyToSections (n := n) hW) =
      (B.presheaf.map (eqToHom hsW).op).hom.comp MvPolynomial.constantCoeff := by
    refine MvPolynomial.ringHom_ext (fun c ↦ ?_) fun k ↦ ?_
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.constantCoeff_C]
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_app]
      rw [Scheme.Hom.congr_app (AffineSpace.zeroSection_over n B) W, Scheme.Hom.id_app,
        Category.id_comp]
    · simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X', MvPolynomial.constantCoeff_X,
        map_zero, AffineSpace.coordRes']
      rw [← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
      change (B.presheaf.map _).hom (s.appTop _) = 0
      rw [AffineSpace.zeroSection_appTop_coord, map_zero]
  have hinj : Function.Injective (B.presheaf.map (eqToHom hsW).op).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  ext x
  obtain ⟨p, rfl⟩ := hbij.2 x
  rw [IdealSheafData.siteIdeal, Scheme.Hom.ker_apply, RingHom.mem_ker,
    Ideal.mem_map_iff_of_surjective _ hbij.2]
  change (s.app ((𝔸(n; B) ↘ B) ⁻¹ᵁ W)).hom (polyToSections (n := n) hW p) = 0 ↔ _
  rw [← RingHom.comp_apply, hkey, RingHom.comp_apply, map_eq_zero_iff _ hinj,
    constantCoeff_eq_zero_iff]
  exact ⟨fun h ↦ ⟨p, h, rfl⟩, fun ⟨q, hq, hqp⟩ ↦ hbij.1 hqp ▸ hq⟩

variable {B} {W : B.Opens} (hW : IsAffineOpen W)

/-- `Γ(B, W)[t][u_1, …, u_n] ≅ Γ(p⁻¹ W)[t, I t⁻¹]`, `u_k ↦ x_k t⁻¹`. -/
noncomputable def reesEquiv :
    MvPolynomial n (Polynomial Γ(B, W)) →+*
      ((AffineSpace.zeroSection n B).ker.siteIdeal (affineOpenOver hW)).extendedReesAlgebra :=
  ((Ideal.mvPolynomialOrigin Γ(B, W) n).extendedReesAlgebraMap
    (RingEquiv.ofBijective (polyToSections (n := n) hW)
      (AffineSpace.bijective_eval₂Hom_app_preimage n B hW)).toRingHom _
    (siteIdeal_affineOpenOver n B hW).symm.le).comp
    (Ideal.mvPolynomialExtendedReesAlgebraEquiv Γ(B, W) n).toRingHom

lemma bijective_reesEquiv : Function.Bijective (reesEquiv n hW) := by
  rw [reesEquiv]
  have h₁ := Ideal.bijective_extendedReesAlgebraMap (RingEquiv.ofBijective
    (polyToSections (n := n) hW) (AffineSpace.bijective_eval₂Hom_app_preimage n B hW)) _
    (siteIdeal_affineOpenOver n B hW).symm
  have h₂ := (Ideal.mvPolynomialExtendedReesAlgebraEquiv Γ(B, W) n).bijective
  exact h₁.comp h₂

lemma reesEquiv_X (k : n) :
    reesEquiv n hW (MvPolynomial.X k) = uCoord n B (affineOpenOver hW) k := by
  apply Subtype.ext
  change LaurentPolynomial.mapRingHom _ (Ideal.mvPolynomialToLaurent _ _ (MvPolynomial.X k)) = _
  rw [Ideal.mvPolynomialToLaurent_X, map_mul, LaurentPolynomial.mapRingHom_C,
    LaurentPolynomial.mapRingHom_T]
  change LaurentPolynomial.C (polyToSections (n := n) hW (MvPolynomial.X k)) * T (-1) = _
  rw [MvPolynomial.eval₂Hom_X']
  rfl

lemma reesEquiv_comp_C :
    (reesEquiv n hW).comp MvPolynomial.C =
      ((AffineSpace.zeroSection n B).ker.siteIdeal (affineOpenOver hW)).toExtendedReesAlgebra.comp
        (Polynomial.mapRingHom ((𝔸(n; B) ↘ B).app W).hom) := by
  refine RingHom.ext fun p ↦ Subtype.ext ?_
  change LaurentPolynomial.mapRingHom _ (Ideal.mvPolynomialToLaurent _ _ (MvPolynomial.C p)) = _
  rw [Ideal.mvPolynomialToLaurent_C, LaurentPolynomial.mapRingHom_toLaurent, Polynomial.map_map]
  congr 2
  ext c
  change polyToSections (n := n) hW (MvPolynomial.C c) = _
  rw [MvPolynomial.eval₂Hom_C]

set_option backward.isDefEq.respectTransparency false in
lemma homOfVector_specMap_eq :
    AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom
      (((AffineSpace.zeroSection n B).ker.siteIdeal (affineOpenOver hW)).toExtendedReesAlgebra.comp
        (Polynomial.mapRingHom ((𝔸(n; B) ↘ B).appLE W (affineOpenOver hW).1 le_rfl).hom))))
      (fun k ↦ (ΓSpecIso _).inv (uCoord n B (affineOpenOver hW) k)) =
      Spec.map (CommRingCat.ofHom (reesEquiv n hW)) ≫
        (AffineSpace.SpecIso n (.of (Polynomial Γ(B, W)))).inv := by
  refine AffineSpace.hom_ext ?_ fun k ↦ ?_
  · rw [AffineSpace.homOfVector_over, Category.assoc, AffineSpace.SpecIso_inv_over,
      ← Spec.map_comp]
    congr 1
    rw [← CommRingCat.ofHom_comp]
    change _ = CommRingCat.ofHom ((reesEquiv n hW).comp MvPolynomial.C)
    rw [reesEquiv_comp_C, Scheme.Hom.app_eq_appLE]
    rfl
  · rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.SpecIso_inv_appTop_coord]
    have h := congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (reesEquiv n hW)))
      (MvPolynomial.X k))
    refine Eq.trans ?_ h
    exact congrArg _ (reesEquiv_X n hW k).symm

lemma deformationSpaceToAffineSpaceChart_eq :
    deformationSpaceToAffineSpaceChart n B (affineOpenOver hW) =
      Spec.map (CommRingCat.ofHom (reesEquiv n hW)) ≫
        (AffineSpace.SpecIso n (.of (Polynomial Γ(B, W)))).inv ≫
          AffineSpace.map n (affineLineChart hW) := by
  rw [deformationSpaceToAffineSpaceChart, ι_deformationSpaceProj (𝔸(n; B) ↘ B)
    (AffineSpace.zeroSection n B) (affineOpenOver hW) hW le_rfl, ← AffineSpace.homOfVector_map,
    ← Category.assoc]
  exact congrArg (· ≫ _) (homOfVector_specMap_eq n hW)

instance : IsIso (Spec.map (CommRingCat.ofHom (reesEquiv n hW))) := by
  have : IsIso (CommRingCat.ofHom (reesEquiv n hW)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact bijective_reesEquiv n hW
  infer_instance

/-- Over the chart `𝔸^n_{Γ(B, W)[t]}` of `𝔸^n_{𝔸¹_B}`, the comparison morphism is the chart of
the deformation space over the affine open `𝔸^n_W`, followed by an isomorphism. -/
lemma isPullback_deformationSpaceToAffineSpace :
    IsPullback (Spec.map (CommRingCat.ofHom (reesEquiv n hW)) ≫
        (AffineSpace.SpecIso n (.of (Polynomial Γ(B, W)))).inv)
      (colimit.ι (relativeGluingData
        (AffineSpace.zeroSection n B).ker.coequifibered_toReesPresheaf).functor (affineOpenOver hW))
      (AffineSpace.map n (affineLineChart hW)) (deformationSpaceToAffineSpace n B) := by
  refine IsOpenImmersion.isPullback _ _ _ _ ?_ ?_
  · rw [ι_deformationSpaceToAffineSpace, deformationSpaceToAffineSpaceChart_eq, Category.assoc]
  · rw [AffineSpace.opensRange_map, opensRange_affineLineChart, ← Scheme.Hom.comp_preimage,
      ← Scheme.Hom.comp_preimage, deformationSpaceToAffineSpace_over,
      deformationSpaceProj_over, Scheme.Hom.comp_preimage]
    exact toBase_preimage _ (affineOpenOver hW)

/-- Blueprint `prose-09-12` (4), **the standard pair**: the deformation space of the zero
section of `𝔸^n_B ⟶ B` is `𝔸^n_{𝔸¹_B} = 𝔸^n_B ×_B 𝔸¹_B`, with coordinates `u_k = x_k t⁻¹`. -/
instance isIso_deformationSpaceToAffineSpace : IsIso (deformationSpaceToAffineSpace n B) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun W : B.affineOpens ↦ (AffineSpace.map n (affineLineChart W.2)).opensRange) ?_ fun W ↦ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := B.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ ((𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _ ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) x))
      isOpen_univ
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨W, hW⟩, ?_⟩
    rw [AffineSpace.opensRange_map, opensRange_affineLineChart]
    exact hxW
  · refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictOpensRange _ _)).mpr ?_
    have sq := (isPullback_deformationSpaceToAffineSpace n W.2).flip
    have e : pullback.snd (deformationSpaceToAffineSpace n B)
        (AffineSpace.map n (affineLineChart W.2)) = sq.isoPullback.inv ≫
          Spec.map (CommRingCat.ofHom (reesEquiv n W.2)) ≫
            (AffineSpace.SpecIso n (.of (Polynomial Γ(B, W)))).inv := by
      rw [Iso.eq_inv_comp, sq.isoPullback_hom_snd]
    rw [MorphismProperty.isomorphisms.iff, e]
    infer_instance

variable {n} in
/-- The comparison of the deformation spaces of the standard pair over `B'` and over `B`, along a
morphism `b : B' ⟶ B`. -/
noncomputable def deformationSpaceMap {B' : Scheme.{u}} (b : B' ⟶ B) :
    (AffineSpace.zeroSection n B').ker.deformationSpace ⟶
      (AffineSpace.zeroSection n B).ker.deformationSpace :=
  deformationSpaceToAffineSpace n B' ≫ AffineSpace.map n (AffineSpace.map _ b) ≫
    inv (deformationSpaceToAffineSpace n B)

/-- Blueprint `prose-09-12` (5) for the standard pair: the deformation space of the zero
section commutes with base change in `B`,
`D_0 𝔸^n_{B'} = D_0 𝔸^n_B ×_{𝔸¹_B} 𝔸¹_{B'}`. -/
lemma isPullback_deformationSpaceMap {B' : Scheme.{u}} (b : B' ⟶ B) :
    IsPullback (deformationSpaceMap b)
      (deformationSpaceProj (𝔸(n; B') ↘ B') (AffineSpace.zeroSection n B'))
      (deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
      (AffineSpace.map _ b) := by
  have P₁ := IsPullback.of_horiz_isIso (g := 𝟙 _)
    ⟨(deformationSpaceToAffineSpace_over n B').trans (Category.comp_id _).symm⟩
  have P₃ := IsPullback.of_horiz_isIso (fst := inv (deformationSpaceToAffineSpace n B))
    (snd := 𝔸(n; 𝔸(ULift.{u} (Fin 1); B)) ↘ _)
    (f := deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B)) (g := 𝟙 _)
    ⟨by rw [IsIso.inv_comp_eq, Category.comp_id, deformationSpaceToAffineSpace_over]⟩
  have := (P₁.paste_horiz (AffineSpace.isPullback_map (n := n) (AffineSpace.map _ b))).paste_horiz
    P₃
  simpa [deformationSpaceMap] using this

/-- Blueprint `prose-09-12` (5) for the standard pair: the base change of the section `s̃` is
the section `s̃` over `B'`. -/
lemma deformationSpaceSection_comp_deformationSpaceMap {B' : Scheme.{u}} (b : B' ⟶ B) :
    (AffineSpace.zeroSection n B').deformationSpaceSection ≫ deformationSpaceMap b =
      AffineSpace.map _ b ≫ (AffineSpace.zeroSection n B).deformationSpaceSection := by
  rw [deformationSpaceMap, reassoc_of% deformationSpaceSection_comp_deformationSpaceToAffineSpace,
    ← Category.assoc (AffineSpace.zeroSection _ _), AffineSpace.zeroSection_comp_map,
    Category.assoc]
  congr 1
  rw [IsIso.comp_inv_eq,
    deformationSpaceSection_comp_deformationSpaceToAffineSpace]

end AlgebraicGeometry.Scheme.Hom
