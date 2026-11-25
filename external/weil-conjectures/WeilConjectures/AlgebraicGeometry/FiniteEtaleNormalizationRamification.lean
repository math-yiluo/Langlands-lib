/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.CurveCoverBase
public import WeilConjectures.AlgebraicGeometry.FiniteCoverFiberCount
public import WeilConjectures.AlgebraicGeometry.NormalizationCover
public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.Curve.NormalSmooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp

/-!
# Normalizing a finite étale cover of a punctured curve: a ramification index prime to `ℓ`

Covering step of blueprint `lemma-tangent-cones-on-cover` ("normalizing gives covers of degree
prime to `ℓ`"). Let `X` be a smooth curve over an algebraically closed field `k`, `y` a
`k`-point of `X` lying in an irreducible affine open `U`, `U' ⊆ U` an open and `v : V ⟶ U'` a
connected finite étale cover all of whose geometric fibres have `d` points, `ℓ ∤ d`. The
normalization `C` of `U` in `V` is a smooth curve, finite over `U`, containing `V` as the preimage
of `U'`, and some `k`-point `c` of `C` over `y` has ramification index `e` prime to `ℓ`: a
uniformizer at `y` becomes `w ξ ^ e` at `c` for a unit `w` and a uniformizer `ξ`
(`AlgebraicGeometry.exists_finite_smooth_cover_not_dvd_ramificationIdx`).

The degree `d` is the rank of `Γ(C)` over the Dedekind domain `Γ(U)` (count the geometric points
over a closed point of `U'`, where `C ⟶ U` is unramified), which is the sum of `e_c f_c` over
the points `c` over `y`; so `ℓ ∤ d` forces `ℓ ∤ e_c` for some `c`. The ramification index `e_c`
is the length of `𝒪_{C,c} / 𝔪_y 𝒪_{C,c}`, i.e. the valuation of a uniformizer at `y`.
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

/-- If a morphism `p : C ⟶ Y` to an integral scheme maps some point to the generic point, then
`p` is injective on sections over every open containing the generic point. -/
lemma Scheme.Hom.app_injective_of_apply_eq_genericPoint {C Y : Scheme.{u}} [IsIntegral Y]
    (p : C ⟶ Y) (U : Y.Opens) (c₀ : C) (hc₀ : p c₀ = genericPoint Y) (hU : p c₀ ∈ U) :
    Function.Injective (p.app U) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hfield : IsField (Y.presheaf.stalk (p c₀)) := hc₀ ▸ Field.toIsField Y.functionField
  let := hfield.toField
  have h1 := p.germ_stalkMap_apply U c₀ hU a
  rw [ha, map_zero] at h1
  refine germ_injective_of_isIntegral Y (p c₀) hU ?_
  rw [map_zero]
  exact (p.stalkMap c₀).hom.injective (h1.trans (map_zero _).symm)

/-- If `j ≫ p` is formally unramified and locally of finite type with `j` an open immersion,
then `𝔪_{Y, p c} 𝒪_{C, c} = 𝔪_{C, c}` at every point `c` of the image of `j`. -/
lemma Scheme.Hom.map_maximalIdeal_stalkMap_of_isOpenImmersion_comp {V C Y : Scheme.{u}}
    (j : V ⟶ C) [IsOpenImmersion j] (p : C ⟶ Y) [FormallyUnramified (j ≫ p)]
    [LocallyOfFiniteType (j ≫ p)] (c₀ : V) :
    (maximalIdeal (Y.presheaf.stalk (p (j c₀)))).map (p.stalkMap (j c₀)).hom =
      maximalIdeal (C.presheaf.stalk (j c₀)) := by
  have h := FormallyUnramified.map_maximalIdeal_stalkMap (j ≫ p) c₀
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, ← Ideal.map_map] at h
  exact eq_maximalIdeal_of_map_eq _ (ConcreteCategory.bijective_of_isIso (j.stalkMap c₀)) h

/-- Let `j : V ⟶ C` be an open immersion identifying `v : V ⟶ Y'` with the restriction of
`p : C ⟶ Y` over a monomorphism `k : Y' ⟶ Y` (i.e. `j ≫ p = v ≫ k` and `j(V) = p⁻¹(k(Y'))`).
Then the geometric fibres of `v` over `s` and of `p` over `s ≫ k` agree. -/
noncomputable def Scheme.Hom.geometricFiberEquivOfIsOpenImmersion {Ω : Type u} [Field Ω]
    {V C Y Y' : Scheme.{u}} (j : V ⟶ C) [IsOpenImmersion j] (p : C ⟶ Y) (v : V ⟶ Y')
    (k : Y' ⟶ Y) [Mono k] (h : j ≫ p = v ≫ k)
    (hr : Set.range j.base = p.base ⁻¹' Set.range k.base) (s : Spec (.of Ω) ⟶ Y') :
    v.GeometricFiber s ≃ p.GeometricFiber (s ≫ k) where
  toFun t := ⟨t.1 ≫ j, by rw [Category.assoc, h, ← Category.assoc, t.2]⟩
  invFun x := ⟨IsOpenImmersion.lift j x.1 (by
      rintro _ ⟨a, rfl⟩
      rw [hr]
      refine ⟨s a, ?_⟩
      have := congrArg (fun g : Spec (.of Ω) ⟶ Y ↦ g a) x.2
      simpa using this.symm), by
    rw [← cancel_mono k, Category.assoc, ← h, ← Category.assoc, IsOpenImmersion.lift_fac, x.2]⟩
  left_inv t := by
    apply Subtype.ext
    dsimp only
    rw [← cancel_mono j, IsOpenImmersion.lift_fac]
  right_inv x := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

/-- The specialization map between the stalks at two equal points is bijective. -/
lemma Scheme.stalkSpecializes_bijective_of_eq {X : Scheme.{u}} {x x' : X} (h : x = x') :
    Function.Bijective (X.presheaf.stalkSpecializes (specializes_of_eq h)).hom := by
  subst h
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact Function.bijective_id

attribute [local instance] Scheme.Hom.affineAlgebra in
/-- **Normalizing a prime-to-`ℓ` finite étale cover of a punctured curve** (blueprint
`lemma-tangent-cones-on-cover`). Let `X` be smooth of relative dimension one over an
algebraically closed field `k`, `y` a `k`-point of `X` in an irreducible affine open `U`, `U' ≤ U`
an open, and `v : V ⟶ U'` a finite étale morphism with `V` connected all of whose geometric fibres
have `d` points, `ℓ ∤ d`. Then there are a scheme `C` with a finite morphism `p : C ⟶ U`, smooth
of relative dimension one over `k`, a `k`-point `c` of `C` over `y` and an integer `e ≥ 1` prime
to `ℓ` (the ramification index of `p` at `c`) such that every generator `u` of the maximal ideal of
`𝒪_{X,y}` becomes `w * ξ ^ e` in `𝒪_{C,c}` for a unit `w` and a generator `ξ` of the maximal ideal;
moreover `p` restricts over `U'` to `v`: there is an open immersion `j : V ⟶ C` with
`j ≫ p = v ≫ (U' ⟶ U)` whose image is `p⁻¹(U')`. -/
theorem exists_finite_smooth_cover_not_dvd_ramificationIdx {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f]
    (y : Spec (.of k) ⟶ X) (hy : y ≫ f = 𝟙 _) {U U' : X.Opens} (hU : IsAffineOpen U)
    [IrreducibleSpace U] (hyU : y default ∈ U) (hU'U : U' ≤ U) {V : Scheme.{u}}
    (v : V ⟶ U') [IsFinite v] [Etale v] [ConnectedSpace V] (ℓ d : ℕ)
    (hd : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U'),
      Nat.card (v.GeometricFiber s) = d)
    (hℓd : ¬ ℓ ∣ d) :
    ∃ (C : Scheme.{u}) (p : C ⟶ U) (_ : IsFinite p)
      (_ : SmoothOfRelativeDimension 1 (p ≫ U.ι ≫ f)) (c : Spec (.of k) ⟶ C)
      (hc : c ≫ p ≫ U.ι = y) (e : ℕ), 1 ≤ e ∧ ¬ ℓ ∣ e ∧
      (∀ u : X.presheaf.stalk (y default),
        Ideal.span {u} = maximalIdeal (X.presheaf.stalk (y default)) →
        ∃ w ξ : C.presheaf.stalk (c default), IsUnit w ∧
          Ideal.span {ξ} = maximalIdeal (C.presheaf.stalk (c default)) ∧
          (X.presheaf.stalkSpecializes
              (specializes_of_eq (congrArg (fun g : Spec (.of k) ⟶ X ↦ g default) hc) :
                (p ≫ U.ι) (c default) ⤳ y default) ≫
            (p ≫ U.ι).stalkMap (c default)).hom u = w * ξ ^ e) ∧
      ∃ j : V ⟶ C, IsOpenImmersion j ∧ j ≫ p = v ≫ X.homOfLE hU'U ∧
        Set.range j.base = p.base ⁻¹' Set.range (X.homOfLE hU'U).base := by
  classical
  -- the base `U`
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : SmoothOfRelativeDimension 1 (U.ι ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U.ι ≫ f))
  have : SmoothOfRelativeDimension 1 (U'.ι ≫ f) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) (U'.ι ≫ f))
  have : Smooth (U.ι ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have : Smooth (U'.ι ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have : IsAffine U := hU
  have : IsIntegral U := isIntegral_of_smooth_of_irreducibleSpace (U.ι ≫ f)
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (U.ι ≫ f)
  have : IsRegular U := IsRegular.of_smooth (U.ι ≫ f)
  have : IsRegular U' := IsRegular.of_smooth (U'.ι ≫ f)
  obtain ⟨v₀⟩ : Nonempty V := inferInstance
  have : Nonempty U' := ⟨v v₀⟩
  -- the normalization `C` of `U` in `V`
  let kV := X.homOfLE hU'U
  obtain ⟨hVint, -, hj, hpfin, hCint, hCst, hrange⟩ := Scheme.normalization_comp_of_finite_etale
    (U.ι ≫ f) kV (fun x ↦ IsRegular.isIntegrallyClosed_stalk x) v
  set C := (v ≫ kV).normalization
  set p := (v ≫ kV).fromNormalization
  set j := (v ≫ kV).toNormalization
  have hjp : j ≫ p = v ≫ kV := Scheme.Hom.toNormalization_fromNormalization _
  -- `y` as a point of `U`
  let yU : Spec (.of k) ⟶ U := IsOpenImmersion.lift U.ι y (by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim a default]
    exact hyU)
  have hyU' : yU ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  have hyUs : yU ≫ U.ι ≫ f = 𝟙 _ := by rw [← Category.assoc, hyU', hy]
  -- the rings `A = Γ(U)` and `B = Γ(C)`
  have hA : IsAffineOpen (⊤ : U.toScheme.Opens) := isAffineOpen_top U
  have hB : IsAffineOpen (p ⁻¹ᵁ ⊤) := hA.preimage p
  have : Module.Finite Γ(U, ⊤) Γ(C, p ⁻¹ᵁ ⊤) := Scheme.Hom.finite_affineAlgebra p hA
  have : Nonempty (p ⁻¹ᵁ ⊤) := ⟨⟨j v₀, trivial⟩⟩
  have hgen : (v ≫ kV) (genericPoint V) = genericPoint U := by
    obtain ⟨x, hx, hfx⟩ := Flat.generalizingMap (v ≫ kV)
      (genericPoint_specializes ((v ≫ kV) (genericPoint V)))
    obtain rfl : x = genericPoint V := (hx.antisymm (genericPoint_specializes x)).eq
    exact hfx
  have : FaithfulSMul Γ(U, ⊤) Γ(C, p ⁻¹ᵁ ⊤) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (p.app_injective_of_apply_eq_genericPoint ⊤ (j (genericPoint V))
      (by rw [← Scheme.Hom.comp_apply, hjp, hgen]) trivial)
  -- dimensions
  have hdimU : topologicalKrullDim U = 1 := by
    have hle : topologicalKrullDim U ≤ 1 := by
      exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension (U.ι ≫ f) 1
    refine le_antisymm hle ?_
    have hcl := isClosed_singleton_apply_of_comp_eq_id (U.ι ≫ f) yU hyUs default
    rw [← ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one (U.ι ≫ f) hcl]
    exact ringKrullDim_stalk_le_topologicalKrullDim _
  have hdimA : ringKrullDim Γ(U, ⊤) = 1 := by
    rw [← topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen hA (by simp), hdimU]
  have hdimC : topologicalKrullDim C = 1 := by
    rw [topologicalKrullDim_eq_ringKrullDim_of_isAffineOpen hB
      (Set.eq_univ_of_forall fun _ ↦ trivial), ringKrullDim_eq_of_isIntegral Γ(U, ⊤), hdimA]
  have : Nonempty (⊤ : U.toScheme.Opens) := ⟨⟨yU default, trivial⟩⟩
  have : IsDedekindDomain Γ(U, ⊤) :=
    isDedekindDomain_of_isAffineOpen_of_isIntegrallyClosed_stalk hA
    (fun x ↦ IsRegular.isIntegrallyClosed_stalk x) hdimA.le
  -- `C` is a smooth curve
  have hCsm : SmoothOfRelativeDimension 1 (p ≫ U.ι ≫ f) :=
    smoothOfRelativeDimension_one_of_isIntegrallyClosed_stalk _
      (fun x ↦ ⟨inferInstance, hCst x⟩) hdimC
  -- the degree `d` is the rank of `B` over `A`, computed at a closed point of `U'`
  have : JacobsonSpace U' := LocallyOfFiniteType.jacobsonSpace (U'.ι ≫ f)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (X := U') Set.univ_nonempty
    isOpen_univ.isLocallyClosed
  let y' := pointOfClosedPoint (U'.ι ≫ f) z hz
  have hy's : (y' ≫ kV) ≫ U.ι ≫ f = 𝟙 _ := by
    simp [kV, y']
  have hdeg : d = Module.finrank Γ(U, ⊤) Γ(C, p ⁻¹ᵁ ⊤) := by
    rw [← hd k y', Nat.card_congr
      (Scheme.Hom.geometricFiberEquivOfIsOpenImmersion j p v kV hjp hrange y')]
    refine Scheme.Hom.natCard_geometricFiber_eq_finrank p hA (y' ≫ kV) trivial (U.ι ≫ f) hy's
      fun c hc ↦ ?_
    obtain ⟨c₀, rfl⟩ : c ∈ Set.range j.base := by
      rw [hrange]
      exact ⟨y' default, hc.symm⟩
    have : FormallyUnramified (j ≫ p) := by
      rw [hjp]
      infer_instance
    have : LocallyOfFiniteType (j ≫ p) := by
      rw [hjp]
      infer_instance
    exact Scheme.Hom.map_maximalIdeal_stalkMap_of_isOpenImmersion_comp j p c₀
  -- a point `c` over `y` with ramification index prime to `ℓ`
  let φ := Scheme.Hom.affinePoint yU hA (Set.mem_univ (yU default))
  obtain ⟨q, ⟨hqp, hqo⟩, hℓq⟩ := Ideal.exists_not_dvd_ramificationIdx (RingHom.ker φ)
    (hdeg ▸ hℓd)
  obtain ⟨t, ht⟩ := RingHom.PointsOver.exists_ker_eq (φ := φ) q
  let x := (Scheme.Hom.geometricFiberEquivPointsOver p yU hA (Set.mem_univ (yU default))).symm t
  have hc : x.1 ≫ p ≫ U.ι = y := by
    rw [← Category.assoc, x.2, hyU']
  have hmem : x.1 default ∈ p ⁻¹ᵁ ⊤ := trivial
  have hq : (hB.primeIdealOf ⟨x.1 default, hmem⟩).asIdeal = q := by
    rw [Scheme.Hom.primeIdealOf_geometricFiberEquivPointsOver_symm hA yU _ p t hmem]
    exact ht
  refine ⟨C, p, hpfin, hCsm, x.1, hc, q.ramificationIdx Γ(U, ⊤), Ideal.ramificationIdx_pos _ _,
    hℓq, fun u hu ↦ ?_, j, hj, hjp, hrange⟩
  -- the local ring of `C` at `c` is a discrete valuation ring
  have : Smooth (p ≫ U.ι ≫ f) := SmoothOfRelativeDimension.smooth 1 _
  have : IsRegular C := IsRegular.of_smooth (p ≫ U.ι ≫ f)
  have hcl := isClosed_singleton_apply_of_comp_eq_id (p ≫ U.ι ≫ f) x.1
    (by rw [reassoc_of% hc, hy]) default
  have := IsRegularLocalRing.isDiscreteValuationRing _
    (ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one (p ≫ U.ι ≫ f) hcl)
  -- transport the uniformizer from `X` to `U`
  let ψ := X.presheaf.stalkSpecializes
    (specializes_of_eq (congrArg (fun g : Spec (.of k) ⟶ X ↦ g default) hc) :
      (p ≫ U.ι) (x.1 default) ⤳ y default) ≫ U.ι.stalkMap (p (x.1 default))
  have hψ : Function.Bijective ψ.hom := by
    rw [CommRingCat.hom_comp]
    exact (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap (p (x.1 default)))).comp
      (Scheme.stalkSpecializes_bijective_of_eq
        (congrArg (fun g : Spec (.of k) ⟶ X ↦ g default) hc))
  have hu' : Ideal.span {ψ.hom u} = maximalIdeal (U.toScheme.presheaf.stalk (p (x.1 default))) := by
    rw [← Set.image_singleton, ← Ideal.map_span, hu, map_maximalIdeal_of_surjective _ hψ.2]
  obtain ⟨w, ξ, hw, hξ, h⟩ := p.exists_stalkMap_eq_unit_mul_pow_ramificationIdx hA _ hmem hu'
  rw [hq] at h
  refine ⟨w, ξ, hw, hξ, ?_⟩
  rw [Scheme.Hom.stalkMap_comp, ← Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply]
  exact h

end AlgebraicGeometry
