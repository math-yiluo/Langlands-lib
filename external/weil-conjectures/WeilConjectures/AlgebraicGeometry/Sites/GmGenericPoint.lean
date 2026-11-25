/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# The pullback of `𝔾ₘ` to the generic point

Let `X` be an integral scheme with generic point `i : Spec k(X) ⟶ X`. The comparison map
`i^* 𝔾ₘ ⟶ 𝔾ₘ` of `AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf` is an isomorphism,
although `i` is not étale.

The isomorphism is checked on stalks. For a morphism of sheaves `φ : G ⟶ f_* G'` and a
geometric point `s` of the source of `f`, the stalk at `s` of the transpose `f^* G ⟶ G'` of `φ`
is, up to the identification of the stalk of `f^* G` at `s` with the stalk of `G` at `s ≫ f`,
the map on stalks `G_{s ≫ f} ⟶ G'_s` which sends the germ of a section `δ` of `G` over a pointed
étale neighbourhood `(V, v)` of `s ≫ f` to the germ of `φ(δ)` over the base change
`(V ×_Y X, v)` (`AlgebraicGeometry.Etale.stalkComparison`). For `𝔾ₘ` along the generic point
this map is bijective: an étale neighbourhood of the generic point is cut out by finitely many
equations with coefficients in `k(X)`, which are defined over a nonempty open of `X`, and a
local ring of an étale `X`-scheme at a point over the generic point is a field.

## Main definitions

- `AlgebraicGeometry.Etale.stalkComparison`: the map on stalks `G_{s ≫ f} ⟶ G'_s` induced by
  `φ : G ⟶ f_* G'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_sheafFiber_map_homEquiv_symm_iff`: the stalk of the transpose
  of `φ` is an isomorphism if and only if `AlgebraicGeometry.Etale.stalkComparison` is.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ X) {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  (φ : G ⟶ (f)_*[AddCommGrpCat.{u + 1}].obj G')

/-- The map on stalks `G_{s ≫ f} ⟶ G'_s` induced by a morphism `φ : G ⟶ f_* G'`: the germ of a
section `δ` of `G` over a pointed étale neighbourhood `(V, v)` of `s ≫ f` goes to the germ of the
section `φ(δ)` of `G'` over the base change `V ×_Y X`, pointed by `v` and `s`. -/
noncomputable def stalkComparison :
    (pointSmallEtale (s ≫ f)).sheafFiber.obj G ⟶ (pointSmallEtale s).sheafFiber.obj G' :=
  (pointSmallEtale (s ≫ f)).presheafFiberDesc
    (fun V v ↦ φ.hom.app (op V) ≫ (pointSmallEtale s).toPresheafFiber (f.Etale.obj V)
      ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) G'.obj)
    (fun V W g v ↦ by
      have h₁ := φ.hom.naturality g.op
      have h₂ := (pointSmallEtale s).toPresheafFiber_w (f.Etale.map g)
        ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) G'.obj
      have h₃ := NatTrans.naturality_apply (pointSmallEtaleFiberEtaleIso f s).inv g v
      rw [h₃]
      erw [← h₂]
      rw [← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ _) h₁)

@[reassoc (attr := simp)]
lemma toPresheafFiber_stalkComparison (V : Y.Etale) (v : (pointSmallEtale (s ≫ f)).fiber.obj V) :
    (pointSmallEtale (s ≫ f)).toPresheafFiber V v G.obj ≫ stalkComparison f s φ =
      φ.hom.app (op V) ≫ (pointSmallEtale s).toPresheafFiber (f.Etale.obj V)
        ((pointSmallEtaleFiberEtaleIso f s).inv.app V v) G'.obj :=
  (pointSmallEtale (s ≫ f)).toPresheafFiber_presheafFiberDesc _ _ V v

/-- **The stalk of a transpose.** For `φ : G ⟶ f_* G'`, the stalk at a geometric point `s` of
the transpose `f^* G ⟶ G'` of `φ` under `f^* ⊣ f_*`, composed with the identification
`G_{s ≫ f} ≅ (f^* G)_s` of `AlgebraicGeometry.Etale.upperStarCompSheafFiberIso`, is the map on
stalks `AlgebraicGeometry.Etale.stalkComparison`. -/
lemma upperStarCompSheafFiberIso_inv_app_comp_sheafFiber_map :
    ((upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f s).inv.app G) ≫
        (pointSmallEtale s).sheafFiber.map
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm φ) =
      stalkComparison f s φ := by
  refine (pointSmallEtale (s ≫ f)).presheafFiber_hom_ext fun V v ↦ ?_
  refine Eq.trans ?_ (toPresheafFiber_stalkComparison f s φ V v).symm
  simp only [upperStarCompSheafFiberIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Category.assoc]
  erw [GrothendieckTopology.Point.toPresheafFiber_sheafFiberIso_inv_app_assoc,
    GrothendieckTopology.Point.toPresheafFiber_sheafFiberComapIso_hom_app_assoc]
  rw [← Functor.map_comp]
  erw [GrothendieckTopology.Point.toPresheafFiber_naturality]
  -- the unit of the abstract pullback followed by the transpose of `φ` is `φ`
  have key : ((Hom.Etale f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1} Y.smallEtaleTopology
      X.smallEtaleTopology).unit.app G ≫ (f)_*[AddCommGrpCat.{u + 1}].map
        ((Functor.sheafPullbackConstruction.sheafPullbackIso
          (MorphismProperty.Over.pullback @Etale ⊤ f) AddCommGrpCat.{u + 1}
          (smallGrothendieckTopology (@Etale) Y) (smallGrothendieckTopology (@Etale) X)).hom.app G ≫
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv G G').symm φ) = φ := by
    rw [Functor.map_comp, ← Category.assoc]
    erw [Adjunction.unit_leftAdjointUniq_hom_app]
    exact ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_unit G G' _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [← Category.assoc]
  exact congrArg (· ≫ _) (congrArg (fun h ↦ h.hom.app (op V)) key)

end Etale

end AlgebraicGeometry

section Spreading

open Polynomial

/-- **Spreading out a unit of a standard étale algebra over a fraction field.** Let `R` be a
domain with fraction field `K`, `S` a standard étale `K`-algebra and `γ` a unit of `S`. Then there
are an étale `R`-algebra `T`, an `R`-algebra map `ψ : T ⟶ S` and a unit `δ` of `T` with
`ψ δ = γ`: the finitely many coefficients of a presentation of `S` and of an expression of `γ`
lie in a localization `R[1/a]`, over which they define a standard étale algebra, and `T` is a
further localization of it in which the numerator of `γ` is inverted. -/
theorem StandardEtalePresentation.exists_etale_units_eq {R K S : Type u} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [CommRing S] [Algebra K S]
    (Q : StandardEtalePresentation K S) (γ : Sˣ) :
    ∃ (T : Type u) (_ : CommRing T) (ρ : R →+* T) (ψ : T →+* S), ρ.Etale ∧
      ψ.comp ρ = (algebraMap K S).comp (algebraMap R K) ∧ ∃ δ : Tˣ, ψ δ = γ := by
  classical
  obtain ⟨p, n, hp⟩ := Q.exists_mul_aeval_x_g_pow_eq_aeval_x γ.val
  -- a common denominator `b` of the coefficients of `f`, `g` and `p`
  obtain ⟨⟨b, hb⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Q.f.coeffs ∪ Q.g.coeffs ∪ p.coeffs : Finset K)
  have hbu : IsUnit (algebraMap R K b) := IsLocalization.map_units K ⟨b, hb⟩
  let Ra := Localization.Away b
  let φ : Ra →+* K := IsLocalization.Away.lift b hbu
  have hφ : φ.comp (algebraMap R Ra) = algebraMap R K := IsLocalization.Away.lift_comp b hbu
  have hrange (c : K) (hc : c ∈ Q.f.coeffs ∪ Q.g.coeffs ∪ p.coeffs) : c ∈ Set.range φ := by
    obtain ⟨r, hr⟩ := hint c hc
    refine ⟨IsLocalization.mk' Ra r (⟨b, 1, pow_one b⟩ : Submonoid.powers b), ?_⟩
    have h₁ : φ (IsLocalization.mk' Ra r (⟨b, 1, pow_one b⟩ : Submonoid.powers b)) *
        algebraMap R K b = algebraMap R K r := by
      rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
    refine mul_right_cancel₀ hbu.ne_zero (h₁.trans ?_)
    rw [hr, Algebra.smul_def, mul_comm]
  have hsub (q : K[X]) (hq : q.coeffs ⊆ Q.f.coeffs ∪ Q.g.coeffs ∪ p.coeffs) :
      q ∈ Polynomial.lifts φ :=
    (Polynomial.lifts_iff_coeffs_subset_range _).2 fun c hc ↦ hrange c (hq hc)
  obtain ⟨F, hF, -, hFm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (hsub Q.f (fun c hc ↦ by simp [hc])) Q.monic_f
  obtain ⟨G, hG⟩ := hsub Q.g (fun c hc ↦ by simp [hc])
  obtain ⟨Pa, hPa⟩ := hsub p (fun c hc ↦ by simp [hc])
  rw [Polynomial.coe_mapRingHom] at hG hPa
  -- the standard étale pair over `R[1/b]`
  let P' := StandardEtalePair.ofMonic hFm G
  let : Algebra Ra S := ((algebraMap K S).comp φ).toAlgebra
  have haeval (q : Ra[X]) : aeval Q.x q = aeval Q.x (q.map φ) := by
    rw [aeval_def, aeval_def, eval₂_map]
    rfl
  have hx : P'.HasMap Q.x := by
    refine ⟨?_, ?_⟩
    · rw [StandardEtalePair.ofMonic_f, haeval, hF]
      exact Q.hasMap.1
    · rw [StandardEtalePair.ofMonic_g, map_mul, haeval, haeval, hG, ← Polynomial.derivative_map, hF]
      exact Q.hasMap.2.mul Q.hasMap.isUnit_derivative_f
  let ψ₀ : P'.Ring →ₐ[Ra] S := P'.lift Q.x hx
  let e : P'.Ring := aeval P'.X Pa
  have he : ψ₀ e = γ * aeval Q.x Q.g ^ n := by
    rw [show ψ₀ e = aeval (ψ₀ P'.X) Pa from (aeval_algHom_apply _ _ _).symm,
      StandardEtalePair.lift_X, haeval, hPa, hp]
  have heu : IsUnit (ψ₀ e) := he ▸ γ.isUnit.mul (Q.hasMap.2.pow n)
  let T := Localization.Away e
  let ψ : T →+* S := IsLocalization.Away.lift e heu
  have hψ : ψ.comp (algebraMap P'.Ring T) = ψ₀ := IsLocalization.Away.lift_comp e heu
  have hGX : IsUnit (aeval P'.X G) := by
    have h := P'.hasMap_X.2
    rw [StandardEtalePair.ofMonic_g, map_mul] at h
    exact isUnit_of_mul_isUnit_left h
  refine ⟨T, inferInstance, (algebraMap P'.Ring T).comp ((algebraMap Ra P'.Ring).comp
    (algebraMap R Ra)), ψ, ?_, ?_, (IsLocalization.Away.algebraMap_isUnit e).unit *
      (hGX.map (algebraMap P'.Ring T)).unit⁻¹ ^ n, ?_⟩
  · refine RingHom.Etale.stableUnderComposition _ _ ?_
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway e))
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway b))
      (RingHom.etale_algebraMap.2 inferInstance)
  · rw [← RingHom.comp_assoc, hψ, ← RingHom.comp_assoc, ψ₀.comp_algebraMap]
    change ((algebraMap K S).comp φ).comp (algebraMap R Ra) = _
    rw [RingHom.comp_assoc, hφ]
  · have h₁ : ψ (algebraMap P'.Ring T (aeval P'.X G)) = aeval Q.x Q.g := by
      rw [← RingHom.comp_apply, hψ]
      change ψ₀ (aeval P'.X G) = _
      rw [show ψ₀ (aeval P'.X G) = aeval (ψ₀ P'.X) G from (aeval_algHom_apply _ _ _).symm,
        StandardEtalePair.lift_X, haeval, hG]
    have h₂ : ψ (algebraMap P'.Ring T e) = γ * aeval Q.x Q.g ^ n := by
      rw [← RingHom.comp_apply, hψ]
      exact he
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, IsUnit.unit_spec]
    rw [h₂]
    have h₃ : aeval Q.x Q.g * ψ ↑(hGX.map (algebraMap P'.Ring T)).unit⁻¹ = 1 := by
      rw [← h₁, ← map_mul]
      change ψ (↑(hGX.map (algebraMap P'.Ring T)).unit *
        ↑(hGX.map (algebraMap P'.Ring T)).unit⁻¹) = 1
      rw [Units.mul_inv, map_one]
    rw [mul_assoc, ← mul_pow, h₃, one_pow, mul_one]

end Spreading

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-- The local ring of an étale `X`-scheme at a point over the generic point of the integral
scheme `X` is a field: the étale map is unramified, so the maximal ideal of the local ring is
generated by that of the function field of `X`, which is zero. -/
lemma isField_stalk_of_hom_eq_genericPoint (V : X.Etale) {y : V.left}
    (hy : V.hom y = genericPoint X) : IsField (V.left.presheaf.stalk y) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  have h₁ := FormallyUnramified.map_maximalIdeal_stalkMap V.hom y
  have h₂ : IsLocalRing.maximalIdeal (X.presheaf.stalk (V.hom y)) = ⊥ := by
    rw [hy]
    exact IsLocalRing.maximalIdeal_eq_bot
  erw [h₂, Ideal.map_bot] at h₁
  exact h₁.symm

/-- A function on an étale `X`-scheme `V` which vanishes after pullback along a morphism
`h : W ⟶ V` vanishes on an open neighbourhood of the image `h w` of any point `w` lying over the
generic point of `X`: the local ring of `V` at `h w` is a field, so the map of local rings at `w`
is injective. -/
lemma exists_opens_res_eq_zero (V : X.Etale) {W : Scheme.{u}} (h : W ⟶ V.left) (w : W)
    (hw : V.hom (h w) = genericPoint X) (a : Γ(V.left, ⊤)) (ha : h.appTop a = 0) :
    ∃ (N : V.left.Opens) (_ : h w ∈ N),
      V.left.presheaf.map (homOfLE (le_top : N ≤ ⊤)).op a = 0 := by
  let := (isField_stalk_of_hom_eq_genericPoint V hw).toField
  have hgerm : V.left.presheaf.germ ⊤ (h w) trivial a = 0 := by
    refine (h.stalkMap w).hom.injective ?_
    rw [map_zero, ← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap, CommRingCat.comp_apply]
    change W.presheaf.germ _ w _ (h.appTop a) = 0
    rw [ha, map_zero]
  obtain ⟨N, hN, i₁, i₂, e⟩ := V.left.presheaf.germ_eq (U := ⊤) (V := ⊤) (h w) trivial trivial a 0
    (hgerm.trans (map_zero _).symm)
  refine ⟨N, hN, ?_⟩
  rw [show homOfLE (le_top : N ≤ ⊤) = i₁ from rfl, e, map_zero]

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme

variable (X : Scheme.{u}) [IsIntegral X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Spec X.functionField)

omit [IsSepClosed Ω] in
/-- The geometric point `s ≫ i` of `X` lies over the generic point. -/
lemma comp_fromSpecFunctionField_apply (z : Spec (.of Ω)) :
    (s ≫ X.fromSpecFunctionField) z = genericPoint X := by
  have : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  rw [Scheme.Hom.comp_apply, Subsingleton.elim (s z) (IsLocalRing.closedPoint _),
    fromSpecStalk_closedPoint]

/-- **The stalks of `𝔾ₘ` along the generic point: injectivity.** Let `δ` be a unit on an étale
`X`-scheme `V` whose pullback to the generic fibre is trivial near a geometric point of
`Spec k(X)`. Then `δ` is trivial near the image point in `V`, since the local ring of `V` there is
a field. -/
lemma injective_stalkComparison_gmSheafToLowerStarGmSheaf :
    Function.Injective (stalkComparison X.fromSpecFunctionField s
      (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  set i := X.fromSpecFunctionField
  rw [injective_iff_map_eq_zero]
  intro p hp
  obtain ⟨V, v, δ, rfl⟩ :=
    (pointSmallEtale (s ≫ i)).toPresheafFiber_jointly_surjective (P := X.gmSheaf.obj) p
  have h₁ := ConcreteCategory.congr_hom
    (toPresheafFiber_stalkComparison i s (gmSheafToLowerStarGmSheaf i) V v) δ
  simp only [ConcreteCategory.comp_apply] at h₁
  obtain ⟨W, g, w, hw, hgw⟩ := ((pointSmallEtale s).toPresheafFiber_eq_iff' _ _ _ _).1
    (h₁.symm.trans (hp.trans (map_zero _).symm))
  -- the pullback of `δ` to `W` is trivial
  set δu : Γ(V.left, ⊤)ˣ := Additive.toMul δ.down
  have key : (g.left ≫ pullback.fst V.hom i).appTop (δu.val - 1 : Γ(V.left, ⊤)) = 0 := by
    rw [map_zero] at hgw
    have := congrArg (fun z ↦ ((Additive.toMul (ULift.down z) : Γ(W.left, ⊤)ˣ) : Γ(W.left, ⊤)))
      hgw
    change g.left.appTop ((pullback.fst V.hom i).appTop δu.val) = 1 at this
    rw [map_sub, map_one, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    exact sub_eq_zero.2 this
  -- the points involved
  let z₀ : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have hv : (g.left ≫ pullback.fst V.hom i) (w.left z₀) = v.left z₀ := by
    have h₂ := congrArg (fun t ↦ t.left) hw
    change w.left ≫ g.left = ((pointSmallEtaleFiberEtaleIso i s).inv.app V v).left at h₂
    have h₃ := pointSmallEtaleFiberEtaleIso_inv_app_left_fst i s V v
    rw [← h₂, Category.assoc] at h₃
    exact congrArg (fun t ↦ t z₀) h₃
  have hη : V.hom ((g.left ≫ pullback.fst V.hom i) (w.left z₀)) = genericPoint X := by
    rw [hv]
    exact (congrArg (fun t ↦ t z₀) (CategoryTheory.Over.w v)).trans
      (comp_fromSpecFunctionField_apply X s z₀)
  obtain ⟨N, hN, hres⟩ := exists_opens_res_eq_zero V _ _ hη _ key
  replace hN : v.left z₀ ∈ N := hv ▸ hN
  -- so `δ` is trivial on a Zariski neighbourhood of the image of `v`
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨v', hv'⟩ := exists_pointSmallEtale_fiber_ofOpens (s ≫ i) v N (by
    rintro _ ⟨z, rfl⟩
    rwa [show z = z₀ from Subsingleton.elim (α := Spec (.of Ω)) z z₀])
  have hres' : N.ι.appTop (δu.val - 1 : Γ(V.left, ⊤)) = 0 := by
    rw [Scheme.Opens.ι_appTop]
    have : homOfLE (le_top : N.ι ''ᵁ ⊤ ≤ ⊤) =
        homOfLE N.ι_image_top.le ≫ homOfLE (le_top : N ≤ ⊤) := rfl
    rw [this, op_comp, Functor.map_comp, CommRingCat.comp_apply, hres, map_zero]
  have hδ : X.gmSheaf.obj.map (Scheme.Etale.ofOpensι V N).op δ = 0 := by
    refine ULift.ext (congrArg Additive.ofMul (Units.ext ?_))
    change N.ι.appTop δu.val = 1
    rw [map_sub, map_one, sub_eq_zero] at hres'
    exact hres'
  rw [← hv', ← (pointSmallEtale (s ≫ i)).toPresheafFiber_w_apply, hδ, map_zero]

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

/-- **Étale schemes over a field are locally standard étale.** Let `U` be étale over the
spectrum of a field `K` and `y` a point of `U`. Then `y` has an affine open neighbourhood `D`
whose ring of functions is a standard étale `K`-algebra (`Algebra.IsEtaleAt.exists_isStandardEtale`
applied to an affine open neighbourhood of `y`). -/
lemma exists_isStandardEtale_nbhd {K : Type u} [Field K] (U : (Spec (.of K)).Etale) (y : U.left) :
    ∃ (D : U.left.Opens) (_ : IsAffineOpen D) (_ : y ∈ D),
      letI : Algebra K Γ((Etale.ofOpens U D).left, ⊤) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ (Etale.ofOpens U D).hom.appTop).hom.toAlgebra
      Algebra.IsStandardEtale K Γ((Etale.ofOpens U D).left, ⊤) := by
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, hyW₀, -⟩ :=
    U.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let B := Γ(U.left, W₀)
  let φ : CommRingCat.of K ⟶ B :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ U.hom.appLE ⊤ W₀ le_top
  let : Algebra K B := φ.hom.toAlgebra
  have hφ : φ.hom.Etale := by
    refine (RingHom.Etale.respectsIso.cancel_left_isIso _ _).2 ?_
    exact HasRingHomProperty.appLE @Etale U.hom inferInstance
      ⟨⊤, isAffineOpen_top (Spec (.of K))⟩ ⟨W₀, hW₀⟩ le_top
  have : Algebra.Etale K B := RingHom.etale_algebraMap.1 hφ
  let Q := (hW₀.primeIdealOf ⟨y, hyW₀⟩).asIdeal
  obtain ⟨b, hbQ, hb⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := K) Q
  -- the basic open `D(b)` works
  have hyD : y ∈ U.left.basicOpen b := by
    let := U.left.presheaf.algebra_section_stalk ⟨y, hyW₀⟩
    have := hW₀.isLocalization_stalk ⟨y, hyW₀⟩
    exact (U.left.mem_basicOpen b y hyW₀).2
      (IsLocalization.map_units (U.left.presheaf.stalk y) (⟨b, hbQ⟩ : Q.primeCompl))
  refine ⟨U.left.basicOpen b, hW₀.basicOpen b, hyD, ?_⟩
  let D := U.left.basicOpen b
  have := hW₀.isLocalization_basicOpen b
  let e₁ := IsLocalization.algEquiv (Submonoid.powers b) (Localization.Away b) Γ(U.left, D)
  let e₂ : Γ(U.left, D) ≃+* Γ((Etale.ofOpens U D).left, ⊤) :=
    (Scheme.Opens.topIso D).symm.commRingCatIsoToRingEquiv
  let : Algebra K Γ((Etale.ofOpens U D).left, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Etale.ofOpens U D).hom.appTop).hom.toAlgebra
  refine Algebra.IsStandardEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e₁.toRingEquiv.trans e₂)
    fun k ↦ ?_)
  rw [IsScalarTower.algebraMap_apply K B (Localization.Away b)]
  change e₂ (e₁ (algebraMap B _ (φ k))) = _
  rw [AlgEquiv.commutes]
  change (Scheme.Opens.topIso D).inv (U.left.presheaf.map (homOfLE (U.left.basicOpen_le b)).op
    (U.hom.appLE ⊤ W₀ le_top ((Scheme.ΓSpecIso (.of K)).inv k))) =
      (D.ι ≫ U.hom).appTop ((Scheme.ΓSpecIso (.of K)).inv k)
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Scheme.Hom.comp_appTop,
    Scheme.Opens.ι_appTop, CommRingCat.comp_apply]
  erw [Scheme.presheaf_map_map_apply, Scheme.presheaf_map_map_apply]
  exact congrArg (fun (h : D.ι ''ᵁ ⊤ ⟶ U.hom ⁻¹ᵁ ⊤) ↦ U.left.presheaf.map h.op _)
    (Subsingleton.elim _ _)

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

open Scheme

variable (X : Scheme.{u}) [IsIntegral X] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Spec X.functionField)

/-- **The stalks of `𝔾ₘ` along the generic point: surjectivity.** Every germ of a unit on an
étale neighbourhood of a geometric point of `Spec k(X)` comes from an étale `X`-scheme: near the
point, the neighbourhood is the spectrum of a standard étale `k(X)`-algebra
(`AlgebraicGeometry.Scheme.exists_isStandardEtale_nbhd`), whose presentation and the unit are
defined over a nonempty affine open of `X`
(`StandardEtalePresentation.exists_etale_units_eq`). -/
lemma surjective_stalkComparison_gmSheafToLowerStarGmSheaf :
    Function.Surjective (stalkComparison X.fromSpecFunctionField s
      (gmSheafToLowerStarGmSheaf X.fromSpecFunctionField)) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  set i := X.fromSpecFunctionField
  intro q
  obtain ⟨U, u, γ, rfl⟩ :=
    (pointSmallEtale s).toPresheafFiber_jointly_surjective
      (P := (Spec X.functionField).gmSheaf.obj) q
  set γu : Γ(U.left, ⊤)ˣ := Additive.toMul γ.down
  let z₀ : Spec (.of Ω) := IsLocalRing.closedPoint Ω
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨D, hD, hyD, hstd⟩ := exists_isStandardEtale_nbhd U (u.left z₀)
  let W := Scheme.Etale.ofOpens U D
  let : Algebra X.functionField Γ(W.left, ⊤) :=
    ((Scheme.ΓSpecIso X.functionField).inv ≫ W.hom.appTop).hom.toAlgebra
  obtain ⟨Qp⟩ := hstd.nonempty_standardEtalePresentation
  -- a nonempty affine open `Spec R` of `X`
  obtain ⟨_, ⟨UX, hUX, rfl⟩, hηUX, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty UX := ⟨⟨_, hηUX⟩⟩
  have : IsFractionRing Γ(X, UX) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X UX hUX
  -- spreading out the presentation and the unit
  obtain ⟨T, _, ρ, ψ, hρ, hψρ, δ, hδ⟩ :=
    Qp.exists_etale_units_eq (R := Γ(X, UX)) (Units.map D.ι.appTop.hom.toMonoidHom γu)
  -- the étale `X`-scheme `V = Spec T`
  have : Etale (Spec.map (CommRingCat.ofHom ρ)) := (HasRingHomProperty.Spec_iff (P := @Etale)).2 hρ
  let V : X.Etale := Scheme.Etale.mk (Spec.map (CommRingCat.ofHom ρ) ≫ hUX.fromSpec)
  let h : W.left ⟶ V.left := W.left.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ)
  have hi : i = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, UX) X.functionField)) ≫
      hUX.fromSpec := by
    change X.fromSpecStalk (genericPoint X) = _
    rw [← hUX.fromSpecStalk_eq_fromSpecStalk hηUX]
    rfl
  have hcomp : h ≫ V.hom = W.hom ≫ i := by
    rw [hi]
    change h ≫ Spec.map (CommRingCat.ofHom ρ) ≫ hUX.fromSpec = _
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    apply ext_of_isAffine
    simp only [h, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    rw [Scheme.ΓSpecIso_naturality, ← Category.assoc, Scheme.ΓSpecIso_naturality, Category.assoc]
    have e : (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, UX) X.functionField))).appTop =
        (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom (algebraMap Γ(X, UX) X.functionField) ≫
          (Scheme.ΓSpecIso X.functionField).inv := by
      rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc]
      erw [Iso.hom_inv_id]
      rw [Category.comp_id]
    refine Eq.trans ?_ (congrArg (· ≫ W.hom.appTop) e.symm)
    simp only [Category.assoc]
    congr 1
    exact CommRingCat.hom_ext hψρ
  -- the point `u` lies in `D`
  obtain ⟨u', hu'⟩ := exists_pointSmallEtale_fiber_ofOpens s u D (by
    rintro _ ⟨z, rfl⟩
    rwa [show z = z₀ from Subsingleton.elim (α := Spec (.of Ω)) z z₀])
  -- the pointed étale neighbourhood `(V, v)` of `s ≫ i`
  let v : (pointSmallEtale (s ≫ i)).fiber.obj V := CategoryTheory.Over.homMk (u'.left ≫ h) (by
    change (u'.left ≫ h) ≫ V.hom = s ≫ i
    rw [Category.assoc, hcomp, ← Category.assoc]
    exact congrArg (· ≫ i) (CategoryTheory.Over.w u'))
  let k : W ⟶ (Hom.Etale i).obj V :=
    MorphismProperty.Over.homMk (pullback.lift h W.hom hcomp) (pullback.lift_snd _ _ _)
  have hk : (pointSmallEtale s).fiber.map k u' =
      (pointSmallEtaleFiberEtaleIso i s).inv.app V v := by
    refine CategoryTheory.Over.OverMorphism.ext ?_
    change u'.left ≫ pullback.lift h W.hom hcomp = _
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pointSmallEtaleFiberEtaleIso_inv_app_left_fst]
      rfl
    · rw [Category.assoc, pullback.lift_snd, pointSmallEtaleFiberEtaleIso_inv_app_left_snd]
      exact CategoryTheory.Over.w u'
  -- the unit `δ` of `T` is a section of `𝔾ₘ` over `V`
  let δ' : X.gmSheaf.obj.obj (op V) :=
    ULift.up (Additive.ofMul (Units.map (Scheme.ΓSpecIso (.of T)).inv.hom.toMonoidHom δ))
  refine ⟨(pointSmallEtale (s ≫ i)).toPresheafFiber V v X.gmSheaf.obj δ', ?_⟩
  have h₁ := ConcreteCategory.congr_hom
    (toPresheafFiber_stalkComparison i s (gmSheafToLowerStarGmSheaf i) V v) δ'
  simp only [ConcreteCategory.comp_apply] at h₁
  refine h₁.trans ?_
  rw [← hk, ← hu']
  refine ((pointSmallEtale s).toPresheafFiber_w_apply k u' _ _).symm.trans
    (Eq.trans ?_ ((pointSmallEtale s).toPresheafFiber_w_apply (Scheme.Etale.ofOpensι U D) u' _ _))
  refine congrArg _ (ULift.ext (congrArg Additive.ofMul (Units.ext ?_)))
  change k.left.appTop ((pullback.fst V.hom i).appTop ((Scheme.ΓSpecIso (.of T)).inv δ.val)) =
    D.ι.appTop γu.val
  have hkf : k.left ≫ pullback.fst V.hom i = h := pullback.lift_fst _ _ _
  have e₁ (x : Γ(V.left, ⊤)) : k.left.appTop ((pullback.fst V.hom i).appTop x) = h.appTop x := by
    rw [← hkf, Scheme.Hom.comp_appTop]
    rfl
  have e₂ : h.appTop ((Scheme.ΓSpecIso (.of T)).inv δ.val) = ψ δ.val := by
    have := congrArg (fun f ↦ f.hom ((Scheme.ΓSpecIso (.of T)).inv δ.val))
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ψ))
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply, CommRingCat.hom_ofHom] at this
    simp only [h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.toSpecΓ_appTop]
    exact this
  exact (e₁ _).trans (e₂.trans hδ)

end AlgebraicGeometry.Etale
