import Langlands.GroupScheme.LocalUnramifiedIntegralCocycle
import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.IntegralModel.CoefficientPoints
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyFamily
import Mathlib.FieldTheory.Normal.Closure

/-! # Twisting points over the maximal unramified extension

A cocycle on a finite Galois cover `Spec E → Spec F` is trivial as soon as a single point of the
group over a normal subextension `L` of the maximal unramified extension of `F` twists its
inflated Galois values into points with integral coordinates for a smooth model with connected
special fibre. The twisting point has finitely many coordinates, so it is defined over a finite
Galois unramified extension, where the finite level criterion
`GaloisCocycle.isTrivial_of_integral_twist` applies.

The module also identifies integral coordinates over the maximal unramified extension with the
integral points of the unramified base change `IntegralModel.baseChangeUnramified`, and shows that
integral coordinates descend along field extensions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.LocalGalois.Separable GaloisPointComparison

namespace IntegralModel

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance unramifiedTwistIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

local instance unramifiedTwistIntegerScalarTower :
    IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)

/-- An element of the maximal unramified extension is an integer of its valuation exactly when it
is integral over `𝒪[F]`. -/
theorem mem_range_fixedFieldIntegers_iff_isIntegral (y : inertiaFixedField F) :
    y ∈ Set.range (algebraMap (fixedFieldIntegers F) (inertiaFixedField F)) ↔
      IsIntegral ↥𝒪[F] y := by
  rw [← mem_integralClosure_iff, ← LocalUnramified.integers,
    LocalUnramified.mem_integers_iff, ← fixedFieldIntegers_eq]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **Integral points of the unramified base change.** A point of `G` over the maximal
unramified extension lies in the image of the integral points of the base-changed model exactly
when its generic model coordinates are integral over `𝒪[F]`. -/
theorem mem_baseChangeUnramified_integralPoints_iff
    (p : G.affinePoints (CommAlgCat.of F (inertiaFixedField F))) :
    (baseChangeCoeffEquiv F (inertiaFixedField F) G).symm p ∈
        M.baseChangeUnramified.integralPoints ↔
      M.HasIntegralCoordinates (inertiaFixedField F) p := by
  rw [← mem_coefficientIntegralPoints_iff]
  change p ∈ (M.baseChange (fixedFieldIntegers F) (inertiaFixedField F)).coefficientIntegralPoints
    F (inertiaFixedField F) ↔ _
  rw [M.mem_baseChange_coefficientIntegralPoints_iff_genericCoordinates]
  exact forall_congr' fun a => mem_range_fixedFieldIntegers_iff_isIntegral _

/-- **Integrality descends along field extensions.** A point over a field `E` has integral
coordinates for `M` as soon as its extension to a larger field `L` does. -/
theorem hasIntegralCoordinates_of_relativeExtend
    {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffine G.X.left] (M : IntegralModel R K G)
    {E L : Type u} [Field E] [Field L] [Algebra K E] [Algebra K L] [Algebra E L]
    [IsScalarTower K E L] [Algebra R E] [IsScalarTower R K E] [Algebra R L] [IsScalarTower R K L]
    (p : G.affinePoints (CommAlgCat.of K E))
    (hp : M.HasIntegralCoordinates L (GaloisPoint.relativeExtend K E L G p)) :
    M.HasIntegralCoordinates E p := by
  intro a
  have ha := hp a
  rw [← GaloisPoint.coordinates_apply, GaloisPoint.coordinates_relativeExtend] at ha
  rw [← GaloisPoint.coordinates_apply]
  let f : E →ₐ[R] L := (IsScalarTower.toAlgHom K E L).restrictScalars R
  exact (isIntegral_algHom_iff f f.toRingHom.injective).mp ha

end IntegralModel

namespace GaloisCocycle

open IntermediateField in
/-- A finite-dimensional subextension of a normal subextension `L` of the separable closure lies in
a finite Galois subextension of `L`: its normal closure. -/
theorem exists_finiteDimensional_isGalois_between {F : Type u} [Field F]
    (L K₀ : IntermediateField F (SeparableClosure F)) [Normal F L] [FiniteDimensional F K₀]
    (hK₀L : K₀ ≤ L) :
    ∃ E' : IntermediateField F (SeparableClosure F),
      FiniteDimensional F E' ∧ IsGalois F E' ∧ K₀ ≤ E' ∧ E' ≤ L :=
  ⟨normalClosure F K₀ (SeparableClosure F), inferInstance,
    { to_isSeparable := Algebra.isSeparable_tower_bot_of_isSeparable F _ (SeparableClosure F)
      to_normal := inferInstance },
    le_normalClosure K₀, normalClosure_le_iff_of_normal.mpr hK₀L⟩

set_option backward.isDefEq.respectTransparency true in
/-- **Descent of a twist along a finite Galois tower.** Let `E'/F` be a finite Galois extension
inside the maximal unramified extension, sitting in a tower `E → E' → L` of extensions with `L/F`
normal. If a point `h' ∈ G(E')`, extended to `L`, twists the inflated Galois values of a cocycle on
`Spec E → Spec F` into points with integral coordinates for `M`, the cocycle is trivial. -/
theorem isTrivial_of_integral_twist_of_tower
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (M : IntegralModel 𝒪[F] F G) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    (L : IntermediateField F (SeparableClosure F)) [Normal F L]
    {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [Algebra E L] [IsScalarTower F E L]
    {E' : IntermediateField F (SeparableClosure F)} [FiniteDimensional F E'] [IsGalois F E']
    (hE' : E' ≤ inertiaFixedField F)
    [Algebra E E'] [IsScalarTower F E E'] [Algebra E' L] [IsScalarTower F E' L]
    [IsScalarTower E E' L]
    (ξ : Cocycle G (cover F E)) (h' : G.affinePoints (CommAlgCat.of F E'))
    (hh : ∀ σ : L ≃ₐ[F] L, M.HasIntegralCoordinates L
      ((GaloisPoint.relativeExtend F E' L G h')⁻¹ *
        GaloisPoint.relativeExtend F E L G (value ξ (σ.restrictNormal E)) *
          GaloisPoint.conjugate F L G σ (GaloisPoint.relativeExtend F E' L G h'))) :
    ξ.IsTrivial := by
  have : IsGalois E E' := IsGalois.tower_top_of_isGalois F E E'
  have : FiniteDimensional E E' := Module.Finite.of_restrictScalars_finite F E E'
  have hext : ∀ x : G.affinePoints (CommAlgCat.of F E),
      GaloisPoint.relativeExtend F E' L G (GaloisPoint.relativeExtend F E E' G x) =
        GaloisPoint.relativeExtend F E L G x := by
    intro x
    apply (GaloisPoint.coordinates F G L).injective
    apply AlgHom.ext
    intro a
    rw [GaloisPoint.coordinates_relativeExtend, GaloisPoint.coordinates_relativeExtend,
      GaloisPoint.coordinates_relativeExtend, ← IsScalarTower.algebraMap_apply]
  have hres : ∀ σ' : E' ≃ₐ[F] E', (σ'.liftNormal L).restrictNormal E = σ'.restrictNormal E := by
    intro σ'
    have hσ := IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E E' (σ'.liftNormal L)
    simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply,
      AlgEquiv.restrict_liftNormal] at hσ
    exact hσ
  let ξ' := ξ.refine (coverMap F E E')
  have key : ∀ σ' : E' ≃ₐ[F] E', GaloisPoint.relativeExtend F E' L G
      (h'⁻¹ * value ξ' σ' * GaloisPoint.conjugate F E' G σ' h') =
      (GaloisPoint.relativeExtend F E' L G h')⁻¹ *
        GaloisPoint.relativeExtend F E L G (value ξ ((σ'.liftNormal L).restrictNormal E)) *
          GaloisPoint.conjugate F L G (σ'.liftNormal L) (GaloisPoint.relativeExtend F E' L G h') := by
    intro σ'
    rw [map_mul, map_mul, map_inv, value_refine, hext,
      GaloisPoint.relativeExtend_conjugate_lift, hres σ']
  refine isTrivial_of_refine F E E' ξ
    (isTrivial_of_integral_twist M hM hconn hE' ξ' h' fun σ' => ?_)
  apply IntegralModel.hasIntegralCoordinates_of_relativeExtend M (L := L)
  rw [key σ']
  exact hh (σ'.liftNormal L)

open IntermediateField in
/-- **Descent of an unramified integral twist.** Let `M` be a smooth integral model of `G` over
`𝒪[F]` with connected special fibre, `L` a normal subextension of the maximal unramified extension
of `F` (inside `SeparableClosure F`), and `E/F` a finite Galois extension with an `F`-embedding
into `L`. A cocycle on `Spec E → Spec F` is trivial as soon as some point `h ∈ G(L)` makes all the
twisted values `h⁻¹ · c(σ|E) · σ(h)`, `σ ∈ Gal(L/F)`, have integral coordinates for `M`. -/
theorem isTrivial_of_unramified_integral_twist
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (M : IntegralModel 𝒪[F] F G) (hM : M.IsSmooth)
    (hconn : ConnectedSpace
      ((GroupScheme.baseChange (Spec.algebraMap 𝒪[F] 𝓀[F])).obj M.group).X.left)
    (L : IntermediateField F (SeparableClosure F)) [Normal F L]
    (hL : L ≤ inertiaFixedField F)
    {E : Type u} [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [Algebra E L] [IsScalarTower F E L]
    (ξ : Cocycle G (cover F E)) (h : G.affinePoints (CommAlgCat.of F L))
    (hh : ∀ σ : L ≃ₐ[F] L, M.HasIntegralCoordinates L
      (h⁻¹ * GaloisPoint.relativeExtend F E L G (value ξ (σ.restrictNormal E)) *
        GaloisPoint.conjugate F L G σ h)) :
    ξ.IsTrivial := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType F (AffineCoordinateRing F G.X)).out
  let c := GaloisPoint.coordinates F G L h
  let φ : E →ₐ[F] SeparableClosure F := L.val.comp (IsScalarTower.toAlgHom F E L)
  let S : Set (SeparableClosure F) := (fun a => (c a : SeparableClosure F)) '' (s : Set _)
  let K₀ : IntermediateField F (SeparableClosure F) := φ.fieldRange ⊔ adjoin F S
  have : FiniteDimensional F φ.fieldRange := φ.toLinearMap.finiteDimensional_range
  have : FiniteDimensional F (adjoin F S) :=
    finiteDimensional_adjoin fun x _ => Algebra.IsSeparable.isIntegral F x
  have : FiniteDimensional F K₀ := finiteDimensional_sup _ _
  have hK₀L : K₀ ≤ L := by
    refine sup_le ?_ ?_
    · intro y hy
      obtain ⟨x, rfl⟩ := AlgHom.mem_fieldRange.mp hy
      exact (IsScalarTower.toAlgHom F E L x).property
    · rw [adjoin_le_iff]
      rintro _ ⟨a, -, rfl⟩
      exact (c a).property
  obtain ⟨E', _, _, hK₀E', hE'L⟩ := exists_finiteDimensional_isGalois_between L K₀ hK₀L
  have hφE' : ∀ x, φ x ∈ E' := fun x =>
    hK₀E' ((le_sup_left : φ.fieldRange ≤ K₀) (AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩))
  have hcE' : ∀ a ∈ s, (c a : SeparableClosure F) ∈ E' := fun a ha =>
    hK₀E' ((le_sup_right : adjoin F S ≤ K₀) (subset_adjoin F S ⟨a, ha, rfl⟩))
  let : Algebra E E' := (φ.toRingHom.codRestrict E' hφE').toAlgebra
  let : Algebra E' L := (inclusion hE'L).toAlgebra
  have : IsScalarTower F E E' :=
    IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (φ.commutes x).symm
  have : IsScalarTower F E' L := IsScalarTower.of_algebraMap_eq fun x => rfl
  have : IsScalarTower E E' L := IsScalarTower.of_algebraMap_eq fun x => rfl
  -- the twisting point is defined over `E'`
  let incl := IsScalarTower.toAlgHom F E' L
  have hincl : Function.Injective incl := incl.toRingHom.injective
  have hrange : c.range ≤ incl.range := by
    rw [← Algebra.map_top, ← hs, AlgHom.map_adjoin, Algebra.adjoin_le_iff]
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨⟨c a, hcE' a ha⟩, rfl⟩
  let c' : AffineCoordinateRing F G.X →ₐ[F] E' :=
    (AlgEquiv.ofInjective incl hincl).symm.toAlgHom.comp
      (c.codRestrict incl.range fun a => hrange ⟨a, rfl⟩)
  let h' : G.affinePoints (CommAlgCat.of F E') := (GaloisPoint.coordinates F G E').symm c'
  have hh' : GaloisPoint.relativeExtend F E' L G h' = h := by
    apply (GaloisPoint.coordinates F G L).injective
    apply AlgHom.ext
    intro a
    rw [GaloisPoint.coordinates_relativeExtend, Equiv.apply_symm_apply]
    change incl ((AlgEquiv.ofInjective incl hincl).symm ⟨c a, _⟩) = c a
    rw [← AlgEquiv.ofInjective_apply incl hincl, AlgEquiv.apply_symm_apply]
  rw [← hh'] at hh
  exact isTrivial_of_integral_twist_of_tower M hM hconn L (hE'L.trans hL) ξ h' hh

end GaloisCocycle

end Langlands.GroupScheme
