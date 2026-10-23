import Langlands.ClassField.Global.IdeleCohomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The actual principal-idele coefficient sequence -/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField CategoryTheory
open scoped NumberField
open Langlands.Global.AdelicFunctoriality Langlands.ClassFieldTheory.Local

universe u

variable (F E : Type u) [Field F] [Field E] [NumberField E] [Algebra F E]

/-- The principal embedding is equivariant for the arithmetic actions. -/
theorem relativeIdeleAut_unitEmbedding (σ : E ≃ₐ[F] E) (x : Eˣ) :
    relativeIdeleAut F E σ (IdeleGroup.unitEmbedding (𝓞 E) E x) =
      IdeleGroup.unitEmbedding (𝓞 E) E (Units.map σ.toRingEquiv.toMonoidHom x) :=
  ideleEquiv_diagonal σ.toRingEquiv x

/-- The quotient projection is equivariant for the arithmetic actions. -/
theorem relativeIdeleClassAut_quotient (σ : E ≃ₐ[F] E) (x : IdeleGroup (𝓞 E) E) :
    relativeIdeleClassAut F E σ (QuotientGroup.mk x) =
      QuotientGroup.mk (relativeIdeleAut F E σ x) := rfl

/-- The actual principal embedding, linear over the lifted integers. -/
def principalIdeleLinear :
    (unitsRepresentation F E).V →ₗ[NormalizedTwoCocycle.CoefficientScalars.{u}]
      (relativeIdeleRepresentation F E).V where
  toFun x := Additive.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E (@Additive.toMul Eˣ x))
  map_add' x y := congrArg Additive.ofMul (map_mul (IdeleGroup.unitEmbedding (𝓞 E) E)
    (@Additive.toMul Eˣ x) (@Additive.toMul Eˣ y))
  map_smul' r x := congrArg Additive.ofMul (map_zpow (IdeleGroup.unitEmbedding (𝓞 E) E)
    (@Additive.toMul Eˣ x) r.down)

/-- The actual principal embedding as a morphism of representations. -/
def principalIdeleCoefficients : unitsRepresentation F E ⟶ relativeIdeleRepresentation F E :=
  Rep.ofHom
    { toLinearMap := principalIdeleLinear F E
      isIntertwining' σ := by
        ext x
        exact congrArg Additive.ofMul
          (relativeIdeleAut_unitEmbedding F E σ (@Additive.toMul Eˣ x)).symm }

@[simp] theorem principalIdeleCoefficients_apply (x : Additive Eˣ) :
    (principalIdeleCoefficients F E).hom x =
      Additive.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E x.toMul) := rfl

/-- The actual quotient by principal ideles, linear over the lifted integers. -/
def ideleQuotientLinear :
    (relativeIdeleRepresentation F E).V →ₗ[NormalizedTwoCocycle.CoefficientScalars.{u}]
      (relativeIdeleClassRepresentation F E).V where
  toFun x := Additive.ofMul
    (QuotientGroup.mk (@Additive.toMul (IdeleGroup (𝓞 E) E) x))
  map_add' x y := congrArg Additive.ofMul
    (map_mul (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E))
      (@Additive.toMul (IdeleGroup (𝓞 E) E) x) (@Additive.toMul (IdeleGroup (𝓞 E) E) y))
  map_smul' r x := congrArg Additive.ofMul
    (map_zpow (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 E) E))
      (@Additive.toMul (IdeleGroup (𝓞 E) E) x) r.down)

/-- The actual quotient as a morphism of representations. -/
def ideleQuotientCoefficients :
    relativeIdeleRepresentation F E ⟶ relativeIdeleClassRepresentation F E :=
  Rep.ofHom
    { toLinearMap := ideleQuotientLinear F E
      isIntertwining' σ := by ext x; rfl }

@[simp] theorem ideleQuotientCoefficients_apply (x : Additive (IdeleGroup (𝓞 E) E)) :
    (ideleQuotientCoefficients F E).hom x =
      Additive.ofMul (QuotientGroup.mk x.toMul) := rfl

/-- Injectivity of the principal embedding follows from the adelic diagonal. -/
theorem principalIdeleCoefficients_injective :
    Function.Injective (principalIdeleCoefficients F E).hom := by
  intro x y h
  apply Additive.toMul.injective
  apply Units.ext
  apply AdeleRing.algebraMap_injective (𝓞 E) E
  exact congrArg (fun z : Additive (IdeleGroup (𝓞 E) E) => (z.toMul : AdeleRing (𝓞 E) E)) h

/-- Every idele class has an idele representative. -/
theorem ideleQuotientCoefficients_surjective :
    Function.Surjective (ideleQuotientCoefficients F E).hom := by
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective x.toMul
  exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

/-- The kernel of the actual quotient is the image of the actual principal embedding. -/
theorem principalIdeleCoefficients_range_eq_ker :
    LinearMap.range (principalIdeleCoefficients F E).hom.toLinearMap =
      LinearMap.ker (ideleQuotientCoefficients F E).hom.toLinearMap := by
  ext x
  change (∃ y : Additive Eˣ, Additive.ofMul
    (IdeleGroup.unitEmbedding (𝓞 E) E y.toMul) = x) ↔
      Additive.ofMul (QuotientGroup.mk x.toMul : IdeleClassGroup (𝓞 E) E) = 0
  constructor
  · rintro ⟨y, rfl⟩
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff _).mpr ⟨y.toMul, rfl⟩)
  · intro h
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff (@Additive.toMul (IdeleGroup (𝓞 E) E) x)).mp
      (congrArg (@Additive.toMul (IdeleClassGroup (𝓞 E) E)) h)
    exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩

@[reassoc (attr := simp)]
theorem principalIdeleCoefficients_comp_ideleQuotientCoefficients :
    principalIdeleCoefficients F E ≫ ideleQuotientCoefficients F E = 0 := by
  ext x
  exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff _).mpr
    ⟨@Additive.toMul Eˣ x, rfl⟩)

/-- The actual coefficient complex `Eˣ → J_E → C_E`. -/
def ideleCoefficientSequence :
    ShortComplex (Rep.{u} NormalizedTwoCocycle.CoefficientScalars.{u} (E ≃ₐ[F] E)) :=
  ShortComplex.mk (principalIdeleCoefficients F E) (ideleQuotientCoefficients F E)
    (principalIdeleCoefficients_comp_ideleQuotientCoefficients F E)

private theorem rep_exact_of_range_eq_ker {R G : Type u} [CommRing R] [Group G]
    (S : ShortComplex (Rep.{u} R G))
    (h : LinearMap.range S.f.hom.toLinearMap = LinearMap.ker S.g.hom.toLinearMap) :
    S.Exact := by
  apply (S.exact_map_iff_of_faithful (forget₂ (Rep.{u} R G) (ModuleCat.{u} R))).mp
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr h

/-- The actual coefficient complex is short exact, with no additional arithmetic assumptions. -/
theorem ideleCoefficientSequence_shortExact : (ideleCoefficientSequence F E).ShortExact where
  exact := rep_exact_of_range_eq_ker _ (principalIdeleCoefficients_range_eq_ker F E)
  mono_f := (Rep.mono_iff_injective _).mpr (principalIdeleCoefficients_injective F E)
  epi_g := (Rep.epi_iff_surjective _).mpr (ideleQuotientCoefficients_surjective F E)

/-- The principal embedding on ordinary cohomology in every degree. -/
abbrev principalIdeleCohomologyMap (n : ℕ) :
    relativeCohomology F E n ⟶ relativeIdeleCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (principalIdeleCoefficients F E) n

/-- The quotient projection on ordinary cohomology in every degree. -/
abbrev ideleQuotientCohomologyMap (n : ℕ) :
    relativeIdeleCohomology F E n ⟶ relativeIdeleClassCohomology F E n :=
  groupCohomology.map (MonoidHom.id _) (ideleQuotientCoefficients F E) n

/-- The consecutive maps on ordinary cohomology compose to zero, including degree zero. -/
@[reassoc (attr := simp)]
theorem principalIdeleCohomologyMap_comp_ideleQuotientCohomologyMap (n : ℕ) :
    principalIdeleCohomologyMap F E n ≫ ideleQuotientCohomologyMap F E n = 0 := by
  rw [← groupCohomology.map_id_comp,
    principalIdeleCoefficients_comp_ideleQuotientCoefficients]
  exact (groupCohomology.functor NormalizedTwoCocycle.CoefficientScalars.{u}
    (E ≃ₐ[F] E) n).map_zero _ _

/-- Push a two-cocycle forward along the actual principal embedding. -/
abbrev principalIdeleCocycles₂ :
    ModuleCat.of NormalizedTwoCocycle.CoefficientScalars.{u} (groupCohomology.cocycles₂ (unitsRepresentation F E)) ⟶
      ModuleCat.of NormalizedTwoCocycle.CoefficientScalars.{u} (groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :=
  groupCohomology.mapCocycles₂ (MonoidHom.id _) (principalIdeleCoefficients F E)

/-- Push a two-cocycle forward along the actual quotient. -/
abbrev ideleQuotientCocycles₂ :
    ModuleCat.of NormalizedTwoCocycle.CoefficientScalars.{u} (groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) ⟶
      ModuleCat.of NormalizedTwoCocycle.CoefficientScalars.{u} (groupCohomology.cocycles₂ (relativeIdeleClassRepresentation F E)) :=
  groupCohomology.mapCocycles₂ (MonoidHom.id _) (ideleQuotientCoefficients F E)

@[simp] theorem principalIdeleCocycles₂_apply
    (z : groupCohomology.cocycles₂ (unitsRepresentation F E)) (σ τ : E ≃ₐ[F] E) :
    principalIdeleCocycles₂ F E z (σ, τ) =
      Additive.ofMul (IdeleGroup.unitEmbedding (𝓞 E) E (z (σ, τ)).toMul) := rfl

@[simp] theorem ideleQuotientCocycles₂_apply
    (z : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) (σ τ : E ≃ₐ[F] E) :
    ideleQuotientCocycles₂ F E z (σ, τ) =
      Additive.ofMul (QuotientGroup.mk (@Additive.toMul (IdeleGroup (𝓞 E) E) (z (σ, τ)))) := rfl

@[simp] theorem principalIdeleCohomologyMap_H2π
    (z : groupCohomology.cocycles₂ (unitsRepresentation F E)) :
    principalIdeleCohomologyMap F E 2 (groupCohomology.H2π _ z) =
      groupCohomology.H2π _ (principalIdeleCocycles₂ F E z) :=
  groupCohomology.H2π_comp_map_apply _ _ _

@[simp] theorem ideleQuotientCohomologyMap_H2π
    (z : groupCohomology.cocycles₂ (relativeIdeleRepresentation F E)) :
    ideleQuotientCohomologyMap F E 2 (groupCohomology.H2π _ z) =
      groupCohomology.H2π _ (ideleQuotientCocycles₂ F E z) :=
  groupCohomology.H2π_comp_map_apply _ _ _

section FinitePlace

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.Global.CompletionPadic

variable {F E} [NumberField F] [Normal F E]
  (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Taking a finite coordinate of a principal idele is the field localization map. -/
@[reassoc (attr := simp)]
theorem principalIdeleCoefficients_comp_ideleLocalProjection :
    (Rep.resFunctor (k := NormalizedTwoCocycle.CoefficientScalars.{u})
      (FundamentalClass.decompositionHom v w)).map (principalIdeleCoefficients F E) ≫
      ideleLocalProjection v w = unitsLocalization v w := by
  ext x
  exact congrArg Additive.ofMul (Units.ext (ideleCoordinate_unitEmbedding w
    (@Additive.toMul Eˣ x)))

/-- The finite local component of a principal cohomology class is its localization. -/
@[reassoc (attr := simp)]
theorem principalIdeleCohomologyMap_comp_ideleLocalMap (n : ℕ) :
    principalIdeleCohomologyMap F E n ≫ ideleLocalMap v w n = unitsLocalMap v w n := by
  rw [principalIdeleCohomologyMap, ideleLocalMap, ← groupCohomology.map_comp,
    principalIdeleCoefficients_comp_ideleLocalProjection]
  rfl

end FinitePlace

end Langlands.ClassField.Global
