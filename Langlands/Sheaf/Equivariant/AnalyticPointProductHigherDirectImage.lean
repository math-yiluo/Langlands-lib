import Langlands.Sheaf.Equivariant.AnalyticOpenEtaleCohomology
import Langlands.Cohomology.PointProductAcyclic

/-! # Ordinary higher direct images of actual analytic point products -/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointProduct Langlands.Cohomology.PointProductAcyclic

universe u v uL

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable {I : Type (max u (v + 1) uL)}
variable (points : I → (etaleTopology X).Point.{max u (v + 1) uL})

section Constructions

variable [HasSheafify (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]
variable [HasSheafify (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
  (ModuleCat.{max u (v + 1) uL} R)]
variable [LocallySmall.{max u (v + 1) uL} (EtaleSite X)]
variable [(etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).Additive]
variable [PreservesFiniteLimits
  (etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R))]
variable [(etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).PreservesInjectiveObjects]

/-- Ordinary restriction of a raw point product is exact in its coefficients. -/
instance coefficientPointProduct_underlying_preservesEpimorphisms :
    (coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R ⋙
      etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).PreservesEpimorphisms where
  preserves f _ := by
    apply (sheafToPresheaf
      (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
      (ModuleCat.{max u (v + 1) uL} R)).epi_of_epi_map
    have : ∀ U, Epi (((sheafToPresheaf
        (Opens.grothendieckTopology (localizedSpaceFunctor.obj X))
        (ModuleCat.{max u (v + 1) uL} R)).map
          ((coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R ⋙
            etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).map f)).app U) := by
      intro U
      apply (ModuleCat.epi_iff_surjective _).mpr
      exact coefficientProductFunctor_map_surjective.{max u (v + 1) uL, max u (v + 1) uL}
        points R f (op (openEtaleObject X U.unop))
    exact NatTrans.epi_of_epi_app _

instance coefficientPointProduct_underlying_preservesHomology :
    (coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R ⋙
      etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).PreservesHomology := by
  have := coefficientPointProduct_underlying_preservesEpimorphisms.{u, v, uL} X R points
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Resolving the actual independent coefficients gives an injective resolution of
ordinary restriction of the raw analytic point product. -/
def etalePointProductUnderlyingInjectiveResolution
    (M : Discrete I ⥤ ModuleCat.{max u (v + 1) uL} R) :
    InjectiveResolution
      ((etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).obj
        ((coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R).obj M)) := by
  letI := coefficientPointProduct_underlying_preservesHomology.{u, v, uL} X R points
  exact Langlands.Cohomology.DerivedComparison.mapInjectiveResolution
    (coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R ⋙
      etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R))
    (injectiveResolution M)

omit [(etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)).PreservesInjectiveObjects] in
/-- Positive ordinary higher direct images vanish on a raw analytic point product
with arbitrary independent module coefficients. No smooth coreflector is involved. -/
theorem isZero_etaleUnderlyingHigherDirectImage_coefficientPointProduct
    (M : Discrete I ⥤ ModuleCat.{max u (v + 1) uL} R) (q : ℕ) :
    IsZero ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj
      ((coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R).obj M)) := by
  have := etale_enoughInjectives.{u, v, uL} X R
  have := coefficientPointProduct_underlying_preservesHomology.{u, v, uL} X R points
  let T := coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R
  let ε := etaleUnderlyingSheaf X (ModuleCat.{max u (v + 1) uL} R)
  let Q := injectiveResolution M
  let Q' := coefficientProductInjectiveResolution.{max u (v + 1) uL, max u (v + 1) uL} points R M
  refine IsZero.of_iso ?_ (Q'.isoRightDerivedObj ε (q + 1))
  apply HomologicalComplex.ExactAt.isZero_homology
  have h := Q.cocomplex_exactAt_succ q
  rw [HomologicalComplex.exactAt_iff] at h ⊢
  exact h.map (T ⋙ ε)

end Constructions

/-- The raw point-product higher-direct-image vanishing uses only the already
proved analytic size and ordinary-direct-image instances. -/
theorem isZero_etaleUnderlyingHigherDirectImage_pointProduct
    (M : Discrete I ⥤ ModuleCat.{max u (v + 1) uL} R) (q : ℕ) :
    IsZero ((etaleUnderlyingHigherDirectImage.{u, v, uL} X R (q + 1)).obj
      ((coefficientProductFunctor.{max u (v + 1) uL, max u (v + 1) uL} points R).obj M)) := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := underlyingTopology_hasSheafify.{u, v, uL} X R
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := etaleUnderlyingSheaf_additive.{u, v, uL} X R
  have := etaleUnderlyingSheaf_preservesFiniteLimits.{u, v, uL} X R
  exact isZero_etaleUnderlyingHigherDirectImage_coefficientPointProduct.{u, v, uL} X R points M q

end Langlands.Sheaf.Equivariant.Analytic
