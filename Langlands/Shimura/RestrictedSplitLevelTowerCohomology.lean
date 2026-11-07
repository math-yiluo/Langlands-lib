import Langlands.Shimura.RestrictedReindexLevelTowerCohomology
import Langlands.Shimura.SplitLevelTowerCohomology

/-! # Cohomology of towers over levels satisfying a property, away from a fixed factor

For a splitting `e : G ≃ₜ* H × H'`, a level `K₀` of `H` and a tower `T` of schemes over the
levels of `G` satisfying `P`, the schemes `T (e⁻¹ (K₀ × K'))`, for the levels `K'` of `H'` with
`e⁻¹ (K₀ × K')` satisfying `P`, form a tower over levels of `H'`. Its colimit cohomology is
compared `H'`-equivariantly with the colimit cohomology of `T`, compatibly with the Galois action
on base changes. For a rational involution this applies to the splitting of `GG(A_f)` at the
places dividing `m`. See `RestrictedSplitLevelTowerCohomology.md`.
-/

noncomputable section

universe u

namespace Langlands.Shimura.RestrictedSplitLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open CompactOpenLevel.FunctorOver
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Geometry.EtaleGaloisAction
open Langlands.Shimura.RestrictedLevelTowerCohomology Langlands.Shimura.RestrictedLevelTowerGalois
open Langlands.Shimura.RestrictedReindexLevelTowerCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G H H' : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H')

/-! ## The away levels and the away tower -/

section Levels

variable (P : ObjectProperty (CompactOpenLevel G)) (K₀ : CompactOpenLevel H)

/-- The levels `K'` of `H'` for which `e⁻¹ (K₀ × K')` satisfies `P`. -/
abbrev awayProperty : ObjectProperty (CompactOpenLevel H') :=
  P.inverseImage (awayOver e K₀).functor

theorem awayProperty_iff (K' : CompactOpenLevel H') :
    awayProperty e P K₀ K' ↔ P (transport e.symm (prod K₀ K')) :=
  Iff.rfl

/-- The levels `e⁻¹ (K₀ × K')`, for `K'` in `awayProperty e P K₀`, as levels satisfying `P`. -/
abbrev awayFunctor : (awayProperty e P K₀).FullSubcategory ⥤ P.FullSubcategory :=
  (awayOver e K₀).restrictedFunctor ((awayOver e K₀).mapsTo_inverseImage (P := P))

theorem awayFunctor_obj_obj (K' : (awayProperty e P K₀).FullSubcategory) :
    ((awayFunctor e P K₀).obj K').obj = transport e.symm (prod K₀ K'.obj) :=
  rfl

end Levels

/-! ## The away tower and its coefficients -/

section Coefficients

variable {P : ObjectProperty (CompactOpenLevel G)} (K₀ : CompactOpenLevel H)
variable (T : P.FullSubcategory ⥤ Scheme.{u})
variable {R : Type u} [CommRing R]

/-- The tower `K' ↦ T (e⁻¹ (K₀ × K'))` over the levels `K'` of `H'` with `e⁻¹ (K₀ × K')`
satisfying `P`. -/
abbrev awayLevelTower : (awayProperty e P K₀).FullSubcategory ⥤ Scheme.{u} :=
  awayFunctor e P K₀ ⋙ T

variable {T}

/-- If each `k ∈ K` acts on level `K` of `T` by the identity, the same holds for the away
tower. -/
theorem awayLevelTower_selfArrow
    (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
      T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
    (K' : (awayProperty e P K₀).FullSubcategory) (k : H') (hk : k ∈ K'.obj.subgroup) :
    (awayLevelTower e K₀ T).map (restrictedSelfArrow (awayProperty e P K₀) K' k hk) =
      𝟙 ((awayLevelTower e K₀ T).obj K') :=
  reindex_selfArrow (awayOver e K₀) _ hT K' k hk

variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]

/-- Coefficients on `T`, restricted to the levels `e⁻¹ (K₀ × K')`. -/
abbrev awayCoefficients (D : CoefficientDiagram R T.op) :
    CoefficientDiagram R (awayLevelTower e K₀ T).op :=
  reindexCoefficients (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P)) D

/-- The cohomology of the away coefficients is the reindexed cohomology presheaf. -/
theorem awayCoefficients_cohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    (awayCoefficients e K₀ D).cohomology q =
      RestrictedLevelColimit.reindex (awayOver e K₀)
        ((awayOver e K₀).mapsTo_inverseImage (P := P)) (D.cohomology q) :=
  rfl

theorem isLevelTrivialCoefficients_away {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) : IsLevelTrivialCoefficients (awayCoefficients e K₀ D) :=
  isLevelTrivialCoefficients_reindex (awayOver e K₀) _ hD

/-- The coefficients pulled back from a base `X`, restricted to the away tower, are those pulled
back along the restricted projections. -/
theorem awayCoefficients_canonical {X : Scheme.{u}}
    (p : T ⟶ (Functor.const P.FullSubcategory).obj X) (M : ModuleSheaf X R) :
    awayCoefficients e K₀ (canonicalCoefficients R p M) =
      canonicalCoefficients R
        (reindexProjection (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P)) p) M :=
  reindexCoefficients_canonical (awayOver e K₀) _ R p M

/-- Coefficients on a tower over all levels, restricted to the levels satisfying `P` and then to
the away levels, are the away coefficients restricted to the levels in `awayProperty e P K₀`. -/
theorem awayCoefficients_restrict {T₀ : CompactOpenLevel G ⥤ Scheme.{u}}
    [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T₀.map a)]
    (D₀ : CoefficientDiagram R T₀.op) :
    awayCoefficients e K₀ (restrictCoefficients (P := P) D₀) =
      restrictCoefficients (P := awayProperty e P K₀)
        (SplitLevelTowerCohomology.awayCoefficients e K₀ D₀) :=
  rfl

end Coefficients

/-! ## Away colimit cohomology -/

section Comparison

variable [IsTopologicalGroup G] [IsTopologicalGroup H']
variable {P : ObjectProperty (CompactOpenLevel G)} [IsDownwardClosed P] [IsConjStable P]
variable (K₀ : CompactOpenLevel H) {T : P.FullSubcategory ⥤ Scheme.{u}}
  [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The colimit over the levels `K'` of `H'` with `e⁻¹ (K₀ × K')` satisfying `P` of the degree
`q` cohomology of `T (e⁻¹ (K₀ × K'))`, with its action of `H'`. -/
abbrev awayColimitCohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    Action (ModuleCat.{u} R) H' :=
  colimitCohomology (awayCoefficients e K₀ D) q

/-- The away colimit cohomology of level-trivial coefficients, as a smooth representation of
`H'`. -/
abbrev smoothAwayColimitCohomology (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) : SmoothRep.{u, u, u} R H' :=
  smoothColimitCohomology (awayCoefficients e K₀ D) (isLevelTrivialCoefficients_away e K₀ hD) q

/-- The comparison from the away colimit cohomology at `K₀` to the colimit cohomology of `T`, as
a morphism of objects with an action of `H'`, where `H'` acts on the target through
`awayHom e`. -/
abbrev awayCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ) :
    awayColimitCohomology e K₀ D q ⟶
      (Action.res (ModuleCat.{u} R) (awayHom e)).obj (colimitCohomology D q) :=
  colimitCohomologyComparison (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P)) D q

/-- On a class of level `K'`, the comparison is the inclusion of level `e⁻¹ (K₀ × K')`. -/
@[reassoc]
theorem ι_awayCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ)
    (K' : (awayProperty e P K₀).FullSubcategory) :
    RestrictedLevelColimit.ι ((awayCoefficients e K₀ D).cohomology q) K' ≫
        (awayCohomologyComparison e K₀ D q).hom =
      RestrictedLevelColimit.ι (D.cohomology q) ((awayFunctor e P K₀).obj K') :=
  ι_colimitCohomologyComparison (awayOver e K₀) _ D q K'

/-- The image of the comparison at `K₀` is fixed by `e⁻¹ (k, 1)` for every `k ∈ K₀`. -/
theorem translate_awayCohomologyComparison_apply_of_mem
    [Nonempty (awayProperty e P K₀).FullSubcategory] {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) {k : H} (hk : k ∈ K₀.subgroup)
    (x : (awayColimitCohomology e K₀ D q).V) :
    ((colimitCohomology D q).ρ (factorHom e k)).hom
        ((awayCohomologyComparison e K₀ D q).hom.hom x) =
      (awayCohomologyComparison e K₀ D q).hom.hom x :=
  translate_colimitCohomologyComparison_apply_of_mem (awayOver e K₀) _ hD q
    (fun K' => factorHom_mem_transport_symm_prod e K'.obj hk) x

variable {K₀} in
/-- If every level satisfying `P` contains a level `e⁻¹ (K₀ × K')` satisfying `P`, the comparison
at `K₀` is an isomorphism of objects with an action of `H'`. -/
def awayCohomologyIso (hK₀ : (awayOver e K₀).IsRestrictedCofinal (awayProperty e P K₀) P)
    (D : CoefficientDiagram R T.op) (q : ℕ) :
    awayColimitCohomology e K₀ D q ≅
      (Action.res (ModuleCat.{u} R) (awayHom e)).obj (colimitCohomology D q) :=
  colimitCohomologyReindexIso hK₀ D q

theorem awayCohomologyIso_hom (hK₀ : (awayOver e K₀).IsRestrictedCofinal (awayProperty e P K₀) P)
    (D : CoefficientDiagram R T.op) (q : ℕ) :
    (awayCohomologyIso e hK₀ D q).hom = awayCohomologyComparison e K₀ D q :=
  rfl

/-- Under the identifications of colimit cohomology over levels satisfying a property with
colimit cohomology over all levels, the restricted away comparison at `K₀` is the away
comparison at `K₀` over all levels. -/
theorem awayCohomologyComparison_restrictIso [Nonempty P.FullSubcategory]
    [Nonempty (awayProperty e P K₀).FullSubcategory]
    {T₀ : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
      Etale (T₀.map a)] (D₀ : CoefficientDiagram R T₀.op) (q : ℕ) :
    awayCohomologyComparison e K₀ (restrictCoefficients (P := P) D₀) q ≫
        (Action.res (ModuleCat.{u} R) (awayHom e)).map (colimitCohomologyRestrictIso D₀ q).hom =
      (colimitCohomologyRestrictIso (P := awayProperty e P K₀)
          (SplitLevelTowerCohomology.awayCoefficients e K₀ D₀) q).hom ≫
        SplitLevelTowerCohomology.awayCohomologyComparison e K₀ D₀ q :=
  colimitCohomologyComparison_restrictIso (awayOver e K₀) _ D₀ q

end Comparison

/-! ## Base change and the Galois action -/

section Galois

variable [IsTopologicalGroup G] [IsTopologicalGroup H']
variable {P : ObjectProperty (CompactOpenLevel G)} [IsDownwardClosed P] [IsConjStable P]
variable (K₀ : CompactOpenLevel H) {T : P.FullSubcategory ⥤ Scheme.{u}}
  [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
variable (F L : Type u) [CommRing F] [CommRing L] [Algebra F L]
variable (s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec (CommRingCat.of F)))
variable {X : Scheme.{u}} (p : T ⟶ (Functor.const P.FullSubcategory).obj X)
variable (R : Type u) [CommRing R]
variable (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))

/-- The colimit over the levels `K'` of `H'` with `e⁻¹ (K₀ × K')` satisfying `P` of the
cohomology of the base changes of `T (e⁻¹ (K₀ × K'))`, with coefficients pulled back from `X`,
as a smooth representation of `H'` with the commuting action of `L ≃ₐ[F] L`. -/
abbrev awayGaloisCohomologyFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R H') (L ≃ₐ[F] L) :=
  reindexGaloisCohomologyFunctor (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P))
    F L s p R hT n

/-- The comparison at `K₀` commutes with the action of every `σ : L ≃ₐ[F] L`. -/
theorem galois_awayComparison_apply (n : ℕ) (M : ModuleSheaf X R) (σ : L ≃ₐ[F] L)
    (x : ((awayGaloisCohomologyFunctor e K₀ F L s p R hT n).obj M).V.obj) :
    (RestrictedLevelColimit.reindexComparison (awayOver e K₀)
        ((awayOver e K₀).mapsTo_inverseImage (P := P))
        ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom
        ((((awayGaloisCohomologyFunctor e K₀ F L s p R hT n).obj M).ρ σ).hom.hom x) =
      (((galoisCohomologyFunctor F L s p R hT n).obj M).ρ σ).hom.hom
        ((RestrictedLevelColimit.reindexComparison (awayOver e K₀)
          ((awayOver e K₀).mapsTo_inverseImage (P := P))
          ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom x) :=
  galois_reindexComparison_apply (awayOver e K₀) _ F L s p R hT n M σ x

end Galois

/-! ## Away from the places dividing an integer -/

section PrimeTo

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable (σ : AlgebraInvolution ℚ A) (m : ℕ) (hm : m ≠ 0)
variable {P : ObjectProperty (CompactOpenLevel σ.FiniteAdelicPoints)}
variable (K₀ : CompactOpenLevel (σ.DividingPoints m))

/-- The levels `K'` of `GG(A_f^{(m)})` for which `e⁻¹ (K₀ × K')` satisfies `P`, where `e` is the
splitting at the places dividing `m`. -/
abbrev primeToProperty (P : ObjectProperty (CompactOpenLevel σ.FiniteAdelicPoints)) :
    ObjectProperty (CompactOpenLevel (σ.PrimeToPoints m)) :=
  awayProperty (σ.finiteAdelicPointsSplit m hm) P K₀

variable (T : P.FullSubcategory ⥤ Scheme.{u})

/-- The tower `K' ↦ T (e⁻¹ (K₀ × K'))` over the levels `K'` of `GG(A_f^{(m)})` in
`primeToProperty σ m hm K₀ P`, for a tower `T` over the levels of `GG(A_f)` satisfying `P`. -/
abbrev primeToSchemeTower : (primeToProperty σ m hm K₀ P).FullSubcategory ⥤ Scheme.{u} :=
  awayLevelTower (σ.finiteAdelicPointsSplit m hm) K₀ T

variable {T} [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
variable [IsDownwardClosed P] [IsConjStable P]
variable {R : Type u} [CommRing R]

/-- The prime-to-`m` colimit cohomology at `K₀`, with its action of `GG(A_f^{(m)})`. -/
abbrev primeToColimitCohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    Action (ModuleCat.{u} R) (σ.PrimeToPoints m) :=
  awayColimitCohomology (σ.finiteAdelicPointsSplit m hm) K₀ D q

/-- The prime-to-`m` colimit cohomology of level-trivial coefficients, as a smooth
representation of `GG(A_f^{(m)})`. -/
abbrev smoothPrimeToColimitCohomology (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) : SmoothRep.{u, u, u} R (σ.PrimeToPoints m) :=
  smoothAwayColimitCohomology (σ.finiteAdelicPointsSplit m hm) K₀ D hD q

/-- The comparison from the prime-to-`m` colimit cohomology at `K₀` to the colimit cohomology of
`T`, equivariant for `GG(A_f^{(m)})` acting on the target through the splitting. -/
abbrev primeToCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ) :
    primeToColimitCohomology σ m hm K₀ D q ⟶
      (Action.res (ModuleCat.{u} R) (awayHom (σ.finiteAdelicPointsSplit m hm))).obj
        (colimitCohomology D q) :=
  awayCohomologyComparison (σ.finiteAdelicPointsSplit m hm) K₀ D q

end PrimeTo

end Langlands.Shimura.RestrictedSplitLevelTowerCohomology
