import Langlands.Shimura.ReindexLevelTowerCohomology
import Langlands.Shimura.SplitLevelTower
import Langlands.Shimura.Unitary.PointsSplit

/-! # Cohomology of level towers of schemes away from a fixed factor of the level

For a splitting `e : G ≃ₜ* H × H'` and a level `K₀` of `H`, the schemes `T (e⁻¹ (K₀ × K'))` of a
level tower `T` of `G` form a level tower of `H'`. Its colimit cohomology is a smooth
representation of `H'`, compared `H'`-equivariantly with the colimit cohomology of `T`, and the
colimit cohomology of `T` is the colimit over `K₀` of these away colimits. For a rational
involution this applies to the splitting of `GG(A_f)` at the places dividing `m`.
See `SplitLevelTowerCohomology.md`.
-/

noncomputable section

universe u

namespace Langlands.Shimura.SplitLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Geometry.EtaleGaloisAction
open Langlands.Shimura.LevelTowerCohomology Langlands.Shimura.LevelTowerGalois
open Langlands.Shimura.ReindexLevelTowerCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G H H' : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H')

/-! ## The away tower and its coefficients -/

section Coefficients

variable (K₀ : CompactOpenLevel H) (T : CompactOpenLevel G ⥤ Scheme.{u})
variable {R : Type u} [CommRing R]

/-- The level tower `K' ↦ T (e⁻¹ (K₀ × K'))` of `H'`, with the level `K₀` of `H` fixed. -/
abbrev awayLevelTower : CompactOpenLevel H' ⥤ Scheme.{u} :=
  (awayOver e K₀).functor ⋙ T

variable {T}

/-- If each `k ∈ K` acts on level `K` of `T` by the identity, the same holds for the away
tower. -/
theorem awayLevelTower_selfArrow
    (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
      T.map (selfArrow K k hk) = 𝟙 (T.obj K))
    (K' : CompactOpenLevel H') (k : H') (hk : k ∈ K'.subgroup) :
    (awayLevelTower e K₀ T).map (selfArrow K' k hk) = 𝟙 ((awayLevelTower e K₀ T).obj K') :=
  reindex_selfArrow (awayOver e K₀) hT K' k hk

variable [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)]

/-- Coefficients on `T`, restricted to the levels `e⁻¹ (K₀ × K')`. -/
abbrev awayCoefficients (D : CoefficientDiagram R T.op) :
    CoefficientDiagram R (awayLevelTower e K₀ T).op :=
  reindexCoefficients (awayOver e K₀) D

/-- The cohomology of the away coefficients is the away tower of the cohomology presheaf. -/
theorem awayCoefficients_cohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    (awayCoefficients e K₀ D).cohomology q = LevelColimit.awayTower e K₀ (D.cohomology q) :=
  rfl

theorem isLevelTrivialCoefficients_away {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) : IsLevelTrivialCoefficients (awayCoefficients e K₀ D) :=
  isLevelTrivialCoefficients_reindex (awayOver e K₀) hD

/-- The coefficients pulled back from a base `X`, restricted to the away tower, are those pulled
back along the restricted projections. -/
theorem awayCoefficients_canonical {X : Scheme.{u}}
    (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X) (M : ModuleSheaf X R) :
    awayCoefficients e K₀ (canonicalCoefficients R p M) =
      canonicalCoefficients R (reindexProjection (awayOver e K₀) p) M :=
  reindexCoefficients_canonical (awayOver e K₀) R p M

end Coefficients

/-! ## Away colimit cohomology -/

section Comparison

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H']
variable (K₀ : CompactOpenLevel H) {T : CompactOpenLevel G ⥤ Scheme.{u}}
  [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The colimit over the levels `K'` of `H'` of the degree `q` cohomology of
`T (e⁻¹ (K₀ × K'))`, with its action of `H'`. -/
abbrev awayColimitCohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    Action (ModuleCat.{u} R) H' :=
  colimitCohomology (awayCoefficients e K₀ D) q

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem awayColimitCohomology_eq (D : CoefficientDiagram R T.op) (q : ℕ) :
    awayColimitCohomology e K₀ D q =
      LevelColimit.action (LevelColimit.awayTower e K₀ (D.cohomology q)) :=
  rfl

/-- The away colimit cohomology of level-trivial coefficients, as a smooth representation of
`H'`. -/
abbrev smoothAwayColimitCohomology (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) : SmoothRep.{u, u, u} R H' :=
  smoothColimitCohomology (awayCoefficients e K₀ D) (isLevelTrivialCoefficients_away e K₀ hD) q

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem smoothAwayColimitCohomology_eq (D : CoefficientDiagram R T.op)
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) :
    smoothAwayColimitCohomology e K₀ D hD q =
      LevelColimit.awaySmoothRep e K₀ (D.cohomology q) (isLevelTrivial_cohomology hD q) :=
  rfl

/-- The comparison from the away colimit cohomology at `K₀` to the colimit cohomology of `T`, as
a morphism of objects with an action of `H'`, where `H'` acts on the target through
`awayHom e`. -/
abbrev awayCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ) :
    awayColimitCohomology e K₀ D q ⟶
      (Action.res (ModuleCat.{u} R) (awayHom e)).obj (colimitCohomology D q) :=
  colimitCohomologyComparison (awayOver e K₀) D q

omit [IsTopologicalGroup H] in
theorem awayCohomologyComparison_eq (D : CoefficientDiagram R T.op) (q : ℕ) :
    awayCohomologyComparison e K₀ D q = LevelColimit.awayComparison e (D.cohomology q) K₀ :=
  rfl

omit [IsTopologicalGroup H] in
/-- On a class of level `K'`, the comparison is the inclusion of level `e⁻¹ (K₀ × K')`. -/
@[reassoc]
theorem ι_awayCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ)
    (K' : CompactOpenLevel H') :
    LevelColimit.ι ((awayCoefficients e K₀ D).cohomology q) K' ≫
        (awayCohomologyComparison e K₀ D q).hom =
      LevelColimit.ι (D.cohomology q) (transport e.symm (prod K₀ K')) :=
  ι_colimitCohomologyComparison (awayOver e K₀) D q K'

omit [IsTopologicalGroup H] in
/-- The image of the comparison at `K₀` is fixed by `e⁻¹ (k, 1)` for every `k ∈ K₀`. -/
theorem translate_awayCohomologyComparison_apply_of_mem [Nonempty (CompactOpenLevel H')]
    {D : CoefficientDiagram R T.op} (hD : IsLevelTrivialCoefficients D) (q : ℕ) {k : H}
    (hk : k ∈ K₀.subgroup) (x : (awayColimitCohomology e K₀ D q).V) :
    ((colimitCohomology D q).ρ (factorHom e k)).hom
        ((awayCohomologyComparison e K₀ D q).hom.hom x) =
      (awayCohomologyComparison e K₀ D q).hom.hom x :=
  LevelColimit.translate_awayComparison_apply_of_mem e (D.cohomology q)
    (isLevelTrivial_cohomology hD q) K₀ hk x

variable {K₀} in
/-- If every level of `G` contains a level `e⁻¹ (K₀ × K')`, the comparison at `K₀` is an
isomorphism of objects with an action of `H'`. -/
def awayCohomologyIso (hK₀ : (awayOver e K₀).IsCofinal) (D : CoefficientDiagram R T.op)
    (q : ℕ) :
    awayColimitCohomology e K₀ D q ≅
      (Action.res (ModuleCat.{u} R) (awayHom e)).obj (colimitCohomology D q) :=
  colimitCohomologyReindexIso hK₀ D q

omit [IsTopologicalGroup H] in
theorem awayCohomologyIso_hom (hK₀ : (awayOver e K₀).IsCofinal)
    (D : CoefficientDiagram R T.op) (q : ℕ) :
    (awayCohomologyIso e hK₀ D q).hom = awayCohomologyComparison e K₀ D q :=
  rfl

end Comparison

/-! ## Varying the fixed level -/

section Varying

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H']
variable {T : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The away colimit cohomology as a presheaf on the levels `K₀` of `H`, with values objects
with an action of `H'`. -/
abbrev awayColimitCohomologyFunctor (D : CoefficientDiagram R T.op) (q : ℕ) :
    (CompactOpenLevel H)ᵒᵖ ⥤ Action (ModuleCat.{u} R) H' :=
  LevelColimit.awayColimitFunctor e (D.cohomology q)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
theorem awayColimitCohomologyFunctor_obj (D : CoefficientDiagram R T.op) (q : ℕ)
    (K₀ : CompactOpenLevel H) :
    (awayColimitCohomologyFunctor e D q).obj (op K₀) = awayColimitCohomology e K₀ D q :=
  rfl

/-- The transition along `a : K₀ ⟶ K₁` followed by the comparison at `K₀` is the comparison at
`K₁` followed by translation by `e⁻¹ (a.element, 1)`. -/
@[reassoc]
theorem awayColimitCohomologyFunctor_map_comparison (D : CoefficientDiagram R T.op) (q : ℕ)
    {K₀ K₁ : CompactOpenLevel H} (a : K₀ ⟶ K₁) :
    ((awayColimitCohomologyFunctor e D q).map a.op).hom ≫
        (awayCohomologyComparison e K₀ D q).hom =
      (awayCohomologyComparison e K₁ D q).hom ≫
        (colimitCohomology D q).ρ (factorHom e a.element) :=
  LevelColimit.awayColimitFunctor_map_comparison e (D.cohomology q) a

/-- The colimit cohomology of `T` is the colimit over the levels `K₀` of `H` of the away colimit
cohomology, as objects with an action of `H'`, where `H'` acts on the colimit cohomology of `T`
through `awayHom e`. -/
def splitCohomologyIsoAway (D : CoefficientDiagram R T.op) (q : ℕ) :
    LevelColimit.iteratedAction (LevelColimit.splitTower e (D.cohomology q)) ≅
      (Action.res (ModuleCat.{u} R) (awayHom e)).obj (colimitCohomology D q) :=
  LevelColimit.splitColimitIsoAway e (D.cohomology q)

/-- The same isomorphism, as objects with an action of `H`, where `H` acts on the colimit
cohomology of `T` through `factorHom e`. -/
def splitCohomologyIsoFactor (D : CoefficientDiagram R T.op) (q : ℕ) :
    LevelColimit.action (LevelColimit.partialColimit
        (LevelColimit.splitTower e (D.cohomology q))) ≅
      (Action.res (ModuleCat.{u} R) (factorHom e)).obj (colimitCohomology D q) :=
  LevelColimit.splitColimitIsoFactor e (D.cohomology q)

theorem splitCohomologyIsoAway_hom_hom (D : CoefficientDiagram R T.op) (q : ℕ) :
    (splitCohomologyIsoAway e D q).hom.hom = (splitCohomologyIsoFactor e D q).hom.hom :=
  rfl

end Varying

/-! ## Base change and the Galois action -/

section Galois

variable [IsTopologicalGroup G] [IsTopologicalGroup H] [IsTopologicalGroup H']
variable (K₀ : CompactOpenLevel H) {T : CompactOpenLevel G ⥤ Scheme.{u}}
  [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)]
variable (F L : Type u) [CommRing F] [CommRing L] [Algebra F L]
variable (s : T ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))
variable {X : Scheme.{u}} (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)
variable (R : Type u) [CommRing R]
variable (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T.map (selfArrow K k hk) = 𝟙 (T.obj K))

/-- The colimit over the levels `K'` of `H'` of the cohomology of the base changes of
`T (e⁻¹ (K₀ × K'))`, with coefficients pulled back from `X`, as a smooth representation of `H'`
with the commuting action of `L ≃ₐ[F] L`. -/
abbrev awayGaloisCohomologyFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R H') (L ≃ₐ[F] L) :=
  reindexGaloisCohomologyFunctor (awayOver e K₀) F L s p R hT n

omit [IsTopologicalGroup H] in
/-- The comparison at `K₀` commutes with the action of every `σ : L ≃ₐ[F] L`. -/
theorem galois_awayComparison_apply (n : ℕ) (M : ModuleSheaf X R) (σ : L ≃ₐ[F] L)
    (x : ((awayGaloisCohomologyFunctor e K₀ F L s p R hT n).obj M).V.obj) :
    (LevelColimit.reindexComparison (awayOver e K₀)
        ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom
        ((((awayGaloisCohomologyFunctor e K₀ F L s p R hT n).obj M).ρ σ).hom.hom x) =
      (((galoisCohomologyFunctor F L s p R hT n).obj M).ρ σ).hom.hom
        ((LevelColimit.reindexComparison (awayOver e K₀)
          ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom x) :=
  galois_reindexComparison_apply (awayOver e K₀) F L s p R hT n M σ x

end Galois

/-! ## Away from the places dividing an integer -/

section PrimeTo

variable {A : Type u} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable (σ : AlgebraInvolution ℚ A) (m : ℕ) (hm : m ≠ 0)
variable (K₀ : CompactOpenLevel (σ.DividingPoints m))
variable (T : CompactOpenLevel σ.FiniteAdelicPoints ⥤ Scheme.{u})
  [∀ {K L : CompactOpenLevel σ.FiniteAdelicPoints} (a : K ⟶ L), Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The level tower `K' ↦ T (e⁻¹ (K₀ × K'))` of `GG(A_f^{(m)})` for a level tower `T` of
`GG(A_f)`, where `e` is the splitting at the places dividing `m` and `K₀` is a fixed level of
`GG(∏_{v ∣ m} ℚ_v)`. -/
abbrev primeToSchemeTower : CompactOpenLevel (σ.PrimeToPoints m) ⥤ Scheme.{u} :=
  awayLevelTower (σ.finiteAdelicPointsSplit m hm) K₀ T

variable {T}

/-- The colimit over the levels `K'` of `GG(A_f^{(m)})` of the degree `q` cohomology of
`T (e⁻¹ (K₀ × K'))`, with its action of `GG(A_f^{(m)})`. -/
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

/-- The prime-to-`m` colimit cohomology as a presheaf on the levels `K₀` of
`GG(∏_{v ∣ m} ℚ_v)`. -/
abbrev primeToColimitCohomologyFunctor (D : CoefficientDiagram R T.op) (q : ℕ) :
    (CompactOpenLevel (σ.DividingPoints m))ᵒᵖ ⥤ Action (ModuleCat.{u} R) (σ.PrimeToPoints m) :=
  awayColimitCohomologyFunctor (σ.finiteAdelicPointsSplit m hm) D q

/-- The colimit cohomology of `T` is the colimit over the levels `K₀` of `GG(∏_{v ∣ m} ℚ_v)` of
the prime-to-`m` colimit cohomology, equivariantly for `GG(A_f^{(m)})`. -/
abbrev primeToSplitCohomologyIso (D : CoefficientDiagram R T.op) (q : ℕ) :
    LevelColimit.iteratedAction
        (LevelColimit.splitTower (σ.finiteAdelicPointsSplit m hm) (D.cohomology q)) ≅
      (Action.res (ModuleCat.{u} R) (awayHom (σ.finiteAdelicPointsSplit m hm))).obj
        (colimitCohomology D q) :=
  splitCohomologyIsoAway (σ.finiteAdelicPointsSplit m hm) D q

end PrimeTo

end Langlands.Shimura.SplitLevelTowerCohomology
