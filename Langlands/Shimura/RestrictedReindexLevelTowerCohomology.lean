import Langlands.Shimura.RestrictedLevelReindex
import Langlands.Shimura.RestrictedLevelTowerGalois
import Langlands.Shimura.ReindexLevelTowerCohomology

/-! # Towers of schemes over levels satisfying a property, reindexed along level functors

A level functor `Φ` over `φ : H →* G` sending the levels satisfying `P'` to levels satisfying `P`
restricts a tower `T` of schemes over the levels satisfying `P` to the tower `K ↦ T (Φ K)` over
the levels satisfying `P'`. Its colimit cohomology is compared `H`-equivariantly with that of
`T`. See `RestrictedReindexLevelTowerCohomology.md`.
-/

noncomputable section

universe u

namespace Langlands.Shimura.RestrictedReindexLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel CompactOpenLevel.FunctorOver
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Geometry.EtaleGaloisAction
open Langlands.Shimura.RestrictedLevelTowerCohomology Langlands.Shimura.RestrictedLevelTowerGalois

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {H G : Type u} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {φ : H →* G} (Φ : FunctorOver φ) {P : ObjectProperty (CompactOpenLevel G)}
  {P' : ObjectProperty (CompactOpenLevel H)} (hΦ : ∀ K, P' K → P (Φ.functor.obj K))

/-! ## Reindexed towers and coefficients -/

section Coefficients

variable {T : P.FullSubcategory ⥤ Scheme.{u}} [∀ {K L : P.FullSubcategory} (a : K ⟶ L),
  Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The level maps of the reindexed tower `K ↦ T (Φ K)` are étale. -/
instance etale_reindex_map {K L : P'.FullSubcategory} (a : K ⟶ L) :
    Etale ((Φ.restrictedFunctor hΦ ⋙ T).map a) :=
  inferInstanceAs (Etale (T.map ((Φ.restrictedFunctor hΦ).map a)))

omit [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)] in
/-- If each `k ∈ K` acts on level `K` of `T` by the identity, the same holds for the
reindexed tower `K ↦ T (Φ K)`. -/
theorem reindex_selfArrow
    (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
      T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
    (K : P'.FullSubcategory) (k : H) (hk : k ∈ K.obj.subgroup) :
    (Φ.restrictedFunctor hΦ ⋙ T).map (restrictedSelfArrow P' K k hk) =
      𝟙 ((Φ.restrictedFunctor hΦ ⋙ T).obj K) := by
  change T.map ((Φ.restrictedFunctor hΦ).map (restrictedSelfArrow P' K k hk)) =
    𝟙 (T.obj ((Φ.restrictedFunctor hΦ).obj K))
  rw [restrictedFunctor_map_restrictedSelfArrow]
  exact hT _ _ _

/-- Coefficients on the tower `T`, restricted to the levels `Φ K`: a coefficient diagram on the
reindexed tower `K ↦ T (Φ K)`. -/
def reindexCoefficients (D : CoefficientDiagram R T.op) :
    CoefficientDiagram R (Φ.restrictedFunctor hΦ ⋙ T).op :=
  CoefficientDiagram.reindex (Φ.restrictedFunctor hΦ).op D

@[simp] theorem reindexCoefficients_obj (D : CoefficientDiagram R T.op)
    (K : P'.FullSubcategoryᵒᵖ) :
    (reindexCoefficients Φ hΦ D).obj K = D.obj (op ((Φ.restrictedFunctor hΦ).obj K.unop)) := rfl

theorem reindexCoefficients_map (D : CoefficientDiagram R T.op) {K L : P'.FullSubcategoryᵒᵖ}
    (a : K ⟶ L) :
    (reindexCoefficients Φ hΦ D).map a = D.map ((Φ.restrictedFunctor hΦ).op.map a) := rfl

theorem reindexCoefficients_cohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    (reindexCoefficients Φ hΦ D).cohomology q =
      RestrictedLevelColimit.reindex Φ hΦ (D.cohomology q) := rfl

theorem reindexCoefficients_sections (D : CoefficientDiagram R T.op) :
    (reindexCoefficients Φ hΦ D).sections = RestrictedLevelColimit.reindex Φ hΦ D.sections := rfl

/-- Reindexing level-trivial coefficients gives level-trivial coefficients. -/
theorem isLevelTrivialCoefficients_reindex {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) :
    IsLevelTrivialCoefficients (reindexCoefficients Φ hΦ D) := by
  intro K k hk
  obtain ⟨e, he⟩ := hD ((Φ.restrictedFunctor hΦ).obj K) (φ k) (Φ.map_mem K.obj hk)
  change ∃ e : T.map ((Φ.restrictedFunctor hΦ).map (restrictedSelfArrow P' K k hk)) =
      T.map ((Φ.restrictedFunctor hΦ).map (𝟙 K)),
    D.map ((Φ.restrictedFunctor hΦ).map (restrictedSelfArrow P' K k hk)).op =
      (restrictionCongr R e).hom.app (D.obj (op ((Φ.restrictedFunctor hΦ).obj K))) ≫
        D.map ((Φ.restrictedFunctor hΦ).map (𝟙 K)).op
  rw [restrictedFunctor_map_restrictedSelfArrow, (Φ.restrictedFunctor hΦ).map_id]
  exact ⟨e, he⟩

variable (R T) in
/-- Reindexing along `Φ`, as a functor of level-trivial coefficient diagrams. -/
def reindexCoefficientsFunctor :
    (levelTrivialCoefficients T R).FullSubcategory ⥤
      (levelTrivialCoefficients (Φ.restrictedFunctor hΦ ⋙ T) R).FullSubcategory :=
  (levelTrivialCoefficients (Φ.restrictedFunctor hΦ ⋙ T) R).lift
    ((levelTrivialCoefficients T R).ι ⋙
      CoefficientDiagram.reindexFunctor (Φ.restrictedFunctor hΦ).op)
    (fun D => isLevelTrivialCoefficients_reindex Φ hΦ D.property)

@[simp] theorem reindexCoefficientsFunctor_obj_obj
    (D : (levelTrivialCoefficients T R).FullSubcategory) :
    ((reindexCoefficientsFunctor Φ hΦ T R).obj D).obj = reindexCoefficients Φ hΦ D.obj := rfl

/-- The cohomology map of a reindexed coefficient morphism is the restricted cohomology map. -/
theorem cohomologyMap_reindex {D E : CoefficientDiagram R T.op} (α : D ⟶ E) (q : ℕ) :
    CoefficientDiagram.cohomologyMap
        ((CoefficientDiagram.reindexFunctor (Φ.restrictedFunctor hΦ).op).map α) q =
      Functor.whiskerLeft (Φ.restrictedFunctor hΦ).op (CoefficientDiagram.cohomologyMap α q) :=
  rfl

end Coefficients

/-! ## Comparison with towers over all levels -/

section Restrict

variable {T₀ : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T₀.map a)]
variable {R : Type u} [CommRing R]

/-- Coefficients on a tower over all levels, restricted to the levels satisfying `P` and then
reindexed along `Φ`, are the coefficients reindexed along `Φ` and then restricted to the levels
satisfying `P'`. -/
theorem reindexCoefficients_restrict (D₀ : CoefficientDiagram R T₀.op) :
    reindexCoefficients Φ hΦ (restrictCoefficients (P := P) D₀) =
      restrictCoefficients (P := P') (ReindexLevelTowerCohomology.reindexCoefficients Φ D₀) :=
  rfl

end Restrict

/-! ## The comparison of colimit cohomology -/

section Comparison

variable [IsTopologicalGroup H] [IsTopologicalGroup G] [IsConjStable P] [IsConjStable P']
variable {T : P.FullSubcategory ⥤ Scheme.{u}} [∀ {K L : P.FullSubcategory} (a : K ⟶ L),
  Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The comparison from the colimit over the levels satisfying `P'` of the cohomology of
`T (Φ K)` to the colimit over the levels satisfying `P` of the cohomology of `T`, as a morphism
of objects with an action of `H`, where `H` acts on the target through `φ`. -/
def colimitCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ) :
    colimitCohomology (reindexCoefficients Φ hΦ D) q ⟶
      (Action.res (ModuleCat.{u} R) φ).obj (colimitCohomology D q) :=
  RestrictedLevelColimit.reindexComparisonHom Φ hΦ (D.cohomology q)

theorem colimitCohomologyComparison_hom (D : CoefficientDiagram R T.op) (q : ℕ) :
    (colimitCohomologyComparison Φ hΦ D q).hom =
      RestrictedLevelColimit.reindexComparison Φ hΦ (D.cohomology q) :=
  rfl

/-- On a class of level `K`, the comparison is the inclusion of level `Φ K`. -/
@[reassoc]
theorem ι_colimitCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ)
    (K : P'.FullSubcategory) :
    RestrictedLevelColimit.ι ((reindexCoefficients Φ hΦ D).cohomology q) K ≫
        (colimitCohomologyComparison Φ hΦ D q).hom =
      RestrictedLevelColimit.ι (D.cohomology q) ((Φ.restrictedFunctor hΦ).obj K) :=
  RestrictedLevelColimit.ι_reindexComparison Φ hΦ (D.cohomology q) K

/-- The comparison is natural in the coefficient diagram. -/
@[reassoc]
theorem map_colimitCohomologyComparison {D E : CoefficientDiagram R T.op} (α : D ⟶ E) (q : ℕ) :
    RestrictedLevelColimit.map (CoefficientDiagram.cohomologyMap
        ((CoefficientDiagram.reindexFunctor (Φ.restrictedFunctor hΦ).op).map α) q) ≫
        (colimitCohomologyComparison Φ hΦ E q).hom =
      (colimitCohomologyComparison Φ hΦ D q).hom ≫
        RestrictedLevelColimit.map (CoefficientDiagram.cohomologyMap α q) :=
  RestrictedLevelColimit.map_reindexComparison Φ hΦ (CoefficientDiagram.cohomologyMap α q)

/-- If `g` lies in every image level `Φ K`, translation by `g` fixes the image of the
comparison for level-trivial coefficients. -/
theorem translate_colimitCohomologyComparison_apply_of_mem [IsDownwardClosed P']
    [Nonempty P'.FullSubcategory] {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) (q : ℕ) {g : G}
    (hg : ∀ K : P'.FullSubcategory, g ∈ (Φ.functor.obj K.obj).subgroup)
    (x : (colimitCohomology (reindexCoefficients Φ hΦ D) q).V) :
    ((colimitCohomology D q).ρ g).hom ((colimitCohomologyComparison Φ hΦ D q).hom.hom x) =
      (colimitCohomologyComparison Φ hΦ D q).hom.hom x :=
  RestrictedLevelColimit.translate_reindexComparison_apply_of_mem Φ hΦ (D.cohomology q)
    (isLevelTrivial_cohomology hD q) hg x

variable {Φ hΦ} in
/-- If every level satisfying `P` contains the image of a level satisfying `P'`, the comparison
is an isomorphism of objects with an action of `H`. -/
def colimitCohomologyReindexIso [IsDownwardClosed P'] (hc : Φ.IsRestrictedCofinal P' P)
    (D : CoefficientDiagram R T.op) (q : ℕ) :
    colimitCohomology (reindexCoefficients Φ hΦ D) q ≅
      (Action.res (ModuleCat.{u} R) φ).obj (colimitCohomology D q) :=
  RestrictedLevelColimit.reindexActionIso hΦ (D.cohomology q) hc

theorem colimitCohomologyReindexIso_hom [IsDownwardClosed P'] (hc : Φ.IsRestrictedCofinal P' P)
    (D : CoefficientDiagram R T.op) (q : ℕ) :
    (colimitCohomologyReindexIso hc D q).hom = colimitCohomologyComparison Φ hΦ D q :=
  rfl

/-- Under the identifications of colimit cohomology over levels satisfying a property with
colimit cohomology over all levels, the restricted comparison along `Φ` is the comparison along
`Φ` over all levels. -/
theorem colimitCohomologyComparison_restrictIso [IsDownwardClosed P] [Nonempty P.FullSubcategory]
    [IsDownwardClosed P'] [Nonempty P'.FullSubcategory]
    {T₀ : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
      Etale (T₀.map a)] (D₀ : CoefficientDiagram R T₀.op) (q : ℕ) :
    colimitCohomologyComparison Φ hΦ (restrictCoefficients (P := P) D₀) q ≫
        (Action.res (ModuleCat.{u} R) φ).map (colimitCohomologyRestrictIso D₀ q).hom =
      (colimitCohomologyRestrictIso (P := P')
          (ReindexLevelTowerCohomology.reindexCoefficients Φ D₀) q).hom ≫
        ReindexLevelTowerCohomology.colimitCohomologyComparison Φ D₀ q :=
  RestrictedLevelColimit.reindexComparisonHom_actionRestrictIso_hom Φ hΦ (D₀.cohomology q)

end Comparison

/-! ## Coefficients pulled back from a base -/

section Canonical

variable {T : P.FullSubcategory ⥤ Scheme.{u}} [∀ {K L : P.FullSubcategory} (a : K ⟶ L),
  Etale (T.map a)]
variable (R : Type u) [CommRing R] {X : Scheme.{u}}

/-- The projections `T (Φ K) ⟶ X` of the reindexed tower, for projections `p` of `T`. -/
def reindexProjection (p : T ⟶ (Functor.const P.FullSubcategory).obj X) :
    Φ.restrictedFunctor hΦ ⋙ T ⟶ (Functor.const P'.FullSubcategory).obj X where
  app K := p.app ((Φ.restrictedFunctor hΦ).obj K)
  naturality _ _ a := p.naturality ((Φ.restrictedFunctor hΦ).map a)

omit [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)] in
@[simp] theorem reindexProjection_app (p : T ⟶ (Functor.const P.FullSubcategory).obj X)
    (K : P'.FullSubcategory) :
    (reindexProjection Φ hΦ p).app K = p.app ((Φ.restrictedFunctor hΦ).obj K) := rfl

omit [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)] in
/-- The reindexed restriction of the projections of a tower over all levels is the restriction
of its reindexed projections. -/
theorem reindexProjection_restrict {T₀ : CompactOpenLevel G ⥤ Scheme.{u}}
    (p₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj X) :
    reindexProjection Φ hΦ (restrictProjection P p₀) =
      restrictProjection P' (ReindexLevelTowerCohomology.reindexProjection Φ p₀) := rfl

variable (p : T ⟶ (Functor.const P.FullSubcategory).obj X)

/-- Reindexing the coefficients pulled back from `X` gives the coefficients pulled back along
the reindexed projections. -/
theorem reindexCoefficients_canonical (M : ModuleSheaf X R) :
    reindexCoefficients Φ hΦ (canonicalCoefficients R p M) =
      canonicalCoefficients R (reindexProjection Φ hΦ p) M := rfl

variable {T' : P.FullSubcategory ⥤ Scheme.{u}} [∀ {K L : P.FullSubcategory} (a : K ⟶ L),
  Etale (T'.map a)]
variable (ψ : T' ⟶ T) [∀ K, Etale (ψ.app K)]
variable {p' : T' ⟶ (Functor.const P.FullSubcategory).obj X} (hψ : ψ ≫ p = p')

instance etale_whiskerLeft_app (K : P'.FullSubcategory) :
    Etale ((Functor.whiskerLeft (Φ.restrictedFunctor hΦ) ψ).app K) :=
  inferInstanceAs (Etale (ψ.app ((Φ.restrictedFunctor hΦ).obj K)))

omit [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
  [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T'.map a)] [∀ K, Etale (ψ.app K)] in
include hψ in
/-- The reindexed tower morphism lies over the base through the reindexed projections. -/
theorem whiskerLeft_reindexProjection :
    Functor.whiskerLeft (Φ.restrictedFunctor hΦ) ψ ≫ reindexProjection Φ hΦ p =
      reindexProjection Φ hΦ p' := by
  apply NatTrans.ext
  funext K
  exact NatTrans.congr_app hψ ((Φ.restrictedFunctor hΦ).obj K)

/-- Pullback along the reindexed tower morphism is the restriction of the pullback along `ψ` to
the levels `Φ K`. -/
theorem canonicalPullback_reindex (M : ModuleSheaf X R) (n : ℕ) :
    canonicalPullback R (reindexProjection Φ hΦ p) (Functor.whiskerLeft (Φ.restrictedFunctor hΦ) ψ)
        (whiskerLeft_reindexProjection Φ hΦ p ψ hψ) M n =
      Functor.whiskerLeft (Φ.restrictedFunctor hΦ).op (canonicalPullback R p ψ hψ M n) := rfl

/-- The comparison of colimits intertwines the pullbacks along the reindexed tower morphism and
along `ψ`. -/
@[reassoc]
theorem canonicalPullback_reindexComparison (M : ModuleSheaf X R) (n : ℕ) :
    RestrictedLevelColimit.map (canonicalPullback R (reindexProjection Φ hΦ p)
        (Functor.whiskerLeft (Φ.restrictedFunctor hΦ) ψ)
        (whiskerLeft_reindexProjection Φ hΦ p ψ hψ) M n) ≫
        RestrictedLevelColimit.reindexComparison Φ hΦ
          ((canonicalCoefficients R p' M).cohomology n) =
      RestrictedLevelColimit.reindexComparison Φ hΦ
          ((canonicalCoefficients R p M).cohomology n) ≫
        RestrictedLevelColimit.map (canonicalPullback R p ψ hψ M n) :=
  RestrictedLevelColimit.map_reindexComparison Φ hΦ (canonicalPullback R p ψ hψ M n)

end Canonical

/-! ## Base change and the Galois action -/

section Galois

variable {T : P.FullSubcategory ⥤ Scheme.{u}}
variable (F L : Type u) [CommRing F] [CommRing L] [Algebra F L]
variable (s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec (CommRingCat.of F)))

/-- Base change commutes with reindexing: the base change of the reindexed tower is the
reindexed base-changed tower. -/
theorem baseChangeTower_reindex :
    baseChangeTower F L (reindexProjection Φ hΦ s) =
      Φ.restrictedFunctor hΦ ⋙ baseChangeTower F L s := rfl

/-- The Galois automorphism of the reindexed base-changed tower is the restriction of that of
the base-changed tower. -/
theorem towerGaloisAction_reindex (σ : L ≃ₐ[F] L) :
    (towerGaloisAction F L (reindexProjection Φ hΦ s) σ).unop.hom =
      Functor.whiskerLeft (Φ.restrictedFunctor hΦ) (towerGaloisAction F L s σ).unop.hom := rfl

variable {X : Scheme.{u}} (p : T ⟶ (Functor.const P.FullSubcategory).obj X)

/-- The projections of the reindexed base-changed tower to `X` are the reindexed projections
of the base-changed tower. -/
theorem baseChangeProjection_reindex :
    baseChangeProjection F L (reindexProjection Φ hΦ s) ≫ reindexProjection Φ hΦ p =
      reindexProjection Φ hΦ (baseChangeProjection F L s ≫ p) := rfl

variable [∀ {U V : P.FullSubcategory} (a : U ⟶ V), Etale (T.map a)]
variable [IsTopologicalGroup H] [IsTopologicalGroup G] [IsConjStable P] [IsConjStable P']
variable (R : Type u) [CommRing R]
variable (hT : ∀ (U : P.FullSubcategory) (k : G) (hk : k ∈ U.obj.subgroup),
  T.map (restrictedSelfArrow P U k hk) = 𝟙 (T.obj U))

/-- The colimit over the levels satisfying `P'` of the cohomology of the base changes of
`T (Φ K)`, with coefficients pulled back from `X`, as a smooth representation of `H` with the
commuting action of `L ≃ₐ[F] L`. -/
abbrev reindexGaloisCohomologyFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R H) (L ≃ₐ[F] L) :=
  galoisCohomologyFunctor F L (reindexProjection Φ hΦ s) (reindexProjection Φ hΦ p) R
    (reindex_selfArrow Φ hΦ hT) n

/-- The comparison from the colimit over the levels satisfying `P'` to the colimit over the
levels satisfying `P` commutes with the action of every `σ : L ≃ₐ[F] L`. -/
theorem galois_reindexComparison_apply (n : ℕ) (M : ModuleSheaf X R) (σ : L ≃ₐ[F] L)
    (x : ((reindexGaloisCohomologyFunctor Φ hΦ F L s p R hT n).obj M).V.obj) :
    (RestrictedLevelColimit.reindexComparison Φ hΦ
        ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom
        ((((reindexGaloisCohomologyFunctor Φ hΦ F L s p R hT n).obj M).ρ σ).hom.hom x) =
      (((galoisCohomologyFunctor F L s p R hT n).obj M).ρ σ).hom.hom
        ((RestrictedLevelColimit.reindexComparison Φ hΦ
          ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom x) :=
  ConcreteCategory.congr_hom
    (canonicalPullback_reindexComparison Φ hΦ R (baseChangeProjection F L s ≫ p)
      (towerGaloisAction F L s σ).unop.hom (towerGaloisAction_over s p σ) M n) x

end Galois

end Langlands.Shimura.RestrictedReindexLevelTowerCohomology
