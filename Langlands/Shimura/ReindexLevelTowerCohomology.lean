import Langlands.Shimura.CofinalLevelReindex
import Langlands.Shimura.LevelTowerGalois
import Langlands.Geometry.EtaleCohomologyReindex

/-! # Level towers of schemes reindexed along level functors over group homomorphisms -/

noncomputable section

universe u

namespace Langlands.Shimura.ReindexLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Geometry.EtaleGaloisAction
open Langlands.Shimura.LevelTowerCohomology Langlands.Shimura.LevelTowerGalois

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {H G : Type u} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {φ : H →* G} (Φ : FunctorOver φ)

/-! ## Reindexed towers and coefficients -/

section Coefficients

variable {T : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The level maps of the reindexed tower `K ↦ T (Φ K)` are étale. -/
instance etale_reindex_map {K L : CompactOpenLevel H} (a : K ⟶ L) :
    Etale ((Φ.functor ⋙ T).map a) :=
  inferInstanceAs (Etale (T.map (Φ.functor.map a)))

omit [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)] in
/-- If each `k ∈ K` acts on level `K` of `T` by the identity, the same holds for the
reindexed tower `K ↦ T (Φ K)`. -/
theorem reindex_selfArrow
    (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
      T.map (selfArrow K k hk) = 𝟙 (T.obj K))
    (K : CompactOpenLevel H) (k : H) (hk : k ∈ K.subgroup) :
    (Φ.functor ⋙ T).map (selfArrow K k hk) = 𝟙 ((Φ.functor ⋙ T).obj K) := by
  change T.map (Φ.functor.map (selfArrow K k hk)) = 𝟙 (T.obj (Φ.functor.obj K))
  rw [Φ.map_selfArrow]
  exact hT _ _ _

/-- Coefficients on the tower `T`, restricted to the levels `Φ K`: a coefficient diagram on the
reindexed tower `K ↦ T (Φ K)`. -/
def reindexCoefficients (D : CoefficientDiagram R T.op) :
    CoefficientDiagram R (Φ.functor ⋙ T).op :=
  CoefficientDiagram.reindex Φ.functor.op D

@[simp] theorem reindexCoefficients_obj (D : CoefficientDiagram R T.op)
    (K : (CompactOpenLevel H)ᵒᵖ) :
    (reindexCoefficients Φ D).obj K = D.obj (op (Φ.functor.obj K.unop)) := rfl

theorem reindexCoefficients_map (D : CoefficientDiagram R T.op) {K L : (CompactOpenLevel H)ᵒᵖ}
    (a : K ⟶ L) : (reindexCoefficients Φ D).map a = D.map (Φ.functor.op.map a) := rfl

theorem reindexCoefficients_cohomology (D : CoefficientDiagram R T.op) (q : ℕ) :
    (reindexCoefficients Φ D).cohomology q = LevelColimit.reindex Φ (D.cohomology q) := rfl

theorem reindexCoefficients_sections (D : CoefficientDiagram R T.op) :
    (reindexCoefficients Φ D).sections = LevelColimit.reindex Φ D.sections := rfl

/-- Reindexing level-trivial coefficients gives level-trivial coefficients. -/
theorem isLevelTrivialCoefficients_reindex {D : CoefficientDiagram R T.op}
    (hD : IsLevelTrivialCoefficients D) :
    IsLevelTrivialCoefficients (reindexCoefficients Φ D) := by
  intro K k hk
  obtain ⟨e, he⟩ := hD (Φ.functor.obj K) (φ k) (Φ.map_mem K hk)
  change ∃ e : T.map (Φ.functor.map (selfArrow K k hk)) = T.map (Φ.functor.map (𝟙 K)),
    D.map (Φ.functor.map (selfArrow K k hk)).op =
      (restrictionCongr R e).hom.app (D.obj (op (Φ.functor.obj K))) ≫
        D.map (Φ.functor.map (𝟙 K)).op
  rw [Φ.map_selfArrow K k hk, Φ.functor.map_id]
  exact ⟨e, he⟩

variable (R T) in
/-- Reindexing along `Φ`, as a functor of level-trivial coefficient diagrams. -/
def reindexCoefficientsFunctor :
    (levelTrivialCoefficients T R).FullSubcategory ⥤
      (levelTrivialCoefficients (Φ.functor ⋙ T) R).FullSubcategory :=
  (levelTrivialCoefficients (Φ.functor ⋙ T) R).lift
    ((levelTrivialCoefficients T R).ι ⋙ CoefficientDiagram.reindexFunctor Φ.functor.op)
    (fun D => isLevelTrivialCoefficients_reindex Φ D.property)

@[simp] theorem reindexCoefficientsFunctor_obj_obj
    (D : (levelTrivialCoefficients T R).FullSubcategory) :
    ((reindexCoefficientsFunctor Φ T R).obj D).obj = reindexCoefficients Φ D.obj := rfl

/-- The cohomology map of a reindexed coefficient morphism is the restricted cohomology map. -/
theorem cohomologyMap_reindex {D E : CoefficientDiagram R T.op} (α : D ⟶ E) (q : ℕ) :
    CoefficientDiagram.cohomologyMap ((CoefficientDiagram.reindexFunctor Φ.functor.op).map α) q =
      Functor.whiskerLeft Φ.functor.op (CoefficientDiagram.cohomologyMap α q) := rfl

end Coefficients

/-! ## The comparison of colimit cohomology -/

section Comparison

variable [IsTopologicalGroup H] [IsTopologicalGroup G]
variable {T : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable {R : Type u} [CommRing R]

/-- The comparison from the colimit over the levels of `H` of the cohomology of
`T (Φ K)` to the colimit over the levels of `G` of the cohomology of `T`, as a morphism of
objects with an action of `H`, where `H` acts on the target through `φ`. -/
def colimitCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ) :
    colimitCohomology (reindexCoefficients Φ D) q ⟶
      (Action.res (ModuleCat.{u} R) φ).obj (colimitCohomology D q) :=
  LevelColimit.reindexComparisonHom Φ (D.cohomology q)

theorem colimitCohomologyComparison_hom (D : CoefficientDiagram R T.op) (q : ℕ) :
    (colimitCohomologyComparison Φ D q).hom = LevelColimit.reindexComparison Φ (D.cohomology q) :=
  rfl

/-- On a class of level `K`, the comparison is the inclusion of level `Φ K`. -/
@[reassoc]
theorem ι_colimitCohomologyComparison (D : CoefficientDiagram R T.op) (q : ℕ)
    (K : CompactOpenLevel H) :
    LevelColimit.ι ((reindexCoefficients Φ D).cohomology q) K ≫
        (colimitCohomologyComparison Φ D q).hom =
      LevelColimit.ι (D.cohomology q) (Φ.functor.obj K) :=
  LevelColimit.ι_reindexComparison Φ (D.cohomology q) K

/-- The comparison is natural in the coefficient diagram. -/
@[reassoc]
theorem map_colimitCohomologyComparison {D E : CoefficientDiagram R T.op} (α : D ⟶ E) (q : ℕ) :
    LevelColimit.map (CoefficientDiagram.cohomologyMap
        ((CoefficientDiagram.reindexFunctor Φ.functor.op).map α) q) ≫
        (colimitCohomologyComparison Φ E q).hom =
      (colimitCohomologyComparison Φ D q).hom ≫
        LevelColimit.map (CoefficientDiagram.cohomologyMap α q) :=
  LevelColimit.map_reindexComparison Φ (CoefficientDiagram.cohomologyMap α q)

/-- If `g` lies in every image level `Φ K`, translation by `g` fixes the image of the
comparison for level-trivial coefficients. -/
theorem translate_colimitCohomologyComparison_apply_of_mem [Nonempty (CompactOpenLevel H)]
    {D : CoefficientDiagram R T.op} (hD : IsLevelTrivialCoefficients D) (q : ℕ) {g : G}
    (hg : ∀ K : CompactOpenLevel H, g ∈ (Φ.functor.obj K).subgroup)
    (x : (colimitCohomology (reindexCoefficients Φ D) q).V) :
    ((colimitCohomology D q).ρ g).hom ((colimitCohomologyComparison Φ D q).hom.hom x) =
      (colimitCohomologyComparison Φ D q).hom.hom x :=
  LevelColimit.translate_reindexComparison_apply_of_mem Φ (D.cohomology q)
    (isLevelTrivial_cohomology hD q) hg x

variable {Φ} in
/-- If every level of `G` contains an image level, the comparison is an isomorphism of objects
with an action of `H`. -/
def colimitCohomologyReindexIso (hΦ : Φ.IsCofinal) (D : CoefficientDiagram R T.op) (q : ℕ) :
    colimitCohomology (reindexCoefficients Φ D) q ≅
      (Action.res (ModuleCat.{u} R) φ).obj (colimitCohomology D q) :=
  LevelColimit.reindexActionIso (D.cohomology q) hΦ

theorem colimitCohomologyReindexIso_hom {Φ : FunctorOver φ} (hΦ : Φ.IsCofinal)
    (D : CoefficientDiagram R T.op) (q : ℕ) :
    (colimitCohomologyReindexIso hΦ D q).hom = colimitCohomologyComparison Φ D q :=
  rfl

end Comparison

/-! ## Coefficients pulled back from a base -/

section Canonical

variable {T : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable (R : Type u) [CommRing R] {X : Scheme.{u}}

/-- The projections `T (Φ K) ⟶ X` of the reindexed tower, for projections `p` of `T`. -/
def reindexProjection (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X) :
    Φ.functor ⋙ T ⟶ (Functor.const (CompactOpenLevel H)).obj X where
  app K := p.app (Φ.functor.obj K)
  naturality _ _ a := p.naturality (Φ.functor.map a)

omit [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)] in
@[simp] theorem reindexProjection_app (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)
    (K : CompactOpenLevel H) : (reindexProjection Φ p).app K = p.app (Φ.functor.obj K) := rfl

variable (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)

/-- Reindexing the coefficients pulled back from `X` gives the coefficients pulled back along
the reindexed projections. -/
theorem reindexCoefficients_canonical (M : ModuleSheaf X R) :
    reindexCoefficients Φ (canonicalCoefficients R p M) =
      canonicalCoefficients R (reindexProjection Φ p) M := rfl

variable {T' : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T'.map a)]
variable (ψ : T' ⟶ T) [∀ K, Etale (ψ.app K)]
variable {p' : T' ⟶ (Functor.const (CompactOpenLevel G)).obj X} (hψ : ψ ≫ p = p')

instance etale_whiskerLeft_app (K : CompactOpenLevel H) :
    Etale ((Functor.whiskerLeft Φ.functor ψ).app K) :=
  inferInstanceAs (Etale (ψ.app (Φ.functor.obj K)))

omit [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)]
  [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T'.map a)] [∀ K, Etale (ψ.app K)] in
include hψ in
/-- The reindexed tower morphism lies over the base through the reindexed projections. -/
theorem whiskerLeft_reindexProjection :
    Functor.whiskerLeft Φ.functor ψ ≫ reindexProjection Φ p = reindexProjection Φ p' := by
  apply NatTrans.ext
  funext K
  exact NatTrans.congr_app hψ (Φ.functor.obj K)

/-- Pullback along the reindexed tower morphism is the restriction of the pullback along `ψ` to
the levels `Φ K`. -/
theorem canonicalPullback_reindex (M : ModuleSheaf X R) (n : ℕ) :
    canonicalPullback R (reindexProjection Φ p) (Functor.whiskerLeft Φ.functor ψ)
        (whiskerLeft_reindexProjection Φ p ψ hψ) M n =
      Functor.whiskerLeft Φ.functor.op (canonicalPullback R p ψ hψ M n) := rfl

/-- The comparison of colimits intertwines the pullbacks along the reindexed tower morphism and
along `ψ`. -/
@[reassoc]
theorem canonicalPullback_reindexComparison (M : ModuleSheaf X R) (n : ℕ) :
    LevelColimit.map (canonicalPullback R (reindexProjection Φ p)
        (Functor.whiskerLeft Φ.functor ψ) (whiskerLeft_reindexProjection Φ p ψ hψ) M n) ≫
        LevelColimit.reindexComparison Φ ((canonicalCoefficients R p' M).cohomology n) =
      LevelColimit.reindexComparison Φ ((canonicalCoefficients R p M).cohomology n) ≫
        LevelColimit.map (canonicalPullback R p ψ hψ M n) :=
  LevelColimit.map_reindexComparison Φ (canonicalPullback R p ψ hψ M n)

end Canonical

/-! ## Base change and the Galois action -/

section Galois

variable {T : CompactOpenLevel G ⥤ Scheme.{u}}
variable (F L : Type u) [CommRing F] [CommRing L] [Algebra F L]
variable (s : T ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))

/-- Base change commutes with reindexing: the base change of the reindexed tower is the
reindexed base-changed tower. -/
theorem baseChangeTower_reindex :
    baseChangeTower F L (reindexProjection Φ s) = Φ.functor ⋙ baseChangeTower F L s := rfl

/-- The Galois automorphism of the reindexed base-changed tower is the restriction of that of
the base-changed tower. -/
theorem towerGaloisAction_reindex (σ : L ≃ₐ[F] L) :
    (towerGaloisAction F L (reindexProjection Φ s) σ).unop.hom =
      Functor.whiskerLeft Φ.functor (towerGaloisAction F L s σ).unop.hom := rfl

variable {X : Scheme.{u}} (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)

/-- The projections of the reindexed base-changed tower to `X` are the reindexed projections
of the base-changed tower. -/
theorem baseChangeProjection_reindex :
    baseChangeProjection F L (reindexProjection Φ s) ≫ reindexProjection Φ p =
      reindexProjection Φ (baseChangeProjection F L s ≫ p) := rfl

variable [∀ {U V : CompactOpenLevel G} (a : U ⟶ V), Etale (T.map a)]
variable [IsTopologicalGroup H] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R]
variable (hT : ∀ (U : CompactOpenLevel G) (k : G) (hk : k ∈ U.subgroup),
  T.map (selfArrow U k hk) = 𝟙 (T.obj U))

/-- The colimit over the levels of `H` of the cohomology of the base changes of `T (Φ K)`, with
coefficients pulled back from `X`, as a smooth representation of `H` with the commuting action
of `L ≃ₐ[F] L`. -/
abbrev reindexGaloisCohomologyFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R H) (L ≃ₐ[F] L) :=
  galoisCohomologyFunctor F L (reindexProjection Φ s) (reindexProjection Φ p) R
    (reindex_selfArrow Φ hT) n

/-- The comparison from the colimit over the levels of `H` to the colimit over the levels of
`G` commutes with the action of every `σ : L ≃ₐ[F] L`. -/
theorem galois_reindexComparison_apply (n : ℕ) (M : ModuleSheaf X R) (σ : L ≃ₐ[F] L)
    (x : ((reindexGaloisCohomologyFunctor Φ F L s p R hT n).obj M).V.obj) :
    (LevelColimit.reindexComparison Φ
        ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom
        ((((reindexGaloisCohomologyFunctor Φ F L s p R hT n).obj M).ρ σ).hom.hom x) =
      (((galoisCohomologyFunctor F L s p R hT n).obj M).ρ σ).hom.hom
        ((LevelColimit.reindexComparison Φ
          ((canonicalCoefficients R (baseChangeProjection F L s ≫ p) M).cohomology n)).hom x) :=
  ConcreteCategory.congr_hom
    (canonicalPullback_reindexComparison Φ R (baseChangeProjection F L s ≫ p)
      (towerGaloisAction F L s σ).unop.hom (towerGaloisAction_over s p σ) M n) x

end Galois

end Langlands.Shimura.ReindexLevelTowerCohomology
