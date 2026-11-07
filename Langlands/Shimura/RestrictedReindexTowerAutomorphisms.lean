import Langlands.Shimura.RestrictedSplitLevelTowerCohomology

/-! # Automorphisms of towers over levels satisfying a property, reindexed along level functors

A group acting by automorphisms over a base on a tower `T` of schemes over the levels satisfying
`P` acts, by restriction, on the reindexed tower `K ↦ T (Φ K)` along a level functor `Φ`. The
induced action on colimit cohomology with coefficients pulled back from the base commutes with
the comparison of colimits. The same holds for the away tower `K' ↦ T (e⁻¹ (K₀ × K'))`. See
`RestrictedReindexTowerAutomorphisms.md`.
-/

noncomputable section

universe v u

namespace Langlands.Shimura.RestrictedReindexLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel CompactOpenLevel.FunctorOver
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Shimura.RestrictedLevelTowerCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {H G : Type u} [Group H] [TopologicalSpace H] [Group G] [TopologicalSpace G]
  {φ : H →* G} (Φ : FunctorOver φ) {P : ObjectProperty (CompactOpenLevel G)}
  {P' : ObjectProperty (CompactOpenLevel H)} (hΦ : ∀ K, P' K → P (Φ.functor.obj K))

/-! ## Restricting automorphisms of a tower -/

section Automorphisms

variable (T : P.FullSubcategory ⥤ Scheme.{u})

/-- The restriction of automorphisms of the tower `T` to the reindexed tower `K ↦ T (Φ K)`, by
whiskering with the level functor. -/
def reindexAutHom : Aut T →* Aut (Φ.restrictedFunctor hΦ ⋙ T) :=
  ((Functor.whiskeringLeft _ _ Scheme.{u}).obj (Φ.restrictedFunctor hΦ)).mapAut T

@[simp] theorem reindexAutHom_hom (α : Aut T) :
    (reindexAutHom Φ hΦ T α).hom = Functor.whiskerLeft (Φ.restrictedFunctor hΦ) α.hom :=
  rfl

variable {T} {Γ : Type v} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ)

/-- A group acting on the tower `T` by automorphisms acts on the reindexed tower `K ↦ T (Φ K)`
by their restrictions. -/
def reindexAutomorphisms : Γ →* (Aut (Φ.restrictedFunctor hΦ ⋙ T))ᵐᵒᵖ :=
  (MonoidHom.op (reindexAutHom Φ hΦ T)).comp ρ

@[simp] theorem reindexAutomorphisms_hom (γ : Γ) :
    (reindexAutomorphisms Φ hΦ ρ γ).unop.hom =
      Functor.whiskerLeft (Φ.restrictedFunctor hΦ) (ρ γ).unop.hom :=
  rfl

variable {X : Scheme.{u}} {p : T ⟶ (Functor.const P.FullSubcategory).obj X}
  (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

include hρ in
/-- Restrictions of automorphisms over the base are over the base for the reindexed
projections. -/
theorem reindexAutomorphisms_over (γ : Γ) :
    (reindexAutomorphisms Φ hΦ ρ γ).unop.hom ≫ reindexProjection Φ hΦ p =
      reindexProjection Φ hΦ p :=
  whiskerLeft_reindexProjection Φ hΦ p (ρ γ).unop.hom (hρ γ)

/-! ## The action on colimit cohomology and the comparison -/

variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
variable [IsTopologicalGroup H] [IsTopologicalGroup G] [IsConjStable P] [IsConjStable P']
variable (R : Type u) [CommRing R]
variable (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))

/-- The colimit over the levels satisfying `P'` of the cohomology of `T (Φ K)`, with
coefficients pulled back from `X`, as a smooth representation of `H` with the commuting action
of `Γ` by pullback along the restricted automorphisms. -/
abbrev reindexAutomorphismActionFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R H) Γ :=
  automorphismActionFunctor R (reindexProjection Φ hΦ p) (reindex_selfArrow Φ hΦ hT)
    (reindexAutomorphisms Φ hΦ ρ) (reindexAutomorphisms_over Φ hΦ ρ hρ) n

/-- The comparison from the colimit over the levels satisfying `P'` to the colimit over the
levels satisfying `P` commutes with the action of every `γ : Γ`. -/
theorem automorphism_reindexComparison_apply (n : ℕ) (M : ModuleSheaf X R) (γ : Γ)
    (x : ((reindexAutomorphismActionFunctor Φ hΦ ρ hρ R hT n).obj M).V.obj) :
    (RestrictedLevelColimit.reindexComparison Φ hΦ
        ((canonicalCoefficients R p M).cohomology n)).hom
        ((((reindexAutomorphismActionFunctor Φ hΦ ρ hρ R hT n).obj M).ρ γ).hom.hom x) =
      (((automorphismActionFunctor R p hT ρ hρ n).obj M).ρ γ).hom.hom
        ((RestrictedLevelColimit.reindexComparison Φ hΦ
          ((canonicalCoefficients R p M).cohomology n)).hom x) :=
  ConcreteCategory.congr_hom
    (canonicalPullback_reindexComparison Φ hΦ R p (ρ γ).unop.hom (hρ γ) M n) x

end Automorphisms

end Langlands.Shimura.RestrictedReindexLevelTowerCohomology

namespace Langlands.Shimura.RestrictedSplitLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open CompactOpenLevel.FunctorOver
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Shimura.RestrictedLevelTowerCohomology
open Langlands.Shimura.RestrictedReindexLevelTowerCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G H H' : Type u} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
  [Group H'] [TopologicalSpace H'] (e : G ≃ₜ* H × H')

/-! ## Automorphisms of away towers -/

section Automorphisms

variable {P : ObjectProperty (CompactOpenLevel G)} (K₀ : CompactOpenLevel H)
variable {T : P.FullSubcategory ⥤ Scheme.{u}} {Γ : Type v} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ)

/-- A group acting on the tower `T` by automorphisms acts on the away tower
`K' ↦ T (e⁻¹ (K₀ × K'))` by their restrictions. -/
abbrev awayAutomorphisms : Γ →* (Aut (awayLevelTower e K₀ T))ᵐᵒᵖ :=
  reindexAutomorphisms (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P)) ρ

theorem awayAutomorphisms_hom (γ : Γ) :
    (awayAutomorphisms e K₀ ρ γ).unop.hom =
      Functor.whiskerLeft (awayFunctor e P K₀) (ρ γ).unop.hom :=
  rfl

variable {X : Scheme.{u}} {p : T ⟶ (Functor.const P.FullSubcategory).obj X}
  (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

include hρ in
/-- Restrictions of automorphisms over the base are over the base for the away projections. -/
theorem awayAutomorphisms_over (γ : Γ) :
    (awayAutomorphisms e K₀ ρ γ).unop.hom ≫
        reindexProjection (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P)) p =
      reindexProjection (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P)) p :=
  reindexAutomorphisms_over (awayOver e K₀) _ ρ hρ γ

variable [IsTopologicalGroup G] [IsTopologicalGroup H'] [IsDownwardClosed P] [IsConjStable P]
variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]
variable (R : Type u) [CommRing R]
variable (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))

/-- The colimit over the levels `K'` of `H'` with `e⁻¹ (K₀ × K')` satisfying `P` of the
cohomology of `T (e⁻¹ (K₀ × K'))`, with coefficients pulled back from `X`, as a smooth
representation of `H'` with the commuting action of `Γ` by pullback along the restricted
automorphisms. -/
abbrev awayAutomorphismActionFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R H') Γ :=
  reindexAutomorphismActionFunctor (awayOver e K₀) ((awayOver e K₀).mapsTo_inverseImage (P := P))
    ρ hρ R hT n

/-- The comparison at `K₀` commutes with the action of every `γ : Γ`. -/
theorem automorphism_awayComparison_apply (n : ℕ) (M : ModuleSheaf X R) (γ : Γ)
    (x : ((awayAutomorphismActionFunctor e K₀ ρ hρ R hT n).obj M).V.obj) :
    (awayCohomologyComparison e K₀ (canonicalCoefficients R p M) n).hom.hom
        ((((awayAutomorphismActionFunctor e K₀ ρ hρ R hT n).obj M).ρ γ).hom.hom x) =
      (((automorphismActionFunctor R p hT ρ hρ n).obj M).ρ γ).hom.hom
        ((awayCohomologyComparison e K₀ (canonicalCoefficients R p M) n).hom.hom x) :=
  automorphism_reindexComparison_apply (awayOver e K₀) _ ρ hρ R hT n M γ x

end Automorphisms

end Langlands.Shimura.RestrictedSplitLevelTowerCohomology
