import Langlands.Shimura.LevelHecke
import Langlands.Shimura.LevelTowerGalois
import Langlands.Shimura.RestrictedLevelTowerGalois

/-! # Double-coset operators commuting with actions by morphisms of smooth representations -/

noncomputable section

universe t v w u'' u

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CompactOpenLevel

section Action

variable {R : Type t} [CommRing R] {G : Type v} [Group G] [TopologicalSpace G]
variable (Γ : Type u'') [Monoid Γ]

variable (R) in
/-- The `H`-fixed vectors of smooth representations carrying an action of `Γ` by morphisms of
smooth representations, with the induced action of `Γ`. -/
abbrev fixedVectorsActionFunctor (H : Subgroup G) :
    Action (SmoothRep.{t, v, w} R G) Γ ⥤ Action (ModuleCat.{w} R) Γ :=
  (fixedVectorsFunctor R H).mapAction Γ

theorem fixedVectorsActionFunctor_obj_ρ (H : Subgroup G) (A : Action (SmoothRep.{t, v, w} R G) Γ)
    (γ : Γ) :
    ((fixedVectorsActionFunctor R Γ H).obj A).ρ γ =
      ModuleCat.ofHom (fixedVectorsMap (A.ρ γ).hom.hom H) := rfl

variable [IsTopologicalGroup G] (K L : CompactOpenLevel G) (g : G)

variable (R) in
/-- The double-coset operators `[K g L]` commute with every action of `Γ` by morphisms of
smooth representations: they form a natural transformation between the fixed-vector functors
with values in modules with an action of `Γ`. -/
def heckeActionNatTrans :
    fixedVectorsActionFunctor.{t, v, w} R Γ L.subgroup ⟶ fixedVectorsActionFunctor R Γ K.subgroup
    where
  app A :=
    { hom := (heckeNatTrans R K L g).app A.V
      comm := fun γ => (heckeNatTrans R K L g).naturality (A.ρ γ) }
  naturality _ _ f := Action.Hom.ext ((heckeNatTrans R K L g).naturality f.hom)

@[simp] theorem heckeActionNatTrans_app_hom (A : Action (SmoothRep.{t, v, w} R G) Γ) :
    ((heckeActionNatTrans R Γ K L g).app A).hom =
      ModuleCat.ofHom (heckeOperator A.V.obj.ρ K L g) := rfl

/-- The operator `[K 1 K]` is the identity. -/
theorem heckeActionNatTrans_self : heckeActionNatTrans.{t, v, w} R Γ K K 1 = 𝟙 _ := by
  apply NatTrans.ext
  funext A
  apply Action.Hom.ext
  exact NatTrans.congr_app (heckeNatTrans_self K) A.V

end Action

/-! ## Colimit cohomology of level towers with automorphism and Galois actions -/

section Tower

open Langlands.Geometry Langlands.Geometry.EtalePullback
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Shimura.LevelTowerCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {T : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable (R : Type u) [CommRing R] {X : Scheme.{u}}
variable (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)
variable (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T.map (selfArrow K k hk) = 𝟙 (T.obj K))
variable (K L : CompactOpenLevel G) (g : G)

section Automorphisms

variable {Γ : Type u''} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ) (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

/-- The `K`-fixed vectors of the colimit over levels of `H^n(T(U), p_U^* M)`, with the action
of `Γ` by pullback along the automorphisms of the tower, natural in the base sheaf `M`. -/
def automorphismFixedFunctor (n : ℕ) : ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) Γ :=
  automorphismActionFunctor R p hT ρ hρ n ⋙ fixedVectorsActionFunctor R Γ K.subgroup

/-- The double-coset operator `[K g L]` from the `L`-fixed to the `K`-fixed vectors, commuting
with the action of `Γ`, naturally in the base sheaf. -/
def automorphismHecke (n : ℕ) :
    automorphismFixedFunctor R p hT L ρ hρ n ⟶ automorphismFixedFunctor R p hT K ρ hρ n :=
  Functor.whiskerLeft (automorphismActionFunctor R p hT ρ hρ n) (heckeActionNatTrans R Γ K L g)

@[simp] theorem automorphismHecke_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((automorphismHecke R p hT K L g ρ hρ n).app M).hom =
      ModuleCat.ofHom (heckeOperator ((smoothCanonicalCohomologyFunctor R p hT n).obj M).obj.ρ
        K L g) := rfl

end Automorphisms

section Galois

variable (F E : Type u) [CommRing F] [CommRing E] [Algebra F E]
variable (s : T ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))

/-- The `K`-fixed vectors of the colimit over levels of
`H^n(T(U) ×_{Spec F} Spec E, (p_U ∘ pr₁)^* M)`, with the action of `E ≃ₐ[F] E`, natural in
the base sheaf `M`. -/
def galoisFixedFunctor (n : ℕ) : ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) (E ≃ₐ[F] E) :=
  LevelTowerGalois.galoisCohomologyFunctor F E s p R hT n ⋙
    fixedVectorsActionFunctor R (E ≃ₐ[F] E) K.subgroup

/-- The double-coset operator `[K g L]` on these fixed vectors, commuting with the action of
`E ≃ₐ[F] E`, naturally in the base sheaf. -/
def galoisHecke (n : ℕ) :
    galoisFixedFunctor R p hT L F E s n ⟶ galoisFixedFunctor R p hT K F E s n :=
  Functor.whiskerLeft (LevelTowerGalois.galoisCohomologyFunctor F E s p R hT n)
    (heckeActionNatTrans R (E ≃ₐ[F] E) K L g)

@[simp] theorem galoisHecke_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((galoisHecke R p hT K L g F E s n).app M).hom =
      ModuleCat.ofHom (heckeOperator
        (((LevelTowerGalois.galoisCohomologyFunctor F E s p R hT n).obj M).V.obj.ρ) K L g) := rfl

/-- Each Galois element commutes with the double-coset operator. -/
theorem galoisHecke_comm (n : ℕ) (M : ModuleSheaf X R) (σ : E ≃ₐ[F] E) :
    ((galoisFixedFunctor R p hT L F E s n).obj M).ρ σ ≫ ((galoisHecke R p hT K L g F E s n).app M).hom =
      ((galoisHecke R p hT K L g F E s n).app M).hom ≫
        ((galoisFixedFunctor R p hT K F E s n).obj M).ρ σ :=
  ((galoisHecke R p hT K L g F E s n).app M).comm σ

end Galois

end Tower

/-! ## Towers over levels satisfying a property -/

section RestrictedTower

open Langlands.Geometry Langlands.Geometry.EtalePullback
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Shimura.RestrictedLevelTowerCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {P : ObjectProperty (CompactOpenLevel G)} [IsConjStable P]
variable (R : Type u) [CommRing R] {X : Scheme.{u}}

section Restricted

variable {T : P.FullSubcategory ⥤ Scheme.{u}} [∀ {U V : P.FullSubcategory} (a : U ⟶ V),
  Etale (T.map a)]
variable (p : T ⟶ (Functor.const P.FullSubcategory).obj X)
variable (hT : ∀ (U : P.FullSubcategory) (k : G) (hk : k ∈ U.obj.subgroup),
  T.map (restrictedSelfArrow P U k hk) = 𝟙 (T.obj U))
variable (K L : CompactOpenLevel G) (g : G)

section Automorphisms

variable {Γ : Type u''} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ) (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

/-- The `K`-fixed vectors of the colimit over levels satisfying `P` of `H^n(T(U), p_U^* M)`,
with the action of `Γ` by pullback along the automorphisms of the tower, natural in the base
sheaf `M`. -/
def restrictedAutomorphismFixedFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) Γ :=
  RestrictedLevelTowerCohomology.automorphismActionFunctor R p hT ρ hρ n ⋙
    fixedVectorsActionFunctor R Γ K.subgroup

/-- The double-coset operator `[K g L]` from the `L`-fixed to the `K`-fixed vectors, commuting
with the action of `Γ`, naturally in the base sheaf. -/
def restrictedAutomorphismHecke (n : ℕ) :
    restrictedAutomorphismFixedFunctor R p hT L ρ hρ n ⟶
      restrictedAutomorphismFixedFunctor R p hT K ρ hρ n :=
  Functor.whiskerLeft (RestrictedLevelTowerCohomology.automorphismActionFunctor R p hT ρ hρ n)
    (heckeActionNatTrans R Γ K L g)

@[simp] theorem restrictedAutomorphismHecke_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((restrictedAutomorphismHecke R p hT K L g ρ hρ n).app M).hom =
      ModuleCat.ofHom (heckeOperator
        ((RestrictedLevelTowerCohomology.smoothCanonicalCohomologyFunctor R p hT n).obj M).obj.ρ
          K L g) := rfl

end Automorphisms

section Galois

variable (F E : Type u) [CommRing F] [CommRing E] [Algebra F E]
variable (s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec (CommRingCat.of F)))

/-- The `K`-fixed vectors of the colimit over levels satisfying `P` of
`H^n(T(U) ×_{Spec F} Spec E, (p_U ∘ pr₁)^* M)`, with the action of `E ≃ₐ[F] E`, natural in
the base sheaf `M`. -/
def restrictedGaloisFixedFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) (E ≃ₐ[F] E) :=
  RestrictedLevelTowerGalois.galoisCohomologyFunctor F E s p R hT n ⋙
    fixedVectorsActionFunctor R (E ≃ₐ[F] E) K.subgroup

/-- The double-coset operator `[K g L]` on these fixed vectors, commuting with the action of
`E ≃ₐ[F] E`, naturally in the base sheaf. -/
def restrictedGaloisHecke (n : ℕ) :
    restrictedGaloisFixedFunctor R p hT L F E s n ⟶
      restrictedGaloisFixedFunctor R p hT K F E s n :=
  Functor.whiskerLeft (RestrictedLevelTowerGalois.galoisCohomologyFunctor F E s p R hT n)
    (heckeActionNatTrans R (E ≃ₐ[F] E) K L g)

@[simp] theorem restrictedGaloisHecke_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((restrictedGaloisHecke R p hT K L g F E s n).app M).hom =
      ModuleCat.ofHom (heckeOperator
        (((RestrictedLevelTowerGalois.galoisCohomologyFunctor F E s p R hT n).obj M).V.obj.ρ)
          K L g) := rfl

/-- Each Galois element commutes with the double-coset operator. -/
theorem restrictedGaloisHecke_comm (n : ℕ) (M : ModuleSheaf X R) (σ : E ≃ₐ[F] E) :
    ((restrictedGaloisFixedFunctor R p hT L F E s n).obj M).ρ σ ≫
        ((restrictedGaloisHecke R p hT K L g F E s n).app M).hom =
      ((restrictedGaloisHecke R p hT K L g F E s n).app M).hom ≫
        ((restrictedGaloisFixedFunctor R p hT K F E s n).obj M).ρ σ :=
  ((restrictedGaloisHecke R p hT K L g F E s n).app M).comm σ

end Galois

end Restricted

/-! ### Comparison with towers over all levels -/

section Comparison

variable [IsDownwardClosed P] [Nonempty P.FullSubcategory]
variable {T₀ : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {U V : CompactOpenLevel G} (a : U ⟶ V),
  Etale (T₀.map a)]
variable (p₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj X)
variable (hT₀ : ∀ (U : CompactOpenLevel G) (k : G) (hk : k ∈ U.subgroup),
  T₀.map (selfArrow U k hk) = 𝟙 (T₀.obj U))
variable (K L : CompactOpenLevel G) (g : G)

section Automorphisms

variable {Γ : Type u''} [Group Γ]
variable (ρ₀ : Γ →* (Aut T₀)ᵐᵒᵖ) (hρ₀ : ∀ γ, (ρ₀ γ).unop.hom ≫ p₀ = p₀)
variable (ρ : Γ →* (Aut (P.ι ⋙ T₀))ᵐᵒᵖ)
  (hρ : ∀ γ, (ρ γ).unop.hom ≫ restrictProjection P p₀ = restrictProjection P p₀)
  (hρρ₀ : ∀ γ, (ρ γ).unop.hom = Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom)

/-- For the restriction of a tower over all levels, the `K`-fixed vectors with the action of
`Γ` agree with those of the tower over all levels, naturally in the base sheaf. -/
def restrictedAutomorphismFixedRestrictIso (n : ℕ) :
    restrictedAutomorphismFixedFunctor R (restrictProjection P p₀) (restrict_selfArrow hT₀) K ρ
        hρ n ≅
      automorphismFixedFunctor R p₀ hT₀ K ρ₀ hρ₀ n :=
  Functor.isoWhiskerRight (automorphismActionRestrictIso R p₀ hT₀ ρ₀ hρ₀ ρ hρ hρρ₀ n)
    (fixedVectorsActionFunctor R Γ K.subgroup)

/-- The comparison intertwines the double-coset operators. -/
theorem restrictedAutomorphismHecke_restrictIso (n : ℕ) :
    restrictedAutomorphismHecke R (restrictProjection P p₀) (restrict_selfArrow hT₀) K L g ρ hρ
          n ≫
        (restrictedAutomorphismFixedRestrictIso R p₀ hT₀ K ρ₀ hρ₀ ρ hρ hρρ₀ n).hom =
      (restrictedAutomorphismFixedRestrictIso R p₀ hT₀ L ρ₀ hρ₀ ρ hρ hρρ₀ n).hom ≫
        automorphismHecke R p₀ hT₀ K L g ρ₀ hρ₀ n := by
  apply NatTrans.ext
  funext M
  exact ((heckeActionNatTrans R Γ K L g).naturality
    ((automorphismActionRestrictIso R p₀ hT₀ ρ₀ hρ₀ ρ hρ hρρ₀ n).hom.app M)).symm

end Automorphisms

section Galois

variable (F E : Type u) [CommRing F] [CommRing E] [Algebra F E]
variable (s₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))

/-- For the restriction of a tower over all levels, the `K`-fixed vectors of the colimit
cohomology of the base change, with the Galois action, agree with those of the tower over all
levels, naturally in the base sheaf. -/
def restrictedGaloisFixedRestrictIso (n : ℕ) :
    restrictedGaloisFixedFunctor R (restrictProjection P p₀) (restrict_selfArrow hT₀) K F E
        (restrictProjection P s₀) n ≅
      galoisFixedFunctor R p₀ hT₀ K F E s₀ n :=
  Functor.isoWhiskerRight (RestrictedLevelTowerGalois.galoisCohomologyRestrictIso F E R s₀ p₀ hT₀ n)
    (fixedVectorsActionFunctor R (E ≃ₐ[F] E) K.subgroup)

/-- The comparison intertwines the double-coset operators. -/
theorem restrictedGaloisHecke_restrictIso (n : ℕ) :
    restrictedGaloisHecke R (restrictProjection P p₀) (restrict_selfArrow hT₀) K L g F E
          (restrictProjection P s₀) n ≫
        (restrictedGaloisFixedRestrictIso R p₀ hT₀ K F E s₀ n).hom =
      (restrictedGaloisFixedRestrictIso R p₀ hT₀ L F E s₀ n).hom ≫
        galoisHecke R p₀ hT₀ K L g F E s₀ n := by
  apply NatTrans.ext
  funext M
  exact ((heckeActionNatTrans R (E ≃ₐ[F] E) K L g).naturality
    ((RestrictedLevelTowerGalois.galoisCohomologyRestrictIso F E R s₀ p₀ hT₀ n).hom.app M)).symm

end Galois

end Comparison

end RestrictedTower

end Langlands.Shimura.LevelHecke
