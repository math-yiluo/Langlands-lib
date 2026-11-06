import Langlands.Shimura.LevelHeckeAlgebra
import Langlands.Shimura.LevelHeckeAction

/-! # Fixed vectors of level-tower cohomology as modules over Hecke algebras -/

noncomputable section

universe t v w u'' u

set_option autoImplicit false

namespace Langlands.Shimura.LevelHecke

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite CompactOpenLevel

section Algebraic

variable {R : Type t} [CommRing R] {G : Type v} [Group G] [TopologicalSpace G]

variable (R) in
/-- Restricting the scalars of the Hecke-module of `K`-fixed vectors along
`R → LevelHeckeAlgebra R K` recovers the `R`-module of `K`-fixed vectors. -/
def heckeModuleForgetIso (K : Subgroup G) :
    heckeModuleFunctor.{t, v, w} R K ⋙
        ModuleCat.restrictScalars (algebraMap R (LevelHeckeAlgebra R K)) ≅
      fixedVectorsFunctor R K :=
  NatIso.ofComponents
    (fun A =>
      { hom := ModuleCat.ofHom (X := (ModuleCat.restrictScalars
            (algebraMap R (LevelHeckeAlgebra R K))).obj ((heckeModuleFunctor R K).obj A))
          { toFun := fun x => (x : fixedVectors A.obj.ρ K)
            map_add' := fun _ _ => rfl
            map_smul' := fun r x =>
              algebraMap_smul (M := fixedVectors A.obj.ρ K) (LevelHeckeAlgebra R K) r x }
        inv := ModuleCat.ofHom (Y := (ModuleCat.restrictScalars
            (algebraMap R (LevelHeckeAlgebra R K))).obj ((heckeModuleFunctor R K).obj A))
          { toFun := fun x => (x : fixedVectors A.obj.ρ K)
            map_add' := fun _ _ => rfl
            map_smul' := fun r x =>
              (algebraMap_smul (LevelHeckeAlgebra R K) r (x : fixedVectors A.obj.ρ K)).symm }
        hom_inv_id := rfl
        inv_hom_id := rfl })
    (fun _ => rfl)

variable (Γ : Type u'') [Monoid Γ]

variable (R) in
/-- The `K`-fixed vectors of smooth representations carrying an action of `Γ` by morphisms of
smooth representations, as modules over the Hecke algebra of `K` with the induced action of
`Γ` by module maps. -/
abbrev heckeModuleActionFunctor (K : Subgroup G) :
    Action (SmoothRep.{t, v, w} R G) Γ ⥤ Action (ModuleCat.{w} (LevelHeckeAlgebra R K)) Γ :=
  (heckeModuleFunctor R K).mapAction Γ

theorem heckeModuleActionFunctor_smul (K : Subgroup G) (A : Action (SmoothRep.{t, v, w} R G) Γ)
    (a : LevelHeckeAlgebra R K) (x : fixedVectors A.V.obj.ρ K) :
    a • x = heckeAct A.V.obj.ρ K K a x := rfl

/-- The action of each element of `Γ` commutes with the Hecke algebra. -/
theorem heckeModuleActionFunctor_ρ_smul (K : Subgroup G) (A : Action (SmoothRep.{t, v, w} R G) Γ)
    (γ : Γ) (a : LevelHeckeAlgebra R K) (x : fixedVectors A.V.obj.ρ K) :
    (((heckeModuleActionFunctor R Γ K).obj A).ρ γ).hom (a • x) =
      a • (((heckeModuleActionFunctor R Γ K).obj A).ρ γ).hom x :=
  map_smul (((heckeModuleActionFunctor R Γ K).obj A).ρ γ).hom a x

variable (R) in
/-- Restricting the scalars from the Hecke algebra to `R` recovers the `K`-fixed vectors with
the action of `Γ`. -/
def heckeModuleActionForgetIso (K : Subgroup G) :
    heckeModuleActionFunctor.{t, v, w} R Γ K ⋙
        (ModuleCat.restrictScalars (algebraMap R (LevelHeckeAlgebra R K))).mapAction Γ ≅
      fixedVectorsActionFunctor R Γ K :=
  (Functor.mapActionComp Γ _ _).symm ≪≫ Functor.mapActionCongr Γ (heckeModuleForgetIso R K)

variable [IsTopologicalGroup G]

/-- The double-coset element `[K g K]` of the Hecke algebra acts on the `K`-fixed vectors as
the double-coset operator. -/
theorem doubleCoset_smul_heckeActionNatTrans (K : CompactOpenLevel G) (g : G)
    (A : Action (SmoothRep.{t, v, w} R G) Γ) (x : fixedVectors A.V.obj.ρ K.subgroup) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) • x =
      ((heckeActionNatTrans R Γ K K g).app A).hom x :=
  doubleCoset_smul A.V.obj.ρ K g x

end Algebraic

/-! ## Level towers -/

section Tower

open Langlands.Geometry Langlands.Geometry.EtalePullback
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] {X : Scheme.{u}}

section Whole

open Langlands.Shimura.LevelTowerCohomology

variable {T : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {K L : CompactOpenLevel G} (a : K ⟶ L),
  Etale (T.map a)]
variable (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)
variable (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T.map (selfArrow K k hk) = 𝟙 (T.obj K))
variable (K : CompactOpenLevel G)

section Automorphisms

variable {Γ : Type u''} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ) (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

/-- The `K`-fixed vectors of the colimit over levels of `H^n(T(U), p_U^* M)`, as a module over
the Hecke algebra of `K` with the commuting action of `Γ` by pullback along automorphisms of
the tower, natural in the base sheaf `M`. -/
def automorphismHeckeModuleFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} (LevelHeckeAlgebra R K.subgroup)) Γ :=
  automorphismActionFunctor R p hT ρ hρ n ⋙ heckeModuleActionFunctor R Γ K.subgroup

/-- Restricting the scalars to `R` recovers `automorphismFixedFunctor`. -/
def automorphismHeckeModuleForgetIso (n : ℕ) :
    automorphismHeckeModuleFunctor R p hT K ρ hρ n ⋙
        (ModuleCat.restrictScalars (algebraMap R (LevelHeckeAlgebra R K.subgroup))).mapAction Γ ≅
      automorphismFixedFunctor R p hT K ρ hρ n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (heckeModuleActionForgetIso R Γ K.subgroup)

/-- The double-coset element `[K g K]` acts as `automorphismHecke`. -/
theorem automorphismHeckeModule_doubleCoset_smul (g : G) (n : ℕ) (M : ModuleSheaf X R)
    (x : ((automorphismFixedFunctor R p hT K ρ hρ n).obj M).V) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) •
        (show ((automorphismHeckeModuleFunctor R p hT K ρ hρ n).obj M).V from x) =
      ((automorphismHecke R p hT K K g ρ hρ n).app M).hom x :=
  doubleCoset_smul _ K g x

end Automorphisms

section Galois

variable (F E : Type u) [CommRing F] [CommRing E] [Algebra F E]
variable (s : T ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))

/-- The `K`-fixed vectors of the colimit over levels of
`H^n(T(U) ×_{Spec F} Spec E, (p_U ∘ pr₁)^* M)`, as a module over the Hecke algebra of `K` with
the commuting action of `E ≃ₐ[F] E`, natural in the base sheaf `M`. -/
def galoisHeckeModuleFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} (LevelHeckeAlgebra R K.subgroup)) (E ≃ₐ[F] E) :=
  LevelTowerGalois.galoisCohomologyFunctor F E s p R hT n ⋙
    heckeModuleActionFunctor R (E ≃ₐ[F] E) K.subgroup

/-- Restricting the scalars to `R` recovers `galoisFixedFunctor`. -/
def galoisHeckeModuleForgetIso (n : ℕ) :
    galoisHeckeModuleFunctor R p hT K F E s n ⋙
        (ModuleCat.restrictScalars
          (algebraMap R (LevelHeckeAlgebra R K.subgroup))).mapAction (E ≃ₐ[F] E) ≅
      galoisFixedFunctor R p hT K F E s n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (heckeModuleActionForgetIso R (E ≃ₐ[F] E) K.subgroup)

/-- Each Galois element commutes with every element of the Hecke algebra. -/
theorem galoisHeckeModule_ρ_smul (n : ℕ) (M : ModuleSheaf X R) (σ : E ≃ₐ[F] E)
    (a : LevelHeckeAlgebra R K.subgroup) (x : ((galoisHeckeModuleFunctor R p hT K F E s n).obj M).V) :
    (((galoisHeckeModuleFunctor R p hT K F E s n).obj M).ρ σ).hom (a • x) =
      a • (((galoisHeckeModuleFunctor R p hT K F E s n).obj M).ρ σ).hom x :=
  map_smul _ a x

/-- The double-coset element `[K g K]` acts as `galoisHecke`. -/
theorem galoisHeckeModule_doubleCoset_smul (g : G) (n : ℕ) (M : ModuleSheaf X R)
    (x : ((galoisFixedFunctor R p hT K F E s n).obj M).V) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) •
        (show ((galoisHeckeModuleFunctor R p hT K F E s n).obj M).V from x) =
      ((galoisHecke R p hT K K g F E s n).app M).hom x :=
  doubleCoset_smul _ K g x

end Galois

end Whole

/-! ## Towers over levels satisfying a property -/

section Restricted

open Langlands.Shimura.RestrictedLevelTowerCohomology

variable {P : ObjectProperty (CompactOpenLevel G)} [IsConjStable P]
variable {T : P.FullSubcategory ⥤ Scheme.{u}} [∀ {U V : P.FullSubcategory} (a : U ⟶ V),
  Etale (T.map a)]
variable (p : T ⟶ (Functor.const P.FullSubcategory).obj X)
variable (hT : ∀ (U : P.FullSubcategory) (k : G) (hk : k ∈ U.obj.subgroup),
  T.map (restrictedSelfArrow P U k hk) = 𝟙 (T.obj U))
variable (K : CompactOpenLevel G)

section Automorphisms

variable {Γ : Type u''} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ) (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

/-- The `K`-fixed vectors of the colimit over levels satisfying `P` of `H^n(T(U), p_U^* M)`, as
a module over the Hecke algebra of `K` with the commuting action of `Γ`, natural in the base
sheaf `M`. -/
def restrictedAutomorphismHeckeModuleFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} (LevelHeckeAlgebra R K.subgroup)) Γ :=
  RestrictedLevelTowerCohomology.automorphismActionFunctor R p hT ρ hρ n ⋙
    heckeModuleActionFunctor R Γ K.subgroup

/-- Restricting the scalars to `R` recovers `restrictedAutomorphismFixedFunctor`. -/
def restrictedAutomorphismHeckeModuleForgetIso (n : ℕ) :
    restrictedAutomorphismHeckeModuleFunctor R p hT K ρ hρ n ⋙
        (ModuleCat.restrictScalars (algebraMap R (LevelHeckeAlgebra R K.subgroup))).mapAction Γ ≅
      restrictedAutomorphismFixedFunctor R p hT K ρ hρ n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (heckeModuleActionForgetIso R Γ K.subgroup)

/-- The double-coset element `[K g K]` acts as `restrictedAutomorphismHecke`. -/
theorem restrictedAutomorphismHeckeModule_doubleCoset_smul (g : G) (n : ℕ) (M : ModuleSheaf X R)
    (x : ((restrictedAutomorphismFixedFunctor R p hT K ρ hρ n).obj M).V) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) •
        (show ((restrictedAutomorphismHeckeModuleFunctor R p hT K ρ hρ n).obj M).V from x) =
      ((restrictedAutomorphismHecke R p hT K K g ρ hρ n).app M).hom x :=
  doubleCoset_smul _ K g x

end Automorphisms

section Galois

variable (F E : Type u) [CommRing F] [CommRing E] [Algebra F E]
variable (s : T ⟶ (Functor.const P.FullSubcategory).obj (Spec (CommRingCat.of F)))

/-- The `K`-fixed vectors of the colimit over levels satisfying `P` of
`H^n(T(U) ×_{Spec F} Spec E, (p_U ∘ pr₁)^* M)`, as a module over the Hecke algebra of `K` with
the commuting action of `E ≃ₐ[F] E`, natural in the base sheaf `M`. -/
def restrictedGaloisHeckeModuleFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} (LevelHeckeAlgebra R K.subgroup)) (E ≃ₐ[F] E) :=
  RestrictedLevelTowerGalois.galoisCohomologyFunctor F E s p R hT n ⋙
    heckeModuleActionFunctor R (E ≃ₐ[F] E) K.subgroup

/-- Restricting the scalars to `R` recovers `restrictedGaloisFixedFunctor`. -/
def restrictedGaloisHeckeModuleForgetIso (n : ℕ) :
    restrictedGaloisHeckeModuleFunctor R p hT K F E s n ⋙
        (ModuleCat.restrictScalars
          (algebraMap R (LevelHeckeAlgebra R K.subgroup))).mapAction (E ≃ₐ[F] E) ≅
      restrictedGaloisFixedFunctor R p hT K F E s n :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (heckeModuleActionForgetIso R (E ≃ₐ[F] E) K.subgroup)

/-- Each Galois element commutes with every element of the Hecke algebra. -/
theorem restrictedGaloisHeckeModule_ρ_smul (n : ℕ) (M : ModuleSheaf X R) (σ : E ≃ₐ[F] E)
    (a : LevelHeckeAlgebra R K.subgroup)
    (x : ((restrictedGaloisHeckeModuleFunctor R p hT K F E s n).obj M).V) :
    (((restrictedGaloisHeckeModuleFunctor R p hT K F E s n).obj M).ρ σ).hom (a • x) =
      a • (((restrictedGaloisHeckeModuleFunctor R p hT K F E s n).obj M).ρ σ).hom x :=
  map_smul _ a x

/-- The double-coset element `[K g K]` acts as `restrictedGaloisHecke`. -/
theorem restrictedGaloisHeckeModule_doubleCoset_smul (g : G) (n : ℕ) (M : ModuleSheaf X R)
    (x : ((restrictedGaloisFixedFunctor R p hT K F E s n).obj M).V) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) •
        (show ((restrictedGaloisHeckeModuleFunctor R p hT K F E s n).obj M).V from x) =
      ((restrictedGaloisHecke R p hT K K g F E s n).app M).hom x :=
  doubleCoset_smul _ K g x

end Galois

/-! ### Comparison with towers over all levels -/

section Comparison

variable [IsDownwardClosed P] [Nonempty P.FullSubcategory]
variable {T₀ : CompactOpenLevel G ⥤ Scheme.{u}} [∀ {U V : CompactOpenLevel G} (a : U ⟶ V),
  Etale (T₀.map a)]
variable (p₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj X)
variable (hT₀ : ∀ (U : CompactOpenLevel G) (k : G) (hk : k ∈ U.subgroup),
  T₀.map (selfArrow U k hk) = 𝟙 (T₀.obj U))

section Automorphisms

variable {Γ : Type u''} [Group Γ]
variable (ρ₀ : Γ →* (Aut T₀)ᵐᵒᵖ) (hρ₀ : ∀ γ, (ρ₀ γ).unop.hom ≫ p₀ = p₀)
variable (ρ : Γ →* (Aut (P.ι ⋙ T₀))ᵐᵒᵖ)
  (hρ : ∀ γ, (ρ γ).unop.hom ≫ restrictProjection P p₀ = restrictProjection P p₀)
  (hρρ₀ : ∀ γ, (ρ γ).unop.hom = Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom)

/-- For the restriction of a tower over all levels, the Hecke-modules of `K`-fixed vectors with
the action of `Γ` agree with those of the tower over all levels, naturally in the base sheaf. -/
def restrictedAutomorphismHeckeModuleRestrictIso (n : ℕ) :
    restrictedAutomorphismHeckeModuleFunctor R (restrictProjection P p₀) (restrict_selfArrow hT₀)
        K ρ hρ n ≅
      automorphismHeckeModuleFunctor R p₀ hT₀ K ρ₀ hρ₀ n :=
  Functor.isoWhiskerRight (automorphismActionRestrictIso R p₀ hT₀ ρ₀ hρ₀ ρ hρ hρρ₀ n)
    (heckeModuleActionFunctor R Γ K.subgroup)

end Automorphisms

section Galois

variable (F E : Type u) [CommRing F] [CommRing E] [Algebra F E]
variable (s₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))

/-- For the restriction of a tower over all levels, the Hecke-modules of `K`-fixed vectors of
the colimit cohomology of the base change, with the Galois action, agree with those of the
tower over all levels, naturally in the base sheaf. -/
def restrictedGaloisHeckeModuleRestrictIso (n : ℕ) :
    restrictedGaloisHeckeModuleFunctor R (restrictProjection P p₀) (restrict_selfArrow hT₀) K F E
        (restrictProjection P s₀) n ≅
      galoisHeckeModuleFunctor R p₀ hT₀ K F E s₀ n :=
  Functor.isoWhiskerRight
    (RestrictedLevelTowerGalois.galoisCohomologyRestrictIso F E R s₀ p₀ hT₀ n)
    (heckeModuleActionFunctor R (E ≃ₐ[F] E) K.subgroup)

end Galois

end Comparison

end Restricted

end Tower

end Langlands.Shimura.LevelHecke
