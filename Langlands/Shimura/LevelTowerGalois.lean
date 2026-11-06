import Langlands.Shimura.LevelTowerCanonicalCoefficients
import Langlands.Geometry.EtaleGaloisAction

/-! # Base change of level towers and the Galois action on their colimit cohomology -/

noncomputable section

universe u

namespace Langlands.Shimura.LevelTowerGalois

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections
open Langlands.Geometry.EtaleGaloisAction Langlands.Shimura.LevelTowerCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G : Type u} [Group G] [TopologicalSpace G] {T : CompactOpenLevel G ⥤ Scheme.{u}}
variable (F L : Type u) [CommRing F] [CommRing L] [Algebra F L]
variable (s : T ⟶ (Functor.const (CompactOpenLevel G)).obj (Spec (CommRingCat.of F)))

variable {F} in
theorem structure_naturality {U V : CompactOpenLevel G} (a : U ⟶ V) :
    T.map a ≫ s.app V = s.app U := by
  have h := s.naturality a
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
  exact h

/-- The tower of base changes `T(U) ×_{Spec F} Spec L`, with the level maps induced by
those of `T` on the first factor. -/
def baseChangeTower : CompactOpenLevel G ⥤ Scheme.{u} where
  obj U := baseChange F L (s.app U)
  map {U V} a := pullback.map (s.app U) (Spec.algebraMap F L) (s.app V) (Spec.algebraMap F L)
    (T.map a) (𝟙 _) (𝟙 _) (by rw [Category.comp_id, structure_naturality]) (by simp)
  map_id U := by
    apply pullback.hom_ext <;> simp
  map_comp a b := by
    apply pullback.hom_ext <;> simp

theorem baseChangeTower_map_fst {U V : CompactOpenLevel G} (a : U ⟶ V) :
    (baseChangeTower F L s).map a ≫ pullback.fst (s.app V) (Spec.algebraMap F L) =
      pullback.fst (s.app U) (Spec.algebraMap F L) ≫ T.map a :=
  pullback.lift_fst _ _ _

theorem baseChangeTower_map_snd {U V : CompactOpenLevel G} (a : U ⟶ V) :
    (baseChangeTower F L s).map a ≫ pullback.snd (s.app V) (Spec.algebraMap F L) =
      pullback.snd (s.app U) (Spec.algebraMap F L) := by
  change pullback.lift _ _ _ ≫ _ = _
  rw [pullback.lift_snd, Category.comp_id]

/-- Level maps of the base-changed tower are étale, as base changes of étale maps. -/
instance etale_baseChangeTower_map [∀ {U V : CompactOpenLevel G} (a : U ⟶ V), Etale (T.map a)]
    {U V : CompactOpenLevel G} (a : U ⟶ V) : Etale ((baseChangeTower F L s).map a) :=
  MorphismProperty.pullbackMap (P := @Etale) (inferInstanceAs (Etale (T.map a)))
    (inferInstanceAs (Etale (𝟙 (Spec (CommRingCat.of L)))))
    (structure_naturality s a).symm (Category.id_comp _).symm

/-- The first projection from the base-changed tower to the original tower. -/
def baseChangeProjection : baseChangeTower F L s ⟶ T where
  app U := pullback.fst (s.app U) (Spec.algebraMap F L)
  naturality _ _ a := baseChangeTower_map_fst F L s a

/-- If each `k ∈ U` acts on `T(U)` by the identity, the same holds for the base change. -/
theorem baseChangeTower_selfArrow
    (hT : ∀ (U : CompactOpenLevel G) (k : G) (hk : k ∈ U.subgroup),
      T.map (selfArrow U k hk) = 𝟙 (T.obj U))
    (U : CompactOpenLevel G) (k : G) (hk : k ∈ U.subgroup) :
    (baseChangeTower F L s).map (selfArrow U k hk) = 𝟙 ((baseChangeTower F L s).obj U) := by
  apply pullback.hom_ext
  · rw [baseChangeTower_map_fst, hT U k hk, Category.comp_id, Category.id_comp]
  · rw [baseChangeTower_map_snd, Category.id_comp]

variable {F L}

/-- The automorphism of the base-changed tower induced by `σ` on the second factor. -/
def towerGaloisAut (σ : L ≃ₐ[F] L) : baseChangeTower F L s ≅ baseChangeTower F L s :=
  NatIso.ofComponents (fun U => baseChangeAut (s.app U) σ) (fun {U V} a => by
    apply pullback.hom_ext <;> simp [baseChangeTower, baseChangeAut, baseChangeMap])

@[simp] theorem towerGaloisAut_hom_app (σ : L ≃ₐ[F] L) (U : CompactOpenLevel G) :
    (towerGaloisAut s σ).hom.app U = baseChangeMap (s.app U) σ := rfl

variable (F L) in
/-- The action of `L ≃ₐ[F] L` on the base-changed tower, in the opposite of its automorphism
group, as for a single base change. -/
def towerGaloisAction : (L ≃ₐ[F] L) →* (Aut (baseChangeTower F L s))ᵐᵒᵖ where
  toFun σ := MulOpposite.op (towerGaloisAut s σ)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    apply NatTrans.ext
    funext U
    exact baseChangeMap_one (s.app U)
  map_mul' σ τ := by
    apply MulOpposite.unop_injective
    apply Iso.ext
    apply NatTrans.ext
    funext U
    exact (baseChangeMap_comp (s.app U) σ τ).symm

theorem towerGaloisAction_hom_app (σ : L ≃ₐ[F] L) (U : CompactOpenLevel G) :
    ((towerGaloisAction F L s σ).unop.hom).app U = baseChangeMap (s.app U) σ := rfl

variable {X : Scheme.{u}} (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)

/-- The Galois automorphisms lie over every base of the original tower. -/
theorem towerGaloisAction_over (σ : L ≃ₐ[F] L) :
    (towerGaloisAction F L s σ).unop.hom ≫ (baseChangeProjection F L s ≫ p) =
      baseChangeProjection F L s ≫ p := by
  apply NatTrans.ext
  funext U
  change baseChangeMap (s.app U) σ ≫ pullback.fst _ _ ≫ p.app U = pullback.fst _ _ ≫ p.app U
  rw [← Category.assoc, baseChangeMap]
  erw [pullback.lift_fst]
  rw [Category.comp_id]

variable [∀ {U V : CompactOpenLevel G} (a : U ⟶ V), Etale (T.map a)] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R]
variable (hT : ∀ (U : CompactOpenLevel G) (k : G) (hk : k ∈ U.subgroup),
  T.map (selfArrow U k hk) = 𝟙 (T.obj U))

variable (F L) in
/-- The colimit over levels of the degree `n` cohomology of `T(U) ×_{Spec F} Spec L`, with
coefficients pulled back from `X`, as a smooth representation of `G` carrying the commuting
action of `L ≃ₐ[F] L` through the second factor, natural in the base sheaf. -/
def galoisCohomologyFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R G) (L ≃ₐ[F] L) :=
  automorphismActionFunctor R (baseChangeProjection F L s ≫ p)
    (baseChangeTower_selfArrow F L s hT) (towerGaloisAction F L s) (towerGaloisAction_over s p) n

/-- Forgetting the Galois action recovers the smooth colimit cohomology of the base-changed
tower. -/
def galoisCohomologyForgetIso (n : ℕ) :
    galoisCohomologyFunctor F L s p R hT n ⋙ Action.forget _ (L ≃ₐ[F] L) ≅
      smoothCanonicalCohomologyFunctor R (baseChangeProjection F L s ≫ p)
        (baseChangeTower_selfArrow F L s hT) n :=
  Iso.refl _

/-- The Galois element `σ` acts by the smooth pullback along the base change of `σ` at every
level. -/
theorem galoisCohomologyFunctor_ρ (n : ℕ) (M : ModuleSheaf X R) (σ : L ≃ₐ[F] L) :
    ((galoisCohomologyFunctor F L s p R hT n).obj M).ρ σ =
      (smoothCanonicalPullback R (baseChangeProjection F L s ≫ p)
        (towerGaloisAction F L s σ).unop.hom (towerGaloisAction_over s p σ)
        (baseChangeTower_selfArrow F L s hT) (baseChangeTower_selfArrow F L s hT) n).app M :=
  rfl

end Langlands.Shimura.LevelTowerGalois
