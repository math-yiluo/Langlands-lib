import Langlands.Cohomology.DivisibleSystem.SpatialInduction
import Langlands.Cohomology.SmoothExtBaseChangeSummand
import Langlands.Representation.Category.ExactInclusion
import Langlands.Sheaf.Equivariant.SmoothSheafCompactSections
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Smooth locally constant coefficient systems

Harris 1999, Lemma 2.2 resolves the constant sheaves `ℤ/ℓ^mℤ` on `U(ẽ)` by `ℓ`-divisible
systems of smooth `S(ẽ)`-modules. This module proves that the Library's full smooth locally
constant sheaf functor and restriction of smooth representations to a subgroup are exact, lifts
them to `ℓ`-divisible systems, and compares the two locally constant systems under smooth spatial
induction.

* `LocallyConstantSheaf.moduleFunctor R Y`: locally constant functions on `Y` with values in an
  `R`-module, as an additive functor preserving finite limits.
* `LocallyConstantSheaf.smoothFunctorSectionsIso`: the sections over an open `U` of the full
  smooth locally constant sheaf are `moduleFunctor R U` of the coefficient module.
* Instances: `LocallyConstantSheaf.smoothFunctor R G X` preserves finite limits, epimorphisms,
  homology and finite colimits and is additive; `Induction.smoothRestriction R H` preserves
  finite limits and finite colimits; `SpatialInduction.smoothLocallyConstantFunctor H hH X R` is
  additive and preserves finite limits and finite colimits.
* `natIsoMk`, `mapFunctorCompIso`, `mapFunctorComp`: natural isomorphisms of functors on
  `ℓ`-divisible systems, from levelwise data or from a natural isomorphism `F ⋙ F' ≅ F''`.
* `smoothLocallyConstantSystemFunctor R ℓ G X` and `smoothRestrictionSystemFunctor R ℓ H`: the
  two coefficient functors, levelwise on `ℓ`-divisible systems.
* `smoothRestrictLocallyConstantSystemIso R H hH X ℓ` and
  `smoothInduceLocallyConstantSystemIso R H hH X ℓ`: under the equivalence
  `smoothRestrictionSystemEquivalence`, the locally constant system of a system of smooth
  `G`-representations on `G ×ᴴ X` corresponds to the locally constant system on `X` of its
  restriction to `H`, in both directions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Langlands.Sheaf.Equivariant.LocallyConstantSheaf

section ModuleFunctor

variable (R : Type u) [CommRing R] (Y : Type u) [TopologicalSpace Y]

/-- Locally constant functions on a fixed space `Y` with values in an `R`-module, as a
functor on `R`-modules acting by composition. -/
@[simps obj]
def moduleFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (LocallyConstant Y M)
  map f := ModuleCat.ofHom (LocallyConstant.mapₗ R f.hom)

instance moduleFunctor_additive : (moduleFunctor R Y).Additive where
  map_add := rfl

/-- Locally constant functions preserve finite limits: if `0 ⟶ A ⟶ B ⟶ C` is exact, a locally
constant function with values in `B` killed by `B ⟶ C` lifts pointwise to `A`, the lift being a
function of the original one and hence locally constant, and composition with the injection
`A ⟶ B` stays injective. -/
instance moduleFunctor_preservesFiniteLimits : PreservesFiniteLimits (moduleFunctor R Y) := by
  rw [Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have hf : Function.Injective S.f := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
  have hex := (ShortComplex.moduleCat_exact_iff S).1 hS.exact
  refine ⟨(ShortComplex.moduleCat_exact_iff _).2 fun (s : LocallyConstant Y S.X₂) hs => ?_,
    (ModuleCat.mono_iff_injective _).2 fun t t' h => ?_⟩
  · classical
    refine ⟨s.map fun b => if h : ∃ a, S.f a = b then h.choose else 0, ?_⟩
    apply LocallyConstant.ext
    intro y
    have hy : S.g (s y) = 0 := congrArg (fun r : LocallyConstant Y S.X₃ => r y) hs
    have h := hex (s y) hy
    change S.f (if h : ∃ a, S.f a = s y then h.choose else 0) = s y
    split
    next h' => exact h'.choose_spec
    next h' => exact absurd h h'
  · apply LocallyConstant.ext
    intro y
    exact hf (congrArg (fun r : LocallyConstant Y S.X₂ => r y) h)

end ModuleFunctor

section Smooth

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : Type u) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- The sections over an open `U` of the full smooth locally constant sheaf are the locally
constant functions on `U` with values in the coefficient module. -/
def smoothFunctorSectionsIso (U : ActionOpens G X) :
    smoothFunctor R G X ⋙ smoothInclusion R G X ⋙ toTransportPresheaf G X (ModuleCat.{u} R) ⋙
        (CategoryTheory.evaluation _ _).obj (op U) ≅
      Langlands.SmoothRep.toRep ⋙ forget₂ (Rep.{u} R G) (ModuleCat.{u} R) ⋙
        moduleFunctor R U.openSet :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The full smooth locally constant sheaf functor preserves finite limits: so does each of its
section functors, and the underlying presheaf functor reflects finite limits. -/
instance smoothFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (smoothFunctor R G X) := by
  have : PreservesFiniteLimits (smoothFunctor R G X ⋙
      (smoothInclusion R G X ⋙ toTransportPresheaf G X (ModuleCat.{u} R))) := by
    apply preservesFiniteLimits_of_evaluation
    intro U
    exact preservesFiniteLimits_of_natIso (smoothFunctorSectionsIso R G X U.unop).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (smoothInclusion R G X ⋙ toTransportPresheaf G X (ModuleCat.{u} R))

/-- The full smooth locally constant sheaf functor preserves epimorphisms: a surjection of
coefficient modules is surjective on locally constant functions over every open, by composing
with a set-theoretic section. -/
instance smoothFunctor_preservesEpimorphisms :
    (smoothFunctor R G X).PreservesEpimorphisms where
  preserves {A B} f hf := by
    have hs := (Langlands.SmoothRep.epi_iff_surjective f).1 hf
    have : ∀ U, Epi (((toTransportPresheaf G X (ModuleCat.{u} R)).map
        ((smoothInclusion R G X).map ((smoothFunctor R G X).map f))).app U) := by
      intro U
      rw [ModuleCat.epi_iff_surjective]
      intro t
      refine ⟨t.map (Function.surjInv hs), ?_⟩
      apply LocallyConstant.ext
      intro x
      exact Function.surjInv_eq hs _
    have : Epi ((toTransportPresheaf G X (ModuleCat.{u} R)).map
        ((smoothInclusion R G X).map ((smoothFunctor R G X).map f))) :=
      NatTrans.epi_of_epi_app _
    exact (smoothInclusion R G X).epi_of_epi_map
      ((toTransportPresheaf G X (ModuleCat.{u} R)).epi_of_epi_map this)

instance smoothFunctor_additive : (smoothFunctor R G X).Additive :=
  Functor.additive_of_preserves_binary_products _

instance smoothFunctor_preservesHomology : (smoothFunctor R G X).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

instance smoothFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (smoothFunctor R G X) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end Smooth

end Langlands.Sheaf.Equivariant.LocallyConstantSheaf

namespace Langlands.Induction

variable (R : Type u) [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (H : Subgroup G)

instance smoothRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (smoothRestriction.{u, u, u} R H) := by
  have : PreservesFiniteLimits (smoothRestriction.{u, u, u} R H ⋙ SmoothRep.toRep) :=
    inferInstanceAs (PreservesFiniteLimits (SmoothRep.toRep ⋙ Rep.resFunctor H.subtype))
  exact preservesFiniteLimits_of_reflects_of_preserves _ SmoothRep.toRep

instance smoothRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (smoothRestriction.{u, u, u} R H) := by
  have : PreservesFiniteColimits (smoothRestriction.{u, u, u} R H ⋙ SmoothRep.toRep) :=
    inferInstanceAs (PreservesFiniteColimits (SmoothRep.toRep ⋙ Rep.resFunctor H.subtype))
  exact preservesFiniteColimits_of_reflects_of_preserves _ SmoothRep.toRep

end Langlands.Induction

namespace Langlands.Sheaf.Equivariant.SpatialInduction

open Langlands.TopologicalInduction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
  [HasStableNeighbourhoods H X] (R : Type u) [CommRing R]

instance smoothLocallyConstantFunctor_additive :
    (smoothLocallyConstantFunctor H hH X R).Additive := by
  let _ := hasStableNeighbourhoods_induced H hH X
  exact inferInstanceAs (LocallyConstantSheaf.smoothFunctor R G (Space H X)).Additive

instance smoothLocallyConstantFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (smoothLocallyConstantFunctor H hH X R) := by
  let _ := hasStableNeighbourhoods_induced H hH X
  exact inferInstanceAs
    (PreservesFiniteLimits (LocallyConstantSheaf.smoothFunctor R G (Space H X)))

instance smoothLocallyConstantFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (smoothLocallyConstantFunctor H hH X R) := by
  let _ := hasStableNeighbourhoods_induced H hH X
  exact inferInstanceAs
    (PreservesFiniteColimits (LocallyConstantSheaf.smoothFunctor R G (Space H X)))

end Langlands.Sheaf.Equivariant.SpatialInduction

namespace Langlands.Cohomology.DivisibleSystem

section Comp

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] (ℓ : ℕ)

/-- A natural isomorphism of functors on `ℓ`-divisible systems from isomorphisms of the
underlying inverse systems commuting with the maps `i` and natural in the system. -/
def natIsoMk {Φ Ψ : DivisibleSystem C ℓ ⥤ DivisibleSystem D ℓ}
    (e : ∀ T, (Φ.obj T).tower ≅ (Ψ.obj T).tower)
    (he : ∀ (T : DivisibleSystem C ℓ) {m' m : ℕ} (h : m' < m),
      (Φ.obj T).inclusion h ≫ (e T).hom.app (op m) =
        (e T).hom.app (op m') ≫ (Ψ.obj T).inclusion h)
    (naturality : ∀ {T T' : DivisibleSystem C ℓ} (f : T ⟶ T'),
      (Φ.map f).tower ≫ (e T').hom = (e T).hom ≫ (Ψ.map f).tower) :
    Φ ≅ Ψ :=
  NatIso.ofComponents (fun T => isoMk (e T) (he T)) (fun f => hom_ext (naturality f))

@[simp]
lemma natIsoMk_hom_app_tower {Φ Ψ : DivisibleSystem C ℓ ⥤ DivisibleSystem D ℓ}
    (e : ∀ T, (Φ.obj T).tower ≅ (Ψ.obj T).tower)
    (he : ∀ (T : DivisibleSystem C ℓ) {m' m : ℕ} (h : m' < m),
      (Φ.obj T).inclusion h ≫ (e T).hom.app (op m) =
        (e T).hom.app (op m') ≫ (Ψ.obj T).inclusion h)
    (naturality : ∀ {T T' : DivisibleSystem C ℓ} (f : T ⟶ T'),
      (Φ.map f).tower ≫ (e T').hom = (e T).hom ≫ (Ψ.map f).tower)
    (T : DivisibleSystem C ℓ) :
    ((natIsoMk ℓ e he naturality).hom.app T).tower = (e T).hom :=
  rfl

@[simp]
lemma natIsoMk_inv_app_tower {Φ Ψ : DivisibleSystem C ℓ ⥤ DivisibleSystem D ℓ}
    (e : ∀ T, (Φ.obj T).tower ≅ (Ψ.obj T).tower)
    (he : ∀ (T : DivisibleSystem C ℓ) {m' m : ℕ} (h : m' < m),
      (Φ.obj T).inclusion h ≫ (e T).hom.app (op m) =
        (e T).hom.app (op m') ≫ (Ψ.obj T).inclusion h)
    (naturality : ∀ {T T' : DivisibleSystem C ℓ} (f : T ⟶ T'),
      (Φ.map f).tower ≫ (e T').hom = (e T).hom ≫ (Ψ.map f).tower)
    (T : DivisibleSystem C ℓ) :
    ((natIsoMk ℓ e he naturality).inv.app T).tower = (e T).inv :=
  rfl

/-- A natural isomorphism `F ⋙ F' ≅ F''` of exact additive functors induces a natural
isomorphism of the induced functors on `ℓ`-divisible systems, levelwise that of `α`. -/
def mapFunctorCompIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (F'' : C ⥤ E) [F''.Additive] [PreservesFiniteLimits F'']
    [PreservesFiniteColimits F''] (α : F ⋙ F' ≅ F'') :
    mapFunctor C ℓ F ⋙ mapFunctor D ℓ F' ≅ mapFunctor C ℓ F'' :=
  natIsoMk ℓ (fun T => Functor.isoWhiskerLeft T.tower α)
    (fun T _ _ h => α.hom.naturality (T.inclusion h))
    (fun f => by ext m; exact α.hom.naturality (f.tower.app m))

@[simp]
lemma mapFunctorCompIso_hom_app_tower_app (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (F'' : C ⥤ E) [F''.Additive] [PreservesFiniteLimits F'']
    [PreservesFiniteColimits F''] (α : F ⋙ F' ≅ F'') (T : DivisibleSystem C ℓ) (m : ℕᵒᵖ) :
    ((mapFunctorCompIso ℓ F F' F'' α).hom.app T).tower.app m = α.hom.app (T.tower.obj m) :=
  rfl

@[simp]
lemma mapFunctorCompIso_inv_app_tower_app (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] (F'' : C ⥤ E) [F''.Additive] [PreservesFiniteLimits F'']
    [PreservesFiniteColimits F''] (α : F ⋙ F' ≅ F'') (T : DivisibleSystem C ℓ) (m : ℕᵒᵖ) :
    ((mapFunctorCompIso ℓ F F' F'' α).inv.app T).tower.app m = α.inv.app (T.tower.obj m) :=
  rfl

/-- Mapping along `F` and then `F'` is mapping along `F ⋙ F'`. -/
abbrev mapFunctorComp (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (F' : D ⥤ E) [F'.Additive] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] :
    mapFunctor C ℓ F ⋙ mapFunctor D ℓ F' ≅ mapFunctor C ℓ (F ⋙ F') :=
  mapFunctorCompIso ℓ F F' (F ⋙ F') (Iso.refl _)

end Comp

section SmoothLocallyConstant

open Langlands.Sheaf.Equivariant

variable (R : Type u) [CommRing R] (ℓ : ℕ)

/-- The full smooth locally constant sheaves, levelwise on `ℓ`-divisible systems of smooth
coefficient representations. -/
def smoothLocallyConstantSystemFunctor (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : Type u) [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [HasStableNeighbourhoods G X] :
    DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ ⥤ SmoothSheafDivisibleSystem R G X ℓ :=
  mapFunctor _ ℓ (LocallyConstantSheaf.smoothFunctor R G X)

@[simp]
lemma smoothLocallyConstantSystemFunctor_obj_tower (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : Type u) [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]
    (T : DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ) :
    ((smoothLocallyConstantSystemFunctor R ℓ G X).obj T).tower =
      T.tower ⋙ LocallyConstantSheaf.smoothFunctor R G X :=
  rfl

/-- Restriction of smooth coefficient representations to a subgroup, levelwise on
`ℓ`-divisible systems. -/
def smoothRestrictionSystemFunctor {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) :
    DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ ⥤
      DivisibleSystem (Langlands.SmoothRep.{u, u, u} R H) ℓ :=
  mapFunctor _ ℓ (Langlands.Induction.smoothRestriction.{u, u, u} R H)

@[simp]
lemma smoothRestrictionSystemFunctor_obj_tower {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G)
    (T : DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ) :
    ((smoothRestrictionSystemFunctor R ℓ H).obj T).tower =
      T.tower ⋙ Langlands.Induction.smoothRestriction.{u, u, u} R H :=
  rfl

end SmoothLocallyConstant

section SpatialInduction

open Langlands.Sheaf.Equivariant Langlands.TopologicalInduction

variable (R : Type u) [CommRing R] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))
  (X : Type u) [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
  [HasStableNeighbourhoods H X] (ℓ : ℕ)

/-- Restricting the full smooth locally constant system on `G ×ᴴ X` to the unit chart gives the
full smooth locally constant system on `X` of the restricted coefficient system, naturally. -/
def smoothRestrictLocallyConstantSystemIso :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    smoothLocallyConstantSystemFunctor R ℓ G (Space H X) ⋙
        (smoothRestrictionSystemEquivalence R H hH X ℓ).functor ≅
      smoothRestrictionSystemFunctor R ℓ H ⋙ smoothLocallyConstantSystemFunctor R ℓ H X :=
  letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
  natIsoMk ℓ
    (fun T => Functor.isoWhiskerLeft T.tower
      (SpatialInduction.smoothRestrictLocallyConstantNatIso H hH X R))
    (fun T _ _ h =>
      (SpatialInduction.smoothRestrictLocallyConstantNatIso H hH X R).hom.naturality
        (T.inclusion h))
    (fun f => NatTrans.ext (funext fun m =>
      (SpatialInduction.smoothRestrictLocallyConstantNatIso H hH X R).hom.naturality
        (f.tower.app m)))

@[simp]
lemma smoothRestrictLocallyConstantSystemIso_hom_app_tower_app
    (T : DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ) (m : ℕᵒᵖ) :
    ((smoothRestrictLocallyConstantSystemIso R H hH X ℓ).hom.app T).tower.app m =
      (SpatialInduction.smoothRestrictLocallyConstantIso H hH X R (T.tower.obj m)).hom :=
  rfl

@[simp]
lemma smoothRestrictLocallyConstantSystemIso_inv_app_tower_app
    (T : DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ) (m : ℕᵒᵖ) :
    ((smoothRestrictLocallyConstantSystemIso R H hH X ℓ).inv.app T).tower.app m =
      (SpatialInduction.smoothRestrictLocallyConstantIso H hH X R (T.tower.obj m)).inv :=
  rfl

/-- Smooth spatial induction of the full smooth locally constant system on `X` of the restricted
coefficient system recovers the full smooth locally constant system on `G ×ᴴ X`, naturally. -/
def smoothInduceLocallyConstantSystemIso :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    (smoothRestrictionSystemFunctor R ℓ H ⋙ smoothLocallyConstantSystemFunctor R ℓ H X) ⋙
        (smoothRestrictionSystemEquivalence R H hH X ℓ).inverse ≅
      smoothLocallyConstantSystemFunctor R ℓ G (Space H X) :=
  letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
  natIsoMk ℓ
    (fun T => Functor.isoWhiskerLeft T.tower
      (SpatialInduction.smoothInduceLocallyConstantNatIso H hH X R))
    (fun T _ _ h =>
      (SpatialInduction.smoothInduceLocallyConstantNatIso H hH X R).hom.naturality
        (T.inclusion h))
    (fun f => NatTrans.ext (funext fun m =>
      (SpatialInduction.smoothInduceLocallyConstantNatIso H hH X R).hom.naturality
        (f.tower.app m)))

@[simp]
lemma smoothInduceLocallyConstantSystemIso_hom_app_tower_app
    (T : DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ) (m : ℕᵒᵖ) :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    ((smoothInduceLocallyConstantSystemIso R H hH X ℓ).hom.app T).tower.app m =
      (SpatialInduction.smoothInduceLocallyConstantIso H hH X R (T.tower.obj m)).hom :=
  rfl

@[simp]
lemma smoothInduceLocallyConstantSystemIso_inv_app_tower_app
    (T : DivisibleSystem (Langlands.SmoothRep.{u, u, u} R G) ℓ) (m : ℕᵒᵖ) :
    letI := SpatialInduction.hasStableNeighbourhoods_induced H hH X
    ((smoothInduceLocallyConstantSystemIso R H hH X ℓ).inv.app T).tower.app m =
      (SpatialInduction.smoothInduceLocallyConstantIso H hH X R (T.tower.obj m)).inv :=
  rfl

end SpatialInduction

end Langlands.Cohomology.DivisibleSystem
