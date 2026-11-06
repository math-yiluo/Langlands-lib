import Langlands.Shimura.RestrictedLevelTowerCohomology
import Langlands.Shimura.LevelTowerCanonicalCoefficients

/-! # Coefficients pulled back from a base along a tower over levels satisfying a property -/

noncomputable section

universe u v

namespace Langlands.Shimura.RestrictedLevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {G : Type u} [Group G] [TopologicalSpace G] {P : ObjectProperty (CompactOpenLevel G)}

/-- Identity components of a morphism of towers over levels satisfying `P` are étale. -/
instance etale_id_app (T₀ : P.FullSubcategory ⥤ Scheme.{u}) (K : P.FullSubcategory) :
    Etale (NatTrans.app (𝟙 T₀) K) :=
  inferInstanceAs (Etale (𝟙 (T₀.obj K)))

/-- Composites of tower morphisms with étale components have étale components. -/
instance etale_comp_app {T₀ T₁ T₂ : P.FullSubcategory ⥤ Scheme.{u}} (ψ : T₂ ⟶ T₁)
    (φ : T₁ ⟶ T₀) [∀ K, Etale (ψ.app K)] [∀ K, Etale (φ.app K)] (K : P.FullSubcategory) :
    Etale ((ψ ≫ φ).app K) :=
  inferInstanceAs (Etale (ψ.app K ≫ φ.app K))

/-- Isomorphisms of towers have étale components. -/
instance etale_iso_hom_app {T₀ T₁ : P.FullSubcategory ⥤ Scheme.{u}} (e : T₀ ≅ T₁)
    (K : P.FullSubcategory) : Etale (e.hom.app K) :=
  inferInstance

variable {T : P.FullSubcategory ⥤ Scheme.{u}}
variable (R : Type u) [CommRing R]
variable {X : Scheme.{u}} (p : T ⟶ (Functor.const P.FullSubcategory).obj X)

/-- The projections of the levels to the base, as a cone over the opposite scheme diagram. -/
def baseCone : (Functor.const P.FullSubcategoryᵒᵖ).obj (op X) ⟶ T.op where
  app K := (p.app K.unop).op
  naturality K L a := by
    apply Quiver.Hom.unop_inj
    have h := p.naturality a.unop
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.op_obj, Functor.op_map,
      unop_comp, Quiver.Hom.unop_op, CategoryTheory.unop_id, Category.comp_id]
    exact h.symm

@[simp] theorem baseCone_app_unop (K : P.FullSubcategoryᵒᵖ) :
    ((baseCone p).app K).unop = p.app K.unop := rfl

variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T.map a)]

section Generic

variable [IsTopologicalGroup G] [IsConjStable P]

variable (T) in
/-- The colimit over levels satisfying `P` of global sections, as a functor from level-trivial
coefficient diagrams to smooth representations. -/
def smoothColimitSectionsFunctor :
    (levelTrivialCoefficients T R).FullSubcategory ⥤ SmoothRep.{u, u, u} R G :=
  (RestrictedLevelColimit.levelTrivialProperty P (ModuleCat.{u} R)).lift
      ((levelTrivialCoefficients T R).ι ⋙ CoefficientDiagram.sectionsFunctor)
      (fun D => isLevelTrivial_sections D.property) ⋙
    RestrictedLevelColimit.smoothFunctor P R

@[simp] theorem smoothColimitSectionsFunctor_obj
    (D : (levelTrivialCoefficients T R).FullSubcategory) :
    (smoothColimitSectionsFunctor T R).obj D = smoothColimitSections D.obj D.property := rfl

variable (T) in
/-- In degree zero, colimit cohomology of level-trivial coefficients is the colimit of
global sections. -/
def smoothColimitCohomologyZeroIso :
    smoothColimitCohomologyFunctor T R 0 ≅ smoothColimitSectionsFunctor T R :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents
      (fun D => ObjectProperty.isoMk _
        ((CoefficientDiagram.cohomologyZeroFunctorIso (R := R) (S := T.op)).app D.obj))
      (fun {D E} α => by
        apply ObjectProperty.hom_ext
        exact (CoefficientDiagram.cohomologyZeroFunctorIso (R := R) (S := T.op)).hom.naturality
          α.hom))
    (RestrictedLevelColimit.smoothFunctor P R)

end Generic

/-- The inverse images `p_K^* M` of a base sheaf on the levels satisfying `P`, with the
transition along `T(a) : T(L) ⟶ T(K)` the inverse-image composition comparison
`T(a)^* p_K^* M ≅ p_L^* M`, transported to restriction along the étale map `T(a)`. -/
def canonicalCoefficients (M : ModuleSheaf X R) : CoefficientDiagram R T.op :=
  EtaleGeometricDiagram.CoefficientDiagram.toRestriction
    (EtaleGeometricDiagram.canonicalCoefficients R (baseCone p) M)

@[simp] theorem canonicalCoefficients_obj (M : ModuleSheaf X R) (K : P.FullSubcategoryᵒᵖ) :
    (canonicalCoefficients R p M).obj K = (inverseImage (p.app K.unop) R).obj M := rfl

/-- The transition of the coefficients along a level arrow. -/
theorem canonicalCoefficients_map (M : ModuleSheaf X R) {K L : P.FullSubcategoryᵒᵖ}
    (a : K ⟶ L) :
    (canonicalCoefficients R p M).map a =
      (LevelTowerCohomology.restrictionProjectionIso R (p.app K.unop) (p.app L.unop)
        (T.map a.unop) (EtaleGeometricDiagram.baseProjection_triangle (baseCone p) a)).hom.app
          M := rfl

/-- The cohomology transition along a level arrow is the pullback with projection
coefficients. -/
theorem canonicalCoefficients_cohomology_map (M : ModuleSheaf X R) (n : ℕ)
    {K L : P.FullSubcategoryᵒᵖ} (a : K ⟶ L) :
    ((canonicalCoefficients R p M).cohomology n).map a =
      LevelTowerCohomology.projectionCohomologyMap R (p.app K.unop) (p.app L.unop)
        (T.map a.unop) (EtaleGeometricDiagram.baseProjection_triangle (baseCone p) a) n M := rfl

/-- The coefficient transition of a level arrow depends only on its scheme morphism. -/
theorem canonicalCoefficients_map_congr (M : ModuleSheaf X R) {K L : P.FullSubcategoryᵒᵖ}
    (a b : K ⟶ L) (e : (T.op.map a).unop = (T.op.map b).unop) :
    (canonicalCoefficients R p M).map a =
      (restrictionCongr R e).hom.app ((canonicalCoefficients R p M).obj K) ≫
        (canonicalCoefficients R p M).map b :=
  LevelTowerCohomology.restrictionProjectionIso_congr R (p.app K.unop) (p.app L.unop) e _ _ M

/-- A morphism of base sheaves gives a morphism of the pulled-back coefficient diagrams. -/
def canonicalCoefficientsFunctor : ModuleSheaf X R ⥤ CoefficientDiagram R T.op :=
  EtaleGeometricDiagram.canonicalCoefficientsFunctor R (baseCone p) ⋙
    EtaleGeometricDiagram.CoefficientDiagram.toRestrictionFunctor

@[simp] theorem canonicalCoefficientsFunctor_obj (M : ModuleSheaf X R) :
    (canonicalCoefficientsFunctor R p).obj M = canonicalCoefficients R p M := rfl

@[simp] theorem canonicalCoefficientsFunctor_map_app {M N : ModuleSheaf X R} (α : M ⟶ N)
    (K : P.FullSubcategoryᵒᵖ) :
    ((canonicalCoefficientsFunctor R p).map α).app K = (inverseImage (p.app K.unop) R).map α :=
  rfl

/-- The degree `q` cohomology at level `K` is that of `T(K)` with coefficients `p_K^* M`. -/
theorem canonicalCoefficients_cohomology_obj (M : ModuleSheaf X R) (q : ℕ)
    (K : P.FullSubcategory) :
    ((canonicalCoefficients R p M).cohomology q).obj (op K) =
      (EtaleDerivedSections.cohomology (T.obj K) R q).obj ((inverseImage (p.app K) R).obj M) :=
  rfl

variable {p}

/-- If each `k ∈ K` acts on `T(K)` by the identity, the pulled-back coefficients are
level-trivial. -/
theorem isLevelTrivialCoefficients_canonical
    (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
      T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
    (M : ModuleSheaf X R) : IsLevelTrivialCoefficients (canonicalCoefficients R p M) := by
  intro K k hk
  have e : (T.op.map (restrictedSelfArrow P K k hk).op).unop = (T.op.map (𝟙 (op K))).unop := by
    change T.map (restrictedSelfArrow P K k hk) = (T.op.map (𝟙 (op K))).unop
    rw [hT K k hk, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨e, canonicalCoefficients_map_congr R p M _ _ e⟩

variable (p)

section LevelTrivial

variable (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))

/-- Pulled-back coefficients as a functor into level-trivial coefficient diagrams. -/
def levelTrivialCanonicalCoefficientsFunctor :
    ModuleSheaf X R ⥤ (levelTrivialCoefficients T R).FullSubcategory :=
  (levelTrivialCoefficients T R).lift (canonicalCoefficientsFunctor R p)
    (fun M => isLevelTrivialCoefficients_canonical R hT M)

variable [IsTopologicalGroup G] [IsConjStable P]

/-- The colimit over levels satisfying `P` of the degree `q` cohomology of `T(K)` with
coefficients `p_K^* M`, as a smooth representation of `G`, natural in the base sheaf `M`. -/
def smoothCanonicalCohomologyFunctor (q : ℕ) : ModuleSheaf X R ⥤ SmoothRep.{u, u, u} R G :=
  levelTrivialCanonicalCoefficientsFunctor R p hT ⋙ smoothColimitCohomologyFunctor T R q

/-- The colimit over levels satisfying `P` of the global sections of `p_K^* M`, as a smooth
representation of `G`, natural in the base sheaf `M`. -/
def smoothCanonicalSectionsFunctor : ModuleSheaf X R ⥤ SmoothRep.{u, u, u} R G :=
  levelTrivialCanonicalCoefficientsFunctor R p hT ⋙ smoothColimitSectionsFunctor T R

@[simp] theorem smoothCanonicalCohomologyFunctor_obj (q : ℕ) (M : ModuleSheaf X R) :
    (smoothCanonicalCohomologyFunctor R p hT q).obj M =
      smoothColimitCohomology (canonicalCoefficients R p M)
        (isLevelTrivialCoefficients_canonical R hT M) q := rfl

@[simp] theorem smoothCanonicalSectionsFunctor_obj (M : ModuleSheaf X R) :
    (smoothCanonicalSectionsFunctor R p hT).obj M =
      smoothColimitSections (canonicalCoefficients R p M)
        (isLevelTrivialCoefficients_canonical R hT M) := rfl

/-- In degree zero, the colimit cohomology of pulled-back coefficients is the colimit of
their global sections. -/
def smoothCanonicalCohomologyZeroIso :
    smoothCanonicalCohomologyFunctor R p hT 0 ≅ smoothCanonicalSectionsFunctor R p hT :=
  Functor.isoWhiskerLeft (levelTrivialCanonicalCoefficientsFunctor R p hT)
    (smoothColimitCohomologyZeroIso T R)

/-- The action of `g` on the image of a class of level `K`: it is the image at level
`g K g⁻¹` of its pullback along `T(g K g⁻¹ ⟶ K)` followed by the inverse-image comparison
of the pulled-back coefficients. -/
theorem smoothCanonicalCohomology_ρ_ι_apply (q : ℕ) (M : ModuleSheaf X R) (g : G)
    (K : P.FullSubcategory)
    (x : (EtaleDerivedSections.cohomology (T.obj K) R q).obj ((inverseImage (p.app K) R).obj M)) :
    ((smoothCanonicalCohomologyFunctor R p hT q).obj M).obj.ρ g
        ((RestrictedLevelColimit.ι ((canonicalCoefficients R p M).cohomology q) K).hom x) =
      (RestrictedLevelColimit.ι ((canonicalCoefficients R p M).cohomology q)
          (restrictedConj P g K)).hom
        ((cohomologyMapWithCoefficients (T.map (restrictedConjArrow P g K)) R q
          ((canonicalCoefficients R p M).map (restrictedConjArrow P g K).op)).hom x) :=
  smoothColimitCohomology_ρ_ι_apply (canonicalCoefficients R p M)
    (isLevelTrivialCoefficients_canonical R hT M) q g K x

/-- Every class comes from the cohomology of a single level satisfying `P`, if `P` is
downward closed and holds for some level. -/
theorem canonicalCohomology_exists_level [IsDownwardClosed P] [Nonempty P.FullSubcategory]
    (q : ℕ) (M : ModuleSheaf X R)
    (x : ((smoothCanonicalCohomologyFunctor R p hT q).obj M).obj.V) :
    ∃ (K : P.FullSubcategory)
      (y : (EtaleDerivedSections.cohomology (T.obj K) R q).obj
        ((inverseImage (p.app K) R).obj M)),
      (RestrictedLevelColimit.ι ((canonicalCoefficients R p M).cohomology q) K).hom y = x :=
  exists_level_class (canonicalCoefficients R p M) q x

end LevelTrivial

section TowerMorphism

variable {T' T'' : P.FullSubcategory ⥤ Scheme.{u}}
variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T'.map a)]
variable [∀ {K L : P.FullSubcategory} (a : K ⟶ L), Etale (T''.map a)]
variable (φ : T' ⟶ T) [∀ K, Etale (φ.app K)]
variable {p' : T' ⟶ (Functor.const P.FullSubcategory).obj X} (hφ : φ ≫ p = p')

/-- Pullback of the cohomology of pulled-back coefficients along a morphism of towers over
the base whose components are étale. At level `K` it is the pullback along `φ_K` with the
projection comparison `φ_K^* p_K^* M ≅ p'_K^* M`. -/
def canonicalPullback (M : ModuleSheaf X R) (n : ℕ) :
    (canonicalCoefficients R p M).cohomology n ⟶ (canonicalCoefficients R p' M).cohomology n where
  app K := LevelTowerCohomology.projectionCohomologyMap R (p.app K.unop) (p'.app K.unop)
    (φ.app K.unop) (NatTrans.congr_app hφ K.unop) n M
  naturality K L b := by
    change LevelTowerCohomology.projectionCohomologyMap R _ _ (T.map b.unop) _ n M ≫
        LevelTowerCohomology.projectionCohomologyMap R _ _ (φ.app L.unop) _ n M =
      LevelTowerCohomology.projectionCohomologyMap R _ _ (φ.app K.unop) _ n M ≫
        LevelTowerCohomology.projectionCohomologyMap R _ _ (T'.map b.unop) _ n M
    rw [LevelTowerCohomology.projectionCohomologyMap_comp,
      LevelTowerCohomology.projectionCohomologyMap_comp]
    exact LevelTowerCohomology.projectionCohomologyMap_congr R _ _
      (φ.naturality b.unop).symm _ _ n M

theorem canonicalPullback_app (M : ModuleSheaf X R) (n : ℕ) (K : P.FullSubcategoryᵒᵖ) :
    (canonicalPullback R p φ hφ M n).app K =
      LevelTowerCohomology.projectionCohomologyMap R (p.app K.unop) (p'.app K.unop)
        (φ.app K.unop) (NatTrans.congr_app hφ K.unop) n M := rfl

/-- The pullback is natural in the base sheaf. -/
def canonicalPullbackNatTrans (n : ℕ) :
    canonicalCoefficientsFunctor R p ⋙ CoefficientDiagram.cohomologyFunctor n ⟶
      canonicalCoefficientsFunctor R p' ⋙ CoefficientDiagram.cohomologyFunctor n where
  app M := canonicalPullback R p φ hφ M n
  naturality M N α := by
    apply NatTrans.ext
    funext K
    exact LevelTowerCohomology.projectionCohomologyMap_naturality R _ _ _ _ n α

/-- Pullback along the identity tower morphism is the identity. -/
theorem canonicalPullback_id (h : 𝟙 T ≫ p = p) (M : ModuleSheaf X R) (n : ℕ) :
    canonicalPullback R p (𝟙 T) h M n = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  exact LevelTowerCohomology.projectionCohomologyMap_id R _ _ n M

/-- Pullback along a composite of tower morphisms is the composite of the pullbacks. -/
theorem canonicalPullback_comp (ψ : T'' ⟶ T') [∀ K, Etale (ψ.app K)]
    {p'' : T'' ⟶ (Functor.const P.FullSubcategory).obj X} (hψ : ψ ≫ p' = p'')
    (hψφ : (ψ ≫ φ) ≫ p = p'') (M : ModuleSheaf X R) (n : ℕ) :
    canonicalPullback R p φ hφ M n ≫ canonicalPullback R p' ψ hψ M n =
      canonicalPullback R p (ψ ≫ φ) hψφ M n := by
  apply NatTrans.ext
  funext K
  change LevelTowerCohomology.projectionCohomologyMap R _ _ (φ.app K.unop) _ n M ≫
      LevelTowerCohomology.projectionCohomologyMap R _ _ (ψ.app K.unop) _ n M =
    LevelTowerCohomology.projectionCohomologyMap R _ _ (ψ.app K.unop ≫ φ.app K.unop) _ n M
  rw [LevelTowerCohomology.projectionCohomologyMap_comp]

/-- On colimits over levels satisfying `P`, the pullback sends the image of a class of
level `K` to the image of its pullback along `φ_K`. -/
theorem canonicalPullback_ι (M : ModuleSheaf X R) (n : ℕ) (K : P.FullSubcategory) :
    RestrictedLevelColimit.ι ((canonicalCoefficients R p M).cohomology n) K ≫
        RestrictedLevelColimit.map (canonicalPullback R p φ hφ M n) =
      LevelTowerCohomology.projectionCohomologyMap R (p.app K) (p'.app K) (φ.app K)
          (NatTrans.congr_app hφ K) n M ≫
        RestrictedLevelColimit.ι ((canonicalCoefficients R p' M).cohomology n) K :=
  RestrictedLevelColimit.ι_map _ K

variable (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
variable (hT' : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T'.map (restrictedSelfArrow P K k hk) = 𝟙 (T'.obj K))
variable (hT'' : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T''.map (restrictedSelfArrow P K k hk) = 𝟙 (T''.obj K))
variable [IsTopologicalGroup G] [IsConjStable P]

/-- The pullback along a tower morphism as a morphism of smooth representations, natural in
the base sheaf. -/
def smoothCanonicalPullback (n : ℕ) :
    smoothCanonicalCohomologyFunctor R p hT n ⟶ smoothCanonicalCohomologyFunctor R p' hT' n where
  app M := (RestrictedLevelColimit.smoothFunctor P R).map
    (ObjectProperty.homMk (canonicalPullback R p φ hφ M n))
  naturality M N α := by
    dsimp only [smoothCanonicalCohomologyFunctor, smoothColimitCohomologyFunctor,
      Functor.comp_map]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    apply ObjectProperty.hom_ext
    exact (canonicalPullbackNatTrans R p φ hφ n).naturality α

theorem smoothCanonicalPullback_app (n : ℕ) (M : ModuleSheaf X R) :
    (smoothCanonicalPullback R p φ hφ hT hT' n).app M =
      (RestrictedLevelColimit.smoothFunctor P R).map
        (ObjectProperty.homMk (canonicalPullback R p φ hφ M n)) := rfl

/-- The smooth pullback along the identity tower morphism is the identity. -/
theorem smoothCanonicalPullback_id (h : 𝟙 T ≫ p = p) (n : ℕ) :
    smoothCanonicalPullback R p (𝟙 T) h hT hT n = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  rw [smoothCanonicalPullback_app, canonicalPullback_id]
  exact (RestrictedLevelColimit.smoothFunctor P R).map_id _

/-- The smooth pullback along a composite is the composite of the smooth pullbacks. -/
theorem smoothCanonicalPullback_comp (ψ : T'' ⟶ T') [∀ K, Etale (ψ.app K)]
    {p'' : T'' ⟶ (Functor.const P.FullSubcategory).obj X} (hψ : ψ ≫ p' = p'')
    (hψφ : (ψ ≫ φ) ≫ p = p'') (n : ℕ) :
    smoothCanonicalPullback R p φ hφ hT hT' n ≫ smoothCanonicalPullback R p' ψ hψ hT' hT'' n =
      smoothCanonicalPullback R p (ψ ≫ φ) hψφ hT hT'' n := by
  apply NatTrans.ext
  funext M
  rw [NatTrans.comp_app, smoothCanonicalPullback_app, smoothCanonicalPullback_app,
    smoothCanonicalPullback_app, ← CategoryTheory.Functor.map_comp,
    ← canonicalPullback_comp R p φ hφ ψ hψ hψφ M n]
  rfl

/-- The smooth pullback depends only on the tower morphism, not on how its étaleness and
compatibility with the projections are witnessed. -/
theorem smoothCanonicalPullback_congr (φ₁ φ₂ : T' ⟶ T) [∀ K, Etale (φ₁.app K)]
    [∀ K, Etale (φ₂.app K)] (h₁ : φ₁ ≫ p = p') (h₂ : φ₂ ≫ p = p') (e : φ₁ = φ₂) (n : ℕ) :
    smoothCanonicalPullback R p φ₁ h₁ hT hT' n = smoothCanonicalPullback R p φ₂ h₂ hT hT' n := by
  subst e
  rfl

end TowerMorphism

section Automorphisms

variable (hT : ∀ (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup),
  T.map (restrictedSelfArrow P K k hk) = 𝟙 (T.obj K))
variable [IsTopologicalGroup G] [IsConjStable P]

/-- A smooth pullback along an endomorphism equal to the identity is the identity. -/
theorem smoothCanonicalPullback_of_eq_id (φ : T ⟶ T) [∀ K, Etale (φ.app K)] (hφ : φ ≫ p = p)
    (e : φ = 𝟙 T) (n : ℕ) : smoothCanonicalPullback R p φ hφ hT hT n = 𝟙 _ := by
  subst e
  exact smoothCanonicalPullback_id R p hT _ n

/-- A smooth pullback along an endomorphism equal to a composite is the composite of the
smooth pullbacks, in the opposite order. -/
theorem smoothCanonicalPullback_of_eq_comp (χ φ ψ : T ⟶ T) [∀ K, Etale (χ.app K)]
    [∀ K, Etale (φ.app K)] [∀ K, Etale (ψ.app K)] (hχ : χ ≫ p = p) (hφ : φ ≫ p = p)
    (hψ : ψ ≫ p = p) (e : χ = ψ ≫ φ) (n : ℕ) :
    smoothCanonicalPullback R p χ hχ hT hT n =
      smoothCanonicalPullback R p φ hφ hT hT n ≫ smoothCanonicalPullback R p ψ hψ hT hT n := by
  subst e
  exact (smoothCanonicalPullback_comp R p φ hφ hT hT hT ψ hψ hχ n).symm

variable {Γ : Type v} [Group Γ] (ρ : Γ →* (Aut T)ᵐᵒᵖ) (hρ : ∀ γ, (ρ γ).unop.hom ≫ p = p)

/-- A group acting on the tower by automorphisms over the base acts on the colimit
cohomology with pulled-back coefficients by morphisms of smooth representations: `γ` acts
by pullback along the automorphism of `γ`. -/
def automorphismAction (n : ℕ) (M : ModuleSheaf X R) : Action (SmoothRep.{u, u, u} R G) Γ where
  V := (smoothCanonicalCohomologyFunctor R p hT n).obj M
  ρ :=
    { toFun γ := (smoothCanonicalPullback R p (ρ γ).unop.hom (hρ γ) hT hT n).app M
      map_one' := by
        rw [smoothCanonicalPullback_of_eq_id R p hT _ _
          (by rw [map_one, MulOpposite.unop_one]; rfl)]
        rfl
      map_mul' γ δ := by
        rw [End.mul_def, smoothCanonicalPullback_of_eq_comp R p hT (ρ (γ * δ)).unop.hom
          (ρ δ).unop.hom (ρ γ).unop.hom (hρ _) (hρ _) (hρ _)
          (by rw [map_mul, MulOpposite.unop_mul, Aut.Aut_mul_def, Iso.trans_hom])]
        rfl }

theorem automorphismAction_ρ (n : ℕ) (M : ModuleSheaf X R) (γ : Γ) :
    (automorphismAction R p hT ρ hρ n M).ρ γ =
      (smoothCanonicalPullback R p (ρ γ).unop.hom (hρ γ) hT hT n).app M := rfl

/-- The action is natural in the base sheaf. -/
def automorphismActionFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (SmoothRep.{u, u, u} R G) Γ where
  obj M := automorphismAction R p hT ρ hρ n M
  map α :=
    { hom := (smoothCanonicalCohomologyFunctor R p hT n).map α
      comm γ := ((smoothCanonicalPullback R p (ρ γ).unop.hom (hρ γ) hT hT n).naturality α).symm }
  map_id M := Action.Hom.ext ((smoothCanonicalCohomologyFunctor R p hT n).map_id M)
  map_comp α β := Action.Hom.ext ((smoothCanonicalCohomologyFunctor R p hT n).map_comp α β)

/-- Forgetting the action of `Γ` recovers the smooth colimit cohomology functor. -/
def automorphismActionForgetIso (n : ℕ) :
    automorphismActionFunctor R p hT ρ hρ n ⋙ Action.forget _ Γ ≅
      smoothCanonicalCohomologyFunctor R p hT n :=
  Iso.refl _

end Automorphisms

/-! ## Comparison with towers over all levels -/

section Comparison

variable {T₀ : CompactOpenLevel G ⥤ Scheme.{u}}
variable (p₀ : T₀ ⟶ (Functor.const (CompactOpenLevel G)).obj X)

variable (P) in
/-- The projections of a tower over all levels, restricted to the levels satisfying `P`. -/
def restrictProjection : P.ι ⋙ T₀ ⟶ (Functor.const P.FullSubcategory).obj X where
  app K := p₀.app K.obj
  naturality _ _ a := p₀.naturality a.hom

@[simp] theorem restrictProjection_app (K : P.FullSubcategory) :
    (restrictProjection P p₀).app K = p₀.app K.obj := rfl

/-- Components of a restricted tower morphism are étale when those of the original are. -/
instance etale_whiskerLeft_app {T₀' : CompactOpenLevel G ⥤ Scheme.{u}} (φ₀ : T₀' ⟶ T₀)
    [∀ K, Etale (φ₀.app K)] (K : P.FullSubcategory) :
    Etale ((Functor.whiskerLeft P.ι φ₀).app K) :=
  inferInstanceAs (Etale (φ₀.app K.obj))

variable {p₀} in
/-- A morphism of towers over the base, restricted to the levels satisfying `P`, is a
morphism over the restricted projections. -/
theorem restrictProjection_comp {T₀' : CompactOpenLevel G ⥤ Scheme.{u}} (φ₀ : T₀' ⟶ T₀)
    {p₀' : T₀' ⟶ (Functor.const (CompactOpenLevel G)).obj X} (hφ₀ : φ₀ ≫ p₀ = p₀') :
    Functor.whiskerLeft P.ι φ₀ ≫ restrictProjection P p₀ = restrictProjection P p₀' := by
  apply NatTrans.ext
  funext K
  exact NatTrans.congr_app hφ₀ K.obj

/-- If each `k ∈ K` acts on level `K` of a tower over all levels by the identity, the same
holds for its restriction to the levels satisfying `P`. -/
theorem restrict_selfArrow
    (hT₀ : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
      T₀.map (selfArrow K k hk) = 𝟙 (T₀.obj K))
    (K : P.FullSubcategory) (k : G) (hk : k ∈ K.obj.subgroup) :
    (P.ι ⋙ T₀).map (restrictedSelfArrow P K k hk) = 𝟙 ((P.ι ⋙ T₀).obj K) :=
  hT₀ K.obj k hk

variable [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T₀.map a)]

/-- Restricting the pulled-back coefficients of a tower over all levels gives the
pulled-back coefficients of the restricted tower. -/
theorem restrictCoefficients_canonical (M : ModuleSheaf X R) :
    restrictCoefficients (P := P) (LevelTowerCohomology.canonicalCoefficients R p₀ M) =
      canonicalCoefficients R (restrictProjection P p₀) M := rfl

variable (hT₀ : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T₀.map (selfArrow K k hk) = 𝟙 (T₀.obj K))
variable [IsTopologicalGroup G] [IsConjStable P] [IsDownwardClosed P] [Nonempty P.FullSubcategory]

/-- For `P` conjugation stable, downward closed and holding for some level, the smooth
colimit cohomology over levels satisfying `P` of the restricted tower with pulled-back
coefficients is that over all levels, naturally in the base sheaf. -/
def smoothCanonicalCohomologyRestrictIso (q : ℕ) :
    smoothCanonicalCohomologyFunctor R (restrictProjection P p₀) (restrict_selfArrow hT₀) q ≅
      LevelTowerCohomology.smoothCanonicalCohomologyFunctor R p₀ hT₀ q :=
  NatIso.ofComponents
    (fun M => smoothColimitCohomologyRestrictIso (LevelTowerCohomology.canonicalCoefficients R p₀ M)
      (LevelTowerCohomology.isLevelTrivialCoefficients_canonical R hT₀ M) q)
    (fun α => (smoothColimitCohomologyFunctorRestrictIso P R T₀ q).hom.naturality
      ((LevelTowerCohomology.levelTrivialCanonicalCoefficientsFunctor R p₀ hT₀).map α))

/-- The comparison sends the image of a class of level `K` to its image in the colimit over
all levels. -/
theorem smoothCanonicalCohomologyRestrictIso_hom_ι_apply (q : ℕ) (M : ModuleSheaf X R)
    (K : P.FullSubcategory)
    (x : (EtaleDerivedSections.cohomology (T₀.obj K.obj) R q).obj
      ((inverseImage (p₀.app K.obj) R).obj M)) :
    ((smoothCanonicalCohomologyRestrictIso R p₀ hT₀ q).hom.app M).hom.hom
        ((RestrictedLevelColimit.ι
          ((canonicalCoefficients R (restrictProjection P p₀) M).cohomology q) K).hom x) =
      (LevelColimit.ι ((LevelTowerCohomology.canonicalCoefficients R p₀ M).cohomology q)
        K.obj).hom x :=
  RestrictedLevelColimit.smoothRepRestrictIso_hom_ι_apply (P := P)
    ((LevelTowerCohomology.canonicalCoefficients R p₀ M).cohomology q)
    (LevelTowerCohomology.isLevelTrivial_cohomology
      (LevelTowerCohomology.isLevelTrivialCoefficients_canonical R hT₀ M) q) K x

section Morphism

variable {T₀' : CompactOpenLevel G ⥤ Scheme.{u}}
variable [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T₀'.map a)]
variable (φ₀ : T₀' ⟶ T₀) [∀ K, Etale (φ₀.app K)]
variable {p₀' : T₀' ⟶ (Functor.const (CompactOpenLevel G)).obj X} (hφ₀ : φ₀ ≫ p₀ = p₀')
variable (hT₀' : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T₀'.map (selfArrow K k hk) = 𝟙 (T₀'.obj K))

/-- The comparison is compatible with pullback along morphisms of towers over the base. -/
theorem smoothCanonicalPullback_restrictIso (n : ℕ) :
    smoothCanonicalPullback R (restrictProjection P p₀) (Functor.whiskerLeft P.ι φ₀)
        (restrictProjection_comp φ₀ hφ₀) (restrict_selfArrow hT₀) (restrict_selfArrow hT₀') n ≫
        (smoothCanonicalCohomologyRestrictIso R p₀' hT₀' n).hom =
      (smoothCanonicalCohomologyRestrictIso R p₀ hT₀ n).hom ≫
        LevelTowerCohomology.smoothCanonicalPullback R p₀ φ₀ hφ₀ hT₀ hT₀' n := by
  apply NatTrans.ext
  funext M
  apply ObjectProperty.hom_ext
  change (Rep.ActionToRep R G).map _ ≫ (Rep.ActionToRep R G).map _ =
    (Rep.ActionToRep R G).map _ ≫ (Rep.ActionToRep R G).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  congr 1
  exact Action.Hom.ext (RestrictedLevelColimit.map_colimitRestrictIso_hom
    (LevelTowerCohomology.canonicalPullback R p₀ φ₀ hφ₀ M n))

end Morphism

variable {Γ : Type v} [Group Γ]
variable (ρ₀ : Γ →* (Aut T₀)ᵐᵒᵖ) (hρ₀ : ∀ γ, (ρ₀ γ).unop.hom ≫ p₀ = p₀)
variable (ρ : Γ →* (Aut (P.ι ⋙ T₀))ᵐᵒᵖ)
  (hρ : ∀ γ, (ρ γ).unop.hom ≫ restrictProjection P p₀ = restrictProjection P p₀)
  (hρρ₀ : ∀ γ, (ρ γ).unop.hom = Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom)

/-- If a group acts on a tower over all levels by automorphisms over the base, and on its
restriction to the levels satisfying `P` by the restricted automorphisms, the comparison is
an isomorphism of smooth representations with commuting actions of the group, naturally in
the base sheaf. -/
def automorphismActionRestrictIso (n : ℕ) :
    automorphismActionFunctor R (restrictProjection P p₀) (restrict_selfArrow hT₀) ρ hρ n ≅
      LevelTowerCohomology.automorphismActionFunctor R p₀ hT₀ ρ₀ hρ₀ n :=
  NatIso.ofComponents
    (fun M => Action.mkIso ((smoothCanonicalCohomologyRestrictIso R p₀ hT₀ n).app M)
      (fun γ => by
        change (smoothCanonicalPullback R (restrictProjection P p₀) (ρ γ).unop.hom (hρ γ)
            (restrict_selfArrow hT₀) (restrict_selfArrow hT₀) n).app M ≫ _ = _
        rw [smoothCanonicalPullback_congr R (restrictProjection P p₀) (restrict_selfArrow hT₀)
          (restrict_selfArrow hT₀) (ρ γ).unop.hom (Functor.whiskerLeft P.ι (ρ₀ γ).unop.hom)
          (hρ γ) (restrictProjection_comp _ (hρ₀ γ)) (hρρ₀ γ) n]
        exact NatTrans.congr_app
          (smoothCanonicalPullback_restrictIso R p₀ hT₀ (ρ₀ γ).unop.hom (hρ₀ γ) hT₀ n) M))
    (fun α => Action.Hom.ext ((smoothCanonicalCohomologyRestrictIso R p₀ hT₀ n).hom.naturality α))

@[simp] theorem automorphismActionRestrictIso_hom_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((automorphismActionRestrictIso R p₀ hT₀ ρ₀ hρ₀ ρ hρ hρρ₀ n).hom.app M).hom =
      (smoothCanonicalCohomologyRestrictIso R p₀ hT₀ n).hom.app M := rfl

end Comparison

end Langlands.Shimura.RestrictedLevelTowerCohomology
