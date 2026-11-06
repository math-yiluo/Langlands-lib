import Langlands.Shimura.LevelTowerCohomology
import Langlands.Geometry.EtaleCanonicalCoefficientDiagram
import Langlands.Geometry.EtaleCoefficientEquivalence

/-! # Coefficients pulled back from a base along a level tower -/

noncomputable section

universe u v

namespace Langlands.Shimura.LevelTowerCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Geometry Langlands.Geometry.EtalePullback CompactOpenLevel
open Langlands.Geometry.EtaleInverseImage EtaleDerivedSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

section Projection

variable (R : Type u) [CommRing R] {X Y Z : Scheme.{u}}

/-- For an étale map `f` and a commuting triangle `f ≫ q = r`, restriction along `f` of the
inverse image along `q` is the inverse image along `r`: the inverse of the published
comparison of inverse image with restriction, followed by the published triangle
comparison of inverse images. -/
def restrictionProjectionIso (q : Z ⟶ X) (r : Y ⟶ X) (f : Y ⟶ Z) [Etale f] (h : f ≫ q = r) :
    inverseImage q R ⋙ restriction f (ModuleCat.{u} R) ≅ inverseImage r R :=
  Functor.isoWhiskerLeft (inverseImage q R) (inverseImageIsoRestriction f R).symm ≪≫
    projectionInverseImageIso R q r f h

theorem restrictionProjectionIso_hom_app (q : Z ⟶ X) (r : Y ⟶ X) (f : Y ⟶ Z) [Etale f]
    (h : f ≫ q = r) (M : ModuleSheaf X R) :
    (restrictionProjectionIso R q r f h).hom.app M =
      (inverseImageIsoRestriction f R).inv.app ((inverseImage q R).obj M) ≫
        (projectionInverseImageIso R q r f h).hom.app M := rfl

/-- The comparison depends only on the étale map, up to `restrictionCongr`. -/
theorem restrictionProjectionIso_congr (q : Z ⟶ X) (r : Y ⟶ X) {f g : Y ⟶ Z}
    [Etale f] [Etale g] (e : f = g) (hf : f ≫ q = r) (hg : g ≫ q = r) (M : ModuleSheaf X R) :
    (restrictionProjectionIso R q r f hf).hom.app M =
      (restrictionCongr R e).hom.app ((inverseImage q R).obj M) ≫
        (restrictionProjectionIso R q r g hg).hom.app M := by
  subst e
  simp [restrictionCongr]

/-- Along the identity, the comparison is the published identity constraint of
restriction. -/
theorem restrictionProjectionIso_id (q : Y ⟶ X) (h : 𝟙 Y ≫ q = q) (M : ModuleSheaf X R) :
    (restrictionProjectionIso R q q (𝟙 Y) h).hom.app M =
      (restrictionId (ModuleCat.{u} R)).hom.app ((inverseImage q R).obj M) := by
  have h2 := congrArg (fun t => t.app ((inverseImage q R).obj M))
    (inverseImageIsoRestriction_id R Y)
  simp only [NatTrans.comp_app] at h2
  rw [restrictionProjectionIso_hom_app, projectionInverseImageIso_id R q (𝟙 Y) h rfl M]
  simp only [inverseImageCongr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rw [← h2, Iso.inv_hom_id_app_assoc]

/-- The inverse comparisons of inverse image with restriction intertwine the composition
constraints. -/
theorem inverseImageIsoRestriction_comp_inv_app {Y₀ Y₁ Y₂ : Scheme.{u}} (f : Y₁ ⟶ Y₀)
    (g : Y₂ ⟶ Y₁) [Etale f] [Etale g] (F : ModuleSheaf Y₀ R) :
    (restrictionComp f (ModuleCat.{u} R) g).inv.app F ≫
        (restriction g (ModuleCat.{u} R)).map ((inverseImageIsoRestriction f R).inv.app F) ≫
        (inverseImageIsoRestriction g R).inv.app ((inverseImage f R).obj F) ≫
        (inverseImageComp R f g).hom.app F =
      (inverseImageIsoRestriction (g ≫ f) R).inv.app F := by
  rw [← cancel_mono ((inverseImageIsoRestriction (g ≫ f) R).hom.app F), Iso.inv_hom_id_app]
  have hc := congrArg (fun t => t.app F) (inverseImageIsoRestriction_comp R f g)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hc
  simp only [Category.assoc]
  rw [hc]
  simp only [Category.assoc]
  rw [← Category.assoc ((inverseImageIsoRestriction g R).inv.app _),
    ← (inverseImageIsoRestriction g R).inv.naturality]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Category.assoc ((restriction g (ModuleCat.{u} R)).map _),
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app]

/-- Successive comparisons along étale maps compose to the comparison along the
composite, after the published composition constraint of restriction. -/
theorem restrictionProjectionIso_comp {Y₀ Y₁ Y₂ : Scheme.{u}} (q₀ : Y₀ ⟶ X) (q₁ : Y₁ ⟶ X)
    (q₂ : Y₂ ⟶ X) (f : Y₁ ⟶ Y₀) (g : Y₂ ⟶ Y₁) [Etale f] [Etale g] (hf : f ≫ q₀ = q₁)
    (hg : g ≫ q₁ = q₂) (hfg : (g ≫ f) ≫ q₀ = q₂) (M : ModuleSheaf X R) :
    (restrictionComp f (ModuleCat.{u} R) g).inv.app ((inverseImage q₀ R).obj M) ≫
        (restriction g (ModuleCat.{u} R)).map
          ((restrictionProjectionIso R q₀ q₁ f hf).hom.app M) ≫
        (restrictionProjectionIso R q₁ q₂ g hg).hom.app M =
      (restrictionProjectionIso R q₀ q₂ (g ≫ f) hfg).hom.app M := by
  have hP := projectionInverseImageIso_comp R q₀ q₁ q₂ f g (g ≫ f) hf hg hfg rfl M
  simp only [inverseImageCongr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp] at hP
  rw [restrictionProjectionIso_hom_app, restrictionProjectionIso_hom_app,
    restrictionProjectionIso_hom_app, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [(inverseImageIsoRestriction g R).inv.naturality_assoc, hP, ← inverseImageIsoRestriction_comp_inv_app R f g ((inverseImage q₀ R).obj M)]
  simp only [Category.assoc]

/-- Pullback of degree `n` cohomology along an étale map `f`, with coefficients compared
along a commuting triangle `f ≫ q = r`. -/
def projectionCohomologyMap (q : Z ⟶ X) (r : Y ⟶ X) (f : Y ⟶ Z) [Etale f] (h : f ≫ q = r)
    (n : ℕ) (M : ModuleSheaf X R) :
    (EtaleDerivedSections.cohomology Z R n).obj ((inverseImage q R).obj M) ⟶
      (EtaleDerivedSections.cohomology Y R n).obj ((inverseImage r R).obj M) :=
  cohomologyMapWithCoefficients f R n ((restrictionProjectionIso R q r f h).hom.app M)

/-- The pullback depends only on the étale map. -/
theorem projectionCohomologyMap_congr (q : Z ⟶ X) (r : Y ⟶ X) {f g : Y ⟶ Z} [Etale f]
    [Etale g] (e : f = g) (hf : f ≫ q = r) (hg : g ≫ q = r) (n : ℕ) (M : ModuleSheaf X R) :
    projectionCohomologyMap R q r f hf n M = projectionCohomologyMap R q r g hg n M := by
  subst e
  rfl

/-- Pullback along the identity is the identity. -/
theorem projectionCohomologyMap_id (q : Y ⟶ X) (h : 𝟙 Y ≫ q = q) (n : ℕ)
    (M : ModuleSheaf X R) : projectionCohomologyMap R q q (𝟙 Y) h n M = 𝟙 _ := by
  rw [projectionCohomologyMap, cohomologyMapWithCoefficients, restrictionProjectionIso_id]
  exact cohomologyMap_id R n _

/-- Successive pullbacks compose to the pullback along the composite. -/
theorem projectionCohomologyMap_comp {Y₀ Y₁ Y₂ : Scheme.{u}} (q₀ : Y₀ ⟶ X) (q₁ : Y₁ ⟶ X)
    (q₂ : Y₂ ⟶ X) (f : Y₁ ⟶ Y₀) (g : Y₂ ⟶ Y₁) [Etale f] [Etale g] (hf : f ≫ q₀ = q₁)
    (hg : g ≫ q₁ = q₂) (n : ℕ) (M : ModuleSheaf X R) :
    projectionCohomologyMap R q₀ q₁ f hf n M ≫ projectionCohomologyMap R q₁ q₂ g hg n M =
      projectionCohomologyMap R q₀ q₂ (g ≫ f)
        ((Category.assoc g f q₀).trans ((congrArg (g ≫ ·) hf).trans hg)) n M := by
  rw [projectionCohomologyMap, projectionCohomologyMap, projectionCohomologyMap,
    cohomologyMapWithCoefficients_comp, restrictionProjectionIso_comp]

/-- The pullback is natural in the base sheaf. -/
theorem projectionCohomologyMap_naturality (q : Z ⟶ X) (r : Y ⟶ X) (f : Y ⟶ Z) [Etale f]
    (h : f ≫ q = r) (n : ℕ) {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (EtaleDerivedSections.cohomology Z R n).map ((inverseImage q R).map α) ≫
        projectionCohomologyMap R q r f h n N =
      projectionCohomologyMap R q r f h n M ≫
        (EtaleDerivedSections.cohomology Y R n).map ((inverseImage r R).map α) := by
  rw [projectionCohomologyMap, projectionCohomologyMap, cohomologyMapWithCoefficients,
    cohomologyMapWithCoefficients, ← Category.assoc, (cohomologyMap f R n).naturality,
    Category.assoc, Category.assoc, Functor.comp_map, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  congr 2
  exact (restrictionProjectionIso R q r f h).hom.naturality α

end Projection

/-- Identity components of a tower morphism are étale. -/
instance etale_id_app {G : Type u} [Group G] [TopologicalSpace G]
    (T₀ : CompactOpenLevel G ⥤ Scheme.{u}) (K : CompactOpenLevel G) :
    Etale (NatTrans.app (𝟙 T₀) K) :=
  inferInstanceAs (Etale (𝟙 (T₀.obj K)))

/-- Composites of tower morphisms with étale components have étale components. -/
instance etale_comp_app {G : Type u} [Group G] [TopologicalSpace G]
    {T₀ T₁ T₂ : CompactOpenLevel G ⥤ Scheme.{u}} (ψ : T₂ ⟶ T₁) (φ : T₁ ⟶ T₀)
    [∀ K, Etale (ψ.app K)] [∀ K, Etale (φ.app K)] (K : CompactOpenLevel G) :
    Etale ((ψ ≫ φ).app K) :=
  inferInstanceAs (Etale (ψ.app K ≫ φ.app K))

variable {G : Type u} [Group G] [TopologicalSpace G] {T : CompactOpenLevel G ⥤ Scheme.{u}}
variable (R : Type u) [CommRing R]
variable {X : Scheme.{u}} (p : T ⟶ (Functor.const (CompactOpenLevel G)).obj X)

/-- The projections of the levels to the base, as a cone over the opposite scheme diagram. -/
def baseCone : (Functor.const (CompactOpenLevel G)ᵒᵖ).obj (op X) ⟶ T.op where
  app K := (p.app K.unop).op
  naturality K L a := by
    apply Quiver.Hom.unop_inj
    have h := p.naturality a.unop
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.op_obj, Functor.op_map,
      unop_comp, Quiver.Hom.unop_op, CategoryTheory.unop_id, Category.comp_id]
    exact h.symm

@[simp] theorem baseCone_app_unop (K : (CompactOpenLevel G)ᵒᵖ) :
    ((baseCone p).app K).unop = p.app K.unop := rfl

variable [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T.map a)]

section Generic

variable [IsTopologicalGroup G]

variable (T) in
/-- The colimit over levels of global sections, as a functor from level-trivial coefficient
diagrams to smooth representations. -/
def smoothColimitSectionsFunctor :
    (levelTrivialCoefficients T R).FullSubcategory ⥤ SmoothRep.{u, u, u} R G :=
  (LevelColimit.levelTrivialProperty G (ModuleCat.{u} R)).lift
      ((levelTrivialCoefficients T R).ι ⋙ CoefficientDiagram.sectionsFunctor)
      (fun D => isLevelTrivial_sections D.property) ⋙
    LevelColimit.smoothFunctor G R

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
    (LevelColimit.smoothFunctor G R)

end Generic

/-- The inverse images `p_K^* M` of a base sheaf on all levels, with the transition along
`T(a) : T(L) ⟶ T(K)` the inverse-image composition comparison
`T(a)^* p_K^* M ≅ p_L^* M`, transported to restriction along the étale map `T(a)`. -/
def canonicalCoefficients (M : ModuleSheaf X R) : CoefficientDiagram R T.op :=
  EtaleGeometricDiagram.CoefficientDiagram.toRestriction
    (EtaleGeometricDiagram.canonicalCoefficients R (baseCone p) M)

@[simp] theorem canonicalCoefficients_obj (M : ModuleSheaf X R) (K : (CompactOpenLevel G)ᵒᵖ) :
    (canonicalCoefficients R p M).obj K = (inverseImage (p.app K.unop) R).obj M := rfl

/-- The transition of the coefficients along a level arrow. -/
theorem canonicalCoefficients_map (M : ModuleSheaf X R) {K L : (CompactOpenLevel G)ᵒᵖ}
    (a : K ⟶ L) :
    (canonicalCoefficients R p M).map a =
      (restrictionProjectionIso R (p.app K.unop) (p.app L.unop) (T.map a.unop)
        (EtaleGeometricDiagram.baseProjection_triangle (baseCone p) a)).hom.app M := rfl

/-- The cohomology transition along a level arrow is the pullback with projection
coefficients. -/
theorem canonicalCoefficients_cohomology_map (M : ModuleSheaf X R) (n : ℕ)
    {K L : (CompactOpenLevel G)ᵒᵖ} (a : K ⟶ L) :
    ((canonicalCoefficients R p M).cohomology n).map a =
      projectionCohomologyMap R (p.app K.unop) (p.app L.unop) (T.map a.unop)
        (EtaleGeometricDiagram.baseProjection_triangle (baseCone p) a) n M := rfl

/-- The coefficient transition of a level arrow depends only on its scheme morphism. -/
theorem canonicalCoefficients_map_congr (M : ModuleSheaf X R) {K L : (CompactOpenLevel G)ᵒᵖ}
    (a b : K ⟶ L) (e : (T.op.map a).unop = (T.op.map b).unop) :
    (canonicalCoefficients R p M).map a =
      (restrictionCongr R e).hom.app ((canonicalCoefficients R p M).obj K) ≫
        (canonicalCoefficients R p M).map b :=
  restrictionProjectionIso_congr R (p.app K.unop) (p.app L.unop) e _ _ M

/-- A morphism of base sheaves gives a morphism of the pulled-back coefficient diagrams. -/
def canonicalCoefficientsFunctor : ModuleSheaf X R ⥤ CoefficientDiagram R T.op :=
  EtaleGeometricDiagram.canonicalCoefficientsFunctor R (baseCone p) ⋙
    EtaleGeometricDiagram.CoefficientDiagram.toRestrictionFunctor

@[simp] theorem canonicalCoefficientsFunctor_obj (M : ModuleSheaf X R) :
    (canonicalCoefficientsFunctor R p).obj M = canonicalCoefficients R p M := rfl

@[simp] theorem canonicalCoefficientsFunctor_map_app {M N : ModuleSheaf X R} (α : M ⟶ N)
    (K : (CompactOpenLevel G)ᵒᵖ) :
    ((canonicalCoefficientsFunctor R p).map α).app K = (inverseImage (p.app K.unop) R).map α :=
  rfl

/-- The degree `q` cohomology at level `K` is that of `T(K)` with coefficients `p_K^* M`. -/
theorem canonicalCoefficients_cohomology_obj (M : ModuleSheaf X R) (q : ℕ)
    (K : CompactOpenLevel G) :
    ((canonicalCoefficients R p M).cohomology q).obj (op K) =
      (EtaleDerivedSections.cohomology (T.obj K) R q).obj ((inverseImage (p.app K) R).obj M) :=
  rfl

variable {p}

/-- If each `k ∈ K` acts on `T(K)` by the identity, the pulled-back coefficients are
level-trivial. -/
theorem isLevelTrivialCoefficients_canonical
    (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
      T.map (selfArrow K k hk) = 𝟙 (T.obj K))
    (M : ModuleSheaf X R) : IsLevelTrivialCoefficients (canonicalCoefficients R p M) := by
  intro K k hk
  have e : (T.op.map (selfArrow K k hk).op).unop = (T.op.map (𝟙 (op K))).unop := by
    change T.map (selfArrow K k hk) = (T.op.map (𝟙 (op K))).unop
    rw [hT K k hk, CategoryTheory.Functor.map_id]
    rfl
  exact ⟨e, canonicalCoefficients_map_congr R p M _ _ e⟩

variable (p)

section LevelTrivial

variable (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T.map (selfArrow K k hk) = 𝟙 (T.obj K))

/-- Pulled-back coefficients as a functor into level-trivial coefficient diagrams. -/
def levelTrivialCanonicalCoefficientsFunctor :
    ModuleSheaf X R ⥤ (levelTrivialCoefficients T R).FullSubcategory :=
  (levelTrivialCoefficients T R).lift (canonicalCoefficientsFunctor R p)
    (fun M => isLevelTrivialCoefficients_canonical R hT M)

variable [IsTopologicalGroup G]

/-- The colimit over levels of the degree `q` cohomology of `T(K)` with coefficients
`p_K^* M`, as a smooth representation of `G`, natural in the base sheaf `M`. -/
def smoothCanonicalCohomologyFunctor (q : ℕ) : ModuleSheaf X R ⥤ SmoothRep.{u, u, u} R G :=
  levelTrivialCanonicalCoefficientsFunctor R p hT ⋙ smoothColimitCohomologyFunctor T R q

/-- The colimit over levels of the global sections of `p_K^* M`, as a smooth representation
of `G`, natural in the base sheaf `M`. -/
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
`g K g⁻¹` of its pullback along `T(g K g⁻¹ ⟶ K)` followed by the inverse-image
comparison of the pulled-back coefficients. -/
theorem smoothCanonicalCohomology_ρ_ι_apply (q : ℕ) (M : ModuleSheaf X R) (g : G)
    (K : CompactOpenLevel G)
    (x : (EtaleDerivedSections.cohomology (T.obj K) R q).obj ((inverseImage (p.app K) R).obj M)) :
    ((smoothCanonicalCohomologyFunctor R p hT q).obj M).obj.ρ g
        ((LevelColimit.ι ((canonicalCoefficients R p M).cohomology q) K).hom x) =
      (LevelColimit.ι ((canonicalCoefficients R p M).cohomology q) (conjLevel g K)).hom
        ((cohomologyMapWithCoefficients (T.map (conjArrow g K)) R q
          ((canonicalCoefficients R p M).map (conjArrow g K).op)).hom x) :=
  smoothColimitCohomology_ρ_ι_apply (canonicalCoefficients R p M)
    (isLevelTrivialCoefficients_canonical R hT M) q g K x

/-- Every class comes from the cohomology of a single level, provided some level exists. -/
theorem canonicalCohomology_exists_level [Nonempty (CompactOpenLevel G)] (q : ℕ)
    (M : ModuleSheaf X R) (x : ((smoothCanonicalCohomologyFunctor R p hT q).obj M).obj.V) :
    ∃ (K : CompactOpenLevel G)
      (y : (EtaleDerivedSections.cohomology (T.obj K) R q).obj
        ((inverseImage (p.app K) R).obj M)),
      (LevelColimit.ι ((canonicalCoefficients R p M).cohomology q) K).hom y = x :=
  exists_level_class (canonicalCoefficients R p M) q x

end LevelTrivial

section TowerMorphism

variable {T' T'' : CompactOpenLevel G ⥤ Scheme.{u}}
variable [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T'.map a)]
variable [∀ {K L : CompactOpenLevel G} (a : K ⟶ L), Etale (T''.map a)]
variable (φ : T' ⟶ T) [∀ K, Etale (φ.app K)]
variable {p' : T' ⟶ (Functor.const (CompactOpenLevel G)).obj X} (hφ : φ ≫ p = p')

/-- Pullback of the cohomology of pulled-back coefficients along a morphism of towers over
the base whose components are étale. At level `K` it is the pullback along `φ_K` with the
projection comparison `φ_K^* p_K^* M ≅ p'_K^* M`. -/
def canonicalPullback (M : ModuleSheaf X R) (n : ℕ) :
    (canonicalCoefficients R p M).cohomology n ⟶ (canonicalCoefficients R p' M).cohomology n where
  app K := projectionCohomologyMap R (p.app K.unop) (p'.app K.unop) (φ.app K.unop)
    (NatTrans.congr_app hφ K.unop) n M
  naturality K L b := by
    change projectionCohomologyMap R _ _ (T.map b.unop) _ n M ≫
        projectionCohomologyMap R _ _ (φ.app L.unop) _ n M =
      projectionCohomologyMap R _ _ (φ.app K.unop) _ n M ≫
        projectionCohomologyMap R _ _ (T'.map b.unop) _ n M
    rw [projectionCohomologyMap_comp, projectionCohomologyMap_comp]
    exact projectionCohomologyMap_congr R _ _ (φ.naturality b.unop).symm _ _ n M

theorem canonicalPullback_app (M : ModuleSheaf X R) (n : ℕ) (K : (CompactOpenLevel G)ᵒᵖ) :
    (canonicalPullback R p φ hφ M n).app K =
      projectionCohomologyMap R (p.app K.unop) (p'.app K.unop) (φ.app K.unop)
        (NatTrans.congr_app hφ K.unop) n M := rfl

/-- The pullback is natural in the base sheaf. -/
def canonicalPullbackNatTrans (n : ℕ) :
    canonicalCoefficientsFunctor R p ⋙ CoefficientDiagram.cohomologyFunctor n ⟶
      canonicalCoefficientsFunctor R p' ⋙ CoefficientDiagram.cohomologyFunctor n where
  app M := canonicalPullback R p φ hφ M n
  naturality M N α := by
    apply NatTrans.ext
    funext K
    exact projectionCohomologyMap_naturality R _ _ _ _ n α

/-- Pullback along the identity tower morphism is the identity. -/
theorem canonicalPullback_id (h : 𝟙 T ≫ p = p) (M : ModuleSheaf X R) (n : ℕ) :
    canonicalPullback R p (𝟙 T) h M n = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  exact projectionCohomologyMap_id R _ _ n M

/-- Pullback along a composite of tower morphisms is the composite of the pullbacks. -/
theorem canonicalPullback_comp (ψ : T'' ⟶ T') [∀ K, Etale (ψ.app K)]
    {p'' : T'' ⟶ (Functor.const (CompactOpenLevel G)).obj X} (hψ : ψ ≫ p' = p'')
    (hψφ : (ψ ≫ φ) ≫ p = p'') (M : ModuleSheaf X R) (n : ℕ) :
    canonicalPullback R p φ hφ M n ≫ canonicalPullback R p' ψ hψ M n =
      canonicalPullback R p (ψ ≫ φ) hψφ M n := by
  apply NatTrans.ext
  funext K
  change projectionCohomologyMap R _ _ (φ.app K.unop) _ n M ≫
      projectionCohomologyMap R _ _ (ψ.app K.unop) _ n M =
    projectionCohomologyMap R _ _ (ψ.app K.unop ≫ φ.app K.unop) _ n M
  rw [projectionCohomologyMap_comp]

/-- On colimits over levels, the pullback sends the image of a class of level `K` to the
image of its pullback along `φ_K`. -/
theorem canonicalPullback_ι (M : ModuleSheaf X R) (n : ℕ) (K : CompactOpenLevel G) :
    LevelColimit.ι ((canonicalCoefficients R p M).cohomology n) K ≫
        LevelColimit.map (canonicalPullback R p φ hφ M n) =
      projectionCohomologyMap R (p.app K) (p'.app K) (φ.app K) (NatTrans.congr_app hφ K) n M ≫
        LevelColimit.ι ((canonicalCoefficients R p' M).cohomology n) K :=
  LevelColimit.ι_map _ K

variable (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T.map (selfArrow K k hk) = 𝟙 (T.obj K))
variable (hT' : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T'.map (selfArrow K k hk) = 𝟙 (T'.obj K))
variable (hT'' : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T''.map (selfArrow K k hk) = 𝟙 (T''.obj K))
variable [IsTopologicalGroup G]

/-- The pullback along a tower morphism as a morphism of smooth representations, natural in
the base sheaf. -/
def smoothCanonicalPullback (n : ℕ) :
    smoothCanonicalCohomologyFunctor R p hT n ⟶ smoothCanonicalCohomologyFunctor R p' hT' n where
  app M := (LevelColimit.smoothFunctor G R).map
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
      (LevelColimit.smoothFunctor G R).map
        (ObjectProperty.homMk (canonicalPullback R p φ hφ M n)) := rfl

/-- The smooth pullback along the identity tower morphism is the identity. -/
theorem smoothCanonicalPullback_id (h : 𝟙 T ≫ p = p) (n : ℕ) :
    smoothCanonicalPullback R p (𝟙 T) h hT hT n = 𝟙 _ := by
  apply NatTrans.ext
  funext M
  rw [smoothCanonicalPullback_app, canonicalPullback_id]
  exact (LevelColimit.smoothFunctor G R).map_id _

/-- The smooth pullback along a composite is the composite of the smooth pullbacks. -/
theorem smoothCanonicalPullback_comp (ψ : T'' ⟶ T') [∀ K, Etale (ψ.app K)]
    {p'' : T'' ⟶ (Functor.const (CompactOpenLevel G)).obj X} (hψ : ψ ≫ p' = p'')
    (hψφ : (ψ ≫ φ) ≫ p = p'') (n : ℕ) :
    smoothCanonicalPullback R p φ hφ hT hT' n ≫ smoothCanonicalPullback R p' ψ hψ hT' hT'' n =
      smoothCanonicalPullback R p (ψ ≫ φ) hψφ hT hT'' n := by
  apply NatTrans.ext
  funext M
  rw [NatTrans.comp_app, smoothCanonicalPullback_app, smoothCanonicalPullback_app,
    smoothCanonicalPullback_app, ← CategoryTheory.Functor.map_comp,
    ← canonicalPullback_comp R p φ hφ ψ hψ hψφ M n]
  rfl

end TowerMorphism

/-- Isomorphisms of towers have étale components. -/
instance etale_iso_hom_app {T₀ T₁ : CompactOpenLevel G ⥤ Scheme.{u}} (e : T₀ ≅ T₁)
    (K : CompactOpenLevel G) : Etale (e.hom.app K) :=
  inferInstance

section Automorphisms

variable (hT : ∀ (K : CompactOpenLevel G) (k : G) (hk : k ∈ K.subgroup),
  T.map (selfArrow K k hk) = 𝟙 (T.obj K))
variable [IsTopologicalGroup G]

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

end Langlands.Shimura.LevelTowerCohomology
