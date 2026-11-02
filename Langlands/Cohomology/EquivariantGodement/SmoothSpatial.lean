import Langlands.Cohomology.EquivariantGodement.Spatial
import Langlands.Cohomology.DivisibleSystem.ScalarExtension

/-! # Smooth compact spatial maps for the full equivariant Godement complex -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.EquivariantGodementCohomology.Spatial

open CategoryTheory HomologicalComplex Langlands.Sheaf.Equivariant

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Restrict the constructed proper compact spatial chain map to smooth vectors
in every degree, retaining the original full Godement resolution. -/
def smoothCompactComplexMap (hp : IsProperMap f) :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ smoothCompactComplex R G Y ⟶
      smoothCompactComplex R G X :=
  Functor.whiskerRight (compactComplexMap f hf hp)
    (smoothPartComplex R G (ComplexShape.up ℕ))

/-- After forgetting smoothness, this is a map between the original smooth
compact-section complexes in algebraic representations. -/
def smoothCompactRepComplexMap (hp : IsProperMap f) :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ Godement.complexFunctor R G Y ⋙
        EquivariantSections.smoothCompactComplex R G Y (ComplexShape.up ℕ) ⟶
      Godement.complexFunctor R G X ⋙
        EquivariantSections.smoothCompactComplex R G X (ComplexShape.up ℕ) :=
  Functor.whiskerRight (smoothCompactComplexMap f hf hp)
    ((Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex (ComplexShape.up ℕ))

/-- The underlying global section is sent by the actual spatial sheaf map in
each degree; both compactness and smoothness are retained as subtype proofs. -/
@[simp]
theorem smoothCompactComplexMap_apply (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) (n : ℕ)
    (s : Langlands.smoothVectors
      (((compactComplex R G Y).obj
        ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).X n).ρ) :
    (Langlands.SmoothRep.hom (((smoothCompactComplexMap f hf hp).app F).f n) s).val.val =
      (((Godement.Spatial.complexMap f hf F).f n).hom.app
        (Opposite.op ActionOpens.top)).hom s.val.val := rfl

/-- The smooth compact degree-zero map retains the actual stalk-family formula. -/
theorem smoothCompactComplexMap_apply_zero (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R))
    (s : Langlands.smoothVectors
      (((compactComplex R G Y).obj
        ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)).X 0).ρ) :
    (Langlands.SmoothRep.hom (((smoothCompactComplexMap f hf hp).app F).f 0) s).val.val =
      ((Godement.Spatial.zeroMap f hf F).hom.app
        (Opposite.op ActionOpens.top)).hom s.val.val := by
  rw [smoothCompactComplexMap_apply, Godement.Spatial.complexMap_f_zero]
  rfl

/-- The smooth restriction commutes with the actual inclusion in full compact
sections at the chain level. -/
theorem smoothCompactComplexMap_inclusion_square (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactRepComplexMap f hf hp).app F ≫
        (EquivariantSections.forgetSmoothComplex R G X (ComplexShape.up ℕ)).app
          (Godement.complex R G X F) =
      (EquivariantSections.forgetSmoothComplex R G Y (ComplexShape.up ℕ)).app
          (Godement.complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)) ≫
        (compactComplexMap f hf hp).app F :=
  (smoothPartComplexInclusion R G (ComplexShape.up ℕ)).naturality
    ((compactComplexMap f hf hp).app F)

@[simp]
theorem smoothCompactComplexMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactComplexMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id).app F =
      𝟙 ((smoothCompactComplex R G X).obj F) := by
  change (smoothPartComplex R G (ComplexShape.up ℕ)).map _ = _
  rw [compactComplexMap_id]
  exact (smoothPartComplex R G (ComplexShape.up ℕ)).map_id _

/-- The smooth restrictions of actual proper spatial maps compose. -/
theorem smoothCompactComplexMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactComplexMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp)).app F =
      (smoothCompactComplexMap g hg hq).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (smoothCompactComplexMap f hf hp).app F := by
  change (smoothPartComplex R G (ComplexShape.up ℕ)).map _ = _
  rw [compactComplexMap_comp f hf g hg hp hq F]
  exact (smoothPartComplex R G (ComplexShape.up ℕ)).map_comp _ _

@[simp]
theorem smoothCompactRepComplexMap_id (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactRepComplexMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id).app F =
      𝟙 ((EquivariantSections.smoothCompactComplex R G X (ComplexShape.up ℕ)).obj
        (Godement.complex R G X F)) := by
  change ((Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map _ = _
  rw [smoothCompactComplexMap_id]
  exact CategoryTheory.Functor.map_id _ _

theorem smoothCompactRepComplexMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactRepComplexMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp)).app F =
      (smoothCompactRepComplexMap g hg hq).app
          ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (smoothCompactRepComplexMap f hf hp).app F := by
  change ((Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map _ = _
  rw [smoothCompactComplexMap_comp f hf g hg hp hq F]
  exact Functor.map_comp _ _ _

/-- Forgetting smoothness and compact support commutes with the actual spatial map. -/
theorem smoothCompactComplexMap_inclusion_triangle (hp : IsProperMap f)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactRepComplexMap f hf hp).app F ≫
        (EquivariantSections.forgetSmoothComplex R G X (ComplexShape.up ℕ)).app
          (Godement.complex R G X F) ≫
        (EquivariantSections.forgetSupportComplex R G X (ComplexShape.up ℕ)).app
          (Godement.complex R G X F) =
      (EquivariantSections.forgetSmoothComplex R G Y (ComplexShape.up ℕ)).app
          (Godement.complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)) ≫
        (EquivariantSections.forgetSupportComplex R G Y (ComplexShape.up ℕ)).app
          (Godement.complex R G Y ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F)) ≫
        (globalComplexMap f hf).app F := by
  rw [← Category.assoc, smoothCompactComplexMap_inclusion_square, Category.assoc,
    compactComplexMap_inclusion_triangle]

/-- Homology of the smooth restriction, bundled in the existing full smooth
representation category using the existing proved smoothness of homology. -/
def smoothCompactCohomologyMap (hp : IsProperMap f) (q : ℕ) :
    DirectImage.sheaf f hf (ModuleCat.{u} R) ⋙ smoothCompactCohomology R G Y q ⟶
      smoothCompactCohomology R G X q where
  app F := ObjectProperty.homMk
    ((homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map
      ((smoothCompactRepComplexMap f hf hp).app F))
  naturality _ _ a := by
    apply (Langlands.SmoothRep.toRep (R := R) (G := G)).map_injective
    change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ ≫
        (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ =
      (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ ≫
        (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun k => (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map k)
      ((smoothCompactRepComplexMap f hf hp).naturality a)

/-- The underlying smooth cohomology map commutes with inclusion into the
already constructed compact Godement cohomology. -/
theorem smoothCompactCohomologyMap_inclusion_square (hp : IsProperMap f) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    Langlands.SmoothRep.toRep.map ((smoothCompactCohomologyMap f hf hp q).app F) ≫
        (forgetSmooth R G X q).app F =
      (forgetSmooth R G Y q).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (compactCohomologyMap f hf hp q).app F := by
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ ≫
        (𝟙 _ ≫ (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _) =
      (𝟙 _ ≫ (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _) ≫
        (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _
  simp only [Category.id_comp, ← Functor.map_comp]
  exact congrArg (fun k => (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map k)
    (smoothCompactComplexMap_inclusion_square f hf hp F)

/-- The corresponding triangle in cohomology also forgets compact support. -/
theorem smoothCompactCohomologyMap_inclusion_triangle (hp : IsProperMap f) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    Langlands.SmoothRep.toRep.map ((smoothCompactCohomologyMap f hf hp q).app F) ≫
        (forgetSmooth R G X q).app F ≫ (forgetSupport R G X q).app F =
      (forgetSmooth R G Y q).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (forgetSupport R G Y q).app ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (globalCohomologyMap f hf q).app F := by
  rw [← Category.assoc, smoothCompactCohomologyMap_inclusion_square, Category.assoc,
    compactCohomologyMap_inclusion_triangle]

@[simp]
theorem smoothCompactCohomologyMap_id (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactCohomologyMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
        isProperMap_id q).app F =
      𝟙 ((smoothCompactCohomology R G X q).obj F) := by
  apply (Langlands.SmoothRep.toRep (R := R) (G := G)).map_injective
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = 𝟙 _
  rw [smoothCompactRepComplexMap_id]
  exact CategoryTheory.Functor.map_id _ _

/-- Proper spatial maps induce contravariantly composable smooth cohomology maps. -/
theorem smoothCompactCohomologyMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (q : ℕ)
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (smoothCompactCohomologyMap (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) q).app F =
      (smoothCompactCohomologyMap g hg hq q).app
          ((DirectImage.sheaf f hf (ModuleCat.{u} R)).obj F) ≫
        (smoothCompactCohomologyMap f hf hp q).app F := by
  apply (Langlands.SmoothRep.toRep (R := R) (G := G)).map_injective
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ =
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ ≫
      (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _
  rw [smoothCompactRepComplexMap_comp f hf g hg hp hq F]
  exact Functor.map_comp _ _ _

end Langlands.Cohomology.EquivariantGodementCohomology.Spatial
