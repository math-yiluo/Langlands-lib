import Langlands.Shimura.Coefficients.VaryingCoverInverse
import Langlands.CategoryTheory.EquivariantDiagramPreadditive
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.Functor

/-! # Additive associated sheaves and actual associated complexes -/

noncomputable section

universe u v w uJ vJ uι

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section Site

variable {C : Type w} [Category.{v} C] [HasBinaryProducts C]
variable (T : GrothendieckTopology C) {R : Type u} [CommRing R]

/-- Restriction to products with a cover preserves addition of sheaf maps. -/
instance productSheaf_additive (Y : C) :
    (productSheaf (R := R) T Y).Additive where
  map_add := by
    intro F F' f g
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext U
    rfl

variable {G : Type u} [Group G] (Y : Action C G)

/-- The diagonal action construction is additive on equivariant morphisms. -/
instance diagonalFunctor_additive :
    (diagonalFunctor (R := R) T Y).Additive where
  map_add := by
    intro F F' f g
    apply Action.Hom.ext
    exact (productSheaf T Y.V).map_add

/-- Taking the actual invariant subsheaf preserves addition of equivariant maps. -/
instance associatedFunctor_additive :
    (associatedFunctor (R := R) T Y).Additive where
  map_add := by
    intro F F' f g
    apply (cancel_mono (inclusion T Y F')).mp
    rw [Preadditive.add_comp, inclusion_natural, inclusion_natural, inclusion_natural]
    simp only [Action.add_hom, Functor.map_add, Preadditive.comp_add]

/-- Constant coefficients followed by associated invariants form an additive functor. -/
instance constantAssociatedFunctor_additive [HasSheafify T (ModuleCat.{u} R)] :
    (constantAssociatedFunctor (R := R) T Y).Additive := by
  unfold constantAssociatedFunctor
  infer_instance

end Site

section Etale

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {G : Type u} [Group G] (Z : Action X.Etale G)

/-- Associated small-etale coefficient sheaves depend additively on coefficient maps. -/
instance etaleAssociatedFunctor_additive :
    (etaleAssociatedFunctor (R := R) X Z).Additive := by
  unfold etaleAssociatedFunctor
  infer_instance

variable {ι : Type uι} (c : ComplexShape ι)

/-- Apply actual associated small-etale sheaves to an arbitrary-shape coefficient complex. -/
def etaleAssociatedComplexFunctor :
    HomologicalComplex (Action (ModuleCat.{u} R) G) c ⥤
      HomologicalComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c :=
  (etaleAssociatedFunctor X Z).mapHomologicalComplex c

instance etaleAssociatedComplexFunctor_additive :
    (etaleAssociatedComplexFunctor (R := R) X Z c).Additive := by
  unfold etaleAssociatedComplexFunctor
  infer_instance

end Etale

section Varying

variable (X : Scheme.{u}) {R : Type u} [CommRing R]
variable {J : Type uJ} [Category.{vJ} J] {D : J ⥤ GrpCat.{u}}
variable (Y : EquivariantDiagram D X.Etale)

/-- Association at one index is additive on the whole coefficient-diagram category. -/
instance etaleAssociatedAt_additive (j : J) :
    (etaleAssociatedAt (R := R) X Y j).Additive := by
  unfold etaleAssociatedAt
  infer_instance

variable (hY : ∀ j, IsFiniteGeometricTorsor X (Y.action j))

/-- The proved varying-cover construction is additive in coefficient diagrams. -/
instance etaleAssociatedVaryingSystemFunctor_additive :
    (etaleAssociatedVaryingSystemFunctor (R := R) X Y hY).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext j
    exact (etaleAssociatedAt X Y j).map_add

variable {ι : Type uι} (c : ComplexShape ι)

/-- An actual complex of associated sheaf diagrams, including its differentials and maps. -/
def etaleAssociatedVaryingComplexFunctor :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      HomologicalComplex (J ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c :=
  (etaleAssociatedVaryingSystemFunctor X Y hY).mapHomologicalComplex c

instance etaleAssociatedVaryingComplexFunctor_additive :
    (etaleAssociatedVaryingComplexFunctor (R := R) X Y hY c).Additive := by
  unfold etaleAssociatedVaryingComplexFunctor
  infer_instance

/-- The same constructed data, viewed as an index diagram of sheaf complexes. -/
def etaleAssociatedVaryingComplexSystemFunctor :
    HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c ⥤
      (J ⥤ HomologicalComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c) :=
  etaleAssociatedVaryingComplexFunctor X Y hY c ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex

@[simp] theorem etaleAssociatedVaryingComplexFunctor_X
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (n : ι) :
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K).X n =
      etaleAssociatedVaryingSystem X Y hY (K.X n) := rfl

@[simp] theorem etaleAssociatedVaryingComplexFunctor_d
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (p q : ι) :
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).obj K).d p q =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map (K.d p q) := rfl

@[simp] theorem etaleAssociatedVaryingComplexFunctor_map_f
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (n : ι) :
    ((etaleAssociatedVaryingComplexFunctor X Y hY c).map f).f n =
      (etaleAssociatedVaryingSystemFunctor X Y hY).map (f.f n) := rfl

@[simp] theorem etaleAssociatedVaryingComplexSystemFunctor_obj_X
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (j : J) (n : ι) :
    (((etaleAssociatedVaryingComplexSystemFunctor X Y hY c).obj K).obj j).X n =
      (etaleAssociatedFunctor X (Y.action j)).obj ((K.X n).action j) := rfl

@[simp] theorem etaleAssociatedVaryingComplexSystemFunctor_obj_d
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    (j : J) (p q : ι) :
    (((etaleAssociatedVaryingComplexSystemFunctor X Y hY c).obj K).obj j).d p q =
      (etaleAssociatedFunctor X (Y.action j)).map
        ((EquivariantDiagram.evaluation j).map (K.d p q)) := rfl

@[simp] theorem etaleAssociatedVaryingComplexSystemFunctor_transition_f
    (K : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c)
    {i j : J} (a : i ⟶ j) (n : ι) :
    (((etaleAssociatedVaryingComplexSystemFunctor X Y hY c).obj K).map a).f n =
      (etaleAssociatedTransition X Y hY a).app (K.X n) := rfl

@[simp] theorem etaleAssociatedVaryingComplexSystemFunctor_map_app_f
    {K L : HomologicalComplex (EquivariantDiagram D (ModuleCat.{u} R)) c}
    (f : K ⟶ L) (j : J) (n : ι) :
    (((etaleAssociatedVaryingComplexSystemFunctor X Y hY c).map f).app j).f n =
      (etaleAssociatedFunctor X (Y.action j)).map
        ((EquivariantDiagram.evaluation j).map (f.f n)) := rfl

/-- Evaluation at a cover is naturally the complex lift of association at that cover. -/
def etaleAssociatedVaryingComplexEvaluationIso (j : J) :
    etaleAssociatedVaryingComplexSystemFunctor (R := R) X Y hY c ⋙
        (evaluation J
          (HomologicalComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) c)).obj j ≅
      (etaleAssociatedAt X Y j).mapHomologicalComplex c :=
  NatIso.ofComponents (fun K => Iso.refl _) (by
    intro K L f
    apply HomologicalComplex.hom_ext
    intro n
    exact Category.comp_id _ |>.trans (Category.id_comp _).symm)

end Varying

end Langlands.Shimura.Coefficients
