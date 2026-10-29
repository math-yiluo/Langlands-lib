import Langlands.Sheaf.AdicSystem
import Langlands.Shimura.Coefficients.DiagramAdicComplex
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Actual ideal-power quotient complexes of sheaf diagrams -/

noncomputable section

universe u v uC vC uJ vJ uι

namespace Langlands.Sheaf.AdicSystem

open CategoryTheory

variable {C : Type uC} [Category.{vC} C] (T : GrothendieckTopology C)
variable {R : Type u} [CommRing R] (I : Ideal R)
variable [HasSheafify T (ModuleCat.{v} R)]

/-- Sheafified sectionwise ideal-power reduction preserves addition of morphisms. -/
instance powers_obj_additive (n : ℕᵒᵖ) : ((powers T I).obj n).Additive :=
  inferInstanceAs
    (sheafToPresheaf T (ModuleCat.{v} R) ⋙
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{v} R) (ModuleCat.{v} R)).obj
        (Langlands.Coefficients.AdicSystem.powerReduction I n.unop) ⋙
      presheafToSheaf T (ModuleCat.{v} R)).Additive

end Langlands.Sheaf.AdicSystem

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {C : Type uC} [Category.{vC} C] (T : GrothendieckTopology C)
variable {R : Type u} [CommRing R] (I : Ideal R)
variable [HasSheafify T (ModuleCat.{v} R)]
variable (J : Type uJ) [Category.{vJ} J]
variable {ι : Type uι} (c : ComplexShape ι)

/-- Actual sheaf-power reduction on all coordinates of a sheaf diagram. -/
def sheafDiagramPowers :
    ℕᵒᵖ ⥤ ((J ⥤ Sheaf T (ModuleCat.{v} R)) ⥤ (J ⥤ Sheaf T (ModuleCat.{v} R))) :=
  Langlands.Sheaf.AdicSystem.powers T I ⋙
    Functor.whiskeringRight J (Sheaf T (ModuleCat.{v} R)) (Sheaf T (ModuleCat.{v} R))

instance sheafDiagramPowers_obj_additive (n : ℕᵒᵖ) :
    ((sheafDiagramPowers T I J).obj n).Additive :=
  inferInstanceAs
    ((Functor.whiskeringRight J
      (Sheaf T (ModuleCat.{v} R)) (Sheaf T (ModuleCat.{v} R))).obj
        ((Langlands.Sheaf.AdicSystem.powers T I).obj n)).Additive

/-- The ordinary quotient inverse system of a whole sheaf diagram. -/
def sheafDiagramReductionFunctor :
    (J ⥤ Sheaf T (ModuleCat.{v} R)) ⥤
      (ℕᵒᵖ ⥤ (J ⥤ Sheaf T (ModuleCat.{v} R))) :=
  (sheafDiagramPowers T I J).flip

/-- Power reductions applied to the terms, differentials and maps of complexes. -/
def sheafDiagramComplexPowers :
    ℕᵒᵖ ⥤
      (HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c ⥤
        HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) where
  obj n := ((sheafDiagramPowers T I J).obj n).mapHomologicalComplex c
  map f := ((sheafDiagramPowers T I J).map f).mapHomologicalComplex c
  map_id n := by
    rw [(sheafDiagramPowers T I J).map_id, NatTrans.mapHomologicalComplex_id]
  map_comp f g := by
    rw [(sheafDiagramPowers T I J).map_comp, NatTrans.mapHomologicalComplex_comp]

/-- The full inverse system of actual quotient complexes, natural in the complex. -/
def sheafDiagramComplexReductionFunctor :
    HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c ⥤
      (ℕᵒᵖ ⥤ HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) :=
  (sheafDiagramComplexPowers T I J c).flip

/-- The actual quotient unit on complexes of sheaf diagrams. -/
def sheafDiagramComplexPowerUnit (n : ℕ) :
    𝟭 (HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) ⟶
      (sheafDiagramComplexPowers T I J c).obj (op n) :=
  (Functor.mapHomologicalComplexIdIso _ c).inv ≫
    (((Functor.whiskeringRight J
      (Sheaf T (ModuleCat.{v} R)) (Sheaf T (ModuleCat.{v} R))).map
        (Langlands.Sheaf.AdicSystem.quotientMap T I n))).mapHomologicalComplex c

@[reassoc (attr := simp)]
theorem sheafDiagramComplexPowerUnit_transition {m n : ℕ} (h : m ≤ n) :
    sheafDiagramComplexPowerUnit T I J c n ≫
        (sheafDiagramComplexPowers T I J c).map (homOfLE h).op =
      sheafDiagramComplexPowerUnit T I J c m := by
  apply NatTrans.ext
  funext K
  apply HomologicalComplex.hom_ext
  intro i
  apply NatTrans.ext
  funext j
  change (𝟙 _ ≫
      (Langlands.Sheaf.AdicSystem.quotientMap T I n).app ((K.X i).obj j)) ≫
        ((Langlands.Sheaf.AdicSystem.powers T I).map (homOfLE h).op).app
          ((K.X i).obj j) =
    𝟙 _ ≫ (Langlands.Sheaf.AdicSystem.quotientMap T I m).app ((K.X i).obj j)
  simp only [Category.id_comp]
  exact NatTrans.congr_app
    (Langlands.Sheaf.AdicSystem.quotientMap_transition T I h) ((K.X i).obj j)

/-- The genuine quotient chain maps form a cone. -/
def sheafDiagramComplexPowerCone
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) :
    Cone ((sheafDiagramComplexReductionFunctor T I J c).obj K) where
  pt := K
  π :=
    { app n := (sheafDiagramComplexPowerUnit T I J c n.unop).app K
      naturality {_m _n} f := by
        change 𝟙 _ ≫ (sheafDiagramComplexPowerUnit T I J c _n.unop).app K =
          (sheafDiagramComplexPowerUnit T I J c _m.unop).app K ≫
            ((sheafDiagramComplexPowers T I J c).map f).app K
        rw [Category.id_comp]
        simpa only [NatTrans.comp_app,
          show (homOfLE (leOfHom f.unop)).op = f from Subsingleton.elim _ _] using
          (NatTrans.congr_app
            (sheafDiagramComplexPowerUnit_transition T I J c (leOfHom f.unop)) K).symm }

/-- The ordinary inverse limit of the constructed quotient complexes. -/
def sheafDiagramComplexPowerLimit :
    HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c ⥤
      HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c :=
  sheafDiagramComplexReductionFunctor T I J c ⋙ lim

/-- The universal map from the original complex to its quotient-complex limit. -/
def sheafDiagramComplexPowerLimitUnit :
    𝟭 (HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) ⟶
      sheafDiagramComplexPowerLimit T I J c where
  app K := limit.lift _ (sheafDiagramComplexPowerCone T I J c K)
  naturality {K L} f := by
    change f ≫ limit.lift _ (sheafDiagramComplexPowerCone T I J c L) =
      limit.lift _ (sheafDiagramComplexPowerCone T I J c K) ≫
        limMap ((sheafDiagramComplexReductionFunctor T I J c).map f)
    apply limit.hom_ext
    intro n
    rw [Category.assoc, limit.lift_π, Category.assoc, limMap_π,
      ← Category.assoc, limit.lift_π]
    exact (sheafDiagramComplexPowerUnit T I J c n.unop).naturality f

@[reassoc (attr := simp)]
theorem sheafDiagramComplexPowerLimitUnit_π
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) (n : ℕ) :
    (sheafDiagramComplexPowerLimitUnit T I J c).app K ≫
        limit.π ((sheafDiagramComplexReductionFunctor T I J c).obj K) (op n) =
      (sheafDiagramComplexPowerUnit T I J c n).app K :=
  limit.lift_π _ _

/-- All quotient projections characterize the unit among chain maps. -/
theorem sheafDiagramComplexPowerLimitUnit_unique
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c)
    (f : K ⟶ (sheafDiagramComplexPowerLimit T I J c).obj K)
    (hf : ∀ n : ℕ,
      f ≫ limit.π ((sheafDiagramComplexReductionFunctor T I J c).obj K) (op n) =
        (sheafDiagramComplexPowerUnit T I J c n).app K) :
    f = (sheafDiagramComplexPowerLimitUnit T I J c).app K := by
  apply limit.hom_ext
  intro n
  exact (hf n.unop).trans (sheafDiagramComplexPowerLimitUnit_π T I J c K n.unop).symm

@[simp]
theorem sheafDiagramComplexPowers_obj_X
    (n : ℕᵒᵖ) (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c)
    (i : ι) (j : J) :
    ((((sheafDiagramComplexPowers T I J c).obj n).obj K).X i).obj j =
      ((Langlands.Sheaf.AdicSystem.powers T I).obj n).obj ((K.X i).obj j) := rfl

@[simp]
theorem sheafDiagramComplexPowers_obj_d
    (n : ℕᵒᵖ) (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c)
    (i k : ι) (j : J) :
    ((((sheafDiagramComplexPowers T I J c).obj n).obj K).d i k).app j =
      ((Langlands.Sheaf.AdicSystem.powers T I).obj n).map ((K.d i k).app j) := rfl

@[simp]
theorem sheafDiagramComplexPowers_transition_f
    {m n : ℕᵒᵖ} (a : m ⟶ n)
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) (i : ι) (j : J) :
    ((((sheafDiagramComplexPowers T I J c).map a).app K).f i).app j =
      ((Langlands.Sheaf.AdicSystem.powers T I).map a).app ((K.X i).obj j) := rfl

@[simp]
theorem sheafDiagramComplexPowers_map_f
    (n : ℕᵒᵖ) {K L : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c}
    (f : K ⟶ L) (i : ι) (j : J) :
    ((((sheafDiagramComplexPowers T I J c).obj n).map f).f i).app j =
      ((Langlands.Sheaf.AdicSystem.powers T I).obj n).map ((f.f i).app j) := rfl

@[simp]
theorem sheafDiagramComplexPowerUnit_f
    (n : ℕ) (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c)
    (i : ι) (j : J) :
    (((sheafDiagramComplexPowerUnit T I J c n).app K).f i).app j =
      (Langlands.Sheaf.AdicSystem.quotientMap T I n).app ((K.X i).obj j) := by
  change 𝟙 _ ≫ _ = _
  rw [Category.id_comp]
  rfl

/-- Degree evaluation identifies the complex limit with the ordinary diagram limit. -/
def sheafDiagramComplexPowerLimitDegreeIso
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) (i : ι) :
    ((sheafDiagramComplexPowerLimit T I J c).obj K).X i ≅
      limit ((sheafDiagramReductionFunctor T I J).obj (K.X i)) :=
  preservesLimitIso (HomologicalComplex.eval _ c i)
    ((sheafDiagramComplexReductionFunctor T I J c).obj K)

@[reassoc (attr := simp)]
theorem sheafDiagramComplexPowerLimitDegreeIso_hom_π
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) (i : ι) (n : ℕ) :
    (sheafDiagramComplexPowerLimitDegreeIso T I J c K i).hom ≫
        limit.π ((sheafDiagramReductionFunctor T I J).obj (K.X i)) (op n) =
      (limit.π ((sheafDiagramComplexReductionFunctor T I J c).obj K) (op n)).f i :=
  preservesLimitIso_hom_π _ _ _

/-- Evaluation at a degree and diagram coordinate recovers the existing sheaf limit. -/
def sheafDiagramComplexPowerLimitEvaluationIso
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c) (i : ι) (j : J) :
    (((sheafDiagramComplexPowerLimit T I J c).obj K).X i).obj j ≅
      Langlands.Sheaf.AdicSystem.inverseLimit T I ((K.X i).obj j) :=
  ((evaluation J (Sheaf T (ModuleCat.{v} R))).obj j).mapIso
      (sheafDiagramComplexPowerLimitDegreeIso T I J c K i) ≪≫
    limitObjIsoLimitCompEvaluation _ j

@[reassoc (attr := simp)]
theorem sheafDiagramComplexPowerLimitEvaluationIso_hom_projection
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c)
    (i : ι) (j : J) (n : ℕ) :
    (sheafDiagramComplexPowerLimitEvaluationIso T I J c K i j).hom ≫
        Langlands.Sheaf.AdicSystem.projection T I ((K.X i).obj j) n =
      ((limit.π ((sheafDiagramComplexReductionFunctor T I J c).obj K) (op n)).f i).app j := by
  change ((sheafDiagramComplexPowerLimitDegreeIso T I J c K i).hom.app j ≫
      (limitObjIsoLimitCompEvaluation _ j).hom) ≫
        limit.π (((sheafDiagramReductionFunctor T I J).obj (K.X i)) ⋙
          (evaluation J (Sheaf T (ModuleCat.{v} R))).obj j) (op n) = _
  rw [Category.assoc, limitObjIsoLimitCompEvaluation_hom_π]
  exact congrArg (fun a => a.app j)
    (sheafDiagramComplexPowerLimitDegreeIso_hom_π T I J c K i n)

/-- The limit unit still projects to the genuine sheaf quotient in every coordinate. -/
@[reassoc (attr := simp)]
theorem sheafDiagramComplexPowerLimitUnit_evaluation_projection
    (K : HomologicalComplex (J ⥤ Sheaf T (ModuleCat.{v} R)) c)
    (i : ι) (j : J) (n : ℕ) :
    (((sheafDiagramComplexPowerLimitUnit T I J c).app K).f i).app j ≫
        (sheafDiagramComplexPowerLimitEvaluationIso T I J c K i j).hom ≫
          Langlands.Sheaf.AdicSystem.projection T I ((K.X i).obj j) n =
      (Langlands.Sheaf.AdicSystem.quotientMap T I n).app ((K.X i).obj j) := by
  rw [sheafDiagramComplexPowerLimitEvaluationIso_hom_projection]
  exact (congrArg (fun a => (a.f i).app j)
    (sheafDiagramComplexPowerLimitUnit_π T I J c K n)).trans
      (sheafDiagramComplexPowerUnit_f T I J c n K i j)

end Langlands.Shimura.Coefficients
