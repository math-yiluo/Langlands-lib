import Langlands.AbelianScheme.PolarizedFiniteLevel.FullLevel
import Langlands.AlgebraicGeometry.Picard.PolarizationBaseChangeStatement
import Langlands.AbelianScheme.PolarizedFiniteLevel.Degree

/-! # Actual polarized finite-level data and their isomorphism classes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules GroupScheme.Tate

/-- The named tensor, Picard and polarization premises used by the construction.
There is no assertion of universal existence or geometry of relative duals. -/
structure Prerequisites : Prop where
  preservation : pullbackTensorComparisonIsIsoStatement.{u}
  square : MumfordBundlePicardZeroStatement.{u}
  universality : PicardZeroUniversalBaseChangeStatement.{u}
  stability : PicardZeroPullbackStatement.{u}
  composition : PullbackTensorCompositionStatement.{u}
  unitCoherence : PullbackTensorUnitCoherenceStatement.{u}
  associativity : ExplicitPullbackTensorAssociativityStatement.{u}
  comparison : TensorMonoidalLeftUnitorComparisonStatement.{u}
  symmetry : PullbackTensorSymmetryStatement.{u}
  compatibility : DualAbelianBaseChangeStatement.{u}
  polarizationBaseChange : PolarizationBaseChangeStatement.{u}

variable {S : Scheme.{u}} {A B C : AbelianScheme S}

/-- Witnesses for the constructed dual of this particular abelian scheme. -/
structure DualWitness (A : AbelianScheme S) where
  hasDual : HasDualScheme A
  geometry : DualSchemeGeometry A hasDual
  inverseBundle : LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hasDual))
  evaluation : tensorObj (poincareFamily A hasDual).obj.carrier inverseBundle.obj ≅
    structureSheaf ((relativeSpace A.X.hom).obj (dualScheme A hasDual))

variable (P : Prerequisites.{u})

/-- The existing actual dual, with the supplied witnesses for this datum. -/
def DualWitness.dual (W : DualWitness A) : AbelianScheme S :=
  dualAbelianSchemeFromEvaluation A W.hasDual W.geometry P.preservation W.inverseBundle
    W.evaluation P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry

/-- The existing contravariant dual homomorphism, allowing different presentations. -/
def DualWitness.map (WA : DualWitness A) (WB : DualWitness B) (f : A ⟶ B) :
    WB.dual P ⟶ WA.dual P :=
  dualAbelianSchemeMapFromEvaluation WA.hasDual WA.geometry P.preservation WA.inverseBundle
    WA.evaluation P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    WB.hasDual WB.geometry WB.inverseBundle WB.evaluation f

@[simp] theorem DualWitness.map_id (W : DualWitness A) :
    W.map P W (𝟙 A) = 𝟙 (W.dual P) :=
  dualAbelianSchemeMapFromEvaluation_id W.hasDual W.geometry P.preservation W.inverseBundle
    W.evaluation P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry

theorem DualWitness.map_comp (WA : DualWitness A) (WB : DualWitness B)
    (WC : DualWitness C) (f : A ⟶ B) (g : B ⟶ C) :
    WA.map P WC (f ≫ g) = WB.map P WC g ≫ WA.map P WB f :=
  dualAbelianSchemeMapFromEvaluation_comp WA.hasDual WA.geometry P.preservation WA.inverseBundle
    WA.evaluation P.stability P.composition P.unitCoherence P.associativity P.comparison P.symmetry
    WB.hasDual WB.geometry WB.inverseBundle WB.evaluation
    WC.hasDual WC.geometry WC.inverseBundle WC.evaluation f g

@[simp] theorem DualWitness.map_hom (WA : DualWitness A) (WB : DualWitness B)
    (f : A ⟶ B) :
    hom (WA.map P WB f) = (dualSchemeMap homPicardZeroPullback f WA.hasDual WB.hasDual).left :=
  rfl

/-- An actual isomorphism induces an actual contravariant dual isomorphism. -/
def DualWitness.mapIso (WA : DualWitness A) (WB : DualWitness B) (e : A ≅ B) :
    WB.dual P ≅ WA.dual P where
  hom := WA.map P WB e.hom
  inv := WB.map P WA e.inv
  hom_inv_id := by
    rw [← DualWitness.map_comp P WB WA WB, e.inv_hom_id, DualWitness.map_id]
  inv_hom_id := by
    rw [← DualWitness.map_comp P WA WB WA, e.hom_inv_id, DualWitness.map_id]

/-- In particular, different auxiliary evaluations of the same dual have a canonical
comparison induced by the identity of the original abelian scheme. -/
def DualWitness.presentationIso (WA WB : DualWitness A) : WB.dual P ≅ WA.dual P :=
  WA.mapIso P WB (CategoryTheory.Iso.refl A)

@[simp] theorem DualWitness.presentationMap_hom (WA WB : DualWitness A) :
    hom (WA.map P WB (𝟙 A)) = 𝟙 (dualScheme A WA.hasDual).left := by
  rw [DualWitness.map_hom, dualSchemeMap_id homPicardZeroPullback
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence]
  rfl

/-- The exact existing polarization predicate with the datum's dual witnesses. -/
abbrev DualWitness.IsPolarization (W : DualWitness A) (lam : A ⟶ W.dual P) : Prop :=
  AbelianScheme.IsPolarization P.preservation P.square P.universality A W.hasDual W.geometry
    W.inverseBundle W.evaluation P.stability P.composition P.unitCoherence P.associativity
    P.comparison P.symmetry lam

/-- An actual ordinary polarized full finite-level datum. The construction makes
sense for all indices; its moduli application uses `0 < d` and `3 ≤ n`. -/
structure Datum (S : Scheme.{u}) (g d n : ℕ) where
  abelian : AbelianScheme S
  dimension : abelian.HasRelativeDimension g
  dualWitness : DualWitness abelian
  polarization : abelian ⟶ dualWitness.dual P
  polarized : dualWitness.IsPolarization P polarization
  degree : HasDegreeSquare polarization d
  level : FullLevel abelian g n

variable {P} {g d n : ℕ}

/-- An actual polarized isomorphism carrying every ordered torsion section. -/
structure PolarizedIso (a b : Datum P S g d n) where
  abelianIso : a.abelian ≅ b.abelian
  polarization_eq : a.polarization =
    abelianIso.hom ≫ b.polarization ≫
      a.dualWitness.map P b.dualWitness abelianIso.hom
  level_eq : ∀ i, levelIsoLinear abelianIso (Over.mk (𝟙 S)) n (a.level.sections i) =
    b.level.sections i

variable {a b c : Datum P S g d n}

/-- The identity is an actual polarized isomorphism. -/
def PolarizedIso.refl (a : Datum P S g d n) : PolarizedIso a a where
  abelianIso := CategoryTheory.Iso.refl _
  polarization_eq := by simp
  level_eq i := by
    apply toSection_injective a.abelian.toGrp (Over.mk (𝟙 S)) n
    change (Additive.toMul (a.level.sections i)).val ≫ 𝟙 a.abelian.X =
      (Additive.toMul (a.level.sections i)).val
    exact Category.comp_id _

/-- Actual polarized isomorphisms can be inverted. -/
def PolarizedIso.symm (e : PolarizedIso a b) : PolarizedIso b a where
  abelianIso := e.abelianIso.symm
  polarization_eq := by
    rw [e.polarization_eq]
    change b.polarization = e.abelianIso.inv ≫
      (e.abelianIso.hom ≫ b.polarization ≫
        a.dualWitness.map P b.dualWitness e.abelianIso.hom) ≫
      b.dualWitness.map P a.dualWitness e.abelianIso.inv
    simp only [Category.assoc]
    rw [← DualWitness.map_comp P b.dualWitness a.dualWitness b.dualWitness,
      e.abelianIso.inv_hom_id, DualWitness.map_id, Category.comp_id,
      ← Category.assoc, e.abelianIso.inv_hom_id, Category.id_comp]
  level_eq i := by
    rw [← e.level_eq i]
    exact (levelIsoLinear e.abelianIso (Over.mk (𝟙 S)) n).symm_apply_apply _

/-- Actual polarized isomorphisms compose, with contravariant dual order. -/
def PolarizedIso.trans (e : PolarizedIso a b) (f : PolarizedIso b c) :
    PolarizedIso a c where
  abelianIso := e.abelianIso ≪≫ f.abelianIso
  polarization_eq := by
    rw [e.polarization_eq, f.polarization_eq]
    change e.abelianIso.hom ≫ (f.abelianIso.hom ≫ c.polarization ≫
      b.dualWitness.map P c.dualWitness f.abelianIso.hom) ≫
        a.dualWitness.map P b.dualWitness e.abelianIso.hom =
      (e.abelianIso.hom ≫ f.abelianIso.hom) ≫ c.polarization ≫
        a.dualWitness.map P c.dualWitness (e.abelianIso.hom ≫ f.abelianIso.hom)
    rw [DualWitness.map_comp P a.dualWitness b.dualWitness c.dualWitness]
    simp only [Category.assoc]
  level_eq i := by
    rw [← f.level_eq i, ← e.level_eq i]
    apply toSection_injective c.abelian.toGrp (Over.mk (𝟙 S)) n
    exact (Category.assoc (Additive.toMul (a.level.sections i)).val
      (groupHom e.abelianIso.hom).hom.hom (groupHom f.abelianIso.hom).hom.hom).symm

/-- Equivalence is existence of an actual polarized isomorphism. -/
def Isomorphic (a b : Datum P S g d n) : Prop := Nonempty (PolarizedIso a b)

/-- The actual-isomorphism equivalence relation. -/
def datumSetoid (P : Prerequisites.{u}) (S : Scheme.{u}) (g d n : ℕ) :
    Setoid (Datum P S g d n) where
  r := Isomorphic
  iseqv := ⟨fun a => ⟨PolarizedIso.refl a⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Actual isomorphism classes; no smallness assertion is imposed on this quotient. -/
def Moduli (P : Prerequisites.{u}) (S : Scheme.{u}) (g d n : ℕ) : Type (u + 1) :=
  Quotient (datumSetoid P S g d n)

/-- The class of an actual datum. -/
def Datum.classOf (a : Datum P S g d n) : Moduli P S g d n :=
  Quotient.mk (datumSetoid P S g d n) a

theorem Datum.classOf_eq (e : PolarizedIso a b) : a.classOf = b.classOf :=
  Quotient.sound ⟨e⟩


end Langlands.AbelianScheme.PolarizedFiniteLevel
