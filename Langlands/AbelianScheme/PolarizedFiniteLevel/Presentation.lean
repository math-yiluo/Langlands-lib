import Langlands.AbelianScheme.PolarizedFiniteLevel.Data

/-! # Independence of auxiliary dual presentations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules GroupScheme.Tate

variable (P : Prerequisites.{u}) {S : Scheme.{u}} {A : AbelianScheme S}

/-- The existing relative polarization condition, expressed on the actual parameter
map to the chosen dual, before equipping the target with its group structure. -/
def ParameterPolarization (A : AbelianScheme S) (hA : HasDualScheme A)
    (f : A.X ⟶ dualScheme A hA) : Prop :=
  GroupScheme.isogenyProperty f.left ∧
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (s : Spec (CommRingCat.of K) ⟶ S),
      HasFieldAmpleMumfordPresentation P.preservation P.square P.universality K
        ((baseChange s).obj A) (hasDualScheme_baseChange P.universality s A hA)
        (dualBaseChangeMap A hA P.universality s f)

/-- The actual morphism to the dual parameter scheme underlying a polarization. -/
def DualWitness.parameterMap (W : DualWitness A) (lam : A ⟶ W.dual P) :
    A.X ⟶ dualScheme A W.hasDual :=
  (groupHom lam).hom.hom

/-- Reexpressing `IsPolarization` in terms of its underlying actual parameter map
does not add any condition or premise. -/
theorem DualWitness.isPolarization_parameter (W : DualWitness A)
    (lam : A ⟶ W.dual P) :
    W.IsPolarization P lam ↔ ParameterPolarization P A W.hasDual (W.parameterMap P lam) :=
  Iff.rfl

/-- Auxiliary evaluations do not affect the polarization predicate of the same
actual scheme morphism to the constructed dual parameter scheme. -/
theorem DualWitness.isPolarization_iff (WA WB : DualWitness A)
    (lamA : A ⟶ WA.dual P) (lamB : A ⟶ WB.dual P)
    (h : WA.parameterMap P lamA = WB.parameterMap P lamB) :
    WA.IsPolarization P lamA ↔ WB.IsPolarization P lamB := by
  exact (WA.isPolarization_parameter P lamA).trans
    ((Iff.of_eq (congrArg (ParameterPolarization P A WA.hasDual) h)).trans
      (WB.isPolarization_parameter P lamB).symm)

/-- Carry a map to the dual through the canonical auxiliary-presentation comparison. -/
def DualWitness.changeMap (WA WB : DualWitness A) (lam : A ⟶ WA.dual P) :
    A ⟶ WB.dual P :=
  lam ≫ WB.map P WA (𝟙 A)

/-- The parameter-scheme map is unchanged by a change of auxiliary evaluation. -/
theorem DualWitness.parameterMap_changeMap (WA WB : DualWitness A)
    (lam : A ⟶ WA.dual P) :
    WB.parameterMap P (WA.changeMap P WB lam) = WA.parameterMap P lam := by
  change (groupHom lam).hom.hom ≫
    dualSchemeMap homPicardZeroPullback (𝟙 A) WB.hasDual WA.hasDual =
      (groupHom lam).hom.hom
  rw [dualSchemeMap_id homPicardZeroPullback
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence]
  exact Category.comp_id _

variable {g d n : ℕ}

/-- Actual homomorphisms are determined by their underlying parameter maps. -/
theorem DualWitness.parameterMap_injective (W : DualWitness A) :
    Function.Injective (W.parameterMap P) := by
  intro f g h
  apply Additive.toMul.injective
  apply Grp.hom_ext
  exact h

/-- An underlying parameter-map equation gives precisely the required actual
polarization equation, together with the unchanged ordered-section condition. -/
def PolarizedIso.ofParameterMap {a b : Datum P S g d n}
    (e : a.abelian ≅ b.abelian)
    (hpol : a.dualWitness.parameterMap P a.polarization =
      (groupHom e.hom).hom.hom ≫ b.dualWitness.parameterMap P b.polarization ≫
        dualSchemeMap homPicardZeroPullback e.hom a.dualWitness.hasDual b.dualWitness.hasDual)
    (hlevel : ∀ i, levelIsoLinear e (Over.mk (𝟙 S)) n (a.level.sections i) =
      b.level.sections i) : PolarizedIso a b where
  abelianIso := e
  polarization_eq := DualWitness.parameterMap_injective P a.dualWitness hpol
  level_eq := hlevel

/-- Replace only a datum's auxiliary dual witnesses by the canonical comparison. -/
def Datum.withDualWitness (a : Datum P S g d n) (W : DualWitness a.abelian) :
    Datum P S g d n where
  abelian := a.abelian
  dimension := a.dimension
  dualWitness := W
  polarization := a.dualWitness.changeMap P W a.polarization
  polarized := (DualWitness.isPolarization_iff P W a.dualWitness _ _
    (DualWitness.parameterMap_changeMap P a.dualWitness W a.polarization)).mpr a.polarized
  degree := by
    intro y
    change (W.parameterMap P (a.dualWitness.changeMap P W a.polarization)).left.finrank y = _
    rw [DualWitness.parameterMap_changeMap]
    exact a.degree y
  level := a.level

/-- Changing an auxiliary evaluation gives an actual polarized isomorphism. -/
def Datum.withDualWitnessIso (a : Datum P S g d n) (W : DualWitness a.abelian) :
    PolarizedIso a (a.withDualWitness P W) where
  abelianIso := CategoryTheory.Iso.refl _
  polarization_eq := by
    change a.polarization = 𝟙 a.abelian ≫
      (a.polarization ≫ W.map P a.dualWitness (𝟙 a.abelian)) ≫
        a.dualWitness.map P W (𝟙 a.abelian)
    rw [Category.id_comp, Category.assoc,
      ← DualWitness.map_comp P a.dualWitness W a.dualWitness,
      Category.id_comp, DualWitness.map_id, Category.comp_id]
  level_eq := (PolarizedIso.refl a).level_eq

/-- Auxiliary choices introduce no additional quotient classes. -/
theorem Datum.withDualWitness_classOf (a : Datum P S g d n)
    (W : DualWitness a.abelian) :
    (a.withDualWitness P W).classOf = a.classOf :=
  (Datum.classOf_eq (a.withDualWitnessIso P W)).symm

end Langlands.AbelianScheme.PolarizedFiniteLevel
