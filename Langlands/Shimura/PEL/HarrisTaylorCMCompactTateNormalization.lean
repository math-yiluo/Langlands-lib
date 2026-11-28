import Langlands.Shimura.PEL.HarrisCompactOrbitLattice
import Langlands.Shimura.PEL.HarrisTaylorCMTateNormalization
import Langlands.AbelianScheme.Tate.CommensurableInvariantLatticeRealizationProof
import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionProof
import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenProof

/-! # Tate-normalized Harris representatives at arbitrary compact levels -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel

open NumberField _root_.Algebra Langlands.AbelianScheme
open Langlands.AbelianScheme.PolarizedFiniteLevel
open HarrisPolarizedWeilLevel HarrisNumericalWeilLevel
open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.FiniteEtale Langlands.GroupScheme
open GroupScheme.Tate (Index)

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F] [IsCMField F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {L : Type} [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L] [Algebra L F]
  {τ₀ : L →+* ℂ}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n
    (harrisCMSection E (algebraMap L F) τ₀))
  (P : Prerequisites.{0})
  (Z : AdmissibleCMBaseCategory D C P.preservation P.composition P.unitCoherence
    P.associativity P.comparison P.symmetry P.stability P.square P.universality)
  (compatibility : RelativeFiniteWeilTransitionStatement.{0})
  (h : Global.RationalProfiniteIntegerAdeleComparison)
  {Ω : Type} [Field Ω] (s : Spec (.of Ω) ⟶ Z.obj.left)
  (hs : ∀ Y : Cover Z.obj.left, Finite (Fiber s Y))
  (htor : TorsionFiniteEtaleStatement.{0})

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀
local notation "Data" => HarrisLevelData D C P.preservation P.composition P.unitCoherence
  P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h s hs htor Z.property.torsionUnits
local notation "lev" U:max => (hodgeLevelFunctor D C).obj U
local notation "Rat" X:max =>
  Tate.Rational (X).actionObj.abelianScheme (Over.mk s) (fun _ => True)
local notation "toRat" X:max =>
  GroupScheme.Tate.toRational (X).actionObj.abelianScheme.toGrp (Over.mk s) (fun _ => True)
local notation "lattice" U:max x:max =>
  harrisCompactOrbitLattice D C P compatibility h s (x).1 (lev U).toSubgroup (x).2.1
local notation "Condition" X:max => letI := auxiliaryStarRing D C
  D.HarrisTaylorCMDeterminantDimensionCondition C Z.obj.hom
    (X).actionObj.abelianScheme (X).actionObj.action
local notation "jointProof" => determinantDimensionCondition_iff D C P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality Z.obj.hom
local notation "mkClass" => HarrisNumericalWeilLevel.classOf D C hΦ P.preservation
  P.composition P.unitCoherence P.associativity P.comparison P.symmetry P.stability
  P.square P.universality (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h
  s hs htor Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom
local notation "transport" => PolarizedWeilLevel.levelIso P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  compatibility h A (D.harrisHodgePELForm C) s hs htor Z.property.torsionUnits
  Z.property.pairAdditivity
local notation "Mult" => PolarizedWeilLevel.Multiple P.preservation P.composition
  P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square P.universality
  Z.property.pairAdditivity
local notation "model" => cmPolarizedIsogenyModel D C P Z
local notation "modelIso" => cmPolarizedIsogenyModelIso D C P Z
local notation "modelQ" => cmPolarizedIsogenyModelMultiplier D C P Z
local notation "modelMult" => cmPolarizedIsogenyModel_multiple D C P Z

/-- A representative is lattice-normalized when the intersection lattice of
its level orbit is exactly its full integral Tate image. -/
def HarrisCompactTateNormalized {U : HarrisLevel D} (x : Data U) : Prop :=
  letI := auxiliaryStarRing D C
  (lattice U x : Set (Rat x.1)) = Set.range (toRat x.1)

local notation "Normalized" => HarrisCompactTateNormalized D C P Z compatibility h s hs htor

variable [IsAlgClosed Ω] [CharZero Ω]

set_option maxHeartbeats 3200000 in
/-- Each pointed normalized Harris class admits an actual representative
whose full Tate image is the lattice of its compact level orbit. -/
theorem exists_harrisCompactTateNormalized {U : HarrisLevel D} (x : Data U)
    (hx : Condition x.1) :
    ∃ (y : Data U) (hy : Condition y.1), Normalized y ∧
      mkClass y ((jointProof y.1).mp hy).1 ((jointProof y.1).mp hy).2 =
        mkClass x ((jointProof x.1).mp hx).1 ((jointProof x.1).mp hx).2 := by
  let := auxiliaryStarRing D C
  let W : DualWitness x.1.actionObj.abelianScheme :=
    ⟨x.1.hasDual, x.1.geometry, x.1.inversePoincare, x.1.evaluation⟩
  have affineFibre := W.forall_finset_fibre_affine P properFibreAmpleAffineOpen
    x.1.polarization x.1.isPolarization
  obtain ⟨B, e, he⟩ := Tate.commensurableInvariantLatticeRealization htor h Z.obj.left
    Z.property.torsionUnits Ω s hs x.1.actionObj.abelianScheme affineFibre (lattice U x)
    (harrisCompactOrbitLattice_monodromy D C P compatibility h s hs htor
      Z.property.torsionUnits x.1 (lev U) x.2)
    (harrisCompactOrbitLattice_integerBounds D C P compatibility h s hs htor
      Z.property.torsionUnits x.1 (lev U) x.2)
  let Y := model x.1 B e
  let q := modelQ x.1 B e
  let iso := modelIso x.1 B e
  let hm := modelMult x.1 B e
  let y : Data U := ⟨Y, transport x.1 Y (lev U) q iso hm x.2⟩
  have hy : Condition y.1 := (cmPolarizedIsogenyModel_condition_iff D C P Z x.1 B e).mp hx
  refine ⟨y, hy, ?_, ?_⟩
  · let r : Rat y.1 ≃ₗ[ℚ] Rat x.1 := Tate.rationalIso (Over.mk s) (fun _ => True) e
    have move (w : Rat x.1) : r.symm w ∈ lattice U y ↔ w ∈ lattice U x :=
      harrisCompactOrbitLattice_isogeny D C P compatibility h s hs htor Z.property.torsionUnits
        Z.property.pairAdditivity x.1 Y (lev U) q iso hm x.2 w
    apply Set.ext
    intro w
    obtain ⟨z, rfl⟩ := r.symm.surjective w
    change r.symm z ∈ lattice U y ↔ ∃ b, (toRat y.1) b = r.symm z
    rw [move z, he z]
    constructor
    · rintro ⟨b, hb⟩
      exact ⟨b, r.injective (hb.trans (r.apply_symm_apply z).symm)⟩
    · rintro ⟨b, hb⟩
      exact ⟨b, (congrArg r hb).trans (r.apply_symm_apply z)⟩
  · symm
    exact (HarrisNumericalWeilLevel.classOf_eq_iff D C hΦ P.preservation P.composition
      P.unitCoherence P.associativity P.comparison P.symmetry P.stability P.square
      P.universality (D.harrisTaylorReflexStructure C Z.obj.hom) compatibility h s hs htor
      Z.property.torsionUnits Z.property.pairAdditivity L Z.obj.hom x y
      ((jointProof x.1).mp hx).1 ((jointProof y.1).mp hy).1
      ((jointProof x.1).mp hx).2 ((jointProof y.1).mp hy).2).mpr ⟨q, iso, hm, rfl⟩

omit [IsCMField F] [IsScalarTower ℚ F A] in
set_option maxHeartbeats 3200000 in
/-- The normalized Tate images of two representatives at the same point
turn any witness of their class relation into an actual abelian-scheme
isomorphism with both specified rational arrows. -/
theorem harrisCompactTateNormalized_iso_integral {U : HarrisLevel D} (x y : Data U)
    (hx : Normalized x) (hy : Normalized y) (q : ℚˣ) :
    letI := auxiliaryStarRing D C
    ∀ (e : x.1.actionObj ≅ y.1.actionObj) (he : Mult x.1 y.1 q e),
      transport x.1 y.1 (lev U) q e he x.2 = y.2 →
      ∃ g : x.1.actionObj.abelianScheme ≅ y.1.actionObj.abelianScheme,
        Rationalization.ofHom g.hom = RationalAlgebraAction.hom0 e.hom ∧
        Rationalization.ofHom g.inv = RationalAlgebraAction.hom0 e.inv := by
  let := auxiliaryStarRing D C
  intro e he hl
  let B := x.1.actionObj.abelianScheme
  let B' := y.1.actionObj.abelianScheme
  let a := RationalAlgebraAction.underlyingIso e
  let r : Rat x.1 ≃ₗ[ℚ] Rat y.1 := Tate.rationalIso (Over.mk s) (fun _ => True) a
  have mem (w : Rat x.1) : r w ∈ lattice U y ↔ w ∈ lattice U x := by
    have hmem := harrisCompactOrbitLattice_isogeny D C P compatibility h s hs htor
      Z.property.torsionUnits Z.property.pairAdditivity x.1 y.1 (lev U) q e he x.2 w
    rw [hl] at hmem
    exact hmem
  have compat (w : Rat x.1) :
      r w ∈ Set.range (toRat y.1) ↔ w ∈ Set.range (toRat x.1) := by
    change (lattice U x : Set (Rat x.1)) = _ at hx
    change (lattice U y : Set (Rat y.1)) = _ at hy
    have hmem := mem w
    change r w ∈ (lattice U y : Set (Rat y.1)) ↔ w ∈ (lattice U x : Set (Rat x.1)) at hmem
    rwa [hy, hx] at hmem
  exact Tate.connectedIntegralLatticeReflection htor Z.obj.left Z.property.torsionUnits
    Ω s B B' a
    (fun x₀ => by
      obtain ⟨y₀, hEq⟩ := (compat ((toRat x.1) x₀)).mpr ⟨x₀, rfl⟩
      exact ⟨y₀, hEq.symm⟩)
    (fun y₀ => by
      have hmem : r (r.symm ((toRat y.1) y₀)) ∈ Set.range (toRat y.1) :=
        ⟨y₀, (r.apply_symm_apply _).symm⟩
      obtain ⟨x₀, hEq⟩ := (compat (r.symm ((toRat y.1) y₀))).mp hmem
      exact ⟨x₀, hEq.symm⟩)

end Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel
