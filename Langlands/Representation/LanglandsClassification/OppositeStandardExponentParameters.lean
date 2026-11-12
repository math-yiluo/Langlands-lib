import Langlands.GroupScheme.Rational.ParabolicCorootLift
import Langlands.Representation.LanglandsClassification.StandardParabolicRootPresentation
import Langlands.Representation.LanglandsClassification.OppositeStandardActualJacquetFamily
import Langlands.Representation.LanglandsClassification.UnramifiedFullParameter

/-! # Full real parameters of actual opposite standard Jacquet exponents

The original standard root presentation lifts each opposite exponent's real
part to the common full torus space. The lift retains the actual character's
all-point modulus and agrees with the full parameter of an actual unramified
Levi character whenever their split-component real parameters agree.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily

open GroupScheme RealTorusSpace

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- The verified original standard presentation with precisely the split
component already used by the opposite spectrum. -/
def rootPresentation (J : StandardJacquetFamily.Index i ν) :
    ParabolicRootPresentation
      (StandardJacquetFamily.datum i ν hG hi hν J).p
      (StandardJacquetFamily.datum i ν hG hi hν J).l
      (component i ν hG hi hν J).a :=
  ParabolicDatum.standardRootPresentation i ν hG hi hν J.val J.property
    (component i ν hG hi hν J).a (component i ν hG hi hν J).ha
    (component i ν hG hi hν J).g (component i ν hG hi hν J).factor

variable [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]

local instance parameterAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The normalized real part of the original opposite exponent, in its
original actual split-component space. -/
def realPart (x : exponents i ν hG hi hν π) :
    Vstar (component i ν hG hi hν x.1).A :=
  Plancherel.SplitTorus.normalizedRealPart
    (component i ν hG hi hν x.1).ha.isCentralSplitTorus.1.1 x.2.val

variable [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left]
  (D : RelativeRootReflectionData i)

/-- The full torus lift of an actual opposite exponent's normalized real
part, annihilating the selected coroots of its original standard label. -/
def fullRealPart (x : exponents i ν hG hi hν π) : Vstar T :=
  (rootPresentation i ν hG hi hν x.1).selectedCorootLift hG D
    (realPart i ν hG hi hν π x)

/-- Restriction along the original component factor recovers the real part. -/
@[simp] theorem restrict_fullRealPart (x : exponents i ν hG hi hν π) :
    rationalCharacterRestrictReal (component i ν hG hi hν x.1).g
      (fullRealPart i ν hG hi hν π D x) = realPart i ν hG hi hν π x :=
  (rootPresentation i ν hG hi hν x.1).restrict_selectedCorootLift hG D _

/-- The full parameter annihilates every selected actual coroot. -/
theorem pair_fullRealPart_selectedCoroot (x : exponents i ν hG hi hν π)
    (α : relativeRoots i) (hα : α.val ∈ x.1.val) :
    pair T (fullRealPart i ν hG hi hν π D x)
      ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0 :=
  (rootPresentation i ν hG hi hν x.1).pair_selectedCorootLift_selectedCoroot
    hG D _ α hα

/-- The full lift is uniquely characterized by its actual restriction and
the selected-coroot equations. -/
theorem fullRealPart_eq_of_restrict_eq (x : exponents i ν hG hi hν π)
    (y : Vstar T)
    (hres : rationalCharacterRestrictReal (component i ν hG hi hν x.1).g y =
      realPart i ν hG hi hν π x)
    (hzero : ∀ α : relativeRoots i, α.val ∈ x.1.val →
      pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) :
    fullRealPart i ν hG hi hν π D x = y := by
  exact (rootPresentation i ν hG hi hν x.1).eq_of_restrict_eq_of_selectedCoroot_pair_eq_zero
    hG D _ y (pair_fullRealPart_selectedCoroot i ν hG hi hν π D x) hzero
    ((restrict_fullRealPart i ν hG hi hν π D x).trans hres.symm)

/-- Pairing the full lift with the actual component valuation recovers the
modulus of the original exponent at every rational point. -/
theorem norm_eq_rpow_fullRealPart (x : exponents i ν hG hi hν π)
    (t : rationalPoints (component i ν hG hi hν x.1).A.toGrp) :
    ‖(x.2.val t : ℂ)‖ = (LocalField.residueCardinality k : ℝ) ^
      (-pair T (fullRealPart i ν hG hi hν π D x)
        (cocharacterMapReal (Additive.ofMul (component i ν hG hi hν x.1).g)
          (Plancherel.SplitTorus.valuation
            (component i ν hG hi hν x.1).ha.isCentralSplitTorus.1.1 t).toAdd)) := by
  let C := component i ν hG hi hν x.1
  have := C.ha.isAffine
  let : TopologicalSpace (rationalPoints C.A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology C.ha
  have hχ : IsOpen (x.2.val.ker : Set (rationalPoints C.A.toGrp)) := x.2.property.1
  rw [pair_cocharacterMapReal]
  change ‖(x.2.val t : ℂ)‖ = (LocalField.residueCardinality k : ℝ) ^
    (-pair C.A
      (rationalCharacterRestrictReal C.g (fullRealPart i ν hG hi hν π D x))
      (Plancherel.SplitTorus.valuation C.ha.isCentralSplitTorus.1.1 t).toAdd)
  rw [restrict_fullRealPart]
  exact Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart
    C.ha.isCentralSplitTorus.1.1 x.2.val hχ t

/-- The full parameter vanishes exactly when the actual exponent is unitary
on every point of its original split component. -/
theorem fullRealPart_eq_zero_iff (x : exponents i ν hG hi hν π) :
    fullRealPart i ν hG hi hν π D x = 0 ↔ ∀ t, ‖(x.2.val t : ℂ)‖ = 1 := by
  let C := component i ν hG hi hν x.1
  have := C.ha.isAffine
  let : TopologicalSpace (rationalPoints C.A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology C.ha
  have hχ : IsOpen (x.2.val.ker : Set (rationalPoints C.A.toGrp)) := x.2.property.1
  have hzero : fullRealPart i ν hG hi hν π D x = 0 ↔
      realPart i ν hG hi hν π x = 0 := by
    constructor
    · intro h
      have hr := restrict_fullRealPart i ν hG hi hν π D x
      rw [h, map_zero] at hr
      exact hr.symm
    · intro h
      change (rootPresentation i ν hG hi hν x.1).selectedCorootLift hG D
        (realPart i ν hG hi hν π x) = 0
      rw [h, map_zero]
  exact hzero.trans
    (Plancherel.SplitTorus.normalizedRealPart_eq_zero_iff C.ha.isCentralSplitTorus.1.1
      x.2.val hχ)

/-- Matching the split-component real parts identifies the constructed lift
with the actual full torus parameter of the given unramified Levi character. -/
theorem fullRealPart_eq_leviUnramifiedFullRealPart
    (x : exponents i ν hG hi hν π)
    (ψ : leviUnramifiedCharacters
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl)
    (hreal : realPart i ν hG hi hν π x =
      leviUnramifiedRealPart
        (StandardJacquetFamily.datum i ν hG hi hν x.1).l
        (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
        (component i ν hG hi hν x.1).a (component i ν hG hi hν x.1).ha ψ) :
    fullRealPart i ν hG hi hν π D x =
      leviUnramifiedFullRealPart (rootPresentation i ν hG hi hν x.1) ψ := by
  symm
  exact leviUnramifiedFullRealPart_eq_of_restrict_eq
    (rootPresentation i ν hG hi hν x.1) hG D ψ _
    (pair_fullRealPart_selectedCoroot i ν hG hi hν π D x)
    ((restrict_fullRealPart i ν hG hi hν π D x).trans hreal)

end Langlands.Aubert.General.RepresentedParabolic.OppositeStandardJacquetFamily
