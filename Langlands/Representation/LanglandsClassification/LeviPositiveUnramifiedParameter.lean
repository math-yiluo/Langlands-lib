import Langlands.Representation.LanglandsClassification.OppositeStandardExponentParameters
import Langlands.Representation.Plancherel.RationalRealParameterExtension

/-! # Positive unramified Levi characters realizing actual real parameters

Every real parameter on an actual Levi split component has a positive
unramified realization. Applied to an actual opposite Jacquet exponent,
division by the realization leaves a unitary character of that component.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme RealTorusSpace

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  (l : M ⟶ P) (hl : IsRationalLeviSubgroup l)
  (a : A.toGrp ⟶ M) (ha : IsSplitComponent a)

/-- A real functional on the actual Levi valuation image extending the
positive character of the supplied split-component real parameter. -/
def leviPositiveParameterFunctional (y : Vstar A) :
    Plancherel.rationalImageRealFunctionals M :=
  (Plancherel.exists_positiveImageCharacter_extension
    ha.isCentralSplitTorus.1.1 a hl.isConnectedReductive ha y).choose

/-- The chosen functional gives precisely the positive split-torus character
after pullback along the actual component inclusion. -/
theorem leviPositiveParameterFunctional_restrict (y : Vstar A) :
    (Plancherel.rationalImageCharacterPullback M
      (Plancherel.rationalImagePositiveCharacter M
        (leviPositiveParameterFunctional l hl a ha y))).comp (rationalPoints.map a) =
      Plancherel.SplitTorus.positiveCharacter ha.isCentralSplitTorus.1.1 y :=
  (Plancherel.exists_positiveImageCharacter_extension
    ha.isCentralSplitTorus.1.1 a hl.isConnectedReductive ha y).choose_spec

/-- A positive continuous unramified character of the original actual Levi,
realizing the supplied parameter on its split component. -/
def leviPositiveUnramifiedCharacter (y : Vstar A) : leviUnramifiedCharacters l hl := by
  have := hl.isConnectedReductive.isAffineHom
  let : IsAffine M.X.left := isAffine_of_isAffineHom M.X.hom
  have := hl.isConnectedReductive.smooth
  exact Plancherel.rationalCanonicalImageUnramifiedEquiv M
    (Plancherel.rationalImagePositiveCharacter M
      (leviPositiveParameterFunctional l hl a ha y))

/-- Evaluation of the chosen Levi character is the actual-image positive
character evaluated on the valuation of the original Levi point. -/
theorem leviPositiveUnramifiedCharacter_apply (y : Vstar A) (m : rationalPoints M) :
    (leviPositiveUnramifiedCharacter l hl a ha y).val m =
      Plancherel.rationalImagePositiveCharacter M
        (leviPositiveParameterFunctional l hl a ha y)
        (Plancherel.rationalValuationImageProjection M m) := rfl

/-- Restriction to the actual component is the positive character of the
original parameter, as an equality of point homomorphisms. -/
theorem leviPositiveUnramifiedCharacter_restrict (y : Vstar A) :
    letI := leviPointTopology l hl
    (leviPositiveUnramifiedCharacter l hl a ha y).val.toMonoidHom.comp
        (rationalPoints.map a) =
      Plancherel.SplitTorus.positiveCharacter ha.isCentralSplitTorus.1.1 y := by
  let := leviPointTopology l hl
  exact leviPositiveParameterFunctional_restrict l hl a ha y

/-- The positive character construction is a section of the actual Levi
split-component normalized-real-part map. -/
@[simp] theorem leviUnramifiedRealPart_positiveCharacter (y : Vstar A) :
    leviUnramifiedRealPart l hl a ha (leviPositiveUnramifiedCharacter l hl a ha y) = y := by
  unfold leviUnramifiedRealPart
  rw [leviPositiveUnramifiedCharacter_restrict,
    Plancherel.SplitTorus.normalizedRealPart_positiveCharacter]

/-- Every split-component real parameter is realized by a continuous
unramified character of the actual Levi. -/
theorem leviUnramifiedRealPart_surjective :
    Function.Surjective (leviUnramifiedRealPart l hl a ha) := by
  intro y
  exact ⟨leviPositiveUnramifiedCharacter l hl a ha y,
    leviUnramifiedRealPart_positiveCharacter l hl a ha y⟩

/-- Distinct actual component parameters give distinct chosen characters. -/
theorem leviPositiveUnramifiedCharacter_injective :
    Function.Injective (leviPositiveUnramifiedCharacter l hl a ha) := by
  intro y z h
  simpa only [leviUnramifiedRealPart_positiveCharacter] using
    congrArg (leviUnramifiedRealPart l hl a ha) h

/-- At every original Levi point, the realizing character is positive real. -/
theorem leviPositiveUnramifiedCharacter_re_pos (y : Vstar A) (m : rationalPoints M) :
    0 < ((leviPositiveUnramifiedCharacter l hl a ha y).val m : ℂ).re := by
  rw [leviPositiveUnramifiedCharacter_apply, Plancherel.rationalImagePositiveCharacter_val]
  exact Real.exp_pos _

/-- The realizing character has zero imaginary part at every Levi point. -/
theorem leviPositiveUnramifiedCharacter_im (y : Vstar A) (m : rationalPoints M) :
    ((leviPositiveUnramifiedCharacter l hl a ha y).val m : ℂ).im = 0 := by
  rw [leviPositiveUnramifiedCharacter_apply, Plancherel.rationalImagePositiveCharacter_val]
  rfl

namespace OppositeStandardJacquetFamily

variable [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

local instance positiveExponentAmbientTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

/-- The positive unramified character of the original standard Levi that
realizes the real part of this actual opposite Jacquet exponent. -/
def positiveUnramifiedCharacter (x : exponents i ν hG hi hν π) :
    leviUnramifiedCharacters
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl :=
  leviPositiveUnramifiedCharacter
    (StandardJacquetFamily.datum i ν hG hi hν x.1).l
    (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
    (component i ν hG hi hν x.1).a (component i ν hG hi hν x.1).ha
    (realPart i ν hG hi hν π x)

/-- The positive unramified character realizes the original exponent's
actual split-component real part. -/
@[simp] theorem realPart_positiveUnramifiedCharacter (x : exponents i ν hG hi hν π) :
    leviUnramifiedRealPart
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl
      (component i ν hG hi hν x.1).a (component i ν hG hi hν x.1).ha
      (positiveUnramifiedCharacter i ν hG hi hν π x) = realPart i ν hG hi hν π x :=
  leviUnramifiedRealPart_positiveCharacter _ _ _ _ _

/-- On every component point, the realizing Levi character has the original
actual exponent's modulus. -/
theorem norm_positiveUnramifiedCharacter_eq (x : exponents i ν hG hi hν π)
    (t : rationalPoints (component i ν hG hi hν x.1).A.toGrp) :
    ‖((positiveUnramifiedCharacter i ν hG hi hν π x).val
      (rationalPoints.map (component i ν hG hi hν x.1).a t) : ℂ)‖ =
      ‖(x.2.val t : ℂ)‖ := by
  let C := component i ν hG hi hν x.1
  have := C.ha.isAffine
  let : TopologicalSpace (rationalPoints C.A.toGrp) :=
    RationalPointFamily.splitComponentPointTopology C.ha
  have hχ : IsOpen (x.2.val.ker : Set (rationalPoints C.A.toGrp)) := x.2.property.1
  have he := DFunLike.congr_fun
    (leviPositiveUnramifiedCharacter_restrict
      (StandardJacquetFamily.datum i ν hG hi hν x.1).l
      (StandardJacquetFamily.datum i ν hG hi hν x.1).hl C.a C.ha
      (realPart i ν hG hi hν π x)) t
  change (positiveUnramifiedCharacter i ν hG hi hν π x).val
    (rationalPoints.map C.a t) =
      Plancherel.SplitTorus.positiveCharacter C.ha.isCentralSplitTorus.1.1
        (realPart i ν hG hi hν π x) t at he
  rw [he, Plancherel.SplitTorus.positiveCharacter_norm]
  exact (Plancherel.SplitTorus.norm_eq_rpow_normalizedRealPart
    C.ha.isCentralSplitTorus.1.1 x.2.val hχ t).symm

/-- Dividing the actual exponent by the realizing positive character leaves
a unitary character on every point of its original split component. -/
theorem norm_exponent_div_positiveUnramifiedCharacter (x : exponents i ν hG hi hν π)
    (t : rationalPoints (component i ν hG hi hν x.1).A.toGrp) :
    ‖((x.2.val t /
      (positiveUnramifiedCharacter i ν hG hi hν π x).val
        (rationalPoints.map (component i ν hG hi hν x.1).a t) : ℂˣ) : ℂ)‖ = 1 := by
  rw [Units.val_div_eq_div_val, norm_div,
    norm_positiveUnramifiedCharacter_eq]
  exact div_self (norm_ne_zero_iff.mpr (Units.ne_zero _))

variable [LocallyOfFiniteType G.X.hom] [Mono i.hom.hom.left]
  (D : RelativeRootReflectionData i)

/-- The actual unramified realizing character has precisely the full
parameter constructed from the original opposite exponent. -/
theorem fullRealPart_positiveUnramifiedCharacter (x : exponents i ν hG hi hν π) :
    leviUnramifiedFullRealPart (rootPresentation i ν hG hi hν x.1)
      (positiveUnramifiedCharacter i ν hG hi hν π x) =
        fullRealPart i ν hG hi hν π D x := by
  symm
  exact fullRealPart_eq_leviUnramifiedFullRealPart i ν hG hi hν π D x _
    (realPart_positiveUnramifiedCharacter i ν hG hi hν π x).symm

end OppositeStandardJacquetFamily

end Langlands.Aubert.General.RepresentedParabolic
