import Langlands.Representation.Derivative.MirabolicMinus
import Langlands.Group.GL.MirabolicProjection
import Langlands.Representation.Induction.Definitions

/-!
# Mirabolic plus induction functors

The unnormalized Bernstein–Zelevinsky functors `Ψ⁺ : GL_n → P_(n+1)` and
`Φ⁺ : P_(n+1) → P_(n+2)`. `Ψ⁺` inflates along the actual projection `P_(n+1) → GL_n`.
`Φ⁺` extends `τ` to the actual plus subgroup `Q = P_(n+1) V_(n+2)` by the positive
character `thetaPlus` and applies the actual compact induction by right translation.
No normalization character, Haar modulus, exactness or adjunction is stated here.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis

universe uV uF

/-! ## The positive character on the plus subgroup -/

section Character

variable {F : Type uF} [CommRing F] {n : ℕ}

/-- The successor matrices have zero final column. -/
@[simp] theorem lastColumn_successor (g : mirabolic n F) : lastColumn (successor g) = 0 :=
  lastColumn_levi g.val

/-- Levi-first coordinates: the smaller mirabolic action fixes the final coordinate, so
`(p m)_(n,n+1) = m_(n,n+1)` for `p` a successor matrix and `m` a radical matrix. -/
theorem lastColumn_successor_mul_radical_last (g : mirabolic n F) (u : radical (n + 1) F) :
    lastColumn (successor g * u.val) (Fin.last n) = radicalCoordinates u (Fin.last n) := by
  rw [lastColumn_mul, projection_successor, lastColumn_successor, add_zero, lastColumn_val,
    mulVec_last]

/-- Radical-first coordinates: the radical factor contributes its final coordinate. -/
theorem lastColumn_radical_mul_successor_last (u : radical (n + 1) F) (g : mirabolic n F) :
    lastColumn (u.val * successor g) (Fin.last n) = radicalCoordinates u (Fin.last n) := by
  rw [lastColumn_mul, lastColumn_successor, Matrix.mulVec_zero, zero_add, lastColumn_val]

variable (n) in
/-- The final coordinate `q_(n,n+1)` of the last column on the plus subgroup, written
multiplicatively. -/
def plusLastCoordinate : plusSubgroup n F →* Multiplicative F where
  toFun g := Multiplicative.ofAdd (lastColumn g.val (Fin.last n))
  map_one' := by simp
  map_mul' g h := by
    rw [lastColumn_mul_last]
    rfl

@[simp] theorem plusLastCoordinate_apply (g : plusSubgroup n F) :
    (plusLastCoordinate n g).toAdd = lastColumn g.val (Fin.last n) := rfl

theorem plusLastCoordinate_plusRadical (u : radical (n + 1) F) :
    plusLastCoordinate n (plusRadical u) = lastCoordinate n u := rfl

@[simp] theorem plusLastCoordinate_plusSuccessor (g : mirabolic n F) :
    plusLastCoordinate n (plusSuccessor g) = 1 := by
  change Multiplicative.ofAdd (lastColumn (successor g) (Fin.last n)) = 1
  rw [lastColumn_successor]
  rfl

variable [TopologicalSpace F]

/-- The positive extended character `thetaPlus(q) = ψ(q_(n,n+1))` on the plus subgroup;
no inverse is inserted. -/
def thetaPlus (ψ : UnitaryAdditiveCharacter F) (n : ℕ) : plusSubgroup n F →* ℂˣ :=
  Circle.toUnits.comp (ψ.toAddChar.toMonoidHom.comp (plusLastCoordinate n))

@[simp] theorem thetaPlus_apply (ψ : UnitaryAdditiveCharacter F) (q : plusSubgroup n F) :
    (thetaPlus ψ n q : ℂ) = ψ.complex (lastColumn q.val (Fin.last n)) := rfl

theorem thetaPlus_one (ψ : UnitaryAdditiveCharacter F) :
    thetaPlus ψ n 1 = 1 :=
  map_one _

theorem thetaPlus_mul (ψ : UnitaryAdditiveCharacter F) (q r : plusSubgroup n F) :
    thetaPlus ψ n (q * r) = thetaPlus ψ n q * thetaPlus ψ n r :=
  map_mul _ q r

@[simp] theorem norm_thetaPlus (ψ : UnitaryAdditiveCharacter F) (q : plusSubgroup n F) :
    ‖(thetaPlus ψ n q : ℂ)‖ = 1 := by
  simp

/-- On the radical, `thetaPlus` is the published positive radical character. -/
@[simp] theorem thetaPlus_plusRadical (ψ : UnitaryAdditiveCharacter F) (u : radical (n + 1) F) :
    thetaPlus ψ n (plusRadical u) = theta ψ n u := rfl

theorem thetaPlus_comp_plusRadical (ψ : UnitaryAdditiveCharacter F) :
    (thetaPlus ψ n).comp plusRadical = theta ψ n :=
  MonoidHom.ext (thetaPlus_plusRadical ψ)

/-- `thetaPlus` is trivial on the successor copy of the smaller mirabolic. -/
@[simp] theorem thetaPlus_plusSuccessor (ψ : UnitaryAdditiveCharacter F) (g : mirabolic n F) :
    thetaPlus ψ n (plusSuccessor g) = 1 := by
  rw [thetaPlus, MonoidHom.comp_apply, MonoidHom.comp_apply, plusLastCoordinate_plusSuccessor,
    map_one, map_one]

/-- The source's Levi-first value: `thetaPlus(p m) = Θ(m)`. -/
theorem thetaPlus_plusSuccessor_mul_plusRadical (ψ : UnitaryAdditiveCharacter F)
    (g : mirabolic n F) (u : radical (n + 1) F) :
    thetaPlus ψ n (plusSuccessor g * plusRadical u) = theta ψ n u := by
  apply Units.ext
  rw [thetaPlus_apply, theta_apply]
  exact congrArg ψ.complex (lastColumn_successor_mul_radical_last g u)

/-- The published radical-first value: `thetaPlus(m p) = Θ(m)`. -/
theorem thetaPlus_plusRadical_mul_plusSuccessor (ψ : UnitaryAdditiveCharacter F)
    (u : radical (n + 1) F) (g : mirabolic n F) :
    thetaPlus ψ n (plusRadical u * plusSuccessor g) = theta ψ n u := by
  apply Units.ext
  rw [thetaPlus_apply, theta_apply]
  exact congrArg ψ.complex (lastColumn_radical_mul_successor_last u g)

/-- Both semidirect coordinate orders give the same positive character value. -/
theorem thetaPlus_plusSuccessor_mul_plusRadical_eq (ψ : UnitaryAdditiveCharacter F)
    (g : mirabolic n F) (u : radical (n + 1) F) :
    thetaPlus ψ n (plusSuccessor g * plusRadical u) =
      thetaPlus ψ n (plusRadical u * plusSuccessor g) := by
  rw [thetaPlus_plusSuccessor_mul_plusRadical, thetaPlus_plusRadical_mul_plusSuccessor]

/-- Continuity holds for every coefficient topology; it uses one extracted entry. -/
def thetaPlusContinuous (ψ : UnitaryAdditiveCharacter F) (n : ℕ) :
    ContinuousMonoidHom (plusSubgroup n F) ℂˣ where
  toMonoidHom := thetaPlus ψ n
  continuous_toFun := by
    apply Units.continuous_iff.mpr
    have hc : Continuous (fun q : plusSubgroup n F => ψ (lastColumn q.val (Fin.last n))) :=
      ψ.continuous_toFun.comp ((continuous_apply (Fin.last n)).comp
        (continuous_lastColumn.comp continuous_subtype_val))
    exact ⟨continuous_subtype_val.comp hc, continuous_subtype_val.comp hc.inv⟩

theorem continuous_thetaPlus (ψ : UnitaryAdditiveCharacter F) :
    Continuous (thetaPlus ψ n) :=
  (thetaPlusContinuous ψ n).continuous

/-- The open-kernel criterion applied to the actual matrix character. -/
theorem thetaPlus_isOpen_ker (ψ : UnitaryAdditiveCharacter F)
    [NonarchimedeanGroup (plusSubgroup n F)] :
    IsOpen ((thetaPlus ψ n).ker : Set (plusSubgroup n F)) :=
  Langlands.isOpen_ker_of_continuous_complex_character _ (continuous_thetaPlus ψ)

/-! ## The twisted plus-subgroup representation -/

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The source's `τ'`: `τ'(q) v = thetaPlus(q) • τ(plusProjection q) v` on the same carrier. -/
def plusTwistRepresentation (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
    (τ : Representation ℂ (mirabolic n F) V) : Representation ℂ (plusSubgroup n F) V :=
  Langlands.twist (thetaPlus ψ n) (τ.comp plusProjection)

@[simp] theorem plusTwistRepresentation_apply (ψ : UnitaryAdditiveCharacter F)
    (τ : Representation ℂ (mirabolic n F) V) (q : plusSubgroup n F) (v : V) :
    plusTwistRepresentation ψ n τ q v = (thetaPlus ψ n q : ℂ) • τ (plusProjection q) v := rfl

/-- The source formula `τ'(p m) v = Θ(m) τ(p) v` in Levi-first coordinates. -/
theorem plusTwistRepresentation_plusSuccessor_mul_plusRadical (ψ : UnitaryAdditiveCharacter F)
    (τ : Representation ℂ (mirabolic n F) V) (g : mirabolic n F) (u : radical (n + 1) F)
    (v : V) :
    plusTwistRepresentation ψ n τ (plusSuccessor g * plusRadical u) v =
      (theta ψ n u : ℂ) • τ g v := by
  rw [plusTwistRepresentation_apply, thetaPlus_plusSuccessor_mul_plusRadical, map_mul,
    plusProjection_plusSuccessor, plusProjection_plusRadical, mul_one]

/-- The same formula in the published radical-first coordinates. -/
theorem plusTwistRepresentation_plusRadical_mul_plusSuccessor (ψ : UnitaryAdditiveCharacter F)
    (τ : Representation ℂ (mirabolic n F) V) (u : radical (n + 1) F) (g : mirabolic n F)
    (v : V) :
    plusTwistRepresentation ψ n τ (plusRadical u * plusSuccessor g) v =
      (theta ψ n u : ℂ) • τ g v := by
  rw [plusTwistRepresentation_apply, thetaPlus_plusRadical_mul_plusSuccessor, map_mul,
    plusProjection_plusSuccessor, plusProjection_plusRadical, one_mul]

end Character

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The kernel of `thetaPlus` is open for every supplied p-adic topology. -/
theorem isOpen_ker_thetaPlus (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    IsOpen ((thetaPlus ψ n).ker : Set (plusSubgroup n F.Carrier)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : NonarchimedeanGroup (GeneralLinear (n + 1 + 1) F.Carrier) :=
    valuativeGeneralLinearNonarchimedean F.Carrier (n + 1 + 1)
  exact thetaPlus_isOpen_ker ψ

/-! ## Unnormalized Psi-plus -/

/-- Unnormalized `Ψ⁺`: inflate along the actual projection `P_(n+1) → GL_n`, so that
`Ψ⁺(ρ)(g) = ρ(projection g)` on the same carrier. -/
def psiPlusUnnormalized (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) := by
  letI := T.topology
  exact continuousPullbackFunctor projection continuous_projection

/-- The object carrier is the input carrier. -/
theorem psiPlusUnnormalized_obj_carrier (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ((psiPlusUnnormalized T n).obj A : Type uV) = A := by
  intros
  rfl

/-- The object action is the input action composed with `projection`. -/
theorem psiPlusUnnormalized_obj_representation (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      ((psiPlusUnnormalized T n).obj A).representation = A.representation.comp projection := by
  intros
  rfl

/-- `Ψ⁺(ρ)(g) v = ρ(projection g) v`. -/
theorem psiPlusUnnormalized_action (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (g : mirabolic n F.Carrier)
      (v : A), ((psiPlusUnnormalized T n).obj A).representation g v =
        A.representation (projection g) v := by
  intros
  rfl

/-- The radical `V_(n+1)` acts trivially. -/
theorem psiPlusUnnormalized_radical (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (u : radical n F.Carrier)
      (v : A), ((psiPlusUnnormalized T n).obj A).representation (u : mirabolic n F.Carrier) v =
        v := by
  let := T.topology
  intro A u v
  change A.representation (projection (u : mirabolic n F.Carrier)) v = v
  rw [(projection_eq_one_iff _).mpr u.property, map_one, Module.End.one_apply]

/-- The Levi formula `Ψ⁺(ρ)(levi a) = ρ(a)`. -/
theorem psiPlusUnnormalized_levi (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (a : GeneralLinear n F.Carrier),
      ((psiPlusUnnormalized T n).obj A).representation (levi a) = A.representation a := by
  let := T.topology
  intro A a
  change A.representation (projection (levi a)) = _
  rw [projection_levi]

/-- In radical-first coordinates, `Ψ⁺(ρ)(u(v) levi a) = ρ(a)`. -/
theorem psiPlusUnnormalized_radicalElement_mul_levi (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) (v : Fin n → F.Carrier)
      (a : GeneralLinear n F.Carrier),
      ((psiPlusUnnormalized T n).obj A).representation ((radicalElement v).val * levi a) =
        A.representation a := by
  let := T.topology
  intro A v a
  change A.representation (projection ((radicalElement v).val * levi a)) = _
  rw [projection_radicalElement_mul_levi]

theorem psiPlusUnnormalized_isSmooth (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      IsSmooth ((psiPlusUnnormalized T n).obj A).representation := by
  let := T.topology
  intro A
  exact isSmooth_comp projection continuous_projection A.isSmooth

/-- The induced map has the same underlying linear map. -/
theorem psiPlusUnnormalized_map_apply (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B) (v : A),
      SmoothRep.hom ((psiPlusUnnormalized T n).map f) v = SmoothRep.hom f v := by
  intros
  rfl

theorem psiPlusUnnormalized_map_equivariant (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B)
      (g : mirabolic n F.Carrier) (w : (psiPlusUnnormalized T n).obj A),
      SmoothRep.hom ((psiPlusUnnormalized T n).map f)
          (((psiPlusUnnormalized T n).obj A).representation g w) =
        ((psiPlusUnnormalized T n).obj B).representation g
          (SmoothRep.hom ((psiPlusUnnormalized T n).map f) w) := by
  let := T.topology
  intro A B f g w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((psiPlusUnnormalized T n).map f)) g w

theorem psiPlusUnnormalized_map_id (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier),
      (psiPlusUnnormalized T n).map (𝟙 A) = 𝟙 ((psiPlusUnnormalized T n).obj A) := by
  let := T.topology
  intro A
  exact (psiPlusUnnormalized T n).map_id A

theorem psiPlusUnnormalized_map_comp (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ {A B C : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ B) (g : B ⟶ C),
      (psiPlusUnnormalized T n).map (f ≫ g) =
        (psiPlusUnnormalized T n).map f ≫ (psiPlusUnnormalized T n).map g := by
  let := T.topology
  intro A B C f g
  exact (psiPlusUnnormalized T n).map_comp f g

/-! ## The functor `τ ↦ τ'` -/

/-- `τ ↦ τ'`: inflate along `plusProjection`, then twist by `thetaPlus`. -/
def plusTwistFunctor (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (plusSubgroup n F.Carrier) := by
  letI := T.topology
  exact continuousPullbackFunctor plusProjection continuous_plusProjection ⋙
    SmoothRep.twistFunctor (thetaPlus ψ n) (isOpen_ker_thetaPlus T ψ n)

theorem plusTwistFunctor_obj_representation (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((plusTwistFunctor T ψ n).obj τ).representation =
        plusTwistRepresentation ψ n τ.representation := by
  intros
  rfl

/-- `τ'` is smooth: continuous inflation followed by an open-kernel twist. -/
theorem plusTwistRepresentation_isSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      IsSmooth (plusTwistRepresentation ψ n τ.representation) := by
  let := T.topology
  intro τ
  exact (isSmooth_twist_iff _ _ (isOpen_ker_thetaPlus T ψ n)).mpr
    (isSmooth_comp plusProjection continuous_plusProjection τ.isSmooth)

/-! ## Unnormalized Phi-plus -/

/-- Unnormalized `Φ⁺(τ) = ind(P_(n+2), Q, τ')`: actual compact induction from the plus
subgroup `Q`, with compact support modulo `Q` and right translation. -/
def phiPlusUnnormalized (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (mirabolic (n + 1) F.Carrier) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact plusTwistFunctor T ψ n ⋙ SmoothRep.toRep ⋙
    Induction.compactInductionFunctor (plusSubgroup n F.Carrier)

/-- The object carrier is the actual space of compactly supported covariant functions. -/
theorem phiPlusUnnormalized_obj_carrier (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      ((phiPlusUnnormalized T ψ n).obj τ : Type (max uF uV)) =
        Induction.CompactFunctions (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n τ.representation) := by
  intros
  rfl

/-- The object is the bundled actual compact induction of `τ'`. -/
theorem phiPlusUnnormalized_obj (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (phiPlusUnnormalized T ψ n).obj τ =
        SmoothRep.of
          (Induction.compactInduced (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n τ.representation))
          (Induction.compactInduced_smooth (plusSubgroup n F.Carrier)
            (plusTwistRepresentation ψ n τ.representation)) := by
  intros
  rfl

/-- The object action is the actual compact induction of `τ'`. -/
theorem phiPlusUnnormalized_obj_representation (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiPlusUnnormalized T ψ n).obj τ),
      @Eq (Induction.CompactFunctions (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n τ.representation))
        (((phiPlusUnnormalized T ψ n).obj τ).representation g φ)
        (Induction.compactInduced (plusSubgroup n F.Carrier)
          (plusTwistRepresentation ψ n τ.representation) g φ) := by
  intros
  rfl

/-- Evaluation of a vector of `Φ⁺(τ)` at a point of `P_(n+2)`. -/
abbrev phiPlusEval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (phiPlusUnnormalized T ψ n).obj τ → mirabolic (n + 1) F.Carrier → τ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun τ φ x => Induction.eval (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation)
    (show Induction.CompactFunctions (plusSubgroup n F.Carrier)
      (plusTwistRepresentation ψ n τ.representation) from φ).1 x

/-- Vectors of `Φ⁺(τ)` are determined by their values. -/
theorem phiPlusEval_injective (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      Function.Injective (phiPlusEval T ψ n τ) := by
  let := T.topology
  intro τ φ φ' h
  exact Subtype.ext (Subtype.ext (Subtype.ext h))

/-- Covariance `φ(q x) = thetaPlus(q) • τ(plusProjection q) φ(x)` for `q ∈ Q`. -/
theorem phiPlusEval_covariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlusUnnormalized T ψ n).obj τ) (q : plusSubgroup n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusEval T ψ n τ φ ((q : mirabolic (n + 1) F.Carrier) * x) =
        (thetaPlus ψ n q : ℂ) • τ.representation (plusProjection q) (phiPlusEval T ψ n τ φ x) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ q x
  exact (show Induction.CompactFunctions (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) from φ).1.1.2 q x

/-- The source's covariance `φ(p m x) = Θ(m) τ(p) φ(x)` in Levi-first coordinates. -/
theorem phiPlusEval_successor_mul_radical (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlusUnnormalized T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (u : radical (n + 1) F.Carrier) (x : mirabolic (n + 1) F.Carrier),
      phiPlusEval T ψ n τ φ (successor g * u.val * x) =
        (theta ψ n u : ℂ) • τ.representation g (phiPlusEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g u x
  have h := phiPlusEval_covariant T ψ n τ φ (plusSuccessor g * plusRadical u) x
  rw [thetaPlus_plusSuccessor_mul_plusRadical, map_mul, plusProjection_plusSuccessor,
    plusProjection_plusRadical, mul_one] at h
  exact h

/-- Radical elements act on values through `Θ`. -/
theorem phiPlusEval_radical_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlusUnnormalized T ψ n).obj τ) (u : radical (n + 1) F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusEval T ψ n τ φ (u.val * x) = (theta ψ n u : ℂ) • phiPlusEval T ψ n τ φ x := by
  let := T.topology
  intro τ φ u x
  have h := phiPlusEval_covariant T ψ n τ φ (plusRadical u) x
  rw [thetaPlus_plusRadical, plusProjection_plusRadical, map_one, Module.End.one_apply] at h
  exact h

/-- Successor elements act on values through `τ`. -/
theorem phiPlusEval_successor_mul (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlusUnnormalized T ψ n).obj τ) (g : mirabolic n F.Carrier)
      (x : mirabolic (n + 1) F.Carrier),
      phiPlusEval T ψ n τ φ (successor g * x) = τ.representation g (phiPlusEval T ψ n τ φ x) := by
  let := T.topology
  intro τ φ g x
  have h := phiPlusEval_covariant T ψ n τ φ (plusSuccessor g) x
  rw [thetaPlus_plusSuccessor, plusProjection_plusSuccessor, Units.val_one, one_smul] at h
  exact h

/-- The projected nonzero support in `Q \ P_(n+2)` is compact. -/
theorem phiPlusEval_isCompact_quotientSupport (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlusUnnormalized T ψ n).obj τ),
      IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier) (phiPlusEval T ψ n τ φ)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ
  exact (show Induction.CompactFunctions (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) from φ).2

/-- Each vector has one open subgroup of right stabilizers. -/
theorem phiPlusEval_exists_openSubgroup (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (φ : (phiPlusUnnormalized T ψ n).obj τ),
      ∃ K : OpenSubgroup (mirabolic (n + 1) F.Carrier), ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        phiPlusEval T ψ n τ φ (x * (k : mirabolic (n + 1) F.Carrier)) = phiPlusEval T ψ n τ φ x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ φ
  obtain ⟨K, hK⟩ := (show Induction.CompactFunctions (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) from φ).1.2
  exact ⟨K, fun k x => congrArg (fun f => f.1 x) (hK k)⟩

/-- A vector of `Φ⁺(τ)` from a covariant function with one open subgroup of right
stabilizers and compact projected support. -/
def phiPlusMk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) →
      (f : mirabolic (n + 1) F.Carrier → τ) →
      (∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • τ.representation (plusProjection q) (f x)) →
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier)) →
      (∀ (k : K) (x : mirabolic (n + 1) F.Carrier), f (x * (k : mirabolic (n + 1) F.Carrier)) =
        f x) →
      IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier) f) →
      (phiPlusUnnormalized T ψ n).obj τ := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (n + 1 + 1)
  exact fun τ f hcov K hK hc => Induction.compactFunctionOf (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation) f hcov K hK hc

theorem phiPlusEval_mk (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier))
      (f : mirabolic (n + 1) F.Carrier → τ)
      (hcov : ∀ (q : plusSubgroup n F.Carrier) (x : mirabolic (n + 1) F.Carrier),
        f ((q : mirabolic (n + 1) F.Carrier) * x) =
          (thetaPlus ψ n q : ℂ) • τ.representation (plusProjection q) (f x))
      (K : OpenSubgroup (mirabolic (n + 1) F.Carrier))
      (hK : ∀ (k : K) (x : mirabolic (n + 1) F.Carrier),
        f (x * (k : mirabolic (n + 1) F.Carrier)) = f x)
      (hc : IsCompact (Induction.quotientSupport (plusSubgroup n F.Carrier) f)),
      phiPlusEval T ψ n τ (phiPlusMk T ψ n τ f hcov K hK hc) = f := by
  intros
  rfl

/-- The action is right translation: `(g • φ)(x) = φ(x g)`. -/
theorem phiPlusUnnormalized_action (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ (τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)) (g : mirabolic (n + 1) F.Carrier)
      (φ : (phiPlusUnnormalized T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiPlusEval T ψ n τ (((phiPlusUnnormalized T ψ n).obj τ).representation g φ) x =
        phiPlusEval T ψ n τ φ (x * g) := by
  intros
  rfl

theorem phiPlusUnnormalized_isSmooth (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      IsSmooth ((phiPlusUnnormalized T ψ n).obj τ).representation := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (n + 1 + 1)
  intro τ
  exact Induction.compactInduced_smooth (plusSubgroup n F.Carrier)
    (plusTwistRepresentation ψ n τ.representation)

/-- The induced map is the actual compact-induction map of the same intertwiner. -/
theorem phiPlusUnnormalized_map_hom (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (n + 1 + 1)
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ),
      SmoothRep.hom ((phiPlusUnnormalized T ψ n).map f) =
        Induction.compactInducedMap (plusSubgroup n F.Carrier)
          (SmoothRep.hom ((plusTwistFunctor T ψ n).map f)) := by
  intros
  rfl

/-- On values, the induced map is postcomposition: `(Φ⁺ f) φ (x) = f (φ x)`. -/
theorem phiPlusUnnormalized_map_eval (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ)
      (φ : (phiPlusUnnormalized T ψ n).obj τ) (x : mirabolic (n + 1) F.Carrier),
      phiPlusEval T ψ n σ (SmoothRep.hom ((phiPlusUnnormalized T ψ n).map f) φ) x =
        SmoothRep.hom f (phiPlusEval T ψ n τ φ x) := by
  intros
  rfl

theorem phiPlusUnnormalized_map_equivariant (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ)
      (g : mirabolic (n + 1) F.Carrier) (w : (phiPlusUnnormalized T ψ n).obj τ),
      SmoothRep.hom ((phiPlusUnnormalized T ψ n).map f)
          (((phiPlusUnnormalized T ψ n).obj τ).representation g w) =
        ((phiPlusUnnormalized T ψ n).obj σ).representation g
          (SmoothRep.hom ((phiPlusUnnormalized T ψ n).map f) w) := by
  let := T.topology
  intro τ σ f g w
  exact Representation.IntertwiningMap.isIntertwining _ _
    (SmoothRep.hom ((phiPlusUnnormalized T ψ n).map f)) g w

theorem phiPlusUnnormalized_map_id (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ τ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier),
      (phiPlusUnnormalized T ψ n).map (𝟙 τ) = 𝟙 ((phiPlusUnnormalized T ψ n).obj τ) := by
  let := T.topology
  intro τ
  exact (phiPlusUnnormalized T ψ n).map_id τ

theorem phiPlusUnnormalized_map_comp (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    letI := T.topology
    ∀ {τ σ ρ : SmoothRep.{0, uF, uV} ℂ (mirabolic n F.Carrier)} (f : τ ⟶ σ) (g : σ ⟶ ρ),
      (phiPlusUnnormalized T ψ n).map (f ≫ g) =
        (phiPlusUnnormalized T ψ n).map f ≫ (phiPlusUnnormalized T ψ n).map g := by
  let := T.topology
  intro τ σ ρ f g
  exact (phiPlusUnnormalized T ψ n).map_comp f g

end Langlands.Derivative.Mirabolic
