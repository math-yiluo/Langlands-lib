import Langlands.Algebra.NonUnitalBimoduleTensor

/-!
# Canonical additive associativity of original balanced tensors

The evaluation pairings and nested quotient lifts are constructed intrinsically.
Existence of a canonical additive equivalence and its naturality are propositions,
motivated by Renard (9 July 2026), I.2.2.4 and I.2.2.7, PDF21–22.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorAssociativity

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul biadditive lift IsBalanced hom_ext)
open NonUnitalBimoduleTensor (rightModule leftModule rightScalar leftScalar)

universe uR uS uX uY uZ uX' uY' uZ'

section Triple

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
  (hY : ActionsCommute R S Y)

/-- The actual left-associated quotient, with the specified residual right action. -/
abbrev LeftTensor : Type (max uX uY uZ) :=
  letI := rightModule X hY
  Tensor S (Tensor R X Y) Z

/-- The actual right-associated quotient, with the specified residual left action. -/
abbrev RightTensor : Type (max uX uY uZ) :=
  letI := leftModule hY Z
  Tensor R X (Tensor S Y Z)

instance leftTensorGroup : AddCommGroup (LeftTensor R S X Y Z hY) :=
  letI := rightModule X hY
  NonUnitalModuleTensor.addCommGroup S (Tensor R X Y) Z

instance rightTensorGroup : AddCommGroup (RightTensor R S X Y Z hY) :=
  letI := leftModule hY Z
  NonUnitalModuleTensor.addCommGroup R X (Tensor S Y Z)

/-- The fixed-`z` pairing `c_z(x)(y) = x ⊗ (y ⊗ z)`. -/
def forwardInner (z : Z) : X →+ Y →+ RightTensor R S X Y Z hY :=
  letI := rightModule X hY
  letI := leftModule hY Z
  {
  toFun x :=
    (biadditive R X (Tensor S Y Z) x).comp
      { toFun := fun y => tmul S Y Z y z
        map_zero' := NonUnitalModuleTensor.zero_tmul S Y Z z
        map_add' y y' := NonUnitalModuleTensor.add_tmul S Y Z y y' z }
  map_zero' := by ext y; exact NonUnitalModuleTensor.zero_tmul R X (Tensor S Y Z) _
  map_add' x x' := by ext y; exact NonUnitalModuleTensor.add_tmul R X (Tensor S Y Z) x x' _ }

theorem forwardInner_balanced (z : Z) :
    IsBalanced R (forwardInner R S X Y Z hY z) := by
  let _ := rightModule X hY
  let _ := leftModule hY Z
  intro r x y
  change tmul R X (Tensor S Y Z) (op r • x) (tmul S Y Z y z) =
    tmul R X (Tensor S Y Z) x (tmul S Y Z (r • y) z)
  exact NonUnitalModuleTensor.tmul_balanced R X (Tensor S Y Z) r x (tmul S Y Z y z)

/-- The inner published quotient lift, for a fixed `z`. -/
def forwardAt (z : Z) : Tensor R X Y →+ RightTensor R S X Y Z hY :=
  lift R (forwardInner R S X Y Z hY z) (forwardInner_balanced R S X Y Z hY z)

/-- The biadditive pairing `B(t)(z) = lift R c_z hc_z t`. -/
def forwardPairing : Tensor R X Y →+ Z →+ RightTensor R S X Y Z hY :=
  letI := rightModule X hY
  letI := leftModule hY Z
  {
  toFun t :=
    { toFun := fun z => forwardAt R S X Y Z hY z t
      map_zero' := by
        have h : forwardAt R S X Y Z hY 0 = 0 := hom_ext R fun x y => by
          change tmul R X (Tensor S Y Z) x (tmul S Y Z y 0) = 0
          rw [NonUnitalModuleTensor.tmul_zero, NonUnitalModuleTensor.tmul_zero]
        exact DFunLike.congr_fun h t
      map_add' z z' := by
        have h : forwardAt R S X Y Z hY (z + z') =
            forwardAt R S X Y Z hY z + forwardAt R S X Y Z hY z' :=
          hom_ext R fun x y => by
            change tmul R X (Tensor S Y Z) x (tmul S Y Z y (z + z')) =
              tmul R X (Tensor S Y Z) x (tmul S Y Z y z) +
                tmul R X (Tensor S Y Z) x (tmul S Y Z y z')
            rw [NonUnitalModuleTensor.tmul_add, NonUnitalModuleTensor.tmul_add]
        exact DFunLike.congr_fun h t }
  map_zero' := by ext z; exact map_zero (forwardAt R S X Y Z hY z)
  map_add' t t' := by ext z; exact map_add (forwardAt R S X Y Z hY z) t t' }

theorem forwardPairing_balanced :
    letI := rightModule X hY
    IsBalanced S (forwardPairing R S X Y Z hY) := by
  let _ := rightModule X hY
  let _ := leftModule hY Z
  intro s t z
  have h : (forwardAt R S X Y Z hY z).comp (rightScalar X hY (op s)) =
      forwardAt R S X Y Z hY (s • z) :=
    hom_ext R fun x y => by
      change tmul R X (Tensor S Y Z) x (tmul S Y Z (op s • y) z) =
        tmul R X (Tensor S Y Z) x (tmul S Y Z y (s • z))
      rw [NonUnitalModuleTensor.tmul_balanced]
  exact DFunLike.congr_fun h t

/-- The fixed-`x` pairing `d_x(y)(z) = (x ⊗ y) ⊗ z`. -/
def inverseInner (x : X) : Y →+ Z →+ LeftTensor R S X Y Z hY :=
  letI := rightModule X hY
  letI := leftModule hY Z
  {
  toFun y := biadditive S (Tensor R X Y) Z (tmul R X Y x y)
  map_zero' := by
    ext z
    change tmul S (Tensor R X Y) Z (tmul R X Y x 0) z = 0
    rw [NonUnitalModuleTensor.tmul_zero, NonUnitalModuleTensor.zero_tmul]
  map_add' y y' := by
    ext z
    change tmul S (Tensor R X Y) Z (tmul R X Y x (y + y')) z =
      tmul S (Tensor R X Y) Z (tmul R X Y x y) z +
        tmul S (Tensor R X Y) Z (tmul R X Y x y') z
    rw [NonUnitalModuleTensor.tmul_add, NonUnitalModuleTensor.add_tmul] }

theorem inverseInner_balanced (x : X) :
    IsBalanced S (inverseInner R S X Y Z hY x) := by
  let _ := rightModule X hY
  let _ := leftModule hY Z
  intro s y z
  change tmul S (Tensor R X Y) Z (tmul R X Y x (op s • y)) z =
    tmul S (Tensor R X Y) Z (tmul R X Y x y) (s • z)
  exact NonUnitalModuleTensor.tmul_balanced S (Tensor R X Y) Z s (tmul R X Y x y) z

/-- The inner published quotient lift, for a fixed `x`. -/
def inverseAt (x : X) : Tensor S Y Z →+ LeftTensor R S X Y Z hY :=
  lift S (inverseInner R S X Y Z hY x) (inverseInner_balanced R S X Y Z hY x)

/-- The biadditive pairing `C(x)(u) = lift S d_x hd_x u`. -/
def inversePairing : X →+ Tensor S Y Z →+ LeftTensor R S X Y Z hY :=
  letI := rightModule X hY
  letI := leftModule hY Z
  {
  toFun := inverseAt R S X Y Z hY
  map_zero' := hom_ext S fun y z => by
    change tmul S (Tensor R X Y) Z (tmul R X Y 0 y) z = 0
    rw [NonUnitalModuleTensor.zero_tmul, NonUnitalModuleTensor.zero_tmul]
  map_add' x x' := hom_ext S fun y z => by
    change tmul S (Tensor R X Y) Z (tmul R X Y (x + x') y) z =
      tmul S (Tensor R X Y) Z (tmul R X Y x y) z +
        tmul S (Tensor R X Y) Z (tmul R X Y x' y) z
    rw [NonUnitalModuleTensor.add_tmul, NonUnitalModuleTensor.add_tmul] }

theorem inversePairing_balanced :
    letI := leftModule hY Z
    IsBalanced R (inversePairing R S X Y Z hY) := by
  let _ := rightModule X hY
  let _ := leftModule hY Z
  intro r x u
  have h : inverseAt R S X Y Z hY (op r • x) =
      (inverseAt R S X Y Z hY x).comp (leftScalar hY Z r) :=
    hom_ext S fun y z => by
      change tmul S (Tensor R X Y) Z (tmul R X Y (op r • x) y) z =
        tmul S (Tensor R X Y) Z (tmul R X Y x (r • y)) z
      rw [NonUnitalModuleTensor.tmul_balanced]
  exact DFunLike.congr_fun h u

/-- The required triple-tensor evaluations, in both directions. -/
def PureTensorFormulas (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) : Prop :=
  letI := rightModule X hY
  letI := leftModule hY Z
  (∀ (x : X) (y : Y) (z : Z),
    E (tmul S (Tensor R X Y) Z (tmul R X Y x y) z) =
      tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) ∧
  (∀ (x : X) (y : Y) (z : Z),
    E.symm (tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) =
      tmul S (Tensor R X Y) Z (tmul R X Y x y) z)

/-- Equality of both complete maps with the actual nested quotient lifts. -/
def NestedLiftFormulas (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) : Prop :=
  letI := rightModule X hY
  letI := leftModule hY Z
  E.toAddMonoidHom =
      lift S (forwardPairing R S X Y Z hY) (forwardPairing_balanced R S X Y Z hY) ∧
  E.symm.toAddMonoidHom =
      lift R (inversePairing R S X Y Z hY) (inversePairing_balanced R S X Y Z hY)

/-- Both inverse identities as equalities of complete additive maps. -/
def InverseIdentities (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) : Prop :=
  E.symm.toAddMonoidHom.comp E.toAddMonoidHom =
      AddMonoidHom.id (LeftTensor R S X Y Z hY) ∧
  E.toAddMonoidHom.comp E.symm.toAddMonoidHom =
      AddMonoidHom.id (RightTensor R S X Y Z hY)

/-- All canonical clauses; this proposition is not an existence premise. -/
def Canonical (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY) : Prop :=
  PureTensorFormulas R S X Y Z hY E ∧
    NestedLiftFormulas R S X Y Z hY E ∧ InverseIdentities R S X Y Z hY E

/-- Existence at a given original triple, without an equivalence certificate premise. -/
def ExistsCanonical : Prop :=
  ∃ E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY,
    Canonical R S X Y Z hY E

end Triple

section Naturality

variable (R : Type uR) (S : Type uS)
  (X : Type uX) (Y : Type uY) (Z : Type uZ)
  (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
  [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
  [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
  (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y')

/-- Naturality in all three variables, for any two canonical witnesses. -/
def Naturality : Prop :=
  ∀ (E : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY)
    (E' : LeftTensor R S X' Y' Z' hY' ≃+ RightTensor R S X' Y' Z' hY'),
    Canonical R S X Y Z hY E → Canonical R S X' Y' Z' hY' E' →
    ∀ (f : NonUnitalModuleHom Rᵐᵒᵖ X X')
      (g : NonUnitalBimoduleHom R S Y Y') (k : NonUnitalModuleHom S Z Z'),
      letI := rightModule X hY
      letI := rightModule X' hY'
      letI := leftModule hY Z
      letI := leftModule hY' Z'
      let ML := NonUnitalModuleTensor.map S (NonUnitalBimoduleTensor.rightMap hY hY' f g) k
      let MR := NonUnitalModuleTensor.map R f (NonUnitalBimoduleTensor.leftMap hY hY' g k)
      E'.toAddMonoidHom.comp ML = MR.comp E.toAddMonoidHom ∧
        E'.symm.toAddMonoidHom.comp MR = ML.comp E.symm.toAddMonoidHom

end Naturality

end Langlands.Algebra.NonUnitalTensorAssociativity

namespace Langlands.Algebra

open MulOpposite NonUnitalTensorAssociativity

universe uR uS uX uY uZ uX' uY' uZ'

/-- Closed intrinsic additive associativity and three-variable naturality target.
All ring and carrier universes are independent; no unit law is assumed. -/
def NonUnitalTensorAssociativityTheorem : Prop :=
  (∀ (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    (hY : ActionsCommute R S Y), ExistsCanonical R S X Y Z hY) ∧
  (∀ (R : Type uR) (S : Type uS) (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY' : ActionsCommute R S Y'), ExistsCanonical R S X' Y' Z' hY') ∧
  (∀ (R : Type uR) (S : Type uS)
    (X : Type uX) (Y : Type uY) (Z : Type uZ)
    (X' : Type uX') (Y' : Type uY') (Z' : Type uZ')
    [NonUnitalRing R] [NonUnitalRing S]
    [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
    [AddCommGroup X'] [AddCommGroup Y'] [AddCommGroup Z']
    [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
    [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
    [NonUnitalModule Rᵐᵒᵖ X'] [NonUnitalModule R Y']
    [NonUnitalModule Sᵐᵒᵖ Y'] [NonUnitalModule S Z']
    (hY : ActionsCommute R S Y) (hY' : ActionsCommute R S Y'),
    Naturality R S X Y Z X' Y' Z' hY hY')

end Langlands.Algebra
