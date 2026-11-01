import Langlands.Algebra.NonUnitalTensorAssociativityStatements

/-!
# Canonical additive associativity of original balanced tensors

The two actual nested quotient lifts are mutually inverse and natural in all
three original module variables. This is an internal additive proof motivated
by Renard (9 July 2026), I.2.2.4 and I.2.2.7, PDF21–22.
-/

set_option autoImplicit false

namespace Langlands.Algebra.NonUnitalTensorAssociativity

open MulOpposite
open NonUnitalModuleTensor (Tensor tmul biadditive lift hom_ext)
open NonUnitalBimoduleTensor (rightModule leftModule)

universe uR uS uX uY uZ uX' uY' uZ' uW

section Triple

variable (R : Type uR) (S : Type uS) (X : Type uX) (Y : Type uY) (Z : Type uZ)
  [NonUnitalRing R] [NonUnitalRing S]
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [NonUnitalModule Rᵐᵒᵖ X] [NonUnitalModule R Y]
  [NonUnitalModule Sᵐᵒᵖ Y] [NonUnitalModule S Z]
  (hY : ActionsCommute R S Y)

/-- Additive maps out of the left-associated quotient are determined on triples. -/
theorem left_hom_ext {W : Type uW} [AddCommGroup W]
    {F G : LeftTensor R S X Y Z hY →+ W}
    (h : letI := rightModule X hY
      ∀ (x : X) (y : Y) (z : Z),
        F (tmul S (Tensor R X Y) Z (tmul R X Y x y) z) =
          G (tmul S (Tensor R X Y) Z (tmul R X Y x y) z)) : F = G := by
  let _ := rightModule X hY
  apply hom_ext S
  intro t z
  have hz : F.comp ((biadditive S (Tensor R X Y) Z).flip z) =
      G.comp ((biadditive S (Tensor R X Y) Z).flip z) :=
    hom_ext R fun x y => h x y z
  exact DFunLike.congr_fun hz t

/-- Additive maps out of the right-associated quotient are determined on triples. -/
theorem right_hom_ext {W : Type uW} [AddCommGroup W]
    {F G : RightTensor R S X Y Z hY →+ W}
    (h : letI := leftModule hY Z
      ∀ (x : X) (y : Y) (z : Z),
        F (tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) =
          G (tmul R X (Tensor S Y Z) x (tmul S Y Z y z))) : F = G := by
  let _ := leftModule hY Z
  apply hom_ext R
  intro x t
  have hx : F.comp (biadditive R X (Tensor S Y Z) x) =
      G.comp (biadditive R X (Tensor S Y Z) x) :=
    hom_ext S fun y z => h x y z
  exact DFunLike.congr_fun hx t

/-- The forward map is the actual outer lift of the published forward pairing. -/
def forward : LeftTensor R S X Y Z hY →+ RightTensor R S X Y Z hY :=
  letI := rightModule X hY
  lift S (forwardPairing R S X Y Z hY) (forwardPairing_balanced R S X Y Z hY)

/-- The inverse map is the actual outer lift of the published inverse pairing. -/
def inverse : RightTensor R S X Y Z hY →+ LeftTensor R S X Y Z hY :=
  letI := leftModule hY Z
  lift R (inversePairing R S X Y Z hY) (inversePairing_balanced R S X Y Z hY)

@[simp] theorem forward_tmul (x : X) (y : Y) (z : Z) :
    letI := rightModule X hY
    letI := leftModule hY Z
    forward R S X Y Z hY (tmul S (Tensor R X Y) Z (tmul R X Y x y) z) =
      tmul R X (Tensor S Y Z) x (tmul S Y Z y z) := rfl

@[simp] theorem inverse_tmul (x : X) (y : Y) (z : Z) :
    letI := rightModule X hY
    letI := leftModule hY Z
    inverse R S X Y Z hY (tmul R X (Tensor S Y Z) x (tmul S Y Z y z)) =
      tmul S (Tensor R X Y) Z (tmul R X Y x y) z := rfl

/-- The two nested lifts compose to the identity on the whole left quotient. -/
theorem inverse_comp_forward :
    (inverse R S X Y Z hY).comp (forward R S X Y Z hY) =
      AddMonoidHom.id (LeftTensor R S X Y Z hY) :=
  left_hom_ext R S X Y Z hY fun _ _ _ => rfl

/-- The two nested lifts compose to the identity on the whole right quotient. -/
theorem forward_comp_inverse :
    (forward R S X Y Z hY).comp (inverse R S X Y Z hY) =
      AddMonoidHom.id (RightTensor R S X Y Z hY) :=
  right_hom_ext R S X Y Z hY fun _ _ _ => rfl

/-- The intrinsic additive associator, constructed from the two nested lifts. -/
def associator : LeftTensor R S X Y Z hY ≃+ RightTensor R S X Y Z hY where
  toFun := forward R S X Y Z hY
  invFun := inverse R S X Y Z hY
  left_inv t := DFunLike.congr_fun (inverse_comp_forward R S X Y Z hY) t
  right_inv t := DFunLike.congr_fun (forward_comp_inverse R S X Y Z hY) t
  map_add' := map_add (forward R S X Y Z hY)

/-- The constructed associator satisfies every published canonical clause. -/
theorem associator_canonical : Canonical R S X Y Z hY (associator R S X Y Z hY) := by
  refine ⟨⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  exact ⟨inverse_comp_forward R S X Y Z hY, forward_comp_inverse R S X Y Z hY⟩

/-- Canonical existence is unconditional on the original module triple. -/
theorem existsCanonical : ExistsCanonical R S X Y Z hY :=
  ⟨associator R S X Y Z hY, associator_canonical R S X Y Z hY⟩

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

/-- Both whole-map naturality squares hold for every pair of canonical witnesses. -/
theorem naturality : Naturality R S X Y Z X' Y' Z' hY hY' := by
  intro E E' hE hE' f g k
  let _ := rightModule X hY
  let _ := rightModule X' hY'
  let _ := leftModule hY Z
  let _ := leftModule hY' Z'
  constructor
  · apply left_hom_ext R S X Y Z hY
    intro x y z
    change E' (tmul S (Tensor R X' Y') Z' (tmul R X' Y' (f x) (g y)) (k z)) =
      NonUnitalModuleTensor.map R f (NonUnitalBimoduleTensor.leftMap hY hY' g k)
        (E (tmul S (Tensor R X Y) Z (tmul R X Y x y) z))
    rw [hE'.1.1, hE.1.1]
    rfl
  · apply right_hom_ext R S X Y Z hY
    intro x y z
    change E'.symm (tmul R X' (Tensor S Y' Z') (f x) (tmul S Y' Z' (g y) (k z))) =
      NonUnitalModuleTensor.map S (NonUnitalBimoduleTensor.rightMap hY hY' f g) k
        (E.symm (tmul R X (Tensor S Y Z) x (tmul S Y Z y z)))
    rw [hE'.1.2, hE.1.2]
    rfl

end Naturality

end Langlands.Algebra.NonUnitalTensorAssociativity

namespace Langlands.Algebra

universe uR uS uX uY uZ uX' uY' uZ'

/-- Canonical additive associativity and three-variable naturality for the original tensors. -/
theorem nonUnitalTensorAssociativity :
    NonUnitalTensorAssociativityTheorem.{uR, uS, uX, uY, uZ, uX', uY', uZ'} :=
  ⟨NonUnitalTensorAssociativity.existsCanonical,
    NonUnitalTensorAssociativity.existsCanonical,
    NonUnitalTensorAssociativity.naturality⟩

end Langlands.Algebra
