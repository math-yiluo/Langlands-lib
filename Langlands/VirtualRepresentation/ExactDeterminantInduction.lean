import Langlands.VirtualRepresentation.ExactDeterminant
import Langlands.VirtualRepresentation.ExactInduction
import Langlands.VirtualRepresentation.ExactRestriction
import Langlands.LocalFactor.Inductive.Statement

/-! # Determinant transfer on the actual exact quotient -/

noncomputable section

universe uG uH uV

namespace Langlands.VirtualRepresentation.ExactGrothendieckGroup

local instance (K : Type*) [Group K] : AddCommMonoid (Additive (K →* ℂˣ)) :=
  (inferInstance : AddCommGroup (Additive (K →* ℂˣ))).toAddCommMonoid

variable {G : Type uG} [Group G] (S : Subgroup G) [S.FiniteIndex]

/-- The finite-coset transfer respects pointwise multiplication of characters. -/
def characterTransfer : (S →* ℂˣ) →* (G →* ℂˣ) where
  toFun := fun f => f.transfer
  map_one' := by
    classical
    ext g
    simp [MonoidHom.transfer, Subgroup.leftTransversals.diff]
  map_mul' f h := by
    classical
    ext g
    simp [MonoidHom.transfer, Subgroup.leftTransversals.diff, Finset.prod_mul_distrib]

@[simp]
theorem characterTransfer_apply (f : S →* ℂˣ) : characterTransfer S f = f.transfer := rfl

/-- A transfer also commutes with postcomposition by a character homomorphism. -/
theorem characterTransfer_comp {A : Type uH} [CommGroup A]
    (f : S →* A) (h : A →* ℂˣ) (g : G) :
    (h.comp f).transfer g = h (f.transfer g) := by
  rw [MonoidHom.transfer_def _ (default : S.LeftTransversal),
    MonoidHom.transfer_def f (default : S.LeftTransversal)]
  simp only [Subgroup.leftTransversals.diff, MonoidHom.comp_apply, map_prod]

variable (P : FiniteRepresentation.{0, uG, uV} ℂ S → Prop)
variable (Q : FiniteRepresentation.{0, uG, max uG uV} ℂ G → Prop)

/-- Gallagher's formula descends through actual exact relations, with integer degree. -/
theorem determinantCharacter_induce_of_gallagher
    (hgal : LocalFactor.Inductive.GallagherDeterminantStatement.{0, uG, uV})
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A))
    (x : ExactGrothendieckGroup P) :
    determinantCharacter Q (induce S P Q hPQ x) =
      FiniteRepresentation.determinantCharacter
          (FiniteRepresentation.induce S
            (FiniteRepresentation.of (Representation.trivial ℂ S ℂ))) ^ degree P x *
        (determinantCharacter P x).transfer := by
  let t : Additive (S →* ℂˣ) →ₗ[ℤ] Additive (G →* ℂˣ) :=
    (characterTransfer S).toAdditive.toIntLinearMap
  let d : Additive (G →* ℂˣ) := Additive.ofMul
    (FiniteRepresentation.determinantCharacter
      (FiniteRepresentation.induce S
        (FiniteRepresentation.of (Representation.trivial ℂ S ℂ))))
  have he : (determinant Q).comp (induce S P Q hPQ) =
      (degree P).smulRight d + t.comp (determinant P) := by
    apply hom_ext P
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change Additive.ofMul (determinantCharacter Q
        (induce S P Q hPQ (ofRepresentation P A))) = _
      rw [induce_ofRepresentation, determinantCharacter_ofRepresentation]
      change Additive.ofMul (FiniteRepresentation.determinantCharacter
        (FiniteRepresentation.induce S A.val)) =
        Additive.ofMul ((d.toMul ^ degree P (ofRepresentation P A)) *
          (determinantCharacter P (ofRepresentation P A)).transfer)
      rw [degree_ofRepresentation, determinantCharacter_ofRepresentation]
      apply congrArg Additive.ofMul
      ext g
      have hh := congrArg (fun χ : G →* ℂˣ => (χ g : ℂ)) (hgal ℂ G S A.val)
      simpa only [d, toMul_ofMul, MonoidHom.mul_apply, MonoidHom.pow_apply,
        MonoidHom.zpow_apply, Units.val_mul, Units.val_pow_eq_pow_val,
        Units.val_zpow_eq_zpow_val, zpow_natCast] using hh
  exact congrArg Additive.toMul (LinearMap.congr_fun he x)

/-- The permutation determinant disappears on degree-zero exact virtual classes. -/
theorem determinantCharacter_induce_degreeZero_of_gallagher
    (hgal : LocalFactor.Inductive.GallagherDeterminantStatement.{0, uG, uV})
    (hPQ : ∀ A, P A → Q (FiniteRepresentation.induce S A))
    (x : ExactGrothendieckGroup P) (hx : degree P x = 0) :
    determinantCharacter Q (induce S P Q hPQ x) =
      (determinantCharacter P x).transfer := by
  rw [determinantCharacter_induce_of_gallagher S P Q hgal hPQ x, hx]
  ext g
  simp

section Restriction

variable {H : Type uH} [Group H] (φ : H →* G)
variable (P' : FiniteRepresentation.{0, uG, uV} ℂ G → Prop)
variable (Q' : FiniteRepresentation.{0, uH, uV} ℂ H → Prop)

/-- Restriction transports the same virtual determinant along the group map. -/
theorem determinantCharacter_restrict
    (hPQ : ∀ A, P' A → Q' (FiniteRepresentation.restrict φ A))
    (x : ExactGrothendieckGroup P') :
    determinantCharacter Q' (restrict φ P' Q' hPQ x) =
      (determinantCharacter P' x).comp φ := by
  let c : (G →* ℂˣ) →* (H →* ℂˣ) :=
    { toFun := fun f => f.comp φ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let t : Additive (G →* ℂˣ) →ₗ[ℤ] Additive (H →* ℂˣ) :=
    c.toAdditive.toIntLinearMap
  have he : (determinant Q').comp (restrict φ P' Q' hPQ) =
      t.comp (determinant P') := by
    apply hom_ext P'
    intro c
    induction c using Quotient.inductionOn with
    | h A =>
      change Additive.ofMul (determinantCharacter Q'
        (restrict φ P' Q' hPQ (ofRepresentation P' A))) = _
      rw [restrict_ofRepresentation, determinantCharacter_ofRepresentation]
      change Additive.ofMul (FiniteRepresentation.determinantCharacter
        (FiniteRepresentation.restrict φ A.val)) =
          Additive.ofMul ((determinantCharacter P' (ofRepresentation P' A)).comp φ)
      rw [determinantCharacter_ofRepresentation]
      apply congrArg Additive.ofMul
      ext g
      rfl
  exact congrArg Additive.toMul (LinearMap.congr_fun he x)

end Restriction
end Langlands.VirtualRepresentation.ExactGrothendieckGroup
