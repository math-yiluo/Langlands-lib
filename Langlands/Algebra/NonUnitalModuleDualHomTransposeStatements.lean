import Langlands.Algebra.NonUnitalModuleDualHomTranspose

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra.NonUnitalModuleDualHomTransposeStatements

open NonUnitalModuleDualHomTranspose

universe uA uV uW uV' uW'

section Components

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
  (hW : IsNondegenerate A W)

/-- The two prescribed swaps are inverse as entire complex-linear maps. -/
def InverseIdentities : Prop :=
  letI := rModule hA hV hW
  letI := lModule hA hV hW
  (S hA hV hW).comp (T hA hV hW) = LinearMap.id ∧
    (T hA hV hW).comp (S hA hV hW) = LinearMap.id

/-- The equivalence retains both prescribed maps, additive maps and functions. -/
def PrescribedEquivalence : Prop :=
  letI := rModule hA hV hW
  letI := lModule hA hV hW
  ∃ E : R hA hV hW ≃ₗ[ℂ] L hA hV hW,
    E.toLinearMap = T hA hV hW ∧
      E.symm.toLinearMap = S hA hV hW ∧
      E.toLinearMap.toAddMonoidHom = transposeAdd hA hV hW ∧
      E.symm.toLinearMap.toAddMonoidHom = reverseAdd hA hV hW ∧
      (E : R hA hV hW → L hA hV hW) = transpose hA hV hW ∧
      (E.symm : L hA hV hW → R hA hV hW) =
        NonUnitalModuleDualHomTranspose.reverse hA hV hW

end Components

section Naturality

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
  {V : Type uV} [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
  {W : Type uW} [AddCommGroup W] [NonUnitalModule A W]
  {V' : Type uV'} [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
  {W' : Type uW'} [AddCommGroup W'] [NonUnitalModule A W']
  (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
  (hW : IsNondegenerate A W) (hV' : IsNondegenerate Aᵐᵒᵖ V')
  (hW' : IsNondegenerate A W')

/-- Both equivalence squares use exactly the original pre/postcomposition maps. -/
def Naturality (f : NonUnitalModuleHom Aᵐᵒᵖ V' V)
    (g : NonUnitalModuleHom A W' W) : Prop :=
  letI := rModule hA hV hW
  letI := lModule hA hV hW
  letI := rModule hA hV' hW'
  letI := lModule hA hV' hW'
  ∃ r : R hA hV hW →ₗ[ℂ] R hA hV' hW',
    ∃ l : L hA hV hW →ₗ[ℂ] L hA hV' hW',
      ∃ E : R hA hV hW ≃ₗ[ℂ] L hA hV hW,
        ∃ E' : R hA hV' hW' ≃ₗ[ℂ] L hA hV' hW',
          r.toAddMonoidHom = Rfg hA hV hW hV' hW' f g ∧
          l.toAddMonoidHom = Lfg hA hV hW hV' hW' f g ∧
          E.toLinearMap = T hA hV hW ∧
          E.symm.toLinearMap = S hA hV hW ∧
          E'.toLinearMap = T hA hV' hW' ∧
          E'.symm.toLinearMap = S hA hV' hW' ∧
          E'.toLinearMap.comp r = l.comp E.toLinearMap ∧
          E'.symm.toLinearMap.comp l = r.comp E.symm.toLinearMap

end Naturality

/-- Closed statement family over the original actions and five independent universes. -/
def DualHomTranspose : Prop :=
  ∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
    [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
    (V : Type uV) [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
    (W : Type uW) [AddCommGroup W] [NonUnitalModule A W]
    (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
    (hW : IsNondegenerate A W),
    InverseIdentities hA hV hW ∧
      PrescribedEquivalence hA hV hW ∧
      ∀ (V' : Type uV') [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
        (W' : Type uW') [AddCommGroup W'] [NonUnitalModule A W']
        (hV' : IsNondegenerate Aᵐᵒᵖ V') (hW' : IsNondegenerate A W')
        (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W),
        Naturality hA hV hW hV' hW' f g

/-! Unapplied interface checks state every original structure explicitly. -/

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → Prop := @InverseIdentities.{uA, uV, uW}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → Prop := @PrescribedEquivalence.{uA, uV, uW}

example : {A : Type uA} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type uV} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type uW} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type uV'} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type uW'} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    NonUnitalModuleHom Aᵐᵒᵖ V' V → NonUnitalModuleHom A W' W → Prop :=
  @Naturality.{uA, uV, uW, uV', uW'}

example : {A : Type 0} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 1} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 3} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 4} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    NonUnitalModuleHom Aᵐᵒᵖ V' V → NonUnitalModuleHom A W' W → Prop :=
  @Naturality.{0, 1, 2, 3, 4}

example : {A : Type 4} → [NonUnitalRing A] → [Module ℂ A] →
    [IsScalarTower ℂ A A] → [SMulCommClass ℂ A A] →
    {V : Type 3} → [AddCommGroup V] → [NonUnitalModule Aᵐᵒᵖ V] →
    {W : Type 2} → [AddCommGroup W] → [NonUnitalModule A W] →
    {V' : Type 1} → [AddCommGroup V'] → [NonUnitalModule Aᵐᵒᵖ V'] →
    {W' : Type 0} → [AddCommGroup W'] → [NonUnitalModule A W'] →
    (hA : IsIdempotented A) → (hV : IsNondegenerate Aᵐᵒᵖ V) →
    (hW : IsNondegenerate A W) → (hV' : IsNondegenerate Aᵐᵒᵖ V') →
    (hW' : IsNondegenerate A W') →
    NonUnitalModuleHom Aᵐᵒᵖ V' V → NonUnitalModuleHom A W' W → Prop :=
  @Naturality.{4, 3, 2, 1, 0}

example : Prop := DualHomTranspose.{uA, uV, uW, uV', uW'}

/-! These definitional equalities check the entire closed telescope. -/

example : DualHomTranspose.{uA, uV, uW, uV', uW'} =
    (∀ (A : Type uA) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
      (V : Type uV) [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
      (W : Type uW) [AddCommGroup W] [NonUnitalModule A W]
      (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
      (hW : IsNondegenerate A W),
      InverseIdentities hA hV hW ∧ PrescribedEquivalence hA hV hW ∧
        ∀ (V' : Type uV') [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
          (W' : Type uW') [AddCommGroup W'] [NonUnitalModule A W']
          (hV' : IsNondegenerate Aᵐᵒᵖ V') (hW' : IsNondegenerate A W')
          (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W),
          Naturality hA hV hW hV' hW' f g) := rfl

example : DualHomTranspose.{0, 1, 2, 3, 4} =
    (∀ (A : Type 0) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
      (V : Type 1) [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
      (W : Type 2) [AddCommGroup W] [NonUnitalModule A W]
      (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
      (hW : IsNondegenerate A W),
      InverseIdentities hA hV hW ∧ PrescribedEquivalence hA hV hW ∧
        ∀ (V' : Type 3) [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
          (W' : Type 4) [AddCommGroup W'] [NonUnitalModule A W']
          (hV' : IsNondegenerate Aᵐᵒᵖ V') (hW' : IsNondegenerate A W')
          (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W),
          Naturality hA hV hW hV' hW' f g) := rfl

example : DualHomTranspose.{4, 3, 2, 1, 0} =
    (∀ (A : Type 4) [NonUnitalRing A] [Module ℂ A]
      [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]
      (V : Type 3) [AddCommGroup V] [NonUnitalModule Aᵐᵒᵖ V]
      (W : Type 2) [AddCommGroup W] [NonUnitalModule A W]
      (hA : IsIdempotented A) (hV : IsNondegenerate Aᵐᵒᵖ V)
      (hW : IsNondegenerate A W),
      InverseIdentities hA hV hW ∧ PrescribedEquivalence hA hV hW ∧
        ∀ (V' : Type 1) [AddCommGroup V'] [NonUnitalModule Aᵐᵒᵖ V']
          (W' : Type 0) [AddCommGroup W'] [NonUnitalModule A W']
          (hV' : IsNondegenerate Aᵐᵒᵖ V') (hW' : IsNondegenerate A W')
          (f : NonUnitalModuleHom Aᵐᵒᵖ V' V) (g : NonUnitalModuleHom A W' W),
          Naturality hA hV hW hV' hW' f g) := rfl

end Langlands.Algebra.NonUnitalModuleDualHomTransposeStatements
