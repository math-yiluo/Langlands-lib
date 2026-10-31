import Langlands.AlgebraicGeometry.ScalarEigensheafAction
import Langlands.Shimura.PEL.HarrisTaylorLieCondition

/-! # Natural and conjugate central eigensubsheaves of the actual relative Lie sheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  {K : Type} [Field K] [NumberField K] [Algebra L K]
  {S : AlgebraicGeometry.Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of K))
  {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]

/-- The actual imaginary-field action, obtained by differentiating the central rational action. -/
def imaginaryLieAction (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) :
    L →+* End B.Lie :=
  (lieRationalOrderAction s B (centralAction B i)).comp (algebraMap L K)

/-- The natural character for `false`, and its CM conjugate for `true`. -/
def imaginaryLieCharacter (conjugate : Bool) : L →+* Γ(S, ⊤) :=
  let χ := (secHom s ⊤).hom.comp (algebraMap L K)
  if conjugate then χ.comp (IsCMField.complexConj L).toRingHom else χ

omit [NumberField K] in
/-- The character restricts to the actual natural or conjugate structure section. -/
theorem imaginaryLieCharacter_restrict (conjugate : Bool) (U : S.Opens) (r : L) :
    restrictScalar U (imaginaryLieCharacter L s conjugate r) =
      secHom s U (algebraMap L K (if conjugate then IsCMField.complexConj L r else r)) := by
  cases conjugate with
  | false =>
    simpa [imaginaryLieCharacter, restrictScalar] using
      congrArg (fun f : CommRingCat.of K ⟶ Γ(S, U) => f (algebraMap L K r))
        (secHom_map s (show U ≤ ⊤ from le_top))
  | true =>
    simpa [imaginaryLieCharacter, restrictScalar] using
      congrArg (fun f : CommRingCat.of K ⟶ Γ(S, U) =>
        f (algebraMap L K (IsCMField.complexConj L r)))
        (secHom_map s (show U ≤ ⊤ from le_top))

variable (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

omit [NumberField L] [IsCMField L] in
/-- The full actual algebra action commutes with the imaginary-field Lie action. -/
theorem imaginaryLieAction_commutes (r : L) (a : A) :
    imaginaryLieAction L s B i r ≫ lieRationalOrderAction s B i.toRingHom a =
      lieRationalOrderAction s B i.toRingHom a ≫ imaginaryLieAction L s B i r := by
  let α := lieRationalOrderAction s B i.toRingHom
  change α (algebraMap K A (algebraMap L K r)) ≫ α a =
    α a ≫ α (algebraMap K A (algebraMap L K r))
  have h := congrArg α (_root_.Algebra.commutes (algebraMap L K r) a)
  simpa only [map_mul, End.mul_def] using h.symm

/-- The actual Lie eigensubsheaf for the natural (`false`) or conjugate (`true`) character. -/
abbrev lieEigensheaf (conjugate : Bool) : S.Modules :=
  scalarEigensheaf (imaginaryLieAction L s B i) (imaginaryLieCharacter L s conjugate)

/-- The actual inclusion of the central Lie eigensubsheaf. -/
def lieEigensheafι (conjugate : Bool) : lieEigensheaf L s B i conjugate ⟶ B.Lie :=
  scalarEigensheafι (imaginaryLieAction L s B i) (imaginaryLieCharacter L s conjugate)

instance (conjugate : Bool) : Mono (lieEigensheafι L s B i conjugate) :=
  inferInstanceAs (Mono (scalarEigensheafι _ _))

/-- Its sections satisfy the eigencondition for the actual differentiated rational action. -/
theorem mem_lieEigenSections (conjugate : Bool) (U : S.Opens) (x : Γ(B.Lie, U)) :
    x ∈ scalarEigenSections (imaginaryLieAction L s B i)
      (imaginaryLieCharacter L s conjugate) U ↔
    ∀ r : L, (lieMap0 s (i (algebraMap K A (algebraMap L K r)))).app U x =
      secHom s U
        (algebraMap L K (if conjugate then IsCMField.complexConj L r else r)) • x := by
  simp only [mem_scalarEigenSections, imaginaryLieCharacter_restrict]
  rfl

/-- The full rational algebra acts on the constructed actual central Lie eigensubsheaf. -/
def lieEigensheafAction (conjugate : Bool) :
    A →+* End (lieEigensheaf L s B i conjugate) :=
  scalarEigensheafAction (imaginaryLieAction L s B i) (imaginaryLieCharacter L s conjugate)
    (lieRationalOrderAction s B i.toRingHom) (imaginaryLieAction_commutes L s B i)

@[reassoc (attr := simp)]
theorem lieEigensheafAction_ι (conjugate : Bool) (a : A) :
    lieEigensheafAction L s B i conjugate a ≫ lieEigensheafι L s B i conjugate =
      lieEigensheafι L s B i conjugate ≫ lieRationalOrderAction s B i.toRingHom a := rfl

variable {B} {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
  (f : Hom0 B B')
  (hf : ∀ a : A, comp0 B B B' (i a) f = comp0 B B' B' f (i' a))

omit [NumberField L] [IsCMField L] in
include hf in
/-- An actual rational action intertwiner induces an imaginary-field Lie intertwiner. -/
theorem imaginaryLieMap_intertwines (r : L) :
    imaginaryLieAction L s B i r ≫ lieMap0 s f =
      lieMap0 s f ≫ imaginaryLieAction L s B' i' r :=
  lieMap0_intertwines s (centralAction B i) (centralAction B' i') f
    (fun a => hf (algebraMap K A a)) (algebraMap L K r)

/-- Restrict the actual differential of a rational action intertwiner to either eigensubsheaf. -/
def lieEigensheafMap (conjugate : Bool) :
    lieEigensheaf L s B i conjugate ⟶ lieEigensheaf L s B' i' conjugate :=
  scalarEigensheafMap (imaginaryLieAction L s B' i') (lieMap0 s f)
    (imaginaryLieMap_intertwines L s i i' f hf)

@[simp]
theorem lieEigensheafMap_app (conjugate : Bool) (U : S.Opens)
    (x : Γ(lieEigensheaf L s B i conjugate, U)) :
    ((lieEigensheafMap L s i i' f hf conjugate).app U x).val =
      (lieMap0 s f).app U x.val := rfl

@[reassoc (attr := simp)]
theorem lieEigensheafMap_ι (conjugate : Bool) :
    lieEigensheafMap L s i i' f hf conjugate ≫ lieEigensheafι L s B' i' conjugate =
      lieEigensheafι L s B i conjugate ≫ lieMap0 s f := rfl

/-- The induced actual eigensheaf map intertwines the full restricted algebra actions. -/
theorem lieEigensheafMap_intertwines (conjugate : Bool) (a : A) :
    lieEigensheafAction L s B i conjugate a ≫ lieEigensheafMap L s i i' f hf conjugate =
      lieEigensheafMap L s i i' f hf conjugate ≫
        lieEigensheafAction L s B' i' conjugate a :=
  scalarEigensheafMap_intertwines (imaginaryLieAction L s B' i')
    (lieRationalOrderAction s B' i'.toRingHom) (imaginaryLieAction_commutes L s B' i')
    (lieMap0 s f) (imaginaryLieMap_intertwines L s i i' f hf)
    (lieMap0_intertwines s i.toRingHom i'.toRingHom f hf) a

/-- Identity rational maps restrict to the identity on the actual Lie eigensubsheaf. -/
@[simp]
theorem lieEigensheafMap_id (conjugate : Bool) :
    lieEigensheafMap L s i i (id0 B) (fun _ => by simp) conjugate =
      𝟙 (lieEigensheaf L s B i conjugate) := by
  ext U x
  apply Subtype.ext
  exact congrArg (fun g : B.Lie ⟶ B.Lie => g.app U x.val) (lieMap0_id s B)

/-- The restricted maps preserve actual rational composition. -/
theorem lieEigensheafMap_comp {B'' : AbelianScheme S}
    (i'' : A →ₐ[ℚ] End0 B'') (g : Hom0 B' B'')
    (hg : ∀ a : A, comp0 B' B' B'' (i' a) g = comp0 B' B'' B'' g (i'' a))
    (conjugate : Bool) :
    lieEigensheafMap L s i i'' (comp0 B B' B'' f g)
        (fun a => by
          rw [← comp0_assoc, hf a, comp0_assoc, hg a, ← comp0_assoc]) conjugate =
      lieEigensheafMap L s i i' f hf conjugate ≫
        lieEigensheafMap L s i' i'' g hg conjugate := by
  ext U x
  apply Subtype.ext
  exact congrArg (fun h : B.Lie ⟶ B''.Lie => h.app U x.val) (lieMap0_comp s f g)

/-- An actual equivariant rational isomorphism gives actual isomorphisms of both Lie eigensheaves. -/
def lieEigensheafIso (conjugate : Bool)
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    lieEigensheaf L s B i conjugate ≅ lieEigensheaf L s B' i' conjugate :=
  scalarEigensheafIso (imaginaryLieAction L s B i) (imaginaryLieAction L s B' i')
    (imaginaryLieCharacter L s conjugate) (lieIso0 s e)
    (imaginaryLieMap_intertwines L s i i' e.hom he)

@[simp]
theorem lieEigensheafIso_hom (conjugate : Bool)
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    (lieEigensheafIso L s i i' conjugate e he).hom =
      lieEigensheafMap L s i i' e.hom he conjugate := rfl

end Langlands.Shimura.HarrisTaylor
