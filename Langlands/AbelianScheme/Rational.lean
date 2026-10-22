import Langlands.AbelianScheme.Basic
import Langlands.CategoryTheory.Rationalization

/-! # Rational morphisms and endomorphism algebras of abelian schemes -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Langlands.AbelianScheme

/-- The category of actual abelian schemes with rationalized homomorphisms. -/
abbrev RationalCategory (S : Scheme.{u}) := Langlands.Rationalization (AbelianScheme S)

/-- This rational category has the same objects as the original category. -/
def rationalObjectsEquiv (S : Scheme.{u}) : AbelianScheme S ≃ RationalCategory S where
  toFun := Langlands.Rationalization.of
  invFun := Langlands.Rationalization.obj
  left_inv _ := rfl
  right_inv X := by cases X; rfl

variable {S : Scheme.{u}}

/-- Rational Hom, formed from the actual integral Hom group. -/
abbrev Hom0 (A B : AbelianScheme S) := Langlands.Rationalization.Hom A B

/-- Explicit identification with the orientation Hom tensor_Z Q. -/
def hom0TensorComm (A B : AbelianScheme S) : Hom0 A B ≃ₗ[ℤ] (A ⟶ B) ⊗[ℤ] ℚ :=
  Langlands.Rationalization.homTensorComm A B

@[simp] theorem hom0TensorComm_tmul (A B : AbelianScheme S) (q : ℚ) (f : A ⟶ B) :
    hom0TensorComm A B (q ⊗ₜ[ℤ] f) = f ⊗ₜ[ℤ] q := rfl

/-- The canonical additive functor. -/
def rationalization (S : Scheme.{u}) : AbelianScheme S ⥤ RationalCategory S :=
  Langlands.Rationalization.inclusion

instance : (rationalization S).Additive := inferInstanceAs
  (Langlands.Rationalization.inclusion (C := AbelianScheme S)).Additive

/-- The canonical map on homomorphisms. -/
def homToHom0 {A B : AbelianScheme S} : (A ⟶ B) →ₗ[ℤ] Hom0 A B :=
  Langlands.Rationalization.ofHom

@[simp] theorem homToHom0_apply {A B : AbelianScheme S} (f : A ⟶ B) :
    homToHom0 f = (1 : ℚ) ⊗ₜ[ℤ] f := rfl

/-- The identity rational homomorphism. -/
def id0 (A : AbelianScheme S) : Hom0 A A := Langlands.Rationalization.identity A

@[simp] theorem homToHom0_id (A : AbelianScheme S) :
    homToHom0 (𝟙 A) = id0 A := rfl

/-- Composition of rational morphisms. -/
def comp0 (A B C : AbelianScheme S) : Hom0 A B →ₗ[ℚ] Hom0 B C →ₗ[ℚ] Hom0 A C :=
  Langlands.Rationalization.compLinear A B C

@[simp] theorem id0_comp0 {A B : AbelianScheme S} (f : Hom0 A B) :
    comp0 A A B (id0 A) f = f :=
  Langlands.Rationalization.identity_comp f

@[simp] theorem comp0_id0 {A B : AbelianScheme S} (f : Hom0 A B) :
    comp0 A B B f (id0 B) = f :=
  Langlands.Rationalization.comp_identity f

theorem comp0_assoc {A B C D : AbelianScheme S}
    (f : Hom0 A B) (g : Hom0 B C) (h : Hom0 C D) :
    comp0 A C D (comp0 A B C f g) h = comp0 A B D f (comp0 B C D g h) :=
  Langlands.Rationalization.comp_assoc f g h

@[simp] theorem comp0_tmul {A B C : AbelianScheme S} (q r : ℚ)
    (f : A ⟶ B) (g : B ⟶ C) :
    comp0 A B C (q ⊗ₜ[ℤ] f) (r ⊗ₜ[ℤ] g) = (q * r) ⊗ₜ[ℤ] (f ≫ g) :=
  Langlands.Rationalization.compLinear_tmul q r f g

@[simp] theorem comp0_homToHom0 {A B C : AbelianScheme S} (f : A ⟶ B) (g : B ⟶ C) :
    comp0 A B C (homToHom0 f) (homToHom0 g) = homToHom0 (f ≫ g) := by
  change Langlands.Rationalization.comp A B C
    (Langlands.Rationalization.ofHom f) (Langlands.Rationalization.ofHom g) = _
  simp [homToHom0]

/-- The actual endomorphism Q-algebra of an abelian scheme in the rational category. -/
abbrev End0 (A : AbelianScheme S) := Langlands.Rationalization.End A

theorem end0_mul (A : AbelianScheme S) (a b : End0 A) :
    a * b = comp0 A A A b a := rfl

@[simp] theorem end0_algebraMap (A : AbelianScheme S) (q : ℚ) :
    algebraMap ℚ (End0 A) q = q ⊗ₜ[ℤ] 𝟙 A :=
  Langlands.Rationalization.algebraMap_eq A q

/-- The canonical unital ring map to rational endomorphisms. -/
def endToEnd0 (A : AbelianScheme S) : CategoryTheory.End A →+* End0 A :=
  Langlands.Rationalization.ofEnd A

@[simp] theorem endToEnd0_apply (A : AbelianScheme S) (f : CategoryTheory.End A) :
    endToEnd0 A f = homToHom0 f := rfl

/-- End0(B) acts Q-linearly on Hom0(A,B) by postcomposition. -/
def end0PostAction (A B : AbelianScheme S) : End0 B →ₐ[ℚ] Module.End ℚ (Hom0 A B) :=
  Langlands.Rationalization.postAction A B

/-- End0(A) acts contravariantly by precomposition. -/
def end0PreAction (A B : AbelianScheme S) (a : End0 A) : Module.End ℚ (Hom0 A B) :=
  Langlands.Rationalization.preAction A B a

@[simp] theorem end0PreAction_one (A B : AbelianScheme S) : end0PreAction A B 1 = 1 :=
  Langlands.Rationalization.preAction_one A B

theorem end0PreAction_mul (A B : AbelianScheme S) (a a' : End0 A) (f : Hom0 A B) :
    end0PreAction A B (a * a') f = end0PreAction A B a' (end0PreAction A B a f) :=
  Langlands.Rationalization.preAction_mul A B a a' f

@[simp] theorem end0PostAction_endToEnd0 {A B : AbelianScheme S}
    (b : CategoryTheory.End B) (f : A ⟶ B) :
    end0PostAction A B (endToEnd0 B b) (homToHom0 f) = homToHom0 (f ≫ b) :=
  Langlands.Rationalization.postAction_ofEnd b f

@[simp] theorem end0PreAction_endToEnd0 {A B : AbelianScheme S}
    (a : CategoryTheory.End A) (f : A ⟶ B) :
    end0PreAction A B (endToEnd0 A a) (homToHom0 f) = homToHom0 (a ≫ f) :=
  Langlands.Rationalization.preAction_ofEnd a f

theorem end0_actions_commute (A B : AbelianScheme S) (a : End0 A) (b : End0 B)
    (f : Hom0 A B) :
    end0PostAction A B b (end0PreAction A B a f) =
      end0PreAction A B a (end0PostAction A B b f) :=
  Langlands.Rationalization.actions_commute A B a b f

end Langlands.AbelianScheme
