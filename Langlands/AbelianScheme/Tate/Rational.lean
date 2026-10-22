import Langlands.AbelianScheme.Tate.Integral
import Langlands.AbelianScheme.Basic
import Langlands.CategoryTheory.RationalizationLift
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Rational full and prime-to-p Tate modules -/

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace Langlands.GroupScheme.Tate

variable {S : Scheme.{u}} (G : Grp (Over S)) [IsCommMonObj G.X] (T : Over S)

/-- Rationalization of the actual integral inverse limit. The scalar factor is
written first; `rationalTensorComm` gives the source's opposite tensor order. -/
abbrev Rational (P : ℕ → Prop) := ℚ ⊗[ℤ] Integral G T P

/-- Explicit comparison with the convention `T A ⊗_ℤ ℚ`. -/
def rationalTensorComm (P : ℕ → Prop) :
    Rational G T P ≃ₗ[ℤ] Integral G T P ⊗[ℤ] ℚ :=
  TensorProduct.comm ℤ ℚ (Integral G T P)

@[simp] theorem rationalTensorComm_tmul (P : ℕ → Prop) (q : ℚ) (x : Integral G T P) :
    rationalTensorComm G T P (q ⊗ₜ[ℤ] x) = x ⊗ₜ[ℤ] q := rfl

/-- The full rational Tate module. -/
abbrev RationalFull := Rational G T (fun _ => True)

/-- The prime-to-p rational Tate module. -/
abbrev RationalAway (p : ℕ) := Rational G T (fun n => Nat.Coprime n p)

/-- The canonical map from the integral limit to its rationalization. -/
def toRational (P : ℕ → Prop) : Integral G T P →ₗ[ℤ] Rational G T P :=
  TensorProduct.mk ℤ ℚ (Integral G T P) 1

variable {G} {H K : Grp (Over S)} [IsCommMonObj H.X] [IsCommMonObj K.X]

/-- Scalar extension of the actual integral Tate map. -/
def rationalMap (P : ℕ → Prop) (f : G ⟶ H) :
    Rational G T P →ₗ[ℚ] Rational H T P :=
  (map T P f).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalMap_tmul (P : ℕ → Prop) (f : G ⟶ H)
    (q : ℚ) (x : Integral G T P) :
    rationalMap T P f (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] map T P f x := rfl

@[simp] theorem rationalMap_id (P : ℕ → Prop) :
    rationalMap T P (𝟙 G) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp

theorem rationalMap_comp (P : ℕ → Prop) (f : G ⟶ H) (g : H ⟶ K) :
    rationalMap T P (f ≫ g) = (rationalMap T P g).comp (rationalMap T P f) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp [map_comp]

theorem rationalMap_mul (P : ℕ → Prop) (f g : G ⟶ H) :
    rationalMap T P (f * g) = rationalMap T P f + rationalMap T P g := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp [map_mul, TensorProduct.tmul_add]

@[simp] theorem rationalMap_toRational (P : ℕ → Prop) (f : G ⟶ H)
    (x : Integral G T P) :
    rationalMap T P f (toRational G T P x) = toRational H T P (map T P f x) := rfl

variable (G)

/-- Restriction from the full rational Tate module to its prime-to-p counterpart. -/
def rationalRestrictAway (p : ℕ) : RationalFull G T →ₗ[ℚ] RationalAway G T p :=
  (restrictAway G T p).toIntLinearMap.baseChange ℚ

@[simp] theorem rationalRestrictAway_tmul (p : ℕ) (q : ℚ) (x : Full G T) :
    rationalRestrictAway G T p (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] restrictAway G T p x := rfl

/-- Full rational Tate module at a field-valued point. -/
abbrev RationalFullAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  RationalFull G (Over.mk s)

/-- Prime-to-p rational Tate module at a field-valued point. -/
abbrev RationalAwayAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) (p : ℕ) :=
  RationalAway G (Over.mk s) p

end Langlands.GroupScheme.Tate

namespace Langlands.AbelianScheme.Tate

variable {S : Scheme.{u}} (A : AbelianScheme S) (T : Over S) (P : ℕ → Prop)

/-- Rational Tate module of the actual bundled abelian scheme. -/
abbrev Rational := GroupScheme.Tate.Rational A.toGrp T P

abbrev RationalFull := Rational A T (fun _ => True)
abbrev RationalAway (p : ℕ) := Rational A T (fun n => Nat.Coprime n p)

abbrev RationalFullAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) :=
  RationalFull A (Over.mk s)
abbrev RationalAwayAt {Ω : Type u} [Field Ω] (s : Spec (CommRingCat.of Ω) ⟶ S) (p : ℕ) :=
  RationalAway A (Over.mk s) p

variable {A} {B C : AbelianScheme S}

/-- The rational Tate map induced by an actual abelian-scheme homomorphism. -/
def rationalMap (f : A ⟶ B) : Rational A T P →ₗ[ℚ] Rational B T P :=
  GroupScheme.Tate.rationalMap T P (AbelianScheme.groupHom f)

@[simp] theorem rationalMap_id : rationalMap T P (𝟙 A) = LinearMap.id :=
  GroupScheme.Tate.rationalMap_id T P

theorem rationalMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    rationalMap T P (f ≫ g) = (rationalMap T P g).comp (rationalMap T P f) :=
  GroupScheme.Tate.rationalMap_comp T P _ _

theorem rationalMap_add (f g : A ⟶ B) :
    rationalMap T P (f + g) = rationalMap T P f + rationalMap T P g :=
  GroupScheme.Tate.rationalMap_mul T P _ _

/-- The rational Tate construction is an additive functor on actual abelian schemes. -/
def rationalFunctor : AbelianScheme S ⥤ ModuleCat ℚ where
  obj A := ModuleCat.of ℚ (Rational A T P)
  map f := ModuleCat.ofHom (rationalMap T P f)
  map_id A := by apply ModuleCat.hom_ext; exact rationalMap_id T P
  map_comp f g := by apply ModuleCat.hom_ext; exact rationalMap_comp T P f g

instance : (rationalFunctor T P).Additive where
  map_add {_ _ f g} := by apply ModuleCat.hom_ext; exact rationalMap_add T P f g

/-- Canonical extension to the published rationalized category. -/
def rationalizedFunctor : Rationalization (AbelianScheme S) ⥤ ModuleCat ℚ :=
  Rationalization.lift (rationalFunctor T P)

/-- Extension of Tate maps to rational homomorphisms via the published additive lift. -/
def rationalHomMap : Rationalization.Hom A B →ₗ[ℚ]
    (Rational A T P →ₗ[ℚ] Rational B T P) :=
  ModuleCat.homLinearEquiv.toLinearMap.comp
    (Rationalization.liftHom (rationalFunctor T P))

@[simp] theorem rationalHomMap_tmul (q : ℚ) (f : A ⟶ B) :
    rationalHomMap T P (q ⊗ₜ[ℤ] f) = q • rationalMap T P f := rfl

@[simp] theorem rationalHomMap_ofHom (f : A ⟶ B) :
    rationalHomMap T P (Rationalization.ofHom f) = rationalMap T P f := by
  simp

@[simp] theorem rationalHomMap_identity :
    rationalHomMap T P (Rationalization.identity A) = LinearMap.id := by
  simp [Rationalization.identity]

theorem rationalHomMap_comp (f : Rationalization.Hom A B)
    (g : Rationalization.Hom B C) :
    rationalHomMap T P (Rationalization.comp A B C f g) =
      (rationalHomMap T P g).comp (rationalHomMap T P f) :=
  congrArg ModuleCat.Hom.hom (Rationalization.liftHom_comp (rationalFunctor T P) f g)

variable (A)

/-- The actual rational endomorphism algebra acts on the rational Tate module. -/
def rationalEndAction : Rationalization.End A →ₐ[ℚ] Module.End ℚ (Rational A T P) where
  toRingHom := (ModuleCat.endRingEquiv ((rationalFunctor T P).obj A)).toRingHom.comp
    (Rationalization.liftEnd (rationalFunctor T P) A).toRingHom
  commutes' q := by
    change (Rationalization.liftEnd (rationalFunctor T P) A
      (algebraMap ℚ (Rationalization.End A) q)).hom = _
    rw [AlgHom.commutes]
    rfl

@[simp] theorem rationalEndAction_apply (f : Rationalization.End A) :
    rationalEndAction A T P f = rationalHomMap T P f := rfl

@[simp] theorem rationalEndAction_ofEnd (f : CategoryTheory.End A) :
    rationalEndAction A T P (Rationalization.ofEnd A f) = rationalMap T P f := by
  change rationalHomMap T P (Rationalization.ofHom f) = _
  exact rationalHomMap_ofHom T P f

/-- Any rational endomorphism-algebra action induces a rational linear action. -/
def algebraAction {D : Type*} [Ring D] [Algebra ℚ D]
    (i : D →ₐ[ℚ] Rationalization.End A) : D →ₐ[ℚ] Module.End ℚ (Rational A T P) :=
  (rationalEndAction A T P).comp i

variable {A}

/-- An invertible rational homomorphism induces a rational Tate-module equivalence. -/
def rationalIso (e : Rationalization.of A ≅ Rationalization.of B) :
    Rational A T P ≃ₗ[ℚ] Rational B T P :=
  ((rationalizedFunctor T P).mapIso e).toLinearEquiv

@[simp] theorem rationalIso_apply (e : Rationalization.of A ≅ Rationalization.of B)
    (x : Rational A T P) :
    rationalIso T P e x = rationalHomMap T P e.hom x := rfl

@[simp] theorem rationalIso_refl :
    rationalIso T P (Iso.refl (Rationalization.of A)) = LinearEquiv.refl ℚ _ := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_identity T P) x

theorem rationalIso_trans (e : Rationalization.of A ≅ Rationalization.of B)
    (f : Rationalization.of B ≅ Rationalization.of C) :
    rationalIso T P (e.trans f) = (rationalIso T P e).trans (rationalIso T P f) := by
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun (rationalHomMap_comp T P e.hom f.hom) x

end Langlands.AbelianScheme.Tate
