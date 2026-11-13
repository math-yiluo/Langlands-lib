import Langlands.Geometry.FormalGroup.DelignePiAlgebra
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Polynomial.Module.AEval

/-! # Actual cyclically graded sheaves with a distinguished operator -/

noncomputable section

universe u v w

namespace Langlands.DeligneFormalSpace

open CategoryTheory Polynomial

section LinearAction

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A M]
  {d : ℕ} {a : A} (P : Module.End A M)

/-- An operator satisfying the defining equation induces an action of the actual quotient. -/
def piRepresentation (hP : P ^ d = algebraMap A (Module.End A M) a) :
    PiAlgebra d a →+* Module.End A M :=
  Ideal.Quotient.lift _ (aeval P).toRingHom (by
    have h : Ideal.span {piRelation d a} ≤ RingHom.ker (aeval P).toRingHom := by
      rw [Ideal.span_le]
      rintro _ rfl
      change aeval P (piRelation d a) = 0
      simp only [piRelation, map_sub, map_pow, aeval_X, aeval_C, hP, sub_self]
    exact fun q hq => h hq)

@[simp]
theorem piRepresentation_pi (hP : P ^ d = algebraMap A (Module.End A M) a) :
    piRepresentation P hP (PiAlgebra.pi d a) = P := by
  change aeval P X = P
  exact aeval_X P

@[simp]
theorem piRepresentation_algebraMap (hP : P ^ d = algebraMap A (Module.End A M) a) (r : A) :
    piRepresentation P hP (algebraMap A (PiAlgebra d a) r) =
      algebraMap A (Module.End A M) r := by
  change aeval P (C r) = _
  exact aeval_C P r

@[simp]
theorem piRepresentation_mk (hP : P ^ d = algebraMap A (Module.End A M) a) (q : A[X]) :
    piRepresentation P hP (AdjoinRoot.mk (piRelation d a) q) = aeval P q := rfl

end LinearAction

section SemilinearCompatibility

variable {A B : Type u} [CommRing A] [CommRing B]
  {M N : Type w} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
  {φ : A →+* B} (f : M →ₛₗ[φ] N) (P : Module.End A M) (Q : Module.End B N)
  (hf : ∀ x, f (P x) = Q (f x))

include hf in
/-- Polynomial operator actions commute with a semilinear intertwiner. -/
theorem map_aeval_apply (q : A[X]) (x : M) :
    f (aeval P q x) = aeval Q (q.map φ) (f x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq, Polynomial.map_add]
  | monomial n r =>
    have hn : ∀ x, f ((P ^ n) x) = (Q ^ n) (f x) := by
      intro x
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, hf, ih, pow_succ', Module.End.mul_apply]
    simp only [aeval_monomial, Polynomial.map_monomial, Module.End.mul_apply]
    change f (r • (P ^ n) x) = φ r • (Q ^ n) (f x)
    rw [f.map_smulₛₗ, hn]

end SemilinearCompatibility

section Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (d : ℕ) (R : Sheaf J CommRingCat.{u})
  (a : (R.obj ⋙ CategoryTheory.forget CommRingCat).sections)

/-- The compatible scalar, viewed in the section ring rather than its forgetful type. -/
abbrev scalar (U : Cᵒᵖ) : R.obj.obj U := a.val U

/-- The underlying sheaf of rings used by the module-sheaf category. -/
abbrev ringSheaf : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

instance sectionModule (M : SheafOfModules.{u} (ringSheaf R)) (U : Cᵒᵖ) :
    Module (R.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule

/-- Restriction between the actual quotient coefficient algebras. -/
def piRestriction {U V : Cᵒᵖ} (f : U ⟶ V) :
    PiAlgebra d (scalar R a U) →+* PiAlgebra d (scalar R a V) :=
  AdjoinRoot.map (R.obj.map f).hom _ _ (by
    have h : (piRelation d (scalar R a U)).map (R.obj.map f).hom =
        piRelation d (scalar R a V) := by
      simp only [piRelation, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
      have hs : (R.obj.map f).hom (scalar R a U) = scalar R a V := a.property f
      rw [hs]
    exact h.symm.dvd)

@[simp]
theorem piRestriction_mk {U V : Cᵒᵖ} (f : U ⟶ V) (q : (R.obj.obj U)[X]) :
    piRestriction d R a f (AdjoinRoot.mk (piRelation d (scalar R a U)) q) =
      AdjoinRoot.mk (piRelation d (scalar R a V)) (q.map (R.obj.map f).hom) := by
  change q.eval₂ ((AdjoinRoot.of _).comp (R.obj.map f).hom) (AdjoinRoot.root _) = _
  rw [← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]

/-- The coefficient quotients, with their actual restriction homomorphisms. -/
def coefficientPresheaf : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (PiAlgebra d (scalar R a U))
  map f := CommRingCat.ofHom (piRestriction d R a f)
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    induction b using AdjoinRoot.induction_on with
    | ih q =>
      change piRestriction d R a (𝟙 U) (AdjoinRoot.mk _ q) = AdjoinRoot.mk _ q
      rw [piRestriction_mk]
      simp
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    induction b using AdjoinRoot.induction_on with
    | ih q =>
      change piRestriction d R a (f ≫ g) (AdjoinRoot.mk _ q) =
        piRestriction d R a g (piRestriction d R a f (AdjoinRoot.mk _ q))
      rw [piRestriction_mk, piRestriction_mk, piRestriction_mk, Polynomial.map_map]
      congr 1
      simp only [Functor.map_comp, CommRingCat.hom_comp]

/-- A sheaf of actual modules with an operator whose d-th power is the given scalar. -/
structure PiSheaf where
  module : SheafOfModules.{u} (ringSheaf R)
  pi : module ⟶ module
  pi_pow (U : Cᵒᵖ) : (pi.val.app U).hom ^ d =
    algebraMap (R.obj.obj U) (Module.End (R.obj.obj U) (module.val.obj U)) (scalar R a U)

namespace PiSheaf

variable {d R a} (M : PiSheaf d R a)

/-- Sections carry the actual quotient-algebra action supplied by the operator relation. -/
def representation (U : Cᵒᵖ) :
    PiAlgebra d (scalar R a U) →+* Module.End (R.obj.obj U) (M.module.val.obj U) :=
  piRepresentation (A := R.obj.obj U) (M.pi.val.app U).hom (M.pi_pow U)

/-- The quotient action as an operation on sections. -/
def act (U : Cᵒᵖ) (b : PiAlgebra d (scalar R a U)) (x : M.module.val.obj U) :
    M.module.val.obj U := M.representation U b x

@[simp]
theorem act_pi (U : Cᵒᵖ) (x : M.module.val.obj U) :
    M.act U (PiAlgebra.pi d (scalar R a U)) x = M.pi.val.app U x := by
  exact congrArg (fun P : Module.End (R.obj.obj U) (M.module.val.obj U) => P x)
    (piRepresentation_pi (A := R.obj.obj U) (M.pi.val.app U).hom (M.pi_pow U))

@[simp]
theorem act_algebraMap (U : Cᵒᵖ) (r : R.obj.obj U) (x : M.module.val.obj U) :
    M.act U (algebraMap _ _ r) x = r • x := by
  exact congrArg (fun P : Module.End (R.obj.obj U) (M.module.val.obj U) => P x)
    (piRepresentation_algebraMap (A := R.obj.obj U) (M.pi.val.app U).hom (M.pi_pow U) r)

@[simp]
theorem act_one (U : Cᵒᵖ) (x : M.module.val.obj U) : M.act U 1 x = x := by
  simp [act]

theorem act_mul (U : Cᵒᵖ) (b c : PiAlgebra d (scalar R a U)) (x : M.module.val.obj U) :
    M.act U (b * c) x = M.act U b (M.act U c x) := by
  simp only [act, map_mul, Module.End.mul_apply]

theorem act_add (U : Cᵒᵖ) (b c : PiAlgebra d (scalar R a U)) (x : M.module.val.obj U) :
    M.act U (b + c) x = M.act U b x + M.act U c x := by
  simp only [act, map_add, LinearMap.add_apply]

/-- Nilpotence of the scalar gives nilpotence of the actual section operator. -/
theorem isNilpotent_pi (U : Cᵒᵖ) (ha : IsNilpotent (scalar R a U)) :
    IsNilpotent ((M.pi.val.app U).hom : Module.End (R.obj.obj U) (M.module.val.obj U)) := by
  apply IsNilpotent.of_pow (m := d)
  rw [M.pi_pow U]
  exact ha.map (algebraMap (R.obj.obj U) (Module.End (R.obj.obj U) (M.module.val.obj U)))

/-- Restriction intertwines the full quotient action, including its coefficient map. -/
theorem restrict_act {U V : Cᵒᵖ} (f : U ⟶ V) (b : PiAlgebra d (scalar R a U))
    (x : M.module.val.obj U) :
    M.module.val.map f (M.act U b x) =
      M.act V (piRestriction d R a f b) (M.module.val.map f x) := by
  induction b using AdjoinRoot.induction_on with
  | ih q =>
    rw [piRestriction_mk]
    let P : Module.End (R.obj.obj U) (M.module.val.obj U) := (M.pi.val.app U).hom
    let Q : Module.End (R.obj.obj V) (M.module.val.obj V) := (M.pi.val.app V).hom
    let g : M.module.val.obj U →ₛₗ[(R.obj.map f).hom] M.module.val.obj V :=
      M.module.val.restrictₛₗ f
    change g (aeval P q x) = aeval Q (q.map (R.obj.map f).hom) (g x)
    exact map_aeval_apply g P Q
      (fun x => (PresheafOfModules.naturality_apply M.pi.val f x).symm) q x

/-- Morphisms are actual linear sheaf maps commuting with the distinguished operator. -/
structure Hom (M N : PiSheaf d R a) where
  val : M.module ⟶ N.module
  comm : M.pi ≫ val = val ≫ N.pi

@[ext]
theorem Hom.ext {M N : PiSheaf d R a} {f g : Hom M N} (h : f.val = g.val) : f = g := by
  cases f
  cases g
  cases h
  rfl

instance : Category (PiSheaf d R a) where
  Hom := Hom
  id M := ⟨𝟙 M.module, by simp⟩
  comp f g := ⟨f.val ≫ g.val, by
    rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp _)
  comp_id f := Hom.ext (Category.comp_id _)
  assoc f g h := Hom.ext (Category.assoc _ _ _)

/-- Forget the operator, retaining the genuine sheaf of modules. -/
def forgetToModules : PiSheaf d R a ⥤ SheafOfModules (ringSheaf R) where
  obj M := M.module
  map f := f.val

instance : (forgetToModules (d := d) (R := R) (a := a)).Faithful where
  map_injective h := Hom.ext h

variable {M N : PiSheaf d R a} (f : M ⟶ N)

@[simp]
theorem Hom.map_pi (U : Cᵒᵖ) (x : M.module.val.obj U) :
    f.val.val.app U (M.pi.val.app U x) = N.pi.val.app U (f.val.val.app U x) := by
  have h := congrArg (fun k : M.module ⟶ N.module => k.val.app U) f.comm
  exact congrArg (fun k => k x) h

/-- An operator-compatible map is linear for the actual coefficient quotient action. -/
theorem Hom.map_act (U : Cᵒᵖ) (b : PiAlgebra d (scalar R a U)) (x : M.module.val.obj U) :
    f.val.val.app U (M.act U b x) = N.act U b (f.val.val.app U x) := by
  induction b using AdjoinRoot.induction_on with
  | ih q =>
    let P : Module.End (R.obj.obj U) (M.module.val.obj U) := (M.pi.val.app U).hom
    let Q : Module.End (R.obj.obj U) (N.module.val.obj U) := (N.pi.val.app U).hom
    let g : M.module.val.obj U →ₗ[R.obj.obj U] N.module.val.obj U := (f.val.val.app U).hom
    change g (aeval P q x) = aeval Q q (g x)
    simpa only [Polynomial.map_id] using
      map_aeval_apply (A := R.obj.obj U) (B := R.obj.obj U)
        (φ := RingHom.id _) g P Q (f.map_pi U) q x

end PiSheaf

/-- A grading by actual subsheaves, with an internal sum and a degree-one operator. -/
structure GradedPiSheaf [NeZero d] extends PiSheaf d R a where
  component : ZMod d → module.Submodule
  isInternal (U : Cᵒᵖ) :
    DirectSum.IsInternal (fun i => (component i).toSubmodule.obj U)
  pi_mem (U : Cᵒᵖ) (i : ZMod d) (x : module.val.obj U) :
    x ∈ (component i).toSubmodule.obj U →
      pi.val.app U x ∈ (component (i + 1)).toSubmodule.obj U

namespace GradedPiSheaf

variable {d R a} [NeZero d] (M : GradedPiSheaf d R a)

/-- The homogeneous part is a genuine sheaf of modules. -/
def componentSheaf (i : ZMod d) : SheafOfModules (ringSheaf R) :=
  (M.component i).toSheafOfModules

/-- The actual inclusion of a homogeneous subsheaf. -/
def componentInclusion (i : ZMod d) : M.componentSheaf i ⟶ M.module :=
  (M.component i).ι

/-- Π restricted to the degree-i subsheaf, with target degree i+1. -/
def componentPi (i : ZMod d) : M.componentSheaf i ⟶ M.componentSheaf (i + 1) where
  val := {
    app U := ModuleCat.ofHom
      (((M.pi.val.app U).hom.comp ((M.component i).toSubmodule.obj U).subtype).codRestrict
        _ (fun x => M.pi_mem U i x x.property))
    naturality f := by
      ext x
      apply Subtype.ext
      exact PresheafOfModules.naturality_apply M.pi.val f x.val }

@[simp]
theorem componentPi_apply (i : ZMod d) (U : Cᵒᵖ)
    (x : (M.component i).toSubmodule.obj U) :
    ((M.componentPi i).val.app U x).val = M.pi.val.app U x.val := rfl

@[reassoc (attr := simp)]
theorem componentPi_inclusion (i : ZMod d) :
    M.componentPi i ≫ M.componentInclusion (i + 1) = M.componentInclusion i ≫ M.pi := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  rfl

end GradedPiSheaf

end Sheaf

end Langlands.DeligneFormalSpace
