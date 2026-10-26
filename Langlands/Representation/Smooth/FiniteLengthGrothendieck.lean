import Langlands.Representation.Category.Basic
import Langlands.VirtualRepresentation.Integral
import Langlands.Group.GL.Blocks
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The exact Grothendieck group of finite-length smooth representations

Objects are actual smooth representations with finite length over the group
algebra. The free integral module on their genuine isomorphism classes is
quotiented by relations from actual short exact sequences. The construction
keeps the group and carrier universes independent.
-/

noncomputable section

open CategoryTheory
open Langlands.VirtualRepresentation

universe uR uG uV uA uB uC uM uF

namespace Langlands.SmoothRep

variable {R : Type uR} {G : Type uG} [CommRing R] [Group G] [TopologicalSpace G]

/-- Endpoint and middle exactness for actual equivariant linear maps. The three
carriers may lie in independent universes. -/
def IsShortExact {A : SmoothRep.{uR, uG, uA} R G}
    {B : SmoothRep.{uR, uG, uB} R G} {C : SmoothRep.{uR, uG, uC} R G}
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation) : Prop :=
  Function.Injective f ∧ Function.Surjective g ∧
    LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap

variable (R G)

/-- Actual smooth representations of finite group-algebra length, at a fixed
carrier universe. No finite-dimensionality condition is imposed. -/
abbrev FiniteLengthObject :=
  {A : SmoothRep.{uR, uG, uV} R G // A.HasFiniteLength}

/-- Two finite-length objects are related precisely when their actual smooth
representations are isomorphic. -/
def finiteLengthIsoSetoid : Setoid (FiniteLengthObject.{uR, uG, uV} R G) where
  r A B := Nonempty (A.val ≅ B.val)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Genuine isomorphism classes; the object universe is not resized. -/
def FiniteLengthIsoClass : Type (max uR uG (uV + 1)) :=
  Quotient (finiteLengthIsoSetoid.{uR, uG, uV} R G)

variable {R G}

/-- The class of an actual finite-length smooth object. -/
def finiteLengthIsoClass (A : FiniteLengthObject.{uR, uG, uV} R G) :
    FiniteLengthIsoClass.{uR, uG, uV} R G :=
  Quotient.mk _ A

theorem finiteLengthIsoClass_eq_iff (A B : FiniteLengthObject.{uR, uG, uV} R G) :
    finiteLengthIsoClass A = finiteLengthIsoClass B ↔ Nonempty (A.val ≅ B.val) :=
  Quotient.eq

variable (R G)

/-- The free integral module on actual finite-length smooth isomorphism classes. -/
abbrev FiniteLengthPresentation :=
  IntegralLattice (FiniteLengthIsoClass.{uR, uG, uV} R G)

/-- Relations from all actual short exact sequences in the finite-length smooth
category, including nonsplit sequences. -/
def finiteLengthRelationSet : Set (FiniteLengthPresentation.{uR, uG, uV} R G) :=
  {x | ∃ (A B C : FiniteLengthObject.{uR, uG, uV} R G)
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation),
    IsShortExact f g ∧ x = generator (finiteLengthIsoClass B) -
      generator (finiteLengthIsoClass A) - generator (finiteLengthIsoClass C)}

/-- All integral consequences of the actual short-exact-sequence relations. -/
def finiteLengthRelations : Submodule ℤ (FiniteLengthPresentation.{uR, uG, uV} R G) :=
  Submodule.span ℤ (finiteLengthRelationSet R G)

/-- The exact Grothendieck group of actual finite-length smooth representations.
Finite length is over `R[G]`, not over `R`. -/
abbrev FiniteLengthGrothendieckGroup :=
  FiniteLengthPresentation.{uR, uG, uV} R G ⧸ finiteLengthRelations R G

namespace FiniteLengthGrothendieckGroup

/-- The quotient map from the free integral presentation. -/
def quotientMap : FiniteLengthPresentation.{uR, uG, uV} R G →ₗ[ℤ]
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G :=
  (finiteLengthRelations R G).mkQ

/-- The canonical generator indexed by a genuine isomorphism class. -/
def ofClass (c : FiniteLengthIsoClass.{uR, uG, uV} R G) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G :=
  quotientMap R G (generator c)

variable {R G}

/-- The canonical class map on actual finite-length objects. -/
def ofObject (A : FiniteLengthObject.{uR, uG, uV} R G) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G :=
  ofClass R G (finiteLengthIsoClass A)

/-- The class map accepts any actual smooth representation together with its
finite-length proof, without changing its carrier universe. -/
def ofRepresentation (A : SmoothRep.{uR, uG, uV} R G) (hA : A.HasFiniteLength) :
    FiniteLengthGrothendieckGroup.{uR, uG, uV} R G :=
  ofObject ⟨A, hA⟩

/-- Actual categorical isomorphisms give equal classes. -/
theorem ofObject_eq_of_iso {A B : FiniteLengthObject.{uR, uG, uV} R G}
    (e : A.val ≅ B.val) : ofObject A = ofObject B := by
  apply congrArg (ofClass R G)
  exact Quotient.sound ⟨e⟩

/-- Actual equivariant linear equivalences give equal canonical classes. -/
theorem ofRepresentation_eq_of_equiv {A B : SmoothRep.{uR, uG, uV} R G}
    (hA : A.HasFiniteLength) (hB : B.HasFiniteLength)
    (e : A.representation.Equiv B.representation) :
    ofRepresentation A hA = ofRepresentation B hB :=
  ofObject_eq_of_iso (mkIso e)

/-- The defining additivity law for every actual short exact sequence. -/
theorem ofObject_shortExact {A B C : FiniteLengthObject.{uR, uG, uV} R G}
    {f : A.val.representation.IntertwiningMap B.val.representation}
    {g : B.val.representation.IntertwiningMap C.val.representation}
    (h : IsShortExact f g) : ofObject B = ofObject A + ofObject C := by
  have hr : generator (finiteLengthIsoClass B) - generator (finiteLengthIsoClass A) -
      generator (finiteLengthIsoClass C) ∈ finiteLengthRelations R G :=
    Submodule.subset_span ⟨A, B, C, f, g, h, rfl⟩
  have hz := (Submodule.Quotient.mk_eq_zero (finiteLengthRelations R G)).mpr hr
  change quotientMap R G (generator (finiteLengthIsoClass B) -
    generator (finiteLengthIsoClass A) - generator (finiteLengthIsoClass C)) = 0 at hz
  rw [map_sub, map_sub] at hz
  exact sub_eq_zero.mp (by simpa only [ofObject, ofClass, sub_sub] using hz)

/-- The same exact-sequence law with the finite-length proofs supplied separately. -/
theorem ofRepresentation_shortExact {A B C : SmoothRep.{uR, uG, uV} R G}
    (hA : A.HasFiniteLength) (hB : B.HasFiniteLength) (hC : C.HasFiniteLength)
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation} (h : IsShortExact f g) :
    ofRepresentation B hB = ofRepresentation A hA + ofRepresentation C hC :=
  ofObject_shortExact (A := ⟨A, hA⟩) (B := ⟨B, hB⟩) (C := ⟨C, hC⟩) h

variable (R G) {M : Type uM} [AddCommGroup M]

/-- Exact additivity of a function on genuine finite-length smooth classes. -/
def IsExactAdditive (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M) : Prop :=
  ∀ (A B C : FiniteLengthObject.{uR, uG, uV} R G)
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation),
    IsShortExact f g →
      a (finiteLengthIsoClass B) = a (finiteLengthIsoClass A) + a (finiteLengthIsoClass C)

/-- Exact additivity annihilates the entire relation submodule. -/
theorem relations_le_ker_extend (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M)
    (ha : IsExactAdditive R G a) :
    finiteLengthRelations R G ≤ LinearMap.ker (extend a) := by
  apply Submodule.span_le.mpr
  rintro x ⟨A, B, C, f, g, h, rfl⟩
  change extend a _ = 0
  simp only [map_sub, extend, generator, Finsupp.linearCombination_single, one_smul]
  rw [ha A B C f g h, add_sub_cancel_left, sub_self]

/-- The universal additive lift, using the canonical integer module on an
arbitrary abelian target group. -/
def lift (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M)
    (ha : IsExactAdditive R G a) : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ] M :=
  (finiteLengthRelations R G).liftQ (extend a) (relations_le_ker_extend R G a ha)

@[simp] theorem lift_ofClass (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M)
    (ha : IsExactAdditive R G a) (c : FiniteLengthIsoClass.{uR, uG, uV} R G) :
    lift R G a ha (ofClass R G c) = a c := by
  simp [lift, ofClass, quotientMap, extend, generator]

@[simp] theorem lift_ofObject (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M)
    (ha : IsExactAdditive R G a) (A : FiniteLengthObject.{uR, uG, uV} R G) :
    lift R G a ha (ofObject A) = a (finiteLengthIsoClass A) :=
  lift_ofClass R G a ha _

@[simp] theorem lift_ofRepresentation (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M)
    (ha : IsExactAdditive R G a) (A : SmoothRep.{uR, uG, uV} R G) (hA : A.HasFiniteLength) :
    lift R G a ha (ofRepresentation A hA) = a (finiteLengthIsoClass ⟨A, hA⟩) :=
  lift_ofClass R G a ha _

/-- Values on canonical generators determine a homomorphism from the quotient. -/
@[ext] theorem hom_ext
    {l₁ l₂ : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ] M}
    (h : ∀ c, l₁ (ofClass R G c) = l₂ (ofClass R G c)) : l₁ = l₂ := by
  have he : l₁.comp (quotientMap R G) = l₂.comp (quotientMap R G) := by
    apply Finsupp.lhom_ext
    intro c n
    have hn : Finsupp.single c n = n • generator c := by simp [generator]
    rw [hn, LinearMap.map_smul, LinearMap.map_smul]
    exact congrArg (fun m => n • m) (h c)
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (finiteLengthRelations R G).mkQ_surjective x
  exact LinearMap.congr_fun he v

/-- It suffices to compare values on actual finite-length smooth objects. -/
theorem hom_ext_object
    {l₁ l₂ : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ] M}
    (h : ∀ A, l₁ (ofObject A) = l₂ (ofObject A)) : l₁ = l₂ := by
  apply hom_ext R G
  intro c
  induction c using Quotient.inductionOn with
  | h A => exact h A

/-- Every homomorphism from the quotient respects every actual exact sequence. -/
theorem isExactAdditive_of_linearMap
    (l : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ] M) :
    IsExactAdditive R G (fun c => l (ofClass R G c)) := by
  intro A B C f g h
  change l (ofObject B) = l (ofObject A) + l (ofObject C)
  rw [ofObject_shortExact h, map_add]

/-- Existence and uniqueness characterize exact-additive class functions. -/
theorem existsUnique_lift_iff (a : FiniteLengthIsoClass.{uR, uG, uV} R G → M) :
    (∃! l : FiniteLengthGrothendieckGroup.{uR, uG, uV} R G →ₗ[ℤ] M,
      ∀ c, l (ofClass R G c) = a c) ↔ IsExactAdditive R G a := by
  constructor
  · rintro ⟨l, hl, _⟩
    have ha := isExactAdditive_of_linearMap R G l
    simpa only [hl] using ha
  · intro ha
    refine ⟨lift R G a ha, lift_ofClass R G a ha, ?_⟩
    intro l hl
    apply hom_ext R G
    intro c
    rw [hl, lift_ofClass]

end FiniteLengthGrothendieckGroup
end Langlands.SmoothRep

namespace Langlands.GeneralLinear

variable (n : ℕ) (F : Type uF) [Field F] [TopologicalSpace F]

/-- Complex finite-length smooth virtual representations of the actual `GL_n(F)`,
with saturated carrier universe `max uF uV`. -/
abbrev FiniteLengthGrothendieckGroup :=
  SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ (GeneralLinear n F)

/-- The canonical class map for actual GL representations with saturated carriers. -/
def finiteLengthClass (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F))
    (hA : A.HasFiniteLength) : FiniteLengthGrothendieckGroup.{uV, uF} n F :=
  SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA

namespace BlockShape

variable {n} (B : BlockShape n)

/-- The same exact construction on the actual product Levi, with its product
topology and the same saturated carrier universe. -/
abbrev FiniteLengthGrothendieckGroup :=
  SmoothRep.FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ (B.Levi F)

/-- The canonical class map for actual product-Levi representations. -/
def finiteLengthClass (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F))
    (hA : A.HasFiniteLength) : B.FiniteLengthGrothendieckGroup.{uV, uF} F :=
  SmoothRep.FiniteLengthGrothendieckGroup.ofRepresentation A hA

end BlockShape
end Langlands.GeneralLinear
