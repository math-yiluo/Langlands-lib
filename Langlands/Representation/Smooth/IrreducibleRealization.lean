import Langlands.Representation.Smooth.FiniteLengthGrothendieck

/-!
# Irreducible smooth classes and their exact finite-length realization

Genuine isomorphism classes of actual irreducible smooth representations over a
field, their free integral lattice, and the integer-linear map to the exact
Grothendieck group of finite-length smooth representations sending each class
to the class of a representative. Irreducible representations have finite
group-algebra length automatically; no admissibility or finite-dimensionality
is assumed, and the group and carrier universes stay independent. Injectivity
or surjectivity of the realization is not asserted here.
-/

noncomputable section

open CategoryTheory
open Langlands.VirtualRepresentation

universe uR uG uV uF

namespace Langlands.SmoothRep

variable {k : Type uR} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- An irreducible representation is a simple module over the group algebra, so it
has finite group-algebra length. No admissibility is needed. -/
theorem hasFiniteLength_of_isIrreducible {A : SmoothRep.{uR, uG, uV} k G}
    (hA : A.IsIrreducible) : A.HasFiniteLength := by
  have : IsSimpleModule (MonoidAlgebra k G) A.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

/-- Irreducibility is transported along actual equivariant linear equivalences. -/
theorem isIrreducible_of_equiv {A B : SmoothRep.{uR, uG, uV} k G}
    (e : A.representation.Equiv B.representation) (hA : A.IsIrreducible) :
    B.IsIrreducible := by
  rw [SmoothRep.IsIrreducible, Representation.irreducible_iff_isSimpleModule_asModule] at hA ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule _ _ e.toIntertwiningMap)
    e.bijective).1 hA

/-- Irreducibility is transported along actual categorical isomorphisms. -/
theorem isIrreducible_of_iso {A B : SmoothRep.{uR, uG, uV} k G} (e : A ≅ B)
    (hA : A.IsIrreducible) : B.IsIrreducible :=
  isIrreducible_of_equiv (equivOfIso e) hA

variable (k G)

/-- Actual irreducible smooth representations with carriers in `Type uV`. -/
abbrev IrreducibleObject :=
  {A : SmoothRep.{uR, uG, uV} k G // A.IsIrreducible}

/-- Two irreducible objects are related precisely when their actual smooth
representations are isomorphic. -/
def irreducibleIsoSetoid : Setoid (IrreducibleObject.{uR, uG, uV} k G) where
  r A B := Nonempty (A.val ≅ B.val)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Genuine isomorphism classes of actual irreducible smooth representations;
the object universe is not resized. -/
def IrreducibleIsoClass : Type (max uR uG (uV + 1)) :=
  Quotient (irreducibleIsoSetoid.{uR, uG, uV} k G)

variable {k G}

/-- The class of an actual irreducible smooth representation. -/
def irreducibleIsoClass (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible) :
    IrreducibleIsoClass.{uR, uG, uV} k G :=
  Quotient.mk _ ⟨A, hA⟩

/-- Two labels agree exactly when the actual smooth objects are isomorphic. -/
theorem irreducibleIsoClass_eq_iff {A B : SmoothRep.{uR, uG, uV} k G}
    (hA : A.IsIrreducible) (hB : B.IsIrreducible) :
    irreducibleIsoClass A hA = irreducibleIsoClass B hB ↔ Nonempty (A ≅ B) :=
  Quotient.eq

/-- The same criterion with actual equivariant linear equivalences. -/
theorem irreducibleIsoClass_eq_iff_nonempty_equiv {A B : SmoothRep.{uR, uG, uV} k G}
    (hA : A.IsIrreducible) (hB : B.IsIrreducible) :
    irreducibleIsoClass A hA = irreducibleIsoClass B hB ↔
      Nonempty (A.representation.Equiv B.representation) :=
  (irreducibleIsoClass_eq_iff hA hB).trans
    ⟨fun ⟨e⟩ => ⟨equivOfIso e⟩, fun ⟨e⟩ => ⟨mkIso e⟩⟩

theorem irreducibleIsoClass_eq_of_iso {A B : SmoothRep.{uR, uG, uV} k G}
    (hA : A.IsIrreducible) (hB : B.IsIrreducible) (e : A ≅ B) :
    irreducibleIsoClass A hA = irreducibleIsoClass B hB :=
  (irreducibleIsoClass_eq_iff hA hB).mpr ⟨e⟩

theorem irreducibleIsoClass_eq_of_equiv {A B : SmoothRep.{uR, uG, uV} k G}
    (hA : A.IsIrreducible) (hB : B.IsIrreducible)
    (e : A.representation.Equiv B.representation) :
    irreducibleIsoClass A hA = irreducibleIsoClass B hB :=
  (irreducibleIsoClass_eq_iff_nonempty_equiv hA hB).mpr ⟨e⟩

namespace IrreducibleIsoClass

/-- Every label is the class of an actual irreducible smooth representation. -/
theorem exists_eq (c : IrreducibleIsoClass.{uR, uG, uV} k G) :
    ∃ (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible), irreducibleIsoClass A hA = c :=
  Quotient.inductionOn c fun A => ⟨A.val, A.property, rfl⟩

/-- Induction over labels through actual irreducible representatives. -/
@[elab_as_elim] theorem inductionOn {motive : IrreducibleIsoClass.{uR, uG, uV} k G → Prop}
    (c : IrreducibleIsoClass.{uR, uG, uV} k G)
    (h : ∀ (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible),
      motive (irreducibleIsoClass A hA)) : motive c :=
  Quotient.inductionOn c fun A => h A.val A.property

/-- The forgetful map to the existing finite-length labels, using the automatic
finite length of an irreducible representative. -/
def toFiniteLengthIsoClass :
    IrreducibleIsoClass.{uR, uG, uV} k G → FiniteLengthIsoClass.{uR, uG, uV} k G :=
  Quotient.lift (fun A => finiteLengthIsoClass ⟨A.val, hasFiniteLength_of_isIrreducible A.property⟩)
    (fun _ _ h => (finiteLengthIsoClass_eq_iff _ _).mpr h)

/-- On an actual irreducible representation the forgetful label is its existing
finite-length class, for any supplied finite-length proof. -/
@[simp] theorem toFiniteLengthIsoClass_irreducibleIsoClass (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.IsIrreducible) (hLength : A.HasFiniteLength) :
    toFiniteLengthIsoClass (irreducibleIsoClass A hA) = finiteLengthIsoClass ⟨A, hLength⟩ :=
  rfl

/-- The forgetful map between genuine isomorphism-class types is injective. -/
theorem toFiniteLengthIsoClass_injective :
    Function.Injective (toFiniteLengthIsoClass :
      IrreducibleIsoClass.{uR, uG, uV} k G → FiniteLengthIsoClass.{uR, uG, uV} k G) := by
  intro c d h
  induction c using Quotient.inductionOn with
  | h A =>
    induction d using Quotient.inductionOn with
    | h B => exact Quotient.sound ((finiteLengthIsoClass_eq_iff _ _).mp h)

theorem toFiniteLengthIsoClass_inj {c d : IrreducibleIsoClass.{uR, uG, uV} k G} :
    toFiniteLengthIsoClass c = toFiniteLengthIsoClass d ↔ c = d :=
  toFiniteLengthIsoClass_injective.eq_iff

/-- A finite-length label comes from an irreducible label exactly when its
representative is irreducible; irreducibility does not depend on the representative. -/
theorem exists_toFiniteLengthIsoClass_eq_iff (A : FiniteLengthObject.{uR, uG, uV} k G) :
    (∃ c : IrreducibleIsoClass.{uR, uG, uV} k G,
      toFiniteLengthIsoClass c = finiteLengthIsoClass A) ↔ A.val.IsIrreducible := by
  constructor
  · rintro ⟨c, hc⟩
    induction c using Quotient.inductionOn with
    | h B =>
      obtain ⟨e⟩ := (finiteLengthIsoClass_eq_iff _ _).mp hc
      exact isIrreducible_of_iso e B.property
  · intro hA
    exact ⟨irreducibleIsoClass A.val hA, rfl⟩

end IrreducibleIsoClass

variable (k G)

/-- The free integral lattice on genuine irreducible smooth classes. -/
abbrev IrreducibleLattice :=
  IntegralLattice (IrreducibleIsoClass.{uR, uG, uV} k G)

/-- The integer-linear realization in the exact finite-length Grothendieck group,
extending the class of an irreducible representative on basis generators. -/
def realizeIrreducibles :
    IrreducibleLattice.{uR, uG, uV} k G →ₗ[ℤ] FiniteLengthGrothendieckGroup.{uR, uG, uV} k G :=
  extend (fun c => FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass)

variable {k G}

/-- The generator formula for an arbitrary irreducible label. -/
@[simp] theorem realizeIrreducibles_generator (c : IrreducibleIsoClass.{uR, uG, uV} k G) :
    realizeIrreducibles k G (generator c) =
      FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass := by
  simp [realizeIrreducibles, extend, generator]

/-- The generator indexed by an actual irreducible representation realizes its
exact class, for any finite-length proof. -/
theorem realizeIrreducibles_generator_irreducibleIsoClass (A : SmoothRep.{uR, uG, uV} k G)
    (hA : A.IsIrreducible) (hLength : A.HasFiniteLength) :
    realizeIrreducibles k G (generator (irreducibleIsoClass A hA)) =
      FiniteLengthGrothendieckGroup.ofRepresentation A hLength :=
  realizeIrreducibles_generator _

theorem realizeIrreducibles_integralBasis (c : IrreducibleIsoClass.{uR, uG, uV} k G) :
    realizeIrreducibles k G (integralBasis c) =
      FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass := by
  rw [show integralBasis c = generator c by simp [integralBasis, generator]]
  exact realizeIrreducibles_generator c

/-- The realization of a finite integral combination of labels. -/
theorem realizeIrreducibles_apply (v : IrreducibleLattice.{uR, uG, uV} k G) :
    realizeIrreducibles k G v =
      v.sum (fun c n => n • FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass) :=
  Finsupp.linearCombination_apply ℤ v

@[simp] theorem realizeIrreducibles_zero :
    realizeIrreducibles k G (0 : IrreducibleLattice.{uR, uG, uV} k G) = 0 :=
  map_zero _

@[simp] theorem realizeIrreducibles_add (v w : IrreducibleLattice.{uR, uG, uV} k G) :
    realizeIrreducibles k G (v + w) = realizeIrreducibles k G v + realizeIrreducibles k G w :=
  map_add _ v w

@[simp] theorem realizeIrreducibles_neg (v : IrreducibleLattice.{uR, uG, uV} k G) :
    realizeIrreducibles k G (-v) = -realizeIrreducibles k G v :=
  map_neg _ v

@[simp] theorem realizeIrreducibles_sub (v w : IrreducibleLattice.{uR, uG, uV} k G) :
    realizeIrreducibles k G (v - w) = realizeIrreducibles k G v - realizeIrreducibles k G w :=
  map_sub _ v w

@[simp] theorem realizeIrreducibles_smul (z : ℤ) (v : IrreducibleLattice.{uR, uG, uV} k G) :
    realizeIrreducibles k G (z • v) = z • realizeIrreducibles k G v :=
  map_zsmul _ z v

/-- A linear map with the generator values of the realization is the realization. -/
theorem eq_realizeIrreducibles
    {l : IrreducibleLattice.{uR, uG, uV} k G →ₗ[ℤ] FiniteLengthGrothendieckGroup.{uR, uG, uV} k G}
    (h : ∀ c, l (generator c) = FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass) :
    l = realizeIrreducibles k G := by
  apply Finsupp.lhom_ext
  intro c n
  have hn : Finsupp.single c n = n • generator c := by simp [generator]
  rw [hn, map_zsmul, map_zsmul, h, realizeIrreducibles_generator]

/-- Uniqueness checked on actual irreducible representations. -/
theorem eq_realizeIrreducibles_of_irreducible
    {l : IrreducibleLattice.{uR, uG, uV} k G →ₗ[ℤ] FiniteLengthGrothendieckGroup.{uR, uG, uV} k G}
    (h : ∀ (A : SmoothRep.{uR, uG, uV} k G) (hA : A.IsIrreducible),
      l (generator (irreducibleIsoClass A hA)) =
        FiniteLengthGrothendieckGroup.ofRepresentation A (hasFiniteLength_of_isIrreducible hA)) :
    l = realizeIrreducibles k G := by
  apply eq_realizeIrreducibles
  intro c
  induction c using IrreducibleIsoClass.inductionOn with
  | h A hA => exact h A hA

/-- Existence and uniqueness of the linear map with the prescribed generator values. -/
theorem existsUnique_realizeIrreducibles :
    ∃! l : IrreducibleLattice.{uR, uG, uV} k G →ₗ[ℤ] FiniteLengthGrothendieckGroup.{uR, uG, uV} k G,
      ∀ c, l (generator c) = FiniteLengthGrothendieckGroup.ofClass k G c.toFiniteLengthIsoClass :=
  ⟨realizeIrreducibles k G, realizeIrreducibles_generator, fun _ h => eq_realizeIrreducibles h⟩

end Langlands.SmoothRep

namespace Langlands.GeneralLinear

variable (n : ℕ) (F : Type uF) [Field F] [TopologicalSpace F]

/-- Irreducible labels for complex smooth representations of the actual `GL_n(F)`,
with carrier universe `max uF uV`. -/
abbrev IrreducibleIsoClass :=
  SmoothRep.IrreducibleIsoClass.{0, uF, max uF uV} ℂ (GeneralLinear n F)

/-- The label of an actual irreducible smooth representation of `GL_n(F)`. -/
abbrev irreducibleIsoClass (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F))
    (hA : A.IsIrreducible) : IrreducibleIsoClass.{uV, uF} n F :=
  SmoothRep.irreducibleIsoClass A hA

/-- The free integral lattice on irreducible `GL_n(F)` labels. -/
abbrev IrreducibleLattice :=
  SmoothRep.IrreducibleLattice.{0, uF, max uF uV} ℂ (GeneralLinear n F)

/-- The realization in the exact finite-length Grothendieck group of `GL_n(F)`. -/
abbrev realizeIrreducibles :
    IrreducibleLattice.{uV, uF} n F →ₗ[ℤ] FiniteLengthGrothendieckGroup.{uV, uF} n F :=
  SmoothRep.realizeIrreducibles ℂ (GeneralLinear n F)

theorem realizeIrreducibles_generator_irreducibleIsoClass
    (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F)) (hA : A.IsIrreducible)
    (hLength : A.HasFiniteLength) :
    realizeIrreducibles.{uV, uF} n F (generator (irreducibleIsoClass n F A hA)) =
      finiteLengthClass n F A hLength :=
  SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass A hA hLength

namespace BlockShape

variable {n} (B : BlockShape n)

/-- Irreducible labels for complex smooth representations of the actual product
Levi, with no tensor-factorization condition. -/
abbrev IrreducibleIsoClass :=
  SmoothRep.IrreducibleIsoClass.{0, uF, max uF uV} ℂ (B.Levi F)

/-- The label of an actual irreducible product-Levi representation. -/
abbrev irreducibleIsoClass (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F))
    (hA : A.IsIrreducible) : B.IrreducibleIsoClass.{uV, uF} F :=
  SmoothRep.irreducibleIsoClass A hA

/-- The free integral lattice on irreducible product-Levi labels. -/
abbrev IrreducibleLattice :=
  SmoothRep.IrreducibleLattice.{0, uF, max uF uV} ℂ (B.Levi F)

/-- The realization in the exact finite-length Grothendieck group of the product Levi. -/
abbrev realizeIrreducibles :
    B.IrreducibleLattice.{uV, uF} F →ₗ[ℤ] B.FiniteLengthGrothendieckGroup.{uV, uF} F :=
  SmoothRep.realizeIrreducibles ℂ (B.Levi F)

theorem realizeIrreducibles_generator_irreducibleIsoClass
    (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F)) (hA : A.IsIrreducible)
    (hLength : A.HasFiniteLength) :
    B.realizeIrreducibles.{uV, uF} F (generator (B.irreducibleIsoClass F A hA)) =
      B.finiteLengthClass F A hLength :=
  SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass A hA hLength

end BlockShape
end Langlands.GeneralLinear
