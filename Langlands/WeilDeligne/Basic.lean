import Langlands.Weil.Representation.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.Semisimple

/-!
# Algebraic Weil–Deligne pairs

The supplied character is the norm character. Topological and inertia conditions
are separate predicates on the underlying representation.
-/

noncomputable section

universe uK uG uV uW uX

open CategoryTheory

namespace Langlands

/-- A finite-dimensional algebraic Weil–Deligne pair for a specified norm character.
The covariance law uses the actual group inverse action. -/
structure WeilDeligneRepresentation (K : Type uK) (G : Type uG) [Field K] [Group G]
    (ν : G →* Kˣ) where
  toFiniteRepresentation : FiniteRepresentation.{uK, uG, uV} K G
  monodromy : Module.End K toFiniteRepresentation
  nilpotent : IsNilpotent monodromy
  covariance : ∀ g : G,
    toFiniteRepresentation.representation g * monodromy *
      toFiniteRepresentation.representation g⁻¹ = (ν g : K) • monodromy

namespace WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Group G] {ν : G →* Kˣ}

instance : CoeSort (WeilDeligneRepresentation.{uK, uG, uV} K G ν) (Type uV) :=
  ⟨fun A => A.toFiniteRepresentation⟩

instance (A : WeilDeligneRepresentation K G ν) : AddCommGroup A :=
  inferInstanceAs (AddCommGroup A.toFiniteRepresentation)

instance (A : WeilDeligneRepresentation K G ν) : Module K A :=
  inferInstanceAs (Module K A.toFiniteRepresentation)

instance (A : WeilDeligneRepresentation K G ν) : Module.Finite K A :=
  inferInstanceAs (Module.Finite K A.toFiniteRepresentation)

/-- The Weil action of the pair. -/
abbrev representation (A : WeilDeligneRepresentation K G ν) : Representation K G A :=
  A.toFiniteRepresentation.representation

/-- The dimension of the carrier. -/
def rank (A : WeilDeligneRepresentation K G ν) : ℕ := A.toFiniteRepresentation.rank

/-- A linear intertwiner that also commutes with monodromy. -/
structure Hom (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) where
  intertwiner : A.representation.IntertwiningMap B.representation
  comm_monodromy : intertwiner.toLinearMap ∘ₗ A.monodromy =
    B.monodromy ∘ₗ intertwiner.toLinearMap

namespace Hom

@[ext]
theorem ext {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {f g : Hom A B} (h : f.intertwiner = g.intertwiner) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Identity morphism. -/
def id (A : WeilDeligneRepresentation K G ν) : Hom A A :=
  ⟨.id A.representation, by simp⟩

/-- Composition of morphisms, with monodromy compatibility proved. -/
def comp {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {C : WeilDeligneRepresentation.{uK, uG, uX} K G ν}
    (g : Hom B C) (f : Hom A B) : Hom A C where
  intertwiner := g.intertwiner.comp f.intertwiner
  comm_monodromy := by
    change (g.intertwiner.toLinearMap ∘ₗ f.intertwiner.toLinearMap) ∘ₗ A.monodromy =
      C.monodromy ∘ₗ (g.intertwiner.toLinearMap ∘ₗ f.intertwiner.toLinearMap)
    rw [LinearMap.comp_assoc, f.comm_monodromy, ← LinearMap.comp_assoc,
      g.comm_monodromy, LinearMap.comp_assoc]

end Hom

instance : Category (WeilDeligneRepresentation.{uK, uG, uV} K G ν) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp g f
  id_comp := by intros; apply Hom.ext; ext; rfl
  comp_id := by intros; apply Hom.ext; ext; rfl
  assoc := by intros; apply Hom.ext; ext; rfl

/-- Forget monodromy, retaining the original carrier and action. -/
def forget : WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
    FiniteRepresentation.{uK, uG, uV} K G where
  obj A := A.toFiniteRepresentation
  map f := (FiniteRepresentation.homEquiv _ _).symm f.intertwiner

/-- A genuine isomorphism of pairs: a representation equivalence commuting with monodromy. -/
structure Equiv (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν)
    (B : WeilDeligneRepresentation.{uK, uG, uW} K G ν) where
  representationEquiv : A.representation.Equiv B.representation
  comm_monodromy : representationEquiv.toLinearMap ∘ₗ A.monodromy =
    B.monodromy ∘ₗ representationEquiv.toLinearMap

namespace Equiv

/-- The underlying morphism of pairs. -/
def toHom {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A B) : Hom A B :=
  ⟨e.representationEquiv.toIntertwiningMap, e.comm_monodromy⟩

/-- Identity equivalence. -/
def refl (A : WeilDeligneRepresentation K G ν) : Equiv A A :=
  ⟨.refl A.representation, by simp⟩

/-- Inverse equivalence, including its monodromy compatibility. -/
def symm {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A B) : Equiv B A where
  representationEquiv := e.representationEquiv.symm
  comm_monodromy := by
    ext b
    apply e.representationEquiv.toLinearEquiv.injective
    have h := LinearMap.congr_fun e.comm_monodromy (e.representationEquiv.symm b)
    simpa using h.symm

/-- Composition of equivalences. -/
def trans {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {C : WeilDeligneRepresentation.{uK, uG, uX} K G ν}
    (e : Equiv A B) (f : Equiv B C) : Equiv A C :=
  ⟨e.representationEquiv.trans f.representationEquiv,
    (Hom.comp f.toHom e.toHom).comm_monodromy⟩

/-- A pair equivalence gives a categorical isomorphism. -/
def toIso {A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν} (e : Equiv A B) :
    A ≅ B where
  hom := e.toHom
  inv := e.symm.toHom
  hom_inv_id := by
    apply Hom.ext
    ext x
    exact e.representationEquiv.symm_apply_apply x
  inv_hom_id := by
    apply Hom.ext
    ext x
    exact e.representationEquiv.apply_symm_apply x

/-- A categorical isomorphism gives an actual invertible linear map of pairs. -/
def ofIso {A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν} (e : A ≅ B) :
    Equiv A B where
  representationEquiv := FiniteRepresentation.equivOfIso (forget.mapIso e)
  comm_monodromy := e.hom.comm_monodromy

end Equiv

/-- Genuine isomorphism of Weil–Deligne pairs. -/
def IsIsomorphic (A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν) : Prop :=
  Nonempty (Equiv A B)

/-- The equivalence laws follow from actual identity, inverse and composite isomorphisms. -/
def isomorphismSetoid : Setoid (WeilDeligneRepresentation.{uK, uG, uV} K G ν) where
  r := IsIsomorphic
  iseqv := {
    refl := fun A => ⟨Equiv.refl A⟩
    symm := fun ⟨e⟩ => ⟨e.symm⟩
    trans := fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩ }

/-- Isomorphism classes of pairs, allowing nonzero monodromy. -/
def IsomorphismClasses (K : Type uK) (G : Type uG) [Field K] [Group G] (ν : G →* Kˣ) :=
  Quotient (isomorphismSetoid : Setoid (WeilDeligneRepresentation.{uK, uG, uV} K G ν))

/-- The class of a pair. -/
def classOf (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    IsomorphismClasses.{uK, uG, uV} K G ν := Quotient.mk _ A

/-- Quotient equality is precisely pair isomorphism. -/
theorem classOf_eq_iff (A B : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    classOf A = classOf B ↔ Nonempty (Equiv A B) := Quotient.eq

/-- Rank descends to pair isomorphism classes. -/
def classRank : IsomorphismClasses.{uK, uG, uV} K G ν → ℕ :=
  Quotient.lift rank fun _ _ ⟨e⟩ => e.representationEquiv.toLinearEquiv.finrank_eq

/-- All rank-`n` pair classes, including those with nonzero nilpotent monodromy. -/
def IsomorphismClassesOfRank (K : Type uK) (G : Type uG) [Field K] [Group G]
    (ν : G →* Kˣ) (n : ℕ) :=
  {c : IsomorphismClasses.{uK, uG, uV} K G ν // classRank c = n}

/-- The pair with zero monodromy associated to an actual finite representation. -/
def zeroMonodromy (ν : G →* Kˣ) (A : FiniteRepresentation.{uK, uG, uV} K G) :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν where
  toFiniteRepresentation := A
  monodromy := 0
  nilpotent := IsNilpotent.zero
  covariance _ := by simp

/-- The actual functor embedding representations as pairs with zero monodromy. -/
def zeroMonodromyFunctor (ν : G →* Kˣ) : FiniteRepresentation.{uK, uG, uV} K G ⥤
    WeilDeligneRepresentation.{uK, uG, uV} K G ν where
  obj := zeroMonodromy ν
  map f := ⟨FiniteRepresentation.homEquiv _ _ f, by
    ext x
    change (FiniteRepresentation.homEquiv _ _ f).toLinearMap 0 = 0
    exact map_zero _⟩
  map_id := by intros; apply Hom.ext; rfl
  map_comp := by intros; apply Hom.ext; rfl

/-- The zero-monodromy functor is fully faithful: every linear intertwiner lifts uniquely. -/
def zeroMonodromyFullyFaithful (ν : G →* Kˣ) : (zeroMonodromyFunctor ν).FullyFaithful where
  preimage f := (FiniteRepresentation.homEquiv _ _).symm f.intertwiner
  map_preimage _ := by apply Hom.ext; rfl
  preimage_map _ := rfl

/-- Frobenius semisimplicity refers to the Weil action of every nonzero-degree element.
There is no condition that monodromy vanish. -/
def IsFrobeniusSemisimple (A : WeilDeligneRepresentation K G ν)
    (degree : G →* Multiplicative ℤ) : Prop :=
  ∀ g : G, Multiplicative.toAdd (degree g) ≠ 0 →
    Module.End.IsSemisimple (A.representation g)

end WeilDeligneRepresentation

end Langlands
