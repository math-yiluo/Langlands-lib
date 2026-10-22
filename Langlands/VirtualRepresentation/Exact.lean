import Langlands.Weil.Representation.Basic
import Langlands.VirtualRepresentation.Integral
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Virtual representations with actual exact-sequence relations

The quotient is constructed from genuine finite-dimensional representation
classes. A predicate can restrict the objects, for example to continuous Weil
representations. No irreducible decomposition or semisimplicity is assumed.
-/

noncomputable section

universe uK uG uV uA uB uC uM

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Monoid G]

/-- Exactness of actual intertwiners, including the two endpoint conditions. -/
def IsShortExact {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G}
    {C : FiniteRepresentation.{uK, uG, uC} K G}
    (f : A.representation.IntertwiningMap B.representation)
    (g : B.representation.IntertwiningMap C.representation) : Prop :=
  Function.Injective f ∧ Function.Surjective g ∧
    LinearMap.range f.toLinearMap = LinearMap.ker g.toLinearMap

/-- Rank additivity follows from injectivity, surjectivity and rank-nullity;
no equivariant splitting is needed. -/
theorem rank_eq_add_of_shortExact
    {A : FiniteRepresentation.{uK, uG, uA} K G}
    {B : FiniteRepresentation.{uK, uG, uB} K G}
    {C : FiniteRepresentation.{uK, uG, uC} K G}
    {f : A.representation.IntertwiningMap B.representation}
    {g : B.representation.IntertwiningMap C.representation}
    (h : IsShortExact f g) : B.rank = A.rank + C.rank := by
  have hd := g.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr h.2.1, finrank_top,
    ← h.2.2, LinearMap.finrank_range_of_inj h.1] at hd
  simpa only [rank, Nat.add_comm] using hd.symm

end Langlands.FiniteRepresentation

namespace Langlands.VirtualRepresentation

open FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Monoid G]
variable (P : FiniteRepresentation.{uK, uG, uV} K G → Prop)

/-- The free integral module on genuine isomorphism classes satisfying `P`. -/
abbrev ExactPresentation := IntegralLattice (IsomorphismClassesWith P)

/-- The genuine class of an object with its supplied property. -/
def exactClassOf (A : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}) :
    IsomorphismClassesWith P :=
  Quotient.mk _ A

/-- Relations supplied by actual short exact sequences whose three objects
satisfy `P`. This does not impose split relations in place of exact relations. -/
def exactRelationSet : Set (ExactPresentation P) :=
  {x | ∃ (A B C : {A : FiniteRepresentation.{uK, uG, uV} K G // P A})
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation),
    IsShortExact f g ∧
      x = generator (exactClassOf P B) - generator (exactClassOf P A) -
        generator (exactClassOf P C)}

/-- All integral consequences of the actual exact-sequence relations. -/
def exactRelations : Submodule ℤ (ExactPresentation P) :=
  Submodule.span ℤ (exactRelationSet P)

/-- The exact-relation Grothendieck group of the specified family of actual
finite-dimensional representations. For a general predicate this denotes
precisely this quotient; no closure or exact-category axioms are postulated. -/
abbrev ExactGrothendieckGroup := ExactPresentation P ⧸ exactRelations P

namespace ExactGrothendieckGroup

/-- The quotient homomorphism from the presentation. -/
def quotientMap : ExactPresentation P →ₗ[ℤ] ExactGrothendieckGroup P :=
  (exactRelations P).mkQ

/-- Send a genuine isomorphism class to its virtual class. -/
def ofClass (c : IsomorphismClassesWith P) : ExactGrothendieckGroup P :=
  quotientMap P (generator c)

/-- The virtual class of an actual representation satisfying `P`. -/
def ofRepresentation (A : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}) :
    ExactGrothendieckGroup P :=
  ofClass P (exactClassOf P A)

/-- Genuine intertwining equivalences give equal virtual classes. -/
theorem ofRepresentation_eq_of_equiv
    {A B : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}}
    (e : FiniteRepresentation.Equiv A.val B.val) :
    ofRepresentation P A = ofRepresentation P B := by
  apply congrArg (ofClass P)
  exact Quotient.sound ⟨e⟩

/-- The defining exact-sequence identity in the constructed group. -/
theorem ofRepresentation_shortExact
    {A B C : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}}
    {f : A.val.representation.IntertwiningMap B.val.representation}
    {g : B.val.representation.IntertwiningMap C.val.representation}
    (h : IsShortExact f g) :
    ofRepresentation P B = ofRepresentation P A + ofRepresentation P C := by
  have hr : generator (exactClassOf P B) - generator (exactClassOf P A) -
      generator (exactClassOf P C) ∈ exactRelations P :=
    Submodule.subset_span ⟨A, B, C, f, g, h, rfl⟩
  have hz := (Submodule.Quotient.mk_eq_zero (exactRelations P)).mpr hr
  change quotientMap P
    (generator (exactClassOf P B) - generator (exactClassOf P A) -
      generator (exactClassOf P C)) = 0 at hz
  rw [map_sub, map_sub] at hz
  exact sub_eq_zero.mp (by simpa only [ofRepresentation, ofClass, sub_sub] using hz)

variable {M : Type uM} [AddCommGroup M]

/-- Additivity on all actual short exact sequences in the specified family. -/
def IsExactAdditive (a : IsomorphismClassesWith P → M) : Prop :=
  ∀ (A B C : {A : FiniteRepresentation.{uK, uG, uV} K G // P A})
    (f : A.val.representation.IntertwiningMap B.val.representation)
    (g : B.val.representation.IntertwiningMap C.val.representation),
    IsShortExact f g →
      a (exactClassOf P B) = a (exactClassOf P A) + a (exactClassOf P C)

/-- An exact-additive class function kills the relation submodule. -/
theorem relations_le_ker_extend (a : IsomorphismClassesWith P → M)
    (ha : IsExactAdditive P a) : exactRelations P ≤ LinearMap.ker (extend a) := by
  apply Submodule.span_le.mpr
  rintro x ⟨A, B, C, f, g, h, rfl⟩
  change extend a _ = 0
  simp only [map_sub, extend, generator, Finsupp.linearCombination_single, one_smul]
  rw [ha A B C f g h, add_sub_cancel_left, sub_self]

/-- The actual descended homomorphism. Its input includes the exact-additivity
proof; this construction supplies no local-constant existence theorem. -/
def lift (a : IsomorphismClassesWith P → M) (ha : IsExactAdditive P a) :
    ExactGrothendieckGroup P →ₗ[ℤ] M :=
  (exactRelations P).liftQ (extend a) (relations_le_ker_extend P a ha)

@[simp]
theorem lift_ofClass (a : IsomorphismClassesWith P → M)
    (ha : IsExactAdditive P a) (c : IsomorphismClassesWith P) :
    lift P a ha (ofClass P c) = a c := by
  simp [lift, ofClass, quotientMap, extend, generator]

@[simp]
theorem lift_ofRepresentation (a : IsomorphismClassesWith P → M)
    (ha : IsExactAdditive P a)
    (A : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}) :
    lift P a ha (ofRepresentation P A) = a (exactClassOf P A) :=
  lift_ofClass P a ha _

/-- A homomorphism is determined by its values on genuine classes. -/
@[ext]
theorem hom_ext {l₁ l₂ : ExactGrothendieckGroup P →ₗ[ℤ] M}
    (h : ∀ c, l₁ (ofClass P c) = l₂ (ofClass P c)) : l₁ = l₂ := by
  have he : l₁.comp (quotientMap P) = l₂.comp (quotientMap P) := by
    apply Finsupp.lhom_ext
    intro c n
    have hn : Finsupp.single c n = n • generator c := by
      simp [generator]
    rw [hn, LinearMap.map_smul, LinearMap.map_smul]
    exact congrArg (fun m => n • m) (h c)
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := (exactRelations P).mkQ_surjective x
  exact LinearMap.congr_fun he v

/-- Every homomorphism is exact-additive on genuine classes. -/
theorem isExactAdditive_of_linearMap (l : ExactGrothendieckGroup P →ₗ[ℤ] M) :
    IsExactAdditive P (fun c => l (ofClass P c)) := by
  intro A B C f g h
  change l (ofRepresentation P B) = l (ofRepresentation P A) + l (ofRepresentation P C)
  rw [ofRepresentation_shortExact P h, map_add]

/-- The universal property, proved in both directions and with uniqueness. -/
theorem existsUnique_lift_iff (a : IsomorphismClassesWith P → M) :
    (∃! l : ExactGrothendieckGroup P →ₗ[ℤ] M, ∀ c, l (ofClass P c) = a c) ↔
      IsExactAdditive P a := by
  constructor
  · rintro ⟨l, hl, _⟩
    have ha := isExactAdditive_of_linearMap P l
    simpa only [hl] using ha
  · intro ha
    refine ⟨lift P a ha, lift_ofClass P a ha, ?_⟩
    intro l hl
    apply hom_ext P
    intro c
    rw [hl, lift_ofClass]

/-- The dimension of a genuine class, before passing to virtual relations. -/
def classDegree (c : IsomorphismClassesWith P) : ℤ :=
  (classRank (forgetPropertyClass P c) : ℤ)

/-- Actual rank-nullity proves that dimension respects every exact relation. -/
theorem classDegree_isExactAdditive : IsExactAdditive P (classDegree P) := by
  intro A B C f g h
  change (B.val.rank : ℤ) = (A.val.rank : ℤ) + (C.val.rank : ℤ)
  rw [rank_eq_add_of_shortExact h, Nat.cast_add]

/-- The genuine integer degree on virtual representations. -/
def degree : ExactGrothendieckGroup P →ₗ[ℤ] ℤ :=
  lift P (classDegree P) (classDegree_isExactAdditive P)

@[simp]
theorem degree_ofRepresentation
    (A : {A : FiniteRepresentation.{uK, uG, uV} K G // P A}) :
    degree P (ofRepresentation P A) = (A.val.rank : ℤ) :=
  lift_ofRepresentation P (classDegree P) (classDegree_isExactAdditive P) A

/-- The actual degree-zero submodule used by induction of virtual dimension zero. -/
def degreeZero : Submodule ℤ (ExactGrothendieckGroup P) := LinearMap.ker (degree P)

@[simp]
theorem mem_degreeZero (x : ExactGrothendieckGroup P) :
    x ∈ degreeZero P ↔ degree P x = 0 := Iff.rfl

end ExactGrothendieckGroup
end Langlands.VirtualRepresentation
