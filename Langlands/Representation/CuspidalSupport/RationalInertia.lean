import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.Category.Twist
import Langlands.Representation.Category.ConstituentDichotomy
import Langlands.Representation.Category.IrreducibleSubquotientExistence
import Langlands.Representation.Filtration.SubquotientAlgebraProof

/-!
# Actual rational-point inertia classes and their full subcategories

Unramified characters act by the existing same-carrier smooth twist. The
relation is defined using actual isomorphisms, without admissibility. The two
full subcategories quantify over every irreducible actual subquotient, without
finite length. Their product decomposition is a separate assertion.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalInertia1 : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

local instance instRationalInertia2 : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
  rationalPoint_isTopologicalGroup F G

/-- An actual unramified character has open kernel because that kernel contains
 the proved open common rational-character norm kernel. -/
theorem isOpen_rationalUnramifiedCharacter_ker (χ : (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))) :
    IsOpen (χ.val.toMonoidHom.ker : Set (GroupScheme.rationalPoints G)) :=
  Subgroup.isOpen_mono χ.property (isOpen_rationalCommonNormKernel G)

/-- Twist the actual rational-point action by an actual unramified character. -/
abbrev rationalUnramifiedTwist (χ : (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))) (A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :=
  A.twist χ.val.toMonoidHom (isOpen_rationalUnramifiedCharacter_ker G χ)

/-- The trivial actual unramified twist is isomorphic to the original action. -/
def rationalUnramifiedTwistOneIso (A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) :
    rationalUnramifiedTwist G 1 A ≅ A :=
  SmoothRep.twistOneIso _ A

/-- Successive actual unramified twists multiply their characters. -/
def rationalUnramifiedTwistMulIso (χ ψ : (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))) (A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) :
    rationalUnramifiedTwist G χ (rationalUnramifiedTwist G ψ A) ≅
      rationalUnramifiedTwist G (χ * ψ) A :=
  SmoothRep.twistTwistIso χ.val.toMonoidHom ψ.val.toMonoidHom _ _ _ A

/-- Actual unramified twisting preserves irreducibility, with no admissibility
 premise. -/
theorem isIrreducible_rationalUnramifiedTwist_iff (χ : (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))) (A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) :
    (rationalUnramifiedTwist G χ A).IsIrreducible ↔ A.IsIrreducible :=
  SmoothRep.isIrreducible_twist_iff χ.val.toMonoidHom _ A

/-- Two actual smooth actions are inertia-related when the second is isomorphic
 to an unramified twist of the first. For irreducible objects this is Renard's
 inertia relation. -/
def IsRationalInertiaRelated (A B : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) : Prop :=
  ∃ χ : (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul)), Nonempty (B ≅ rationalUnramifiedTwist G χ A)

variable {G}

/-- Isomorphic smooth objects are inertia-related. -/
theorem IsRationalInertiaRelated.of_iso {A B : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))} (e : A ≅ B) :
    IsRationalInertiaRelated G A B :=
  ⟨1, ⟨e.symm ≪≫ (rationalUnramifiedTwistOneIso G A).symm⟩⟩

/-- Reflexivity uses the trivial character. -/
theorem IsRationalInertiaRelated.refl (A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) :
    IsRationalInertiaRelated G A A :=
  .of_iso (Iso.refl A)

/-- Symmetry uses the inverse character and the actual twist isomorphisms. -/
theorem IsRationalInertiaRelated.symm {A B : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))}
    (h : IsRationalInertiaRelated G A B) : IsRationalInertiaRelated G B A := by
  obtain ⟨χ, ⟨e⟩⟩ := h
  have e1 : rationalUnramifiedTwist G χ⁻¹ (rationalUnramifiedTwist G χ A) ≅ A := by
    simpa only [inv_mul_cancel] using
      (rationalUnramifiedTwistMulIso G χ⁻¹ χ A) ≪≫
        (by simpa only [inv_mul_cancel] using rationalUnramifiedTwistOneIso G A)
  exact ⟨χ⁻¹, ⟨e1.symm ≪≫
    SmoothRep.twistIso (χ⁻¹).val.toMonoidHom
      (isOpen_rationalUnramifiedCharacter_ker G χ⁻¹) e.symm⟩⟩

/-- Transitivity uses the product character. -/
theorem IsRationalInertiaRelated.trans {A B C : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))}
    (hAB : IsRationalInertiaRelated G A B) (hBC : IsRationalInertiaRelated G B C) :
    IsRationalInertiaRelated G A C := by
  obtain ⟨χ, ⟨e⟩⟩ := hAB
  obtain ⟨ψ, ⟨f⟩⟩ := hBC
  exact ⟨ψ * χ, ⟨f ≪≫
    SmoothRep.twistIso ψ.val.toMonoidHom
      (isOpen_rationalUnramifiedCharacter_ker G ψ) e ≪≫
    rationalUnramifiedTwistMulIso G ψ χ A⟩⟩

/-- Changing the orbit representative does not change the inertia relation. -/
theorem IsRationalInertiaRelated.iff_left {A B C : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))}
    (h : IsRationalInertiaRelated G A B) :
    IsRationalInertiaRelated G A C ↔ IsRationalInertiaRelated G B C :=
  ⟨fun hAC => h.symm.trans hAC, fun hBC => h.trans hBC⟩

variable (G)

/-- Inertia equivalence on actual irreducible smooth objects. No admissibility
 condition or choice of an irreducible representative is imposed. -/
def rationalIrreducibleInertiaSetoid : Setoid {A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) // A.IsIrreducible} where
  r A B := IsRationalInertiaRelated G A.val B.val
  iseqv := ⟨fun A => .refl A.val, fun h => h.symm, fun h h' => h.trans h'⟩

/-- The actual inertia classes of irreducible smooth rational-point actions,
 at a fixed carrier universe. -/
def RationalIrreducibleInertiaClass :=
  Quotient (rationalIrreducibleInertiaSetoid.{uF, uV} G)

/-- Send an actual irreducible smooth object to its inertia class. -/
def rationalIrreducibleInertiaClass (A : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) (hA : A.IsIrreducible) :
    RationalIrreducibleInertiaClass.{uF, uV} G :=
  Quotient.mk _ ⟨A, hA⟩

/-- Equality of inertia classes is exactly actual unramified-twist equivalence. -/
theorem rationalIrreducibleInertiaClass_eq_iff (A B : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)))
    (hA : A.IsIrreducible) (hB : B.IsIrreducible) :
    rationalIrreducibleInertiaClass G A hA = rationalIrreducibleInertiaClass G B hB ↔
      IsRationalInertiaRelated G A B :=
  Quotient.eq

/-- Every irreducible actual subquotient belongs to the fixed inertia orbit.
 For an irreducible supercuspidal base this is Renard's `M(G)_[π]` property. -/
def rationalInertiaBlockProperty (π : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) : ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :=
  fun A => ∀ D : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)), D.IsIrreducible → SmoothRep.IsSubquotient D A →
    IsRationalInertiaRelated G π D

/-- No irreducible actual subquotient belongs to the fixed inertia orbit.
 This is the complementary object property in Renard VI.3.3. -/
def rationalInertiaComplementProperty (π : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) : ObjectProperty (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)) :=
  fun A => ∀ D : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G)), D.IsIrreducible → SmoothRep.IsSubquotient D A →
    ¬ IsRationalInertiaRelated G π D

/-- The full smooth category with all irreducible subquotients in `[π]`. -/
abbrev RationalInertiaBlock (π : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) :=
  (rationalInertiaBlockProperty G π).FullSubcategory

/-- The full smooth category with no irreducible subquotient in `[π]`. -/
abbrev RationalInertiaComplement (π : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))) :=
  (rationalInertiaComplementProperty G π).FullSubcategory

variable {G} {π A B : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))}

/-- The block property is closed under actual subquotients. -/
theorem rationalInertiaBlockProperty_of_isSubquotient
    (hA : rationalInertiaBlockProperty G π A) (hBA : SmoothRep.IsSubquotient B A) :
    rationalInertiaBlockProperty G π B :=
  fun D hD hDB => hA D hD (smoothSubquotientTransitivity ℂ _ A B D hDB hBA)

/-- The complement property is closed under actual subquotients. -/
theorem rationalInertiaComplementProperty_of_isSubquotient
    (hA : rationalInertiaComplementProperty G π A) (hBA : SmoothRep.IsSubquotient B A) :
    rationalInertiaComplementProperty G π B :=
  fun D hD hDB => hA D hD (smoothSubquotientTransitivity ℂ _ A B D hDB hBA)

/-- The block property is invariant under an isomorphism of ambient objects. -/
theorem rationalInertiaBlockProperty_of_iso
    (hA : rationalInertiaBlockProperty G π A) (e : B ≅ A) :
    rationalInertiaBlockProperty G π B :=
  fun D hD hDB => hA D hD (hDB.of_iso_right e)

/-- The complement property is invariant under an isomorphism of ambient objects. -/
theorem rationalInertiaComplementProperty_of_iso
    (hA : rationalInertiaComplementProperty G π A) (e : B ≅ A) :
    rationalInertiaComplementProperty G π B :=
  fun D hD hDB => hA D hD (hDB.of_iso_right e)

/-- The block property is closed under extensions in the actual submodule model. -/
theorem rationalInertiaBlockProperty_of_subrepresentation_quotient
    (S : Subrepresentation A.representation)
    (hS : rationalInertiaBlockProperty G π (SmoothRep.subrepresentation A S))
    (hQ : rationalInertiaBlockProperty G π (SmoothRep.quotient A S)) :
    rationalInertiaBlockProperty G π A :=
  fun D hD hDA => (SmoothRep.irreducibleSubquotient_dichotomy hD hDA S).elim
    (hS D hD) (hQ D hD)

/-- The complement property is closed under extensions in the same model. -/
theorem rationalInertiaComplementProperty_of_subrepresentation_quotient
    (S : Subrepresentation A.representation)
    (hS : rationalInertiaComplementProperty G π (SmoothRep.subrepresentation A S))
    (hQ : rationalInertiaComplementProperty G π (SmoothRep.quotient A S)) :
    rationalInertiaComplementProperty G π A :=
  fun D hD hDA => (SmoothRep.irreducibleSubquotient_dichotomy hD hDA S).elim
    (hS D hD) (hQ D hD)

/-- The block depends only on the base inertia orbit. -/
theorem rationalInertiaBlockProperty_iff_of_related {π' : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))}
    (h : IsRationalInertiaRelated G π π') :
    rationalInertiaBlockProperty G π A ↔ rationalInertiaBlockProperty G π' A := by
  constructor
  · intro hA D hD hDA
    exact h.iff_left.mp (hA D hD hDA)
  · intro hA D hD hDA
    exact h.iff_left.mpr (hA D hD hDA)

/-- The complement also depends only on the base inertia orbit. -/
theorem rationalInertiaComplementProperty_iff_of_related {π' : (SmoothRep.{0, uF, uV} ℂ (GroupScheme.rationalPoints G))}
    (h : IsRationalInertiaRelated G π π') :
    rationalInertiaComplementProperty G π A ↔
      rationalInertiaComplementProperty G π' A := by
  constructor
  · intro hA D hD hDA hπ'D
    exact hA D hD hDA (h.iff_left.mpr hπ'D)
  · intro hA D hD hDA hπD
    exact hA D hD hDA (h.iff_left.mp hπD)

/-- An object in both full subcategories is zero as a vector space. This uses
 existence of irreducible subquotients, not a finite-length assumption. -/
theorem subsingleton_of_rationalInertiaBlock_and_complement
    (hA : rationalInertiaBlockProperty G π A)
    (hA' : rationalInertiaComplementProperty G π A) : Subsingleton A := by
  rcases subsingleton_or_nontrivial A with h | h
  · exact h
  · let := h
    obtain ⟨D, hD, hDA⟩ := SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial A
    exact False.elim (hA' D hD hDA (hA D hD hDA))

end Langlands.CuspidalSupport
