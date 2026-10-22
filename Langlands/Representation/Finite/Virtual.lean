import Langlands.Representation.Finite.Induction
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.LinearAlgebra.FreeModule.PID

noncomputable section

open CategoryTheory

namespace Langlands.FiniteRep

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The split integral representation Grothendieck group: the group completion of
the direct-sum monoid of actual finite-dimensional representation classes. -/
abbrev VirtualRep (k : Type u) (G : Type v) [Field k] [Group G] :=
  Algebra.GrothendieckAddGroup (RepClass k G)

/-- The canonical map from actual representation classes to virtual representations. -/
abbrev ofClass : RepClass k G →+ VirtualRep k G := Algebra.GrothendieckAddGroup.of

section GroupCompletion

variable {M : Type*} [AddCommMonoid M] {A : Type*} [AddCommGroup A]

@[simp]
theorem completionLift_of (f : M →+ A) (a : M) :
    Algebra.GrothendieckAddGroup.lift f (Algebra.GrothendieckAddGroup.of a) = f a :=
  DFunLike.congr_fun (Algebra.GrothendieckAddGroup.lift.symm_apply_apply f) a

/-- Uniqueness of a map from the group completion, proved from its universal property. -/
theorem completionHom_ext {f g : Algebra.GrothendieckAddGroup M →+ A}
    (h : ∀ a, f (Algebra.GrothendieckAddGroup.of a) =
      g (Algebra.GrothendieckAddGroup.of a)) : f = g :=
  Algebra.GrothendieckAddGroup.lift.symm.injective (AddMonoidHom.ext h)

end GroupCompletion

/-- Every virtual representation is a difference of actual representation classes. -/
theorem virtualRep_exists_difference (x : VirtualRep k G) :
    ∃ a b : RepClass k G, x = ofClass a - ofClass b := by
  let s := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid (RepClass k G))).sec x
  refine ⟨s.1, s.2, ?_⟩
  have hid : Algebra.GrothendieckAddGroup.lift (ofClass (k := k) (G := G)) =
      AddMonoidHom.id (VirtualRep k G) := by
    apply completionHom_ext
    intro a
    exact completionLift_of _ a
  simpa only [hid, AddMonoidHom.id_apply] using
    Algebra.GrothendieckAddGroup.lift_apply (ofClass (k := k) (G := G)) x

/-- Integral character realization by the trace of actual representations and additivity. -/
def virtualCharacter : VirtualRep k G →ₗ[ℤ] (G → k) :=
  (Algebra.GrothendieckAddGroup.lift (characterHom (k := k) (G := G))).toIntLinearMap

@[simp]
theorem virtualCharacter_ofClass (a : RepClass k G) :
    virtualCharacter (k := k) (G := G) (ofClass a) = character a := completionLift_of _ _

/-- Integral virtual characters, as the actual image of the representation group. -/
def virtualCharacters : Submodule ℤ (G → k) := LinearMap.range virtualCharacter

/-- Character realization with codomain its genuine integral image. -/
def realizeCharacter : VirtualRep k G →ₗ[ℤ] virtualCharacters (k := k) (G := G) :=
  (virtualCharacter (k := k) (G := G)).rangeRestrict

/-- Surjectivity onto the image is intrinsic to realization and does not assert injectivity. -/
theorem realizeCharacter_surjective :
    Function.Surjective (realizeCharacter (k := k) (G := G)) :=
  LinearMap.surjective_rangeRestrict _

/-- The realized virtual characters are exactly differences of actual trace characters. -/
theorem mem_virtualCharacters_iff (f : G → k) :
    f ∈ virtualCharacters (k := k) (G := G) ↔
      ∃ a b : RepClass k G, f = character a - character b := by
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
    exact ⟨a, b, by simp only [map_sub, virtualCharacter_ofClass]⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨ofClass a - ofClass b, by simp only [map_sub, virtualCharacter_ofClass]⟩

/-- The universal extension of an additive operation on actual representation classes. -/
def virtualMap {H : Type w} [Group H] (f : RepClass k G →+ RepClass k H) :
    VirtualRep k G →ₗ[ℤ] VirtualRep k H :=
  (Algebra.GrothendieckAddGroup.lift (ofClass.comp f)).toIntLinearMap

@[simp]
theorem virtualMap_ofClass {H : Type w} [Group H]
    (f : RepClass k G →+ RepClass k H) (a : RepClass k G) :
    virtualMap f (ofClass a) = ofClass (f a) := completionLift_of _ _

/-- Contragredient on the split Grothendieck group. -/
def virtualDual : VirtualRep k G →ₗ[ℤ] VirtualRep k G := virtualMap dualHom

/-- Restriction on the split Grothendieck group. -/
def virtualRestrict {H : Type w} [Group H] (φ : H →* G) :
    VirtualRep k G →ₗ[ℤ] VirtualRep k H := virtualMap (restrictHom φ)

/-- Finite-index induction on the split Grothendieck group. -/
def virtualInduce (S : Subgroup G) [S.FiniteIndex] :
    VirtualRep k S →ₗ[ℤ] VirtualRep k G := virtualMap (induceHom S)

/-- Tensoring by an actual class extends additively in the virtual argument. -/
def tensorClassVirtual : RepClass k G →+ (VirtualRep k G →+ VirtualRep k G) where
  toFun a := Algebra.GrothendieckAddGroup.lift (ofClass.comp (tensorHom a))
  map_zero' := by
    apply completionHom_ext
    intro a
    change Algebra.GrothendieckAddGroup.lift (ofClass.comp (tensorHom 0))
      (Algebra.GrothendieckAddGroup.of a) = 0
    rw [completionLift_of]
    simp
  map_add' := by
    intro a b
    apply completionHom_ext
    intro c
    change Algebra.GrothendieckAddGroup.lift (ofClass.comp (tensorHom (a + b)))
      (Algebra.GrothendieckAddGroup.of c) =
      Algebra.GrothendieckAddGroup.lift (ofClass.comp (tensorHom a))
        (Algebra.GrothendieckAddGroup.of c) +
      Algebra.GrothendieckAddGroup.lift (ofClass.comp (tensorHom b))
        (Algebra.GrothendieckAddGroup.of c)
    rw [completionLift_of, completionLift_of, completionLift_of]
    simp

/-- The biadditive tensor product of virtual representations. -/
def virtualTensor : VirtualRep k G →+ (VirtualRep k G →+ VirtualRep k G) :=
  Algebra.GrothendieckAddGroup.lift tensorClassVirtual

@[simp]
theorem virtualTensor_ofClass (a b : RepClass k G) :
    virtualTensor (ofClass a) (ofClass b) = ofClass (tensor a b) := by
  change Algebra.GrothendieckAddGroup.lift tensorClassVirtual
    (Algebra.GrothendieckAddGroup.of a) (ofClass b) = _
  rw [completionLift_of]
  change Algebra.GrothendieckAddGroup.lift (ofClass.comp (tensorHom a))
    (Algebra.GrothendieckAddGroup.of b) = _
  rw [completionLift_of]
  rfl

/-- Realization of a virtual contragredient is inverse pullback of its trace character. -/
theorem virtualCharacter_dual (x : VirtualRep k G) (g : G) :
    virtualCharacter (k := k) (G := G) (virtualDual x) g =
      virtualCharacter (k := k) (G := G) x g⁻¹ := by
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  simp only [map_sub, virtualDual, virtualMap_ofClass, virtualCharacter_ofClass, Pi.sub_apply]
  exact congrArg₂ (· - ·) (character_dual a g) (character_dual b g)

/-- Character realization commutes with group-homomorphism restriction. -/
theorem virtualCharacter_restrict {H : Type w} [Group H] (φ : H →* G)
    (x : VirtualRep k G) (h : H) :
    virtualCharacter (k := k) (G := H) (virtualRestrict φ x) h =
      virtualCharacter (k := k) (G := G) x (φ h) := by
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  simp only [map_sub, virtualRestrict, virtualMap_ofClass, virtualCharacter_ofClass, Pi.sub_apply]
  exact congrArg₂ (· - ·) (character_restrict φ a h) (character_restrict φ b h)

/-- Virtual tensor product realizes as pointwise multiplication of trace characters. -/
theorem virtualCharacter_tensor (x y : VirtualRep k G) :
    virtualCharacter (k := k) (G := G) (virtualTensor x y) =
      virtualCharacter (k := k) (G := G) x * virtualCharacter (k := k) (G := G) y := by
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  obtain ⟨c, d, rfl⟩ := virtualRep_exists_difference y
  simp only [map_sub, AddMonoidHom.sub_apply, virtualTensor_ofClass,
    virtualCharacter_ofClass, character_tensor]
  ring

/-- Virtual trace characters remain class functions. -/
theorem virtualCharacter_conj (x : VirtualRep k G) (g h : G) :
    virtualCharacter (k := k) (G := G) x (h * g * h⁻¹) =
      virtualCharacter (k := k) (G := G) x g := by
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  simp only [map_sub, virtualCharacter_ofClass, Pi.sub_apply, character_conj]

/-- An actual one-dimensional representation associated with a unit-valued character. -/
def oneDimensional {H : Type w} [Group H] (χ : H →* kˣ) : FDRep k H :=
  FDRep.of
    { toFun h := (χ h : k) • (LinearMap.id : k →ₗ[k] k)
      map_one' := by ext; simp
      map_mul' a b := by
        apply LinearMap.ext
        intro x
        simp [mul_smul, mul_comm, mul_left_comm] }

@[simp]
theorem oneDimensional_finrank {H : Type w} [Group H] (χ : H →* kˣ) :
    Module.finrank k (oneDimensional χ) = 1 := Module.finrank_self k

@[simp]
theorem character_oneDimensional {H : Type w} [Group H] (χ : H →* kˣ) (h : H) :
    (oneDimensional χ).character h = (χ h : k) := by
  change LinearMap.trace k k ((χ h : k) • LinearMap.id) = _
  simp

/-- On the one-dimensional scalar space, evaluation at `1` recovers the unit character. -/
def scalarCharacter {H : Type w} [Group H] (ρ : Representation k H k) : H →* kˣ :=
  MonoidHom.toHomUnits
    { toFun h := ρ h 1
      map_one' := by simp
      map_mul' a b := by
        rw [map_mul, Module.End.mul_apply]
        calc
          ρ a (ρ b 1) = ρ a ((ρ b 1) • (1 : k)) := by simp
          _ = (ρ b 1) • ρ a 1 := map_smul _ _ _
          _ = ρ a 1 * ρ b 1 := mul_comm _ _ }

/-- The scalar action and the action recovered from its unit character agree. -/
def scalarCharacterEquiv {H : Type w} [Group H] (ρ : Representation k H k) :
    Representation.Equiv ρ (oneDimensional (scalarCharacter ρ)).ρ :=
  Representation.Equiv.mk (LinearEquiv.refl k k) (by
    intro h
    apply LinearMap.ext_ring
    change ρ h 1 = (ρ h 1) * 1
    exact (mul_one _).symm)

/-- Every one-dimensional representation is isomorphic to one of the scalar
representations used to generate the induced-character lattice. -/
theorem exists_oneDimensional_iso {H : Type w} [Group H] (V : FDRep k H)
    (hV : Module.finrank k V = 1) :
    ∃ χ : H →* kˣ, Nonempty (V ≅ oneDimensional χ) := by
  let e : V ≃ₗ[k] k := (Module.nonempty_linearEquiv_of_finrank_eq_one hV).some.symm
  let ρ : Representation k H k := e.conjRingEquiv.toMonoidHom.comp V.ρ
  let hρ : Representation.Equiv V.ρ ρ := Representation.Equiv.mk e (by
    intro h
    apply LinearMap.ext
    intro v
    change e (V.ρ h v) = e (V.ρ h (e.symm (e v)))
    rw [LinearEquiv.symm_apply_apply])
  exact ⟨scalarCharacter ρ, ⟨isoOfEquiv (hρ.trans (scalarCharacterEquiv ρ))⟩⟩

section FiniteGroup

variable [Finite G]

/-- The finite family of genuine one-dimensional subgroup data. -/
abbrev MonomialDatum (k : Type u) (G : Type v) [Field k] [Group G] :=
  Σ S : Subgroup G, S →* kˣ

/-- An induced character is defined by the actual induced finite-dimensional action. -/
def inducedCharacter (d : MonomialDatum k G) : G → k :=
  character (induce d.1 (classOf (oneDimensional d.2)))

/-- The integral span of characters of actual rank-one subgroup inductions. -/
def inducedCharacterLattice : Submodule ℤ (G → k) :=
  Submodule.span ℤ (Set.range (inducedCharacter (k := k) (G := G)))

/-- The generators are exactly characters induced from all actual rank-one subgroup
representations, not merely a selected subset of such representations. -/
theorem mem_range_inducedCharacter_iff (f : G → k) :
    f ∈ Set.range (inducedCharacter (k := k) (G := G)) ↔
      ∃ (S : Subgroup G) (V : FDRep k S), Module.finrank k V = 1 ∧
        character (induce S (classOf V)) = f := by
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d.1, oneDimensional d.2, oneDimensional_finrank d.2, rfl⟩
  · rintro ⟨S, V, hV, hchar⟩
    obtain ⟨χ, he⟩ := exists_oneDimensional_iso V hV
    refine ⟨⟨S, χ⟩, ?_⟩
    change character (induce S (classOf (oneDimensional χ))) = f
    rw [← (classOf_eq_iff V (oneDimensional χ)).mpr he]
    exact hchar

/-- Each inducing datum has a genuine virtual representation realizing its character. -/
theorem inducedCharacter_mem_virtualCharacters (d : MonomialDatum k G) :
    inducedCharacter d ∈ virtualCharacters (k := k) (G := G) := by
  exact ⟨ofClass (induce d.1 (classOf (oneDimensional d.2))), virtualCharacter_ofClass _⟩

/-- The induced-character integral span lies in the actual character realization. -/
theorem inducedCharacterLattice_le :
    inducedCharacterLattice (k := k) (G := G) ≤ virtualCharacters := by
  apply Submodule.span_le.mpr
  rintro _ ⟨d, rfl⟩
  exact inducedCharacter_mem_virtualCharacters d

/-- There are finitely many subgroup/unit-character pairs for a finite group over a field. -/
instance finiteMonomialDatum : Finite (MonomialDatum k G) := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun S : Subgroup G => (S : Set G)) SetLike.coe_injective
  infer_instance

/-- The induced-character lattice is finitely generated over the integers. -/
instance finiteInducedCharacterLattice :
    Module.Finite ℤ (inducedCharacterLattice (k := k) (G := G)) :=
  Module.Finite.iff_fg.mpr (Submodule.fg_span (Set.finite_range _))

/-- In characteristic zero this integral span is a free, finitely generated abelian group.
No spanning or faithfulness assertion for the whole representation group is used. -/
instance freeInducedCharacterLattice [CharZero k] :
    Module.Free ℤ (inducedCharacterLattice (k := k) (G := G)) :=
  Module.free_of_finite_type_torsion_free'

end FiniteGroup

/-- Complex virtual representations with the genuine split Grothendieck construction. -/
abbrev ComplexVirtualRep (G : Type v) [Group G] := VirtualRep ℂ G

end Langlands.FiniteRep
