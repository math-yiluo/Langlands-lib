import Mathlib.RepresentationTheory.Character
import Mathlib.CategoryTheory.IsomorphismClasses
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Prod

noncomputable section

open CategoryTheory
open scoped MonoidalCategory TensorProduct

namespace Langlands.FiniteRep

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The actual isomorphism classes of Mathlib's finite-dimensional representations. -/
def RepClass (k : Type u) (G : Type v) [Field k] [Group G] :=
  Quotient (isIsomorphicSetoid (FDRep k G))

/-- The class of a finite-dimensional representation. -/
def classOf (V : FDRep k G) : RepClass k G := Quotient.mk _ V

/-- A representation equivalence gives a categorical isomorphism in `FDRep`. -/
def isoOfEquiv {V W : FDRep k G} (e : Representation.Equiv V.ρ W.ρ) : V ≅ W :=
  Action.mkIso e.toLinearEquiv.toFGModuleCatIso (fun g => by
    ext v
    exact LinearMap.congr_fun (e.isIntertwining' g) v)

/-- The representation equivalence underlying an isomorphism in `FDRep`. -/
def equivOfIso {V W : FDRep k G} (e : V ≅ W) : Representation.Equiv V.ρ W.ρ :=
  Representation.Equiv.mk (FDRep.isoToLinearEquiv e) (fun g => by
    rw [FDRep.Iso.conj_ρ e]
    ext v
    simp)

theorem classOf_eq_iff (V W : FDRep k G) :
    classOf V = classOf W ↔ Nonempty (V ≅ W) :=
  Quotient.eq

/-- Product of representation equivalences, allowing independent carrier universes. -/
def prodEquiv {V : Type*} {V' : Type*} {W : Type*} {W' : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [AddCommGroup W] [Module k W]
    [AddCommGroup W'] [Module k W'] {ρ : Representation k G V}
    {ρ' : Representation k G V'} {σ : Representation k G W} {σ' : Representation k G W'}
    (e : Representation.Equiv ρ ρ') (f : Representation.Equiv σ σ') :
    Representation.Equiv (Representation.prod ρ σ) (Representation.prod ρ' σ') :=
  Representation.Equiv.mk (e.toLinearEquiv.prodCongr f.toLinearEquiv) (by
    intro g
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact LinearMap.congr_fun (e.isIntertwining' g) x.1
    · exact LinearMap.congr_fun (f.isIntertwining' g) x.2)

/-- The trace character, descended through genuine representation isomorphisms. -/
def character : RepClass k G → G → k :=
  Quotient.lift FDRep.character (fun _ _ h => by
    obtain ⟨e⟩ := h
    exact FDRep.char_iso e)

@[simp]
theorem character_classOf (V : FDRep k G) : character (classOf V) = V.character := rfl

/-- The zero-dimensional representation. -/
abbrev zeroRep : FDRep k G :=
  FDRep.of (Representation.trivial k G (Fin 0 → k))

/-- The direct sum, using Mathlib's product representation on `V × W`. -/
def sumRep (V W : FDRep k G) : FDRep k G := FDRep.of (Representation.prod V.ρ W.ρ)

/-- Direct sum respects isomorphisms in both variables. -/
def sumIso {V V' W W' : FDRep k G} (e : V ≅ V') (f : W ≅ W') :
    sumRep V W ≅ sumRep V' W' :=
  isoOfEquiv <| Representation.Equiv.mk
    ((equivOfIso e).toLinearEquiv.prodCongr (equivOfIso f).toLinearEquiv) (fun g => by
      apply LinearMap.ext
      intro x
      apply Prod.ext
      · exact LinearMap.congr_fun ((equivOfIso e).isIntertwining' g) x.1
      · exact LinearMap.congr_fun ((equivOfIso f).isIntertwining' g) x.2)

instance : Zero (RepClass k G) := ⟨classOf zeroRep⟩

instance : Add (RepClass k G) where
  add := Quotient.map₂ sumRep (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨sumIso e f⟩)

@[simp]
theorem classOf_sumRep (V W : FDRep k G) :
    classOf (sumRep V W) = classOf V + classOf W := rfl

/-- Associativity of direct sum, as an actual equivariant linear isomorphism. -/
def sumAssoc (U V W : FDRep k G) :
    sumRep (sumRep U V) W ≅ sumRep U (sumRep V W) :=
  isoOfEquiv <| Representation.Equiv.mk (LinearEquiv.prodAssoc k U V W) (by
    intro g
    ext x
    rfl)

/-- Symmetry of direct sum. -/
def sumComm (V W : FDRep k G) : sumRep V W ≅ sumRep W V :=
  isoOfEquiv <| Representation.Equiv.mk (LinearEquiv.prodComm k V W) (by
    intro g
    ext x
    rfl)

/-- The zero-dimensional representation is a right identity for direct sum. -/
def sumZero (V : FDRep k G) : sumRep V zeroRep ≅ V :=
  isoOfEquiv <| Representation.Equiv.mk LinearEquiv.prodUnique (by
    intro g
    ext x
    rfl)

/-- The direct-sum commutative monoid of actual representation classes. -/
instance : AddCommMonoid (RepClass k G) where
  add_assoc := by
    intro a b c
    induction a using Quotient.inductionOn with | h U =>
      induction b using Quotient.inductionOn with | h V =>
        induction c using Quotient.inductionOn with | h W =>
          exact Quotient.sound ⟨sumAssoc U V W⟩
  zero_add := by
    intro a
    induction a using Quotient.inductionOn with | h V =>
      exact Quotient.sound ⟨(sumComm zeroRep V).trans (sumZero V)⟩
  add_zero := by
    intro a
    induction a using Quotient.inductionOn with | h V =>
      exact Quotient.sound ⟨sumZero V⟩
  add_comm := by
    intro a b
    induction a using Quotient.inductionOn with | h V =>
      induction b using Quotient.inductionOn with | h W =>
        exact Quotient.sound ⟨sumComm V W⟩
  nsmul := nsmulRec

/-- Trace additivity for the direct sum constructor. -/
theorem character_sumRep (V W : FDRep k G) :
    (sumRep V W).character = V.character + W.character := by
  funext g
  exact LinearMap.trace_prodMap' (V.ρ g) (W.ρ g)

/-- The additive trace-character map on representation classes. -/
def characterHom : RepClass k G →+ (G → k) where
  toFun := character
  map_zero' := by
    funext g
    change LinearMap.trace k (Fin 0 → k) ((Representation.trivial k G (Fin 0 → k)) g) = 0
    have h : (Representation.trivial k G (Fin 0 → k)) g = 0 := Subsingleton.elim _ _
    rw [h, map_zero]
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | h V =>
      induction b using Quotient.inductionOn with | h W =>
        exact character_sumRep V W

/-- Tensor product on representation classes. -/
def tensor : RepClass k G → RepClass k G → RepClass k G :=
  Quotient.map₂ (fun V W => V ⊗ W) (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨e ⊗ᵢ f⟩)

/-- Tensor product distributes over direct sum, via the usual linear equivalence. -/
def tensorSumIso (U V W : FDRep k G) :
    U ⊗ sumRep V W ≅ sumRep (U ⊗ V) (U ⊗ W) :=
  isoOfEquiv <| Representation.Equiv.mk (TensorProduct.prodRight k k U V W) (by
    intro g
    change (TensorProduct.prodRight k k U V W).toLinearMap ∘ₗ
        TensorProduct.map (U.ρ g) ((V.ρ g).prodMap (W.ρ g)) =
      ((TensorProduct.map (U.ρ g) (V.ρ g)).prodMap
        (TensorProduct.map (U.ρ g) (W.ρ g))) ∘ₗ
          (TensorProduct.prodRight k k U V W).toLinearMap
    apply TensorProduct.ext'
    intro u v
    simp)

/-- Tensoring with the zero-dimensional representation gives the zero representation. -/
def tensorZeroIso (V : FDRep k G) : V ⊗ zeroRep ≅ zeroRep :=
  isoOfEquiv <| Representation.Equiv.mk
    (LinearEquiv.ofSubsingleton (V ⊗[k] (Fin 0 → k)) (Fin 0 → k)) (by
    intro g
    exact Subsingleton.elim _ _)

theorem tensor_comm (a b : RepClass k G) : tensor a b = tensor b a := by
  induction a using Quotient.inductionOn with | h V =>
    induction b using Quotient.inductionOn with | h W =>
      exact Quotient.sound ⟨β_ V W⟩

theorem tensor_add (a b c : RepClass k G) :
    tensor a (b + c) = tensor a b + tensor a c := by
  induction a using Quotient.inductionOn with | h U =>
    induction b using Quotient.inductionOn with | h V =>
      induction c using Quotient.inductionOn with | h W =>
        exact Quotient.sound ⟨tensorSumIso U V W⟩

@[simp]
theorem tensor_zero (a : RepClass k G) : tensor a 0 = 0 := by
  induction a using Quotient.inductionOn with | h V =>
    exact Quotient.sound ⟨tensorZeroIso V⟩

/-- The tensor product as a biadditive operation on actual representation classes. -/
def tensorHom : RepClass k G →+ (RepClass k G →+ RepClass k G) where
  toFun a := { toFun := tensor a, map_zero' := tensor_zero a, map_add' := tensor_add a }
  map_zero' := by
    ext a
    exact (tensor_comm 0 a).trans (tensor_zero a)
  map_add' := by
    intro a b
    ext c
    change tensor (a + b) c = tensor a c + tensor b c
    rw [tensor_comm (a + b), tensor_add, tensor_comm c a, tensor_comm c b]

/-- Restriction along an actual group homomorphism on representation classes. -/
def restrict {H : Type w} [Group H] (φ : H →* G) : RepClass k G → RepClass k H :=
  Quotient.map (Action.res (FGModuleCat k) φ).obj
    (fun _ _ ⟨e⟩ => ⟨(Action.res (FGModuleCat k) φ).mapIso e⟩)

/-- Restriction is additive for direct sum. -/
def restrictHom {H : Type w} [Group H] (φ : H →* G) :
    RepClass k G →+ RepClass k H where
  toFun := restrict φ
  map_zero' := rfl
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | h V =>
      induction b using Quotient.inductionOn with | h W =>
        rfl

/-- The contragredient representation. -/
abbrev dualRep (V : FDRep k G) : FDRep k G := FDRep.of (Representation.dual V.ρ)

/-- The contragredient respects actual representation isomorphisms. -/
def dualIso {V W : FDRep k G} (e : V ≅ W) : dualRep V ≅ dualRep W :=
  isoOfEquiv <| Representation.Equiv.mk (equivOfIso e.symm).toLinearEquiv.dualMap
    (fun g => by
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro w
      exact congrArg f (LinearMap.congr_fun ((equivOfIso e.symm).isIntertwining' g⁻¹) w).symm)

/-- Contragredient on actual isomorphism classes. -/
def dual : RepClass k G → RepClass k G :=
  Quotient.map dualRep (fun _ _ ⟨e⟩ => ⟨dualIso e⟩)

/-- Duality takes a direct sum to the direct sum of the duals. -/
def dualSumIso (V W : FDRep k G) :
    sumRep (dualRep V) (dualRep W) ≅ dualRep (sumRep V W) :=
  isoOfEquiv <| Representation.Equiv.mk (Module.dualProdDualEquivDual k V W) (by
    intro g
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    rfl)

/-- Contragredient is additive on representation classes. -/
def dualHom : RepClass k G →+ RepClass k G where
  toFun := dual
  map_zero' := by
    apply Quotient.sound
    exact ⟨isoOfEquiv <| Representation.Equiv.mk (LinearEquiv.ofSubsingleton _ _) (by
      intro g
      exact Subsingleton.elim _ _)⟩
  map_add' := by
    intro a b
    induction a using Quotient.inductionOn with | h V =>
      induction b using Quotient.inductionOn with | h W =>
        exact Quotient.sound ⟨(dualSumIso V W).symm⟩

@[simp]
theorem character_tensor (a b : RepClass k G) :
    character (tensor a b) = character a * character b := by
  induction a using Quotient.inductionOn with | h V =>
    induction b using Quotient.inductionOn with | h W =>
      exact FDRep.char_tensor V W

@[simp]
theorem character_dual (a : RepClass k G) (g : G) :
    character (dual a) g = character a g⁻¹ := by
  induction a using Quotient.inductionOn with | h V =>
    exact FDRep.char_dual V g

@[simp]
theorem character_restrict {H : Type w} [Group H] (φ : H →* G)
    (a : RepClass k G) (h : H) : character (restrict φ a) h = character a (φ h) := by
  induction a using Quotient.inductionOn with | h V => rfl

/-- Every character defined here is a class function. -/
theorem character_conj (a : RepClass k G) (g h : G) :
    character a (h * g * h⁻¹) = character a g := by
  induction a using Quotient.inductionOn with | h V =>
    exact FDRep.char_conj V g h

section UniverseTransport

variable {V : Type w} [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- A finite coordinate model in the coefficient-field universe. -/
def ofRepresentation (ρ : Representation k G V) : FDRep k G :=
  FDRep.of (((Module.finBasis k V).equivFun.conjRingEquiv.toMonoidHom).comp ρ)

/-- The coordinate model is equivariantly linearly isomorphic to its source. -/
def modelEquiv (ρ : Representation k G V) :
    Representation.Equiv ρ (ofRepresentation ρ).ρ :=
  Representation.Equiv.mk (Module.finBasis k V).equivFun (by
    intro g
    ext x
    change (Module.finBasis k V).equivFun (ρ g x) =
      (Module.finBasis k V).equivFun
        (ρ g ((Module.finBasis k V).equivFun.symm ((Module.finBasis k V).equivFun x)))
    rw [LinearEquiv.symm_apply_apply])

/-- Class of a finite-dimensional representation in an arbitrary carrier universe. -/
def classOfRepresentation (ρ : Representation k G V) : RepClass k G :=
  classOf (ofRepresentation ρ)

@[simp]
theorem character_classOfRepresentation (ρ : Representation k G V) :
    character (classOfRepresentation ρ) = ρ.character :=
  (Representation.char_iso (modelEquiv ρ)).symm

/-- Changing a representation by an actual equivariant equivalence preserves its class,
even when its source and target carriers live in different universes. -/
theorem classOfRepresentation_congr {W : Type*} [AddCommGroup W] [Module k W]
    [Module.Finite k W] {ρ : Representation k G V} {σ : Representation k G W}
    (e : Representation.Equiv ρ σ) :
    classOfRepresentation ρ = classOfRepresentation σ :=
  Quotient.sound ⟨isoOfEquiv (((modelEquiv ρ).symm.trans e).trans (modelEquiv σ))⟩

/-- Equality of coordinate-model classes is exactly actual representation equivalence. -/
theorem classOfRepresentation_eq_iff {W : Type*} [AddCommGroup W] [Module k W]
    [Module.Finite k W] (ρ : Representation k G V) (σ : Representation k G W) :
    classOfRepresentation ρ = classOfRepresentation σ ↔
      Nonempty (Representation.Equiv ρ σ) := by
  constructor
  · intro h
    obtain ⟨e⟩ := (classOf_eq_iff _ _).mp h
    exact ⟨((modelEquiv ρ).trans (equivOfIso e)).trans (modelEquiv σ).symm⟩
  · rintro ⟨e⟩
    exact classOfRepresentation_congr e

end UniverseTransport

@[simp]
theorem classOfRepresentation_rho (V : FDRep k G) :
    classOfRepresentation V.ρ = classOf V :=
  Quotient.sound ⟨isoOfEquiv (modelEquiv V.ρ).symm⟩

/-- The arbitrary-universe class constructor preserves direct sums. -/
theorem classOfRepresentation_prod {V : Type*} {W : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] [AddCommGroup W] [Module k W] [Module.Finite k W]
    (ρ : Representation k G V) (σ : Representation k G W) :
    classOfRepresentation (Representation.prod ρ σ) =
      classOfRepresentation ρ + classOfRepresentation σ := by
  calc
    _ = classOfRepresentation (sumRep (ofRepresentation ρ) (ofRepresentation σ)).ρ :=
      classOfRepresentation_congr (prodEquiv (modelEquiv ρ) (modelEquiv σ))
    _ = _ := classOfRepresentation_rho _

/-- The complex specialization of the genuine isomorphism-class space. -/
abbrev ComplexRepClass (G : Type v) [Group G] := RepClass ℂ G

end Langlands.FiniteRep
