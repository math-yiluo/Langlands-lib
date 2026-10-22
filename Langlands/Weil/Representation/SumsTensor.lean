import Langlands.Weil.Representation.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.CategoryTheory.Products.Basic

/-! # Binary sums and tensor products on actual finite-dimensional carriers -/

noncomputable section

universe uK uG uV uW uX uY

open CategoryTheory

namespace Langlands.FiniteRepresentation

variable {K : Type uK} {G : Type uG} [Field K] [Monoid G]

/-- The binary direct sum, realized on the product of the actual carriers. -/
def sum (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    FiniteRepresentation.{uK, uG, max uV uW} K G :=
  of (A.representation.prod B.representation)

/-- The tensor product with diagonal group action. -/
def tensor (A : FiniteRepresentation.{uK, uG, uV} K G)
    (B : FiniteRepresentation.{uK, uG, uW} K G) :
    FiniteRepresentation.{uK, uG, max uV uW} K G :=
  of (A.representation.tprod B.representation)

/-- Direct sum of linear intertwiners. -/
def sumMap {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G}
    {C : FiniteRepresentation.{uK, uG, uX} K G}
    {D : FiniteRepresentation.{uK, uG, uY} K G}
    (f : A.representation.IntertwiningMap C.representation)
    (g : B.representation.IntertwiningMap D.representation) :
    (sum A B).representation.IntertwiningMap (sum C D).representation where
  toLinearMap := f.toLinearMap.prodMap g.toLinearMap
  isIntertwining' h := by
    ext x
    exact Prod.ext (Representation.IntertwiningMap.isIntertwining _ _ f h x.1)
      (Representation.IntertwiningMap.isIntertwining _ _ g h x.2)

/-- Tensor product of intertwiners, using Mathlib's existing tensor construction. -/
def tensorMap {A : FiniteRepresentation.{uK, uG, uV} K G}
    {B : FiniteRepresentation.{uK, uG, uW} K G}
    {C : FiniteRepresentation.{uK, uG, uX} K G}
    {D : FiniteRepresentation.{uK, uG, uY} K G}
    (f : A.representation.IntertwiningMap C.representation)
    (g : B.representation.IntertwiningMap D.representation) :
    (tensor A B).representation.IntertwiningMap (tensor C D).representation :=
  f.tensor g

/-- The sum bifunctor, including its identity and composition laws. -/
def sumFunctor :
    (FiniteRepresentation.{uK, uG, uV} K G × FiniteRepresentation.{uK, uG, uW} K G) ⥤
      FiniteRepresentation.{uK, uG, max uV uW} K G where
  obj A := sum A.1 A.2
  map f := (homEquiv _ _).symm (sumMap (homEquiv _ _ f.1) (homEquiv _ _ f.2))
  map_id _ := by apply (homEquiv _ _).injective; ext x; rfl
  map_comp _ _ := by apply (homEquiv _ _).injective; ext x; rfl

/-- The tensor bifunctor, with laws checked on pure tensors. -/
def tensorFunctor :
    (FiniteRepresentation.{uK, uG, uV} K G × FiniteRepresentation.{uK, uG, uW} K G) ⥤
      FiniteRepresentation.{uK, uG, max uV uW} K G where
  obj A := tensor A.1 A.2
  map f := (homEquiv _ _).symm (tensorMap (homEquiv _ _ f.1) (homEquiv _ _ f.2))
  map_id _ := by
    apply (homEquiv _ _).injective
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl
  map_comp _ _ := by
    apply (homEquiv _ _).injective
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    rfl

/-- Binary sum respects genuine representation equivalences. -/
def sumEquiv {A C : FiniteRepresentation.{uK, uG, uV} K G}
    {B D : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A C) (f : Equiv B D) :
    Equiv (sum A B) (sum C D) :=
  equivOfIso (sumFunctor.{uK, uG, uV, uW}.mapIso ((isoOfEquiv e).prod (isoOfEquiv f)))

/-- Tensor product respects genuine representation equivalences. -/
def tensorEquiv {A C : FiniteRepresentation.{uK, uG, uV} K G}
    {B D : FiniteRepresentation.{uK, uG, uW} K G} (e : Equiv A C) (f : Equiv B D) :
    Equiv (tensor A B) (tensor C D) :=
  equivOfIso (tensorFunctor.{uK, uG, uV, uW}.mapIso ((isoOfEquiv e).prod (isoOfEquiv f)))

/-- Binary sums descend to the genuine quotient. -/
def sumClass :
    IsomorphismClasses.{uK, uG, uV} K G → IsomorphismClasses.{uK, uG, uW} K G →
      IsomorphismClasses.{uK, uG, max uV uW} K G :=
  Quotient.map₂ sum (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨sumEquiv e f⟩)

/-- Tensor products descend to the genuine quotient. -/
def tensorClass :
    IsomorphismClasses.{uK, uG, uV} K G → IsomorphismClasses.{uK, uG, uW} K G →
      IsomorphismClasses.{uK, uG, max uV uW} K G :=
  Quotient.map₂ tensor (fun _ _ ⟨e⟩ _ _ ⟨f⟩ => ⟨tensorEquiv e f⟩)

end Langlands.FiniteRepresentation
