/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Coefficient.EtaleCoefficientTransportInterfaces
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison

/-! # Ordinary inverse-image transport of strict coefficient systems

Source: Zheng, Construction 4.1 and Construction 5.15; Stacks Tag 03EL.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf
  SheafOfModules.coefficientQuotientSheaf SheafOfModules.coefficientQuotientMap
  SheafOfModules.siteCoefficientTensor SheafOfModules.siteCoefficientTensorAdj
  AlgebraicGeometry.StrictEtaleCoefficientChange.sheaf
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

private theorem systemHom_ext {T : Scheme.{u}} {O : Type (u + 1)} [CommRing O]
    {ell : O} {M N : strictEtaleCoefficientSystem T O ell} (f g : M ⟶ N)
    (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

section
variable {O O' : Type (u + 1)} [CommRing O] [CommRing O'] {ell : O} {mu : O'}
    {phi : O →+* O'} {index : ℕ →o ℕ}
    {a : StrictEtaleCoefficientChange O O' ell mu phi index}
    {T S : Scheme.{u}} {g : T ⟶ S}
    {PTA : StrictEtaleEvaluation T O ell} {PSA : StrictEtaleEvaluation S O ell}
    {PTB : StrictEtaleEvaluation T O' mu} {PSB : StrictEtaleEvaluation S O' mu}
    (UT : StrictEtaleCoefficientTransport a T PTA PTB)
    (US : StrictEtaleCoefficientTransport a S PSA PSB)
    (A : StrictEtaleOrdinaryImage O ell g) (B : StrictEtaleOrdinaryImage O' mu g)
    (finite : ∀ n, siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf S n) ⋙ (B.lift n).modules ≅
        (A.lift (index n)).modules ⋙ siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf T n))

private theorem insertion_naturality (W : Scheme.{u}) (n : ℕ)
    {M N : strictEtaleLevel W O ell (index n)} (f : M ⟶ N) :
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
        (siteTensorUnitUnderlying (a.sheaf W n) M) ≫
        (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
          ((siteCoefficientTensor.{u + 1, u, u + 1} (a.sheaf W n)).map f) =
      (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map f ≫
        (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).map
          (siteTensorUnitUnderlying (a.sheaf W n) N) := by
  let r := isoWhiskerRight (siteScalarUnderlyingIso (a.sheaf W n))
    (sheafCompose W.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1}))
  have h := congrArg
    ((coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map)
    ((siteCoefficientTensorAdj.{u + 1, u, u + 1} (a.sheaf W n)).unit.naturality f)
  have hr := r.hom.naturality ((siteCoefficientTensor (a.sheaf W n)).map f)
  change (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
      ((SheafOfModules.restrictScalars _).map
        ((siteCoefficientTensor (a.sheaf W n)).map f)) ≫ r.hom.app _ =
      r.hom.app _ ≫ (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        ((siteCoefficientTensor (a.sheaf W n)).map f) at hr
  change ((coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
      ((siteCoefficientTensorAdj (a.sheaf W n)).unit.app M) ≫ r.hom.app _) ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O' mu n).map
        ((siteCoefficientTensor (a.sheaf W n)).map f) =
    (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map f ≫
      (coefficientUnderlying (J := W.smallEtaleTopology) O ell (index n)).map
        ((siteCoefficientTensorAdj (a.sheaf W n)).unit.app N) ≫ r.hom.app _
  rw [Category.assoc, ← hr]
  simpa -implicitDefEqProofs only [Functor.map_comp, Category.assoc, coefficientUnderlying,
    Functor.comp_map, Functor.id_map] using congrArg (fun k ↦ k ≫ r.hom.app
      ((siteCoefficientTensor (a.sheaf W n)).obj N)) h.symm

end

end AlgebraicGeometry
