/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import WeilConjectures.AlgebraicGeometry.PointModelRestrictionModule
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.ConstantSliceModuleEncoding
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Transport of a constant slice presentation to internal modules

Source: Stacks, Tags 03CY and 00YV; the encoding comparison in
`lem-sfb-discrete-constant-presentation-lifting`, step 1.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralModelsStacks

-- Supply finite biproducts in the abstract abelian categories used below.
attribute [local instance] Abelian.hasFiniteBiproducts
-- The comparison is pointwise, so the categorical calculation keeps encodings abstract.
attribute [local irreducible] smallModules coefficientModelFixedScalars
  Scheme.coefficientProEtaleFixedModulePullback CondensedRing.upperStar
  CondensedRing.lowerStar upperStar lowerStar CategoryTheory.Sheaf.monoidalCategory

private theorem transport_cokernel
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ≌ D) (P Q M : C) (P' Q' : D)
    (eP : E.functor.obj P ≅ P') (eQ : E.functor.obj Q ≅ Q')
    (q : P' ⟶ Q') (eM : E.functor.obj M ≅ cokernel q) :
    ∃ a : P ⟶ Q, Nonempty (M ≅ cokernel a) := by
  let a := E.functor.preimage (eP.hom ≫ q ≫ eQ.inv)
  have ha : E.functor.map a ≫ eQ.hom = eP.hom ≫ q := by
    simp [a]
  let b : E.functor.obj (cokernel a) ≅ cokernel q :=
    PreservesCokernel.iso E.functor a ≪≫
      cokernel.mapIso _ _ eP eQ ha
  exact ⟨a, ⟨E.functor.preimageIso (eM ≪≫ b.symm)⟩⟩

private noncomputable def free_image
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (k : Type (u + 1)) [CommRing k]
    (E : C ≌ D) (F : ModuleCat.{u + 1} k ⥤ D)
    [F.Additive] [PreservesFiniteColimits F]
    (R : C) (eR : E.functor.obj R ≅ F.obj (ModuleCat.of k k)) (r : ℕ) :
    E.functor.obj (⨁ fun _ : Fin r ↦ R) ≅
      F.obj (ModuleCat.of k (Fin r → k)) := by
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products E.functor
  exact E.functor.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ eR) ≪≫
    (F.mapBiproduct (fun _ : Fin r ↦ ModuleCat.of k k)).symm ≪≫
    F.mapIso (biproduct.isoProduct _ ≪≫ ModuleCat.piIsoPi _)

/-- A displayed constant presentation on a slice gives a finite free presentation of
its internal inverse image on the underlying scheme. This is an encoding comparison;
it makes no claim that the entries of the internal matrix descend to the condensed point.
It applies to any condensed coefficient ring, provided the specified constant-ring
identification on X exists.

Source: Stacks, Modules on Sites, Tag 03CY; Sites, Tag 00YV; the first step of
`lem-sfb-discrete-constant-presentation-lifting`.
(auxiliary; not a blueprint node).

Proof: reconstruct internal modules as sectionwise modules and transport to the
coefficient-sized site. Restriction along c is an equivalence of module categories.
Restriction from modules over the constant ring sheaf to fixed k-scalars is the
constant-ring module equivalence. All three equivalences identify regular modules,
finite sums and cokernels. Compare the fixed-scalar inverse image with the internal
inverse image by conjugating the sectionwise direct-image comparison through their
adjunctions. The coefficient isomorphism in this comparison is the pullback of c;
it need not be scalar-normalized. Localize at U, using the weakly-etale slice-site
equivalence and its transport through AsSmall. The resulting equivalence sends the
internal regular module to the constant regular k-module on the slice. Thus the
inverse image of the displayed constant finite matrix q is a morphism a between
internal free modules of the same ranks. Equivalences and constant sheafification
preserve its cokernel. Apply the inverse equivalence to hN to obtain the asserted
isomorphism. Zero ranks and the empty scheme use the same finite-colimit argument. -/
theorem constant_slice_internal_presentation
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type (u + 1)) [CommRing k]
    (c : ConstantCompletion.constant (Scheme.coefficientProEtaleModelTopology.{u, u} X) k ≅
      smallRing X (condensedRingObj Λ X))
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))
    (U : Scheme.coefficientProEtaleSiteModel.{u, u} Y)
    (m n : ℕ)
    (q : ModuleCat.of k (Fin m → k) ⟶ ModuleCat.of k (Fin n → k))
    (hN : Nonempty (((Scheme.coefficientProEtaleFixedModulePullback.{u, u} f k).obj
          ((coefficientModelFixedScalars _ k).obj
            ((smallModules X (condensedRingObj Λ X) ⋙
              ConstantCompletion.res c.hom).obj N))).over U ≅
      (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
        (ModuleCat.{u + 1} k)).obj (cokernel q))) :
    ∃ a : Mod.finiteFree (condensedRingObj Λ (AsSmall.down.obj U).left) m ⟶
        Mod.finiteFree (condensedRingObj Λ (AsSmall.down.obj U).left) n,
      Nonempty (pointModelRestriction Λ f N (AsSmall.down.obj U).hom ≅ cokernel a) := by
  classical
  obtain ⟨E, e, ⟨eR⟩⟩ := constant_slice_module_encoding f Λ k c U
  let F := constantSheaf
    ((Scheme.coefficientProEtaleModelTopology.{u, u} Y).over U)
    (ModuleCat.{u + 1} k)
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  let R := Mod.regular (condensedRingObj Λ (AsSmall.down.obj U).left)
  let b (r : ℕ) := free_image k E F R eR r
  let q' := F.map q
  obtain ⟨h⟩ := hN
  obtain ⟨eN⟩ := e N
  let h' : E.functor.obj (pointModelRestriction Λ f N (AsSmall.down.obj U).hom) ≅
      cokernel q' :=
    eN ≪≫ h ≪≫ PreservesCokernel.iso F q
  exact transport_cokernel E _ _ _ _ _ (b m) (b n) q' h'

end AlgebraicGeometry.ProEtale.IntegralModelsStacks
