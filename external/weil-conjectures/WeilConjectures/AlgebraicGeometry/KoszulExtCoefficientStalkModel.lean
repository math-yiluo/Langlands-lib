/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulQuotientCoefficientComplex
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import WeilConjectures.AlgebraicGeometry.KoszulExtCoefficientAffineModel
import WeilConjectures.AlgebraicGeometry.AffineModelTensorPullbackStalk

/-! # A commuting stalk model for Koszul coefficient reduction

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry

/-- The finite free affine model identifies the *morphism* on Ext stalks with
extension of scalars of the algebraic coefficient reduction. This statement does
not assert that the algebraic coefficient reduction is an isomorphism. The cohomology degree `m`
is independent of the sequence length `n`.

Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext, affine Koszul
resolution and coefficient comparison.
(blueprint: new-j3-koszul-ext-coefficient-stalk-model).

Proof: Let A=O_Y(U) and I=ker(i)(U). The quotient-spectrum description of a closed
immersion identifies the closed preimage of U with Spec(A/I). Use the quotient
augmentation of the finite free Koszul resolution, sheafify it, and extend from
chain degrees to the corresponding nonpositive cochain degrees. Every exterior
term is finite free by the standard exterior basis and terms outside 0,...,n
vanish. Restriction of derived internal Hom and the bounded finite free Hom
model compute the two degree-m Ext objects by the sheafifications of Hom(K,A) and
Hom(K,A/I), with the signed precomposition differential. Use the same resolution
and the same K-injective comparison for both coefficient objects. The adjunction
unit O_Y -> i_*O_Z is the quotient homomorphism on U, so naturality in the second
argument gives the reduction-of-values cochain morphism, not just an object
isomorphism. Exact associated-module sheafification commutes with cohomology.
On stalks it is localization of these A-modules. The tensor pullback stalk is
O_Z,z tensor over O_Y,i(z) with that localization, which by associativity of
tensor products is O_Z,z tensor over A with the algebraic cohomology module.
Restriction to V identifies O_V,z with O_Z,z and does not change the stalk.
These constructions give the two additive equivalences and the displayed
commuting equation on pure tensors, hence on all elements by additivity.
Representatives in the supplied derived universe are compared through the
common K-injective model; no comparison of distinct derived universes is
assumed. The construction works for n=0 and for every point of the chart. -/
theorem koszulExtCoefficient_stalk_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (V : Z.Opens) (n m : ℕ) (z : V.toScheme)
    (U : Y.affineOpens) (hzU : i z.1 ∈ U.1) (f : Fin n → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let F := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).obj
        (H.obj (op (S.obj B), S.obj (SheafOfModules.unit Y.ringCatSheaf)))
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let c : F ⟶ G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).map
        (H.map (𝟙 (op (S.obj B)), S.map a))
    let φ := (Scheme.Modules.restrictFunctor V.ι).map
      ((Scheme.Modules.tensorPullback i).map c)
    let A := (Γ(Y, U.1) : Type u)
    let R := (V.toScheme.presheaf.stalk z : Type u)
    let ρ : A →+* R := ((Y.presheaf.germ U.1 (i z.1) hzU) ≫
      i.stalkMap z.1 ≫ V.ι.stalkMap z).hom
    letI : Algebra A R := ρ.toAlgebra
    ∃ (eF : ((Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.tensorPullback i).obj F)).presheaf.stalk z ≃+
        R ⊗[A] (ExteriorAlgebra.koszulDualComplex A n f).homology m)
      (eG : ((Scheme.Modules.restrictFunctor V.ι).obj
        ((Scheme.Modules.tensorPullback i).obj G)).presheaf.stalk z ≃+
        R ⊗[A] (ExteriorAlgebra.koszulQuotientDualComplex A (i.ker.ideal U) n f).homology m),
      ∀ x, eG (φ.stalkLinearMap z x) =
        (HomologicalComplex.homologyMap
          (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) m).hom.baseChange R
            (eF x) := by
  obtain ⟨eF, eG, hcomm⟩ :=
    koszulExtCoefficient_affine_model i n m U f hf hreg a ha
  obtain ⟨τ, hτ⟩ := exists_affine_model_tensorPullback_stalk i V z U hzU
  exact ⟨τ _ _ eF, τ _ _ eG, hτ _ _ _ _ _ _ eF eG hcomm⟩

end AlgebraicGeometry
