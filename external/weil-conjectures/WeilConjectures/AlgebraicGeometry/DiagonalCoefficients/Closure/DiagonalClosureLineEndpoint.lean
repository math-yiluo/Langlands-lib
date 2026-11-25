/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Closure.DiagonalClosureOrdinaryLine
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence

/-! # The normalized derived endpoint of the closure root line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option linter.privateModule false
set_option backward.defeqAttrib.useBackward false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
universe u

namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] Functor.leftDerivedFunctor
  Mod.derivedExtendMapDerivedCategoryAdjunction

private def flatExtensionEndpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) (M : Modules Λ X)
    (hM : ObjectProperty.flat M) :
    Endpoint a M ((Mod.extendScalars (coefficientMap a X)).obj M)
      (Mod.extendUnitHom (coefficientMap a X) M) := by
  let h := diagonal_flat_scalar_endpoint_iso a X M hM
  let i := h.exists.choose
  exact { semilinear := ⟨Mod.extendUnit (coefficientMap a X) M, rfl⟩
          iso := i
          normalization := h.exists.choose_spec }

attribute [local irreducible] flatExtensionEndpoint

private def transportEndpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}} {M : Modules Λ X}
    {N N' : Modules Λ' X} {m : M.X ⟶ N.X} (e : Endpoint a M N m) (q : N ≅ N') :
    Endpoint a M N' (m ≫ q.hom.hom) where
  semilinear := ⟨e.semilinear.hom ≫ (Mod.comap (coefficientMap a X)).map q.hom, by
    change e.semilinear.hom.hom ≫ q.hom.hom = m ≫ q.hom.hom
    rw [e.semilinear.underlying]⟩
  iso := e.iso ≪≫ (DerivedCategory.singleFunctor (Modules Λ' X) 0).mapIso q
  normalization := by
    change (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv
        _ _ (e.iso.hom ≫ (DerivedCategory.singleFunctor (Modules Λ' X) 0).map q.hom) =
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map
          (e.semilinear.hom ≫ (Mod.comap (coefficientMap a X)).map q.hom) ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N'
    rw [Adjunction.homEquiv_naturality_right, e.normalization]
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg (_ ≫ ·)
      (((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.naturality
        q.hom).symm

private theorem rationalLine_flat (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField l) : ObjectProperty.flat (spRationalTwist X l E) := by
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj (Profinite.continuousMapRingObj E.1) X)
  let L := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.continuousMapRingObj E.1) X)).functor.obj
      (spRationalTwist X l E)
  have : L.IsFiniteLocallyFreeOfRank 1 := (spTwists_locallyFree X l E).2.1
  apply (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology X) _ (spRationalTwist X l E)).mpr
  obtain ⟨a⟩ := (WeilConjectures.signedLineTensor_equivalence X R L 1).2
  obtain ⟨b⟩ := (WeilConjectures.signedLineTensor_equivalence X R L (-1)).2
  let G := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R)
    (WeilConjectures.coefficientTwistLine X L (-1))
  let H := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) L
  have b' : G ⋙ H ≅ 𝟭 _ := by
    simpa only [G, H, WeilConjectures.coefficientTwistLine,
      WeilConjectures.coefficientTwistPower, SheafOfModules.scalarTensorPower, neg_neg] using b
  change exactFunctor _ _ H
  exact (exactFunctor_iff _).mpr
    (let e := CategoryTheory.Equivalence.mk H G a.symm b'
     ⟨inferInstanceAs (PreservesFiniteLimits e.functor),
      inferInstanceAs (PreservesFiniteColimits e.functor)⟩)

attribute [local irreducible] transportEndpoint

@[instance_reducible] private def residueInvertible (l : ℕ) (X : Scheme.{u})
    (hX : IsUnit (l : Γ(X, ⊤))) : ∀ x : X, Invertible (l : X.residueField x) := by
  intro x
  let φ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
  exact (show IsUnit (l : X.residueField x) from by
    simpa only [map_natCast] using hX.map φ).invertible

attribute [local irreducible] spRationalTwist spQbarTwist closureLineMap
  HasDerivedCategory.standard Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- The prescribed ordinary closure-line leg gives an adjoint-normalized derived endpoint.

Source: blueprint diagonal coefficient changes, paragraph (2), scalar extension of the
rational root line and passage to its degree-zero derived endpoint.
(blueprint: lem-diagonal-closure-line-endpoint).

Proof: the rational line has rank one locally, so tensoring with its signed inverse is
an inverse equivalence. Transporting exactness through the internal/section module
comparison proves flatness. Apply the flat single-complex scalar comparison, whose unit
normalization is already recorded. Transport this endpoint through the ordinary normalized
closure-line isomorphism. Naturality of the scalar adjunction and of the restriction/single
comparison proves its normalization; the ordinary unit equation identifies the resulting
underlying map with the prescribed closureLineMap. -/
theorem diagonalClosure_lineEndpoint (l : ℕ) [Fact l.Prime]
    (E : PadicAlgCl.FiniteIntermediateField l) (X : Scheme.{u})
    (hX : IsUnit (l : Γ(X, ⊤))) :
    Nonempty (Endpoint (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (spRationalTwist X l E) (spQbarTwist X l) (closureLineMap l E X)) := by
  let := residueInvertible l X hX
  let a := Profinite.padicSubfieldRingObjToPadicAlgCl.{u} l E
  obtain ⟨q, hq⟩ := diagonalClosure_ordinaryLine l E X hX
  let e := transportEndpoint a
    (flatExtensionEndpoint a X (spRationalTwist X l E) (rationalLine_flat l X E)) q
  rw [← hq]
  exact ⟨e⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
