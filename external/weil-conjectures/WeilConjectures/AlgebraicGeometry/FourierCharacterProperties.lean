/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierCover
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.CategoryTheory.RingObjects.GlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.CategoryTheory.ModuleObjects.RegularEnd
public import WeilConjectures.FourierTransform.ArtinSchreier
public import WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Finite.Trace
public import WeilConjectures.AlgebraicGeometry.ArtinSchreierTrace.ArtinSchreierTraceComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.ModuleEqualizerInternalHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.MonoidalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.WeilObject.Sheaf.Stalk
public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.Points
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.CategoryTheory.ModuleObjects.Linear
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! # Properties of the canonical condensed Artin–Schreier sheaf

Source: current blueprint, sec-fourier-transform/sk-lem-as-properties/_section.md
(blueprint: lemma-artin-schreier-character-sheaf).

Frobenius is the descent action on the geometric fibre of the actual projector
image. The normalized root-evaluation model is explicitly identified with that
image, and the finite étale model is compared through the finite coefficient
module equivalence and the canonical change of sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CondensedRing.upperStar

/-- The geometric fibre of an actual condensed module at a finite-field point.
Source: blueprint lemma-artin-schreier-character-sheaf, Frobenius paragraph
(blueprint: lemma-artin-schreier-character-sheaf). -/
abbrev characterGeometricFibre
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : Type u) [Field K] (X : Scheme.{u}) (g : Spec (.of K) ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  (CondensedRing.upperStar Λ ((Scheme.specAlgebraicClosure K).hom ≫ g)).obj M

/-- The return map on a geometric fibre over a fixed base point.
The automorphism fixes π, so it fixes π ≫ g. Compose the inverse constant-point
comparison with pullback composition and that equality. No return map is chosen.
Source: blueprint lemma-artin-schreier-character-sheaf, geometric Frobenius action
(blueprint: lemma-artin-schreier-character-sheaf). -/
@[irreducible]
def characterPointReturn
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (Y X : Scheme.{u}) (π : Spec (.of Ω) ⟶ Y)
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (h : σ ≫ π = π) (g : Y ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    End ((CondensedRing.upperStar Λ (π ≫ g)).obj M) :=
  .of ((CondensedRing.upperStarIsoIdOfIsSepClosed Λ σ).inv.app
      ((CondensedRing.upperStar Λ (π ≫ g)).obj M) ≫
    (CondensedRing.upperStarComp Λ σ (π ≫ g)).inv.app M ≫
    (CondensedRing.upperStarEqToIso Λ
      ((Category.assoc σ π g).symm.trans (congrArg (fun t ↦ t ≫ g) h))).hom.app M)

/-- Geometric Frobenius on the fibre of a sheaf descended to a finite field.
Specialize the canonical point-return map to the fixed geometric Frobenius
and its equality over Spec K.
Source: blueprint lemma-artin-schreier-character-sheaf, Frobenius convention and proof paragraph 3
(blueprint: lemma-artin-schreier-character-sheaf). -/
@[irreducible]
def characterGeometricFrobenius
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (K : Type u) [Field K] [hK : Finite K] (X : Scheme.{u}) (g : Spec (.of K) ⟶ X)
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :=
  characterPointReturn Λ (AlgebraicClosure K) (Spec (.of K)) X
    (Scheme.specAlgebraicClosure K).hom (specGeometricFrobenius K).asIso.hom
    (specGeometricFrobenius_hom_comp_specAlgebraicClosure K) g M

/-- A specified endomorphism acts by the specified scalar on its actual module.
This merely packages the equality of underlying morphisms, without choosing a
trace or replacing the module. Source: blueprint lemma-artin-schreier-character-sheaf,
Frobenius scalar clause (blueprint: lemma-artin-schreier-character-sheaf). -/
def characterHasScalarAction
    {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {R : C} [MonObj R] {M : Mod C R} (e : End M) (c : MonObj.Γ R) : Prop :=
  e.asHom.hom = Mod.globalSmul c.hom M

/-- The scalar ψ(Tr f(x)) uses the residue-field algebra structure supplied by X → Spec k₀.
Source: blueprint lemma-artin-schreier-character-sheaf, closed-point clause
(blueprint: lemma-artin-schreier-character-sheaf). -/
def characterResidueTrace
    (k₀ : Type u) [Field k₀] (X : Scheme.{u}) [X.Over (Spec (.of k₀))]
    (f : Γ(X, ⊤)) (x : X) : k₀ :=
  @Algebra.trace k₀ (X.residueField x) _ _
    ((X ↘ Spec (.of k₀)).residueFieldAlgebraMap x).toAlgebra (X.Γevaluation x f)

/-- The ordinary finite-coefficient character sheaf, with the unique lifted inverse
of the field cardinality transported to the coefficient universe.
Source: blueprint lemma-artin-schreier-character-sheaf, finite-coefficient complement
(blueprint: lemma-artin-schreier-character-sheaf). -/
def finiteEtaleCharacter
    (k₀ : Type u) [Field k₀] [Fintype k₀]
    (A : Type) [CommRing A] [Invertible (Fintype.card k₀ : A)]
    (χ : AddChar k₀ A) (X : Scheme.{u}) [X.Over (Spec (.of k₀))] (f : Γ(X, ⊤)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)) := by
  letI : Invertible (Fintype.card k₀ : ULift.{u + 1} A) := by
    simpa using (Invertible.map
      ((ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom) (Fintype.card k₀ : A))
  exact Etale.artinSchreierSheafOf X
    (((ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom).toMonoidHom.compAddChar χ) f

end AlgebraicGeometry.ProEtale
