/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteIntegralEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarDiagramTransport
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

/-! # The finite coefficient stages of a fixed diagonal diagram

Source: diagonal tower coefficient changes, paragraphs (1)--(2).
(blueprint: lem-sfb-diagonal-finite-coefficient-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] RestrictionSquare.mate Functor.leftDerivedFunctor
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

private theorem integralLine_flat (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField l) : ObjectProperty.flat (spIntegralTwist X l E) := by
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)
  let L := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X)
    (condensedRingObj (Profinite.padicIntegersRingObj l E.1) X)).functor.obj
      (spIntegralTwist X l E)
  have : L.IsFiniteLocallyFreeOfRank 1 := (spTwists_locallyFree X l E).1
  apply (InternalAbelianSheafModule.flat_iff_sectionModule
    (Scheme.ProEt.topology X) _ (spIntegralTwist X l E)).mpr
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

@[instance_reducible] private def residueInvertible (l : ℕ) (X : Scheme.{u})
    (hX : IsUnit (l : Γ(X, ⊤))) : ∀ x : X, Invertible (l : X.residueField x) := by
  intro x
  let φ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
  exact (show IsUnit (l : X.residueField x) from by
    simpa only [map_natCast] using hX.map φ).invertible

attribute [local irreducible] derivedScalars

/-- Extend one fixed Z_l diagram to the integers and the field of a single
finite subextension. No closure diagram or finite-field transition is asserted.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1) and the rationalization
part of paragraph (2).
(blueprint: lem-sfb-diagonal-finite-coefficient-extension).

Proof: Choose an integral basis of O_E over Z_l. It identifies scalar extension
with a finite direct sum and hence makes it exact. The coefficient and root-limit
maps have scalar adjoints that are isomorphisms: the coefficient assertion follows
from the basis and the line assertion from the same basis applied to the root
limit. Closed-diagonal direct image is exact, so the supported source has the
same scalar identification. Exact restriction commutes with direct image on
underlying sheaves; derive this square with its universal-unit normalization.
Its scalar mate is invertible since additive right-derived direct image preserves
finite direct sums. Define the new diagonal by conjugating the scalar image of
the old diagonal with the source and line endpoints. Define each new trace by
conjugating its scalar image with the scalar/direct-image mate and unit endpoint.
The normalized supported-source square and naturality carry each integration
composite to scalar extension of its original identity. Use the canonical
right-derived models, so their full universal units have the required normalization.
For rationalization the same construction uses localization at l. The regular
and shifted root-line objects have common lower bound -2, and all three
projective-line projections are qcqs. Bounded continuity therefore makes the
localization/direct-image mates invertible on these lines. Exact filtered
colimits identify the scalar endpoints with the prescribed rational root line.
Apply the same formulas for the diagonal, the traces, and the integration
identities. Every endpoint is the adjoint of the specified coefficient or root
map, so both resulting ScalarCompatibility records have precisely the required
normalizations. -/
theorem diagonalCoefficient_finiteExtension
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (d : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l))
    (E : PadicAlgCl.FiniteIntermediateField l) :
    ∃ i : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
        (fun X ↦ spIntegralTwist X l E),
      ∃ r : Diagram (Profinite.continuousMapRingObj.{u} E.1) Y
          (fun X ↦ spRationalTwist X l E),
        Nonempty (ScalarCompatibility (integralMap l E) Y (zlLine l)
          (fun X ↦ spIntegralTwist X l E) (integralLineMap l E) d i) ∧
        Nonempty (ScalarCompatibility (padicIntegersRingObjToContinuousMapRingObj l E) Y
          (fun X ↦ spIntegralTwist X l E) (fun X ↦ spRationalTwist X l E)
          (rationalLineMap l E) i r) := by
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using
      hP.map (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).appTop.hom
  let := residueInvertible l (ProjectiveLine Y) hP
  let := residueInvertible l (diagonalSurface Y) hW
  obtain ⟨lineP⟩ := diagonalFinite_integralEndpoint l E (ProjectiveLine Y) hP
  obtain ⟨lineW⟩ := diagonalFinite_integralEndpoint l E (diagonalSurface Y) hW
  obtain ⟨sq, hq⟩ := (diagonalFinite_scalarSquares l E (ProjectiveLine Y ↘ Y)).1 d.Rq
  obtain ⟨s₁, h₁⟩ := (diagonalFinite_scalarSquares l E
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).1 d.R₁
  obtain ⟨s₂, h₂⟩ := (diagonalFinite_scalarSquares l E
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).1 d.R₂
  obtain ⟨i, hi⟩ := diagonal_scalar_diagram_of_squares (integralMap l E) Y (zlLine l)
    (fun X ↦ spIntegralTwist X l E) (integralLineMap l E) d lineP lineW
    sq s₁ s₂ hq h₁ h₂
  obtain ⟨tq, htq⟩ := (diagonalFinite_scalarSquares l E (ProjectiveLine Y ↘ Y)).2 i.Rq
  obtain ⟨t₁, ht₁⟩ := (diagonalFinite_scalarSquares l E
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).2 i.R₁
  obtain ⟨t₂, ht₂⟩ := (diagonalFinite_scalarSquares l E
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).2 i.R₂
  let a := padicIntegersRingObjToContinuousMapRingObj l E
  let rationalP := flatExtensionEndpoint a (ProjectiveLine Y) _
    (integralLine_flat l (ProjectiveLine Y) E)
  let rationalW := flatExtensionEndpoint a (diagonalSurface Y) _
    (integralLine_flat l (diagonalSurface Y) E)
  obtain ⟨r, hr⟩ := diagonal_scalar_diagram_of_squares a Y (fun X ↦ spIntegralTwist X l E)
    (fun X ↦ spRationalTwist X l E) (rationalLineMap l E) i rationalP rationalW
    tq t₁ t₂ htq ht₁ ht₂
  exact ⟨i, r, hi, hr⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
