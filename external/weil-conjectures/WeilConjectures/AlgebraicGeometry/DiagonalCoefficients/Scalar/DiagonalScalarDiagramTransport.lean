/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedScalarSource
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.RegularScalarExtensionMultiplication
import WeilConjectures.CategoryTheory.SixFunctors.IntegrationTransport

/-! # Scalar transport of a normalized diagonal diagram

Source: diagonal tower coefficient changes, paragraphs (1)--(2).
(blueprint: lem-diagonal-scalar-diagram-transport).
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

private def regularEndpoint
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (X : Scheme.{u}) :
    Endpoint a (Mod.regular (condensedRingObj Λ X))
      (Mod.regular (condensedRingObj Λ' X)) (coefficientMap a X) := by
  let h := sfbRegularScalarExtensionMultiplication
    (Scheme.ProEt.topology X) (condensedRingObj Λ X) (condensedRingObj Λ' X)
    (coefficientMap a X)
  let q := h.exists.choose
  have hq : Mod.extendUnitHom (coefficientMap a X) (Mod.regular (condensedRingObj Λ X)) ≫
      q.hom.hom = coefficientMap a X := h.exists.choose_spec.2.2.1
  have hflat : ObjectProperty.flat (Mod.regular (condensedRingObj Λ X)) :=
    ObjectProperty.prop_unit _
  have e := transportEndpoint a
    (flatExtensionEndpoint a X (Mod.regular (condensedRingObj Λ X)) hflat) q
  exact hq ▸ e

attribute [local irreducible] regularEndpoint transportEndpoint

private theorem endpoint_hom_unique
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] {X : Scheme.{u}}
    {M : Modules Λ X} {N : Modules Λ' X} {m : M.X ⟶ N.X}
    (e e' : Endpoint a M N m) : e.iso.hom = e'.iso.hom := by
  apply (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv
    _ _ |>.injective
  rw [e.normalization, e'.normalization]
  have he : e.semilinear.hom = e'.semilinear.hom :=
    Mod.hom_ext _ _ (e.semilinear.underlying.trans e'.semilinear.underlying.symm)
  rw [he]

attribute [local irreducible] derivedScalars

private abbrev scalarRightDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :=
  canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f)

/-- Construct a compatible scalar diagram from line endpoints and normalized
scalar/direct-image squares invertible on those lines.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraphs (1)--(2).
(blueprint: lem-diagonal-scalar-diagram-transport).

Proof: Use flat regular modules and the normalized regular scalar multiplication
isomorphism for unit endpoints. The supported-source comparison gives the two
normalized source squares. Their supported endpoint homs agree because the
scalar adjunction and their common underlying map determine each hom uniquely.
Define the new class by conjugating its scalar image with the supported and
shifted line endpoints. Define each trace by conjugating its scalar image with
the invertible direct-image mate and shifted line endpoint. Inverse cancellation
proves the class and trace squares. Integration transport applied to the source,
class and trace squares gives both integration identities. The canonical derived
models have the required full-unit normalization by their definitions. -/
theorem diagonal_scalar_diagram_of_squares
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X) (d : Diagram Λ Y L)
    (lineP : Endpoint a (L (ProjectiveLine Y)) (L' (ProjectiveLine Y))
      (m (ProjectiveLine Y)))
    (lineW : Endpoint a (L (diagonalSurface Y)) (L' (diagonalSurface Y))
      (m (diagonalSurface Y)))
    (q : RestrictionSquare a (ProjectiveLine Y ↘ Y) d.Rq
      (canonicalDiagonalRightDerived
        (CondensedRing.lowerStar Λ' (ProjectiveLine Y ↘ Y))))
    (p₁ : RestrictionSquare a
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'
        (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))))
    (p₂ : RestrictionSquare a
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂
      (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ'
        (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))))
    (hq : IsIso ((q.mate a).app
      (((DerivedCategory.singleFunctor _ 0).obj (L (ProjectiveLine Y)))⟦(2 : ℤ)⟧)))
    (h₁ : IsIso ((p₁.mate a).app
      (((DerivedCategory.singleFunctor _ 0).obj (L (diagonalSurface Y)))⟦(2 : ℤ)⟧)))
    (h₂ : IsIso ((p₂.mate a).app
      (((DerivedCategory.singleFunctor _ 0).obj (L (diagonalSurface Y)))⟦(2 : ℤ)⟧))) :
    ∃ d' : Diagram Λ' Y L', Nonempty (ScalarCompatibility a Y L L' m d d') := by
  let c := regularEndpoint a
  obtain ⟨e₁, s₁, hs₁⟩ := diagonal_supported_scalar_source a Y (c (ProjectiveLine Y))
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁ p₁ d.support₁
  obtain ⟨e₂, s₂, hs₂⟩ := diagonal_supported_scalar_source a Y (c (ProjectiveLine Y))
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂ p₂ d.support₂
  rw [endpoint_hom_unique a e₂ e₁] at hs₂
  let Rq := scalarRightDerived Λ' (ProjectiveLine Y ↘ Y)
  let R₁ := scalarRightDerived Λ'
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let R₂ := scalarRightDerived Λ'
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
  let U := derivedScalars a (diagonalSurface Y)
  let V := derivedScalars a (ProjectiveLine Y)
  let := hq
  let := h₁
  let := h₂
  have hlineP : IsIso (lineP.shift a) := by
    dsimp only [Endpoint.shift]
    infer_instance
  have hlineW : IsIso (lineW.shift a) := by
    dsimp only [Endpoint.shift]
    infer_instance
  let := hlineP
  let := hlineW
  let delta := e₁.iso.inv ≫ U.map d.delta ≫ lineW.shift a
  let traceq := inv ((q.mate a).app _ ≫ Rq.R.map (lineP.shift a)) ≫
    (derivedScalars a Y).map d.traceq ≫ (c Y).iso.hom
  let trace₁ := inv ((p₁.mate a).app _ ≫ R₁.R.map (lineW.shift a)) ≫
    V.map d.trace₁ ≫ (c (ProjectiveLine Y)).iso.hom
  let trace₂ := inv ((p₂.mate a).app _ ≫ R₂.R.map (lineW.shift a)) ≫
    V.map d.trace₂ ≫ (c (ProjectiveLine Y)).iso.hom
  have hdelta : U.map d.delta ≫ lineW.shift a =
      e₁.iso.hom ≫ delta := by
    dsimp only [delta]
    simp only [Iso.hom_inv_id_assoc]
  have htraceq : (derivedScalars a Y).map d.traceq ≫ (c Y).iso.hom =
      (q.mate a).app _ ≫ Rq.R.map (lineP.shift a) ≫ traceq := by
    dsimp only [traceq]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₁ : V.map d.trace₁ ≫ (c (ProjectiveLine Y)).iso.hom =
      (p₁.mate a).app _ ≫ R₁.R.map (lineW.shift a) ≫ trace₁ := by
    dsimp only [trace₁]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have htrace₂ : V.map d.trace₂ ≫ (c (ProjectiveLine Y)).iso.hom =
      (p₂.mate a).app _ ≫ R₂.R.map (lineW.shift a) ≫ trace₂ := by
    dsimp only [trace₂]
    simp only [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  let d' : Diagram Λ' Y L' :=
    { Rq := Rq
      R₁ := R₁
      R₂ := R₂
      q_canonical := rfl
      p₁_canonical := rfl
      p₂_canonical := rfl
      q_unit := by intro K; exact Category.comp_id _
      p₁_unit := by intro K; exact Category.comp_id _
      p₂_unit := by intro K; exact Category.comp_id _
      delta := delta
      traceq := traceq
      trace₁ := trace₁
      trace₂ := trace₂
      support₁ := s₁
      support₂ := s₂
      integration₁ := integration_transport d.R₁.R R₁.R U V
        (p₁.mate a) e₁.iso.hom (lineW.shift a)
        (c (ProjectiveLine Y)).iso d.support₁.hom d.delta d.trace₁
        s₁.hom delta trace₁ hs₁ hdelta htrace₁ d.integration₁
      integration₂ := integration_transport d.R₂.R R₂.R U V
        (p₂.mate a) e₁.iso.hom (lineW.shift a)
        (c (ProjectiveLine Y)).iso d.support₂.hom d.delta d.trace₂
        s₂.hom delta trace₂ hs₂ hdelta htrace₂ d.integration₂ }
  let scalar : ScalarCompatibility a Y L L' m d d' :=
    { units := c
      lineP := lineP
      lineW := lineW
      supported := e₁
      q := { square := q, comparison_iso := hq, trace := htraceq }
      p₁ := { square := p₁, comparison_iso := h₁, trace := htrace₁ }
      p₂ := { square := p₂, comparison_iso := h₂, trace := htrace₂ }
      delta := hdelta }
  exact ⟨d', ⟨scalar⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
