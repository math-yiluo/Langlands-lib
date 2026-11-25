/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFlatScalarEndpoint
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.RegularScalarExtensionMultiplication
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
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Uniformizer.DiagonalUniformizerScalarSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedScalarSource

/-! # Scalar endpoints and supported sources for a uniformizer quotient

Source: diagonal tower coefficient changes, paragraph (1).
(blueprint: lem-diagonal-uniformizer-scalar-frame).
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

/-- The fixed canonical model, parameterized by its coefficient ring to keep
endpoint structures small. Source: coefficient changes paragraph (1).
(blueprint: lem-diagonal-uniformizer-scalar-frame). -/
abbrev scalarRightDerived
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X S : Scheme.{u}} (f : X ⟶ S) :=
  canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ f)

/-- Scalar endpoints, direct-image squares and normalized supported sources,
without a transported class, trace or integration identity. Parameterizing the two
rings and lines avoids expanding a concrete quotient tensor product in every field.
Source: coefficient changes paragraph (1).
(blueprint: lem-diagonal-uniformizer-scalar-frame). -/
structure ScalarFrame
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X) (d : Diagram Λ Y L) where
  units : ∀ X : Scheme.{u}, Endpoint a
    (Mod.regular (condensedRingObj Λ X))
    (Mod.regular (condensedRingObj Λ' X))
    (coefficientMap a X)
  lineP : Endpoint a (L (ProjectiveLine Y))
    (L' (ProjectiveLine Y)) (m (ProjectiveLine Y))
  lineW : Endpoint a (L (diagonalSurface Y))
    (L' (diagonalSurface Y)) (m (diagonalSurface Y))
  supported : Endpoint a (source Λ Y) (source Λ' Y)
    (supportMap a Y (units (ProjectiveLine Y)).semilinear.hom).hom
  q : RestrictionSquare a (ProjectiveLine Y ↘ Y) d.Rq
    (scalarRightDerived Λ' (ProjectiveLine Y ↘ Y))
  p₁ : RestrictionSquare a
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁
    (scalarRightDerived Λ'
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
  p₂ : RestrictionSquare a
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂
    (scalarRightDerived Λ'
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
  q_iso : IsIso ((q.mate a).app
    (((DerivedCategory.singleFunctor _ 0).obj
      (L (ProjectiveLine Y)))⟦(2 : ℤ)⟧))
  p₁_iso : IsIso ((p₁.mate a).app
    (((DerivedCategory.singleFunctor _ 0).obj
      (L (diagonalSurface Y)))⟦(2 : ℤ)⟧))
  p₂_iso : IsIso ((p₂.mate a).app
    (((DerivedCategory.singleFunctor _ 0).obj
      (L (diagonalSurface Y)))⟦(2 : ℤ)⟧))
  support₁ : DiagonalTrace.NormalizedSource
    (CondensedRing.lowerStar Λ'
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (scalarRightDerived Λ'
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (source Λ' Y)
    (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
    (diagonalImmersion Y ≫
      pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) = 𝟙 _)
    (SupportNormalization Λ' Y _)
  support₂ : DiagonalTrace.NormalizedSource
    (CondensedRing.lowerStar Λ'
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (scalarRightDerived Λ'
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)))
    (source Λ' Y)
    (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
    (diagonalImmersion Y ≫
      pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) = 𝟙 _)
    (SupportNormalization Λ' Y _)
  source₁ : (derivedScalars a (ProjectiveLine Y)).map d.support₁.hom ≫
    (p₁.mate a).app _ ≫
    (scalarRightDerived Λ'
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).R.map supported.iso.hom =
      (units (ProjectiveLine Y)).iso.hom ≫ support₁.hom
  source₂ : (derivedScalars a (ProjectiveLine Y)).map d.support₂.hom ≫
    (p₂.mate a).app _ ≫
    (scalarRightDerived Λ'
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))).R.map supported.iso.hom =
      (units (ProjectiveLine Y)).iso.hom ≫ support₂.hom

attribute [local irreducible] canonicalDiagonalRightDerived RestrictionSquare.mate
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction

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

attribute [local irreducible] regularEndpoint transportEndpoint

@[instance_reducible] private def residueInvertible (l : ℕ) (X : Scheme.{u})
    (hX : IsUnit (l : Γ(X, ⊤))) : ∀ x : X, Invertible (l : X.residueField x) := by
  intro x
  let φ := (X.residue x).hom.comp (X.presheaf.germ ⊤ x trivial).hom
  exact (show IsUnit (l : X.residueField x) from by
    simpa only [map_natCast] using hX.map φ).invertible

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

private theorem scalarFrame_of_squares
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
    (q : ScalarSquareIsomorphisms a (ProjectiveLine Y ↘ Y) d.Rq)
    (p₁ : ScalarSquareIsomorphisms a
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁)
    (p₂ : ScalarSquareIsomorphisms a
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂) :
    Nonempty (ScalarFrame a Y L L' m d) := by
  let c := regularEndpoint a
  obtain ⟨e₁, s₁, hs₁⟩ := diagonal_supported_scalar_source a Y (c (ProjectiveLine Y))
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁ p₁.square d.support₁
  obtain ⟨e₂, s₂, hs₂⟩ := diagonal_supported_scalar_source a Y (c (ProjectiveLine Y))
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂ p₂.square d.support₂
  rw [endpoint_hom_unique a e₂ e₁] at hs₂
  exact ⟨{
    units := c
    lineP := lineP
    lineW := lineW
    supported := e₁
    q := q.square
    p₁ := p₁.square
    p₂ := p₂.square
    q_iso := q.isIso _
    p₁_iso := p₁.isIso _
    p₂_iso := p₂.isIso _
    support₁ := s₁
    support₂ := s₂
    source₁ := hs₁
    source₂ := hs₂ }⟩

/-- Construct the scalar frame before transporting any class or trace. In particular,
this assertion does not identify a finite Cartier class or choose a quotient diagram.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), coefficient reduction.
(blueprint: lem-diagonal-uniformizer-scalar-frame).

Proof: The regular module is flat. The K-flat transpose of the ordinary scalar
extension unit computes its derived scalar endpoint; transport by the uniquely
normalized regular scalar multiplication isomorphism. The actual integral Tate
line is locally free of rank one. The signed-line tensor equivalence proves its
flatness in the section-module category, hence in internal modules. The same
single-complex argument gives its two quotient-line endpoints.

For the three projections use the full-unit-normalized uniformizer scalar square.
Its scalar mate is invertible on every complex by the two-term finite free quotient
resolution and the perfect projection argument; in particular it is invertible on
the required shifted lines. This uses no projective-line cohomology computation.

Apply closed-support scalar compatibility separately to both projections, using
their integral normalized sources and the common regular endpoint. This supplies
the quotient normalized sources and the two source equations. Two endpoints for
the same underlying supported coefficient map have equal semilinear maps, and
their adjoint normalization therefore makes their derived homs equal. Replace the
second endpoint hom by the first in the second source equation and assemble the
frame. The argument applies at n = 0 and for ramified uniformizers without requiring
flatness of the quotient coefficient map. -/
theorem diagonalUniformizer_scalarFrame
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    (hY : IsUnit (l : Γ(Y, ⊤)))
    (E : PadicAlgCl.FiniteIntermediateField l) (π : PadicAlgCl.integers l E)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers l E)) (n : ℕ)
    (d : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
      (fun X ↦ spIntegralTwist X l E)) :
    Nonempty (ScalarFrame (quotientMap l E π n) Y (fun X ↦ spIntegralTwist X l E)
      (quotientLine l E π n) (quotientLineMap l E π n) d) := by
  let a := quotientMap.{u} l E π n
  obtain ⟨q⟩ := diagonal_uniformizer_scalar_squares l E π hπ n
    (ProjectiveLine Y ↘ Y) d.Rq
  obtain ⟨p₁⟩ := diagonal_uniformizer_scalar_squares l E π hπ n
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₁
  obtain ⟨p₂⟩ := diagonal_uniformizer_scalar_squares l E π hπ n
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) d.R₂
  have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
    simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
  have hW : IsUnit (l : Γ(diagonalSurface Y, ⊤)) := by
    simpa only [map_natCast] using
      hP.map (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).appTop.hom
  let := residueInvertible l (ProjectiveLine Y) hP
  let := residueInvertible l (diagonalSurface Y) hW
  exact scalarFrame_of_squares a Y (fun X ↦ spIntegralTwist X l E)
    (quotientLine l E π n) (quotientLineMap l E π n) d
    (flatExtensionEndpoint a _ _ (integralLine_flat l (ProjectiveLine Y) E))
    (flatExtensionEndpoint a _ _ (integralLine_flat l (diagonalSurface Y) E)) q p₁ p₂

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
