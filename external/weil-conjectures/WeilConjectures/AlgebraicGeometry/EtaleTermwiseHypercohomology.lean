/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.HypercohomologyFirstPage
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Cartan--Eilenberg presentations of termwise étale hypercohomology

Source: Stacks Project, Tags 015H, 015J and 015K
(blueprint: def-weil-pbc-termwise-hypercohomology-presentation).

This packages witnesses of `Functor.exists_hypercohomology_firstPage`. Bidegrees are
(filtration degree, resolution degree), so the paper's E₁^{p,q} is the term at (q,p).
-/

@[expose] public section

universe uHyper

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The canonical comparison from the cohomology of Γ of a K-injective resolution to the
cohomology of RΓ (the computation of H^n(X,K) in def-weil-pbc-etale-cohomology).
Source: Stacks, Tag 015J; the K-injective recipe
(blueprint: def-weil-pbc-termwise-hypercohomology-presentation). -/
noncomputable def resolutionEtaleCohomologyIso (X : Scheme.{uHyper})
    (K I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}) ℤ)
    (r : K ⟶ I) [QuasiIso r] [I.IsKInjective] (n : ℤ) :
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology n ≅
        (cohomology AddCommGrpCat.{uHyper + 1} X n).obj (DerivedCategory.Q.obj K) :=
  ((DerivedCategory.homologyFunctor AddCommGrpCat.{uHyper + 1} n).mapIso
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).rightDerivedFunctor.mapIso
          (asIso (DerivedCategory.Q.map r)) ≪≫
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).rightDerivedFunctorObjQIso
            I) ≪≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{uHyper + 1} n).app
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)).symm

-- The dependent CE, filtered-total and canonical abutment witnesses are elaborated together.
/-- A presentation of the first hypercohomology spectral sequence, its signed E₁
identifications and its canonical finite abutment filtration. The bicomplex and all
resolution properties are the witnesses of `Functor.exists_hypercohomology_firstPage`;
the comparison to derived global sections is fixed by the resolution map.
Source: Stacks, Tags 015H, 015J, 015K
(blueprint: def-weil-pbc-termwise-hypercohomology-presentation). -/
structure EtaleTermwiseHypercohomology (X : Scheme.{uHyper})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})) where
  I : HomologicalComplex₂ (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})
    (ComplexShape.up ℤ) (ComplexShape.up ℕ)
  a : ((CochainComplex.single₀ (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper +
      1})).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj ⟶ I
  below : ∃ b : ℤ, ∀ s : ℤ, s < b → IsZero (I.X s)
  terms : ∀ (s : ℤ) (r : ℕ), Injective ((I.X s).X r)
  rows : ∀ s : ℤ, QuasiIso (a.f s)
  horizontal : ∀ (s : ℤ) (r : ℕ), Injective ((I.cycles s).X r) ∧
    Injective ((image (I.d (s - 1) s)).X r) ∧ Injective ((I.homology s).X r)
  horizontal_quasi : ∀ s : ℤ, QuasiIso (HomologicalComplex.cyclesMap a s) ∧
    QuasiIso (image.map (Arrow.homMk' (a.f (s - 1)) (a.f s) (a.comm (s - 1) s))) ∧
    QuasiIso (HomologicalComplex.homologyMap a s)
  L : DecreasingFiltration
    ((((CartanEilenbergPresentation.mappedFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})).obj I).flip).total
        (ComplexShape.up ℤ))
  filtration_formula : ∀ p n : ℤ, L.complexStep p n =
    ((((CartanEilenbergPresentation.mappedFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})).obj I).flip).secondFiltration
          n).step p
  E : CohomologicalSpectralSequence AddCommGrpCat.{uHyper + 1} 0
  e₀ : ∀ p q : ℤ, (E.page 0).X (p, q) ≅ (L.gradedPiece p).X (p + q)
  d₀ : ∀ p q : ℤ, (E.page 0).d (p, q) (p, q + 1) ≫ (e₀ p (q + 1)).hom =
    (e₀ p q).hom ≫ (L.gradedPiece p).d (p + q) (p + (q + 1))
  subquotients : ∀ (p q r : ℤ) (hr : 1 ≤ r),
    ∃ hBZ : L.complexBoundaries p (p + q) r ≤ L.complexCycles p (p + q) r,
      Nonempty ((E.page r (le_trans (by decide : (0 : ℤ) ≤ 1) hr)).X (p, q) ≅
        cokernel (Subobject.ofLE _ _ hBZ))
  eDerived : ∀ (p : ℕ) (q : ℤ), (E.page 1).X (q, (p : ℤ)) ≅
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).rightDerived p).obj (K.obj.X q)
  dDerived : ∀ (p : ℕ) (q : ℤ),
    (E.page 1).d (q, (p : ℤ)) (q + 1, (p : ℤ)) ≫ (eDerived p (q + 1)).hom =
      (eDerived p q).hom ≫
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).rightDerived p).map
          (K.obj.d q (q + 1))
  ordinaryComparison : ∀ (p : ℕ) (q : ℤ),
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).rightDerived p).obj (K.obj.X q) ≅
      AddCommGrpCat.of (Sheaf.H (K.obj.X q) p)
  ordinary_naturality : ∀ (p : ℕ) (q : ℤ),
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).rightDerived p).map
        (K.obj.d q (q + 1)) ≫ (ordinaryComparison p (q + 1)).hom =
      (ordinaryComparison p q).hom ≫ AddCommGrpCat.ofHom (Sheaf.H.map (K.obj.d q (q + 1)) p)
  negative : ∀ p q : ℤ, q < 0 → IsZero ((E.page 1).X (p, q))
  ρ : CochainComplex.KInjectiveResolutionChoice K.obj
  aug : K.obj ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 (Sheaf X.smallEtaleTopology
      AddCommGrpCat.{uHyper + 1}))).obj I).flip).total
    (ComplexShape.up ℤ)
  aug_formula : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
    (HomologicalComplex.extendXIso (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper +
        1})).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (I.X n)) ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
    (((CartanEilenbergPresentation.mappedFunctor (𝟭 (Sheaf X.smallEtaleTopology
        AddCommGrpCat.{uHyper + 1}))).obj I).flip).ιTotal
      (ComplexShape.up ℤ) 0 n n (zero_add n)
  comparison : (((CartanEilenbergPresentation.mappedFunctor (𝟭 (Sheaf X.smallEtaleTopology
      AddCommGrpCat.{uHyper + 1}))).obj I).flip).total
    (ComplexShape.up ℤ) ⟶ ρ.complex
  over_K : Nonempty (Homotopy (aug ≫ comparison) ρ.map)
  w : ((((CartanEilenbergPresentation.mappedFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})).obj I).flip).total
      (ComplexShape.up ℤ)) ⟶
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ρ.complex
  w_formula : ∀ (m : ℕ) (s n : ℤ) (h : (m : ℤ) + s = n),
    (((CartanEilenbergPresentation.mappedFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})).obj I).flip).ιTotal
        (ComplexShape.up ℤ) (m : ℤ) s n h ≫ w.f n =
      (HomologicalComplex.extendXIso
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (I.X s)) ComplexShape.embeddingUpNat
            (i := m) (i' := (m : ℤ)) rfl).hom ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1}).map
        ((HomologicalComplex.extendXIso
          (((𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj (I.X s))
            ComplexShape.embeddingUpNat (i := m) (i' := (m : ℤ)) rfl).inv ≫
          (((CartanEilenbergPresentation.mappedFunctor (𝟭 (Sheaf X.smallEtaleTopology
              AddCommGrpCat.{uHyper + 1}))).obj I).flip).ιTotal
            (ComplexShape.up ℤ) (m : ℤ) s n h ≫ comparison.f n)
  c : ∀ n : ℤ,
    ((((CartanEilenbergPresentation.mappedFunctor
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})).obj I).flip).total
        (ComplexShape.up ℤ)).homology n ≅
      (cohomology AddCommGrpCat.{uHyper + 1} X n).obj (DerivedCategory.Q.obj K.obj)
  c_formula : ∀ n : ℤ, (c n).hom = HomologicalComplex.homologyMap w n ≫
    (@resolutionEtaleCohomologyIso.{uHyper} X K.obj ρ.complex ρ.map ρ.quasiIso ρ.isKInjective n).hom
  H : ∀ n : ℤ, DecreasingFiltration
    ((cohomology AddCommGrpCat.{uHyper + 1} X n).obj (DerivedCategory.Q.obj K.obj))
  finite : ∀ n : ℤ, (H n).IsFinite
  H_formula : ∀ p n : ℤ, (H n).step p =
    (Subobject.«exists» (c n).hom).obj
      (imageSubobject (HomologicalComplex.homologyMap (L.step p).arrow n))

namespace EtaleTermwiseHypercohomology

/-- Restrict the resolution spectral sequence to its intrinsic pages E₁ and later.
Source: Stacks, Tags 015J and 015K
(blueprint: def-weil-pbc-termwise-hypercohomology-presentation). -/
def sequence {X : Scheme.{uHyper}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})}
    (D : EtaleTermwiseHypercohomology X K) :
    CohomologicalSpectralSequence AddCommGrpCat.{uHyper + 1} 1 where
  page r hr := D.E.page r (le_trans (by decide : (0 : ℤ) ≤ 1) hr)
  iso r r' pq hrr' hr := D.E.iso r r' pq hrr' (le_trans (by decide : (0 : ℤ) ≤ 1) hr)

/-- The signed identification of E₁^{p,q} with H^p(X,K^q).
Source: Stacks, Tag 015J (blueprint: def-weil-pbc-termwise-hypercohomology-presentation). -/
noncomputable def firstPageIso {X : Scheme.{uHyper}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uHyper + 1})}
    (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    (D.sequence.page 1).X (q, (p : ℤ)) ≅ AddCommGrpCat.of (Sheaf.H (K.obj.X q) p) :=
  D.eDerived p q ≪≫ D.ordinaryComparison p q

end EtaleTermwiseHypercohomology
end AlgebraicGeometry.Etale
