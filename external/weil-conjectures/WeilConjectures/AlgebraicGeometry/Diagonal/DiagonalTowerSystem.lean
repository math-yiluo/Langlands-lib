/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerSystemInterface
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalDerivedReductionExists
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalReductionCompletion
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalKummerReduction

/-! # Existence of the normalized strict diagonal cycle system

Source: the diagonal tower blueprint, clauses 1--4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private theorem single_scalar_mono {A : Type uA} [Category.{vA} A] [Abelian A]
    (n : ℕ) (M : A) (hm : Mono (n • 𝟙 M)) (i : ℤ) :
    Mono (n • 𝟙 (((HomologicalComplex.single A (.up ℤ) 0).obj M).X i)) := by
  classical
  by_cases hi : i = 0
  · subst i
    let e := eqToIso (HomologicalComplex.single_obj_X_self (.up ℤ) 0 M)
    have he : (n • 𝟙 (((HomologicalComplex.single A (.up ℤ) 0).obj M).X 0)) ≫ e.hom =
        e.hom ≫ (n • 𝟙 M) := by
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id]
    exact mono_of_mono_fac he
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi).mono _

private theorem constant_scalar_mono (W : Scheme.{u}) (n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 ((constantSheaf (Scheme.ProEt.topology W)
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
  have : Mono (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro x y h
    change n • x = n • y at h
    exact ULift.ext (nsmul_right_injective hn (congrArg ULift.down h))
  have : Mono ((Functor.const W.ProEtᵒᵖ).map
      (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := NatTrans.mono_of_mono_app _
  have : Mono ((presheafToSheaf (Scheme.ProEt.topology W) AddCommGrpCat.{u + 1}).map
      ((Functor.const W.ProEtᵒᵖ).map
        (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := inferInstance
  simpa only [constantSheaf, Functor.comp_obj, CategoryTheory.Functor.map_nsmul,
    CategoryTheory.Functor.map_id] using this

private theorem source_mono (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u}) (n : ℕ) :
    Mono (ℓ ^ (n + 1) • 𝟙 (diagonalIntegralSource Y)) := by
  have hm := constant_scalar_mono (ProjectiveLine Y) (ℓ ^ (n + 1))
    (pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have := (lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion Y)).map_mono
    (ℓ ^ (n + 1) • 𝟙 ((constantSheaf (Scheme.ProEt.topology (ProjectiveLine Y))
      AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))
  simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id] using this

private theorem source_counit_iso (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (hc : ∀ P : CochainComplex (DiagonalAb (diagonalSurface Y)) ℤ,
      (∀ (n : ℕ) (i : ℤ), Mono (ℓ ^ (n + 1) • 𝟙 (P.X i))) → IsIso (D.ε.app P)) :
    IsIso (diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y)) := by
  have := hc ((HomologicalComplex.single _ (.up ℤ) 0).obj (diagonalIntegralSource Y))
    (fun n i ↦ single_scalar_mono _ _ (source_mono ℓ Y n) i)
  unfold diagonalDerivedSingleCounit
  infer_instance

/-- The diagonal torsion classes form one morphism in the derived category of
strict inverse systems, obtained by simultaneous derived reduction of the positive
integral Cartier roof. No noetherian, finiteness or nonemptiness assumption is imposed
on Y. The displayed typeclasses only choose the localization and Ext size conventions.

Source: blueprint main-20261015, sk-prop-diagonal-tower-system.md, clauses 1--4;
Stacks Project, Tags 099M and 09AD (blueprint: proposition-ell-adic-cycle-class-diagonal).

Proof:
1. The diagonal is a section of the smooth relative curve given by the first
   projection. Its kernel subscheme projects isomorphically to the projective
   line, so the relative Cartier criterion makes its ideal invertible.
   Form the pole extension with all integer powers of t inverse, sending it to +1.
   Exact conservative geometric stalks identify its quotient with Delta_* Z.
2. Exact comparison inverse image preserves the extension and its quotient
   quasi-isomorphism; the open--closed sequence gives the supported comparison.
   The positive cone projection is the negative of the standard Ext boundary,
   which is precisely diagonalIntegralBoundary.
3. Form the actual strict reduction functor by the cokernels specified above,
   with quotient transitions. Resolve every integral input by a flat-term K-flat
   complex. Simultaneous tensor preserves quasi-isomorphisms between these;
   the resolving-class theorem gives its pointwise left derived functor, exact
   because tensor respects shifts and mapping cones.
4. Z_l is torsion free, hence flat over Z. Exact extension is left adjoint to
   restriction, so restriction preserves K-injective strict systems and commutes
   with their inverse limits. Derive with the same resolution. The integral
   composite is Rlim_n(K tensor^L Z/l^(n+1)). The principal-ideal criterion
   of Tags 091S and 091Z identifies completeness with right orthogonality to
   all complexes on which l acts invertibly. Tag 099M supplies complete outputs
   and the natural completion unit, with bijective precomposition for every
   complete target. Thus the composite is the completion reflector, including
   its universal unit, not merely an isomorphism of the naive limit formulas.
5. Open--closed exactness shows Delta_* Z is flat and its ordinary reductions
   are the supported finite constants. These identifications preserve the units
   and every quotient transition, giving a and the normalized level maps s.
6. Kummer exactness computes the reduction of comparison units by
   [G_m --l^(n+1)--> G_m] in degrees -1,0. The resolution transition is l in
   degree -1 and identity in degree 0, hence the roots transition is zeta→zeta^l.
   Exact comparison identifies the roots with the actual pro-etale root sheaves.
   Use the negative Kummer identification, compensating the positive roof sign.
   Concentration in one cohomology degree lifts this to the strict system category.
7. The divisible-extension derived-reduction comparison fixes the complete
   supported Cartier class, not only its Chern composite. Its signed Kummer
   normalization identifies every evaluated arrow with cartierResidueReducedPro.
   The source and roots normalization equations retain the canonical finite
   identifications. Compatibility already holds because T has values in the
   derived category of strict systems, and c is its image of one boundary. -/
theorem exists_diagonalTowerSystem (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))] :
    ∃ D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)),
      DiagonalCompletionSpec ℓ (diagonalSurface Y) D ∧ DiagonalCycleSystemSpec ℓ Y hY D := by
  classical
  obtain ⟨D, _I, hD, _hI⟩ := exists_diagonalDerivedReduction ℓ (diagonalSurface Y)
  have := source_counit_iso ℓ Y D hD
  let a := asIso (diagonalDerivedSingleCounit ℓ
    (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y))
  refine ⟨D, diagonal_reduction_completion ℓ (diagonalSurface Y) D, a, rfl, ?_⟩
  exact diagonal_kummer_reduction ℓ Y hY D a rfl

end AlgebraicGeometry.ProEtale
