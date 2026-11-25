/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergPresentation
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import WeilConjectures.CategoryTheory.CartanEilenbergConeFiltrationSteps
import WeilConjectures.CategoryTheory.DegreewiseFiltration

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
/-- Construction of the degreewise image-sum filtration.
Source: Stacks Project, Homology, Tag 0133.  The construction takes the
finite supremum of the images of the diagonal summands whose complex index is
at least `p`, together with the cone inclusion of `K` when `p ≤ n+1`.  The
canonical biproduct and diagonal coproduct maps give these images directly;
the total differential preserves the indicated index, while the augmentation
equation places its off-diagonal component in index `n+1`.  Factoring these
maps through the monic image-sum inclusions therefore supplies subcomplexes.
The interval `Finset.Icc (max b p) n` is finite, so the supremum exists, and
the interval inclusions prove antitonicity in `p`; the resulting subcomplexes
are the required decreasing filtration.
Source: Stacks Project, Homology, Tag 0133.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration-data). -/
theorem cartanEilenberg_cone_filtration_data
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{vA} A]
    (K : CochainComplex A ℤ)
    (I : HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ))
    (a : ((CochainComplex.single₀ A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K ⟶ I)
    (b : ℤ)
    (hIbelow : ∀ s : ℤ, s < b → IsZero (I.X s))
    (hKbelow : ∀ s : ℤ, s < b → IsZero (K.X s))
    (aug : K ⟶ (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).total
      (ComplexShape.up ℤ))
    (haug : ∀ n : ℤ, aug.f n = (a.f n).f 0 ≫
      (HomologicalComplex.extendXIso
        (((𝟭 A).mapHomologicalComplex (ComplexShape.up ℕ)).obj (I.X n))
        ComplexShape.embeddingUpNat (i := 0) (i' := 0) rfl).inv ≫
      (((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotal
        (ComplexShape.up ℤ) 0 n n (zero_add n)) :
    ∃ F : DecreasingFiltration (CochainComplex.mappingCone aug),
      ∀ p n : ℤ, F.complexStep p n =
        (if p ≤ n + 1 then imageSubobject
          ((CochainComplex.mappingCone.inl aug).v (n + 1) n (by omega)) else ⊥) ⊔
        (Finset.Icc (max b p) n).sup (fun s ↦ imageSubobject
          ((((CartanEilenbergPresentation.mappedFunctor (𝟭 A)).obj I).flip).ιTotalOrZero
            (ComplexShape.up ℤ) (n - s) s n ≫
              (CochainComplex.mappingCone.inr aug).f n)) := by
  let S : ℤ → ∀ n : ℤ, Subobject ((CochainComplex.mappingCone aug).X n) :=
    fun p n ↦ coneFiltrationStep K I aug b p n
  have hprops := coneFiltrationStep_props K I a b hIbelow hKbelow aug haug
  obtain ⟨F, hF⟩ := filtration_of_degreewise (CochainComplex.mappingCone aug) S
    (by simpa [S] using hprops.1) (by simpa [S] using hprops.2)
  refine ⟨F, ?_⟩
  intro p n
  simpa [S, coneFiltrationStep] using hF p n


end CategoryTheory.Functor
