/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonShiftSquare

/-! # Shift stability of localized tensor comparison

Source: Stacks Project, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-localized-tensor-comparison-shift).
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- Core component transport for shift stability.

Proof: shift U by -n to a representative of X, transport its tensor model and
comparison square across the canonical tensor, scalar-extension and cohomology
shift isomorphisms, and apply hX. Naturality identifies the transported map
with the displayed comparison composite.
Source: Stacks Project, Tag 0DJA(1).
(blueprint: lem-pc-localized-tensor-comparison-shift-component). -/
theorem localizedTensorComparisonProperty_shift_component
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : localizedTensorComparisonProperty R A B C Q N t X) (n : ℤ)
    (U : CochainComplex (ModuleCat.{u} A) ℤ)
    (hU : Nonempty (DerivedCategory.Q.obj U ≅ X⟦n⟧))
    (hK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic)
    (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ) :
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  obtain ⟨eU⟩ := hU
  have hV : Nonempty (DerivedCategory.Q.obj (U⟦-n⟧) ≅ X) := ⟨
    (DerivedCategory.Q.commShiftIso (-n)).app U ≪≫
      (shiftFunctor _ (-n)).mapIso eU ≪≫
      (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).app X⟩
  have hVK : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V (U⟦-n⟧) (curriedTensor _)).Acyclic := by
    intro V hV j
    apply HomologicalComplex.ExactAt.of_iso _
      (CochainComplex.mapBifunctorShift₂Iso V U (curriedTensor _) (-n)).symm
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hK V hV (-n + j)).isZero_homology.of_iso
      ((CochainComplex.ShiftSequence.shiftIso (ModuleCat.{u} A)
        (-n) j (-n + j) rfl).app
          (CochainComplex.mapBifunctor V U (curriedTensor _)))
  obtain ⟨mV, eS, eT, heq⟩ :=
    exists_localizedTensorComparison_shift_square R A B C Q N t U n mU i
  have hi := hX (U⟦-n⟧) hV hVK mV (i + n)
  change IsIso (_ ≫ _) at hi ⊢
  rw [heq]
  infer_instance


/-- Localized tensor comparison in all degrees is preserved by integer shifts.
Source: Stacks Project, Tag 0DJA(1), reindexing the cohomological comparison.

Proof: given a K-flat representative U of X[n], shift U by -n. The localization
commutes with shift, and the inverse-shift equivalence gives a representative
of X. Shifts preserve K-flatness: tensoring an acyclic test complex with a
shifted complex is a shift of an acyclic total tensor complex. Apply hX to
this representative and all its base-derived models.
The first-variable total-tensor shift isomorphism identifies
(U[-n] tensor Q)[n] with U tensor Q. Termwise scalar extension commutes with
shift, and the corresponding tensor shift identifies
(F(U[-n]) tensor N)[n] with F(U) tensor N. The tensor-shift signs occur on
both sides of the comparison; naturality identifies the shifted chain map
mu.inv followed by F(U[-n]) tensor t with the map for U.
Transport a base-derived model of U tensor Q through these shift isomorphisms
and reindex its cohomology in degree i to degree i+n for the unshifted complex.
The left-derived functor commutes with shifts by uniqueness of its universal
counit. This uniqueness is compatible with multiplication by A and the B
module structure, so the cohomology transports are A tensor_R B-linear.
The comparison_eq and localized_eq equations identify the resulting square
with the shifted comparison square. Scalar extension to C preserves these
source isomorphisms and cohomology supplies target isomorphisms. Its unshifted
horizontal arrow is invertible by hX; hence the shifted arrow is invertible.
This proves the predicate for each U, model and degree. For n=0 these are the
identity transports. The argument needs neither flatness of C nor bounds on Q.
(blueprint: lem-pc-localized-tensor-comparison-shift). -/
theorem localizedTensorComparisonProperty_shift
    (X : DerivedCategory (ModuleCat.{u} A))
    (hX : localizedTensorComparisonProperty R A B C Q N t X) (n : ℤ) :
    localizedTensorComparisonProperty R A B C Q N t (X⟦n⟧) := by
  rw [localizedTensorComparisonProperty]
  intro U hU hK mU i
  exact localizedTensorComparisonProperty_shift_component R A B C Q N t X hX n U hU hK mU i

end ModuleCat
