/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndConstructibleExtensions
import WeilConjectures.AlgebraicGeometry.SixFunctors.IndHeartKernelsCokernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import all WeilConjectures.AlgebraicGeometry.ConstructibleFiniteHeart

/-!
# The ind-constructible ambient derived category is triangulated

Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived,
node `corollary-ambient-ind-derived--1` (blueprint: corollary-ambient-ind-derived--1).

## Main statements

- `indConstructibleDerived_isTriangulated`: zero, integer shifts, and triangle closure.
- `indConstructibleDerived_isClosedUnderIsomorphisms`: the explicit repleteness clause.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

-- Package the supplied ind-heart results as the weak Serre class API.
private lemma indCohomology_triangulated
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (hKC : IndHeartKernelsCokernelsAssertions Λ X)
    (hExt : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)), S.ShortExact →
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) S.X₁ →
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) S.X₃ →
      ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X) S.X₂) :
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ↦
      ∀ n : ℤ, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  let P := ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
  have : P.ContainsZero := ⟨HasZeroObject.zero.choose, isZero_zero _,
    ObjectProperty.le_ind _ _ (constantModelConstructible_of_isZero Λ X _ (isZero_zero _))⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, fork, hfork, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, hk, _⟩ := hKC _ _ f hA hB
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hfork) hk⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, cofork, hcofork, hA, hB⟩
    obtain ⟨_, _, _, _, _, _, _, _, hc⟩ := hKC _ _ f hA hB
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hcofork) hc⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS hA hB ↦ hExt _ hS hA hB⟩
  change (DerivedCategory.homologyProperty P).IsTriangulated
  infer_instance

/-- The full subcategory of the ordinary derived category whose cohomology objects are
ind-constructible in every degree is triangulated, for each of the two canonical coefficient
rings. `ObjectProperty.ind` uses small filtered colimits in the ambient module category.
Source: blueprint main-20261015, sec-six-functors-basics/sk-cor-ambient-ind-derived,
`sk-cor-ambient-ind-derived-triangulated.md` and its proof, steps 1--7 of the DAG node.

Proof, separately for the canonical coefficients `E` and `Q̄_ℓ`:

1. The zero module is constructible: on each affine open use the single stratum and the zero
   finitely presented scalar module (`definition-constructible-sheaves`). Its constant diagram on
   the one-object filtered category makes it ind-constructible. Since every cohomology of the
   zero complex is zero (`def-weil-abstract-derived-category`), the derived predicate contains
   zero. An isomorphism of complexes induces isomorphisms on every cohomology object; transport
   the filtered-colimit presentation along these isomorphisms to obtain isomorphism closure.
2. For any integers `n,r`, the cohomology-shift isomorphism identifies `Hⁿ(K[r])` with
   `Hⁿ⁺ʳ(K)` (`lem-sp-derived-cohomology-shift`). Thus the predicate is stable under every
   integer shift, including both `[1]` and `[-1]`.
3. For a distinguished triangle `K → L → M → K[1]` with `K,L` in the predicate, apply the
   long exact cohomology sequence in the abelian category of module objects
   (`lem-sf-derived-homology-long-exact`, `pur713-def-module-category`). In each degree it
   gives the exact segment `Hⁿ(K) →α Hⁿ(L) →u Hⁿ(M) →v Hⁿ⁺¹(K) →β Hⁿ⁺¹(L)`.
4. Exactness identifies `ker u` with `im α`, hence `coker α` with the coimage of `u`.
   The coimage map is monic (`lem-weil-pbc-coimage-mono`) with image `ker v`. Apply the same
   result to `v` in the opposite abelian category (`def-sp-abelian`); taking opposites gives
   an epimorphism from `Hⁿ(M)` to `im v = ker β`. Its kernel is `ker v`, since the inclusion
   of `ker β` in `Hⁿ⁺¹(K)` is monic. Therefore these maps form the ambient short exact
   sequence `0 → coker α → Hⁿ(M) → ker β → 0`.
5. The four outer cohomology objects belong to `IndCons`. Fullness makes `α,β` morphisms
   between its objects. Closure under ambient kernels and cokernels
   (`proposition-ind-constructible-sheaves`) puts `coker α` and `ker β` in `IndCons`. Closure under
   extensions (`proposition-ind-constructible-sheaves--7`) puts `Hⁿ(M)` there too. Since `n` was
   arbitrary, `M` satisfies the derived predicate.
6. If instead `L,M` satisfy the predicate, rotate to the distinguished triangle
   `L → M → K[1] → L[1]` (`def-weil-triangulated-category`). Steps 3--5 give `K[1]` in the
   predicate; shift by `[-1]` and use `(K[1])[-1] ≅ K` and steps 1--2 to obtain `K`.
   If `K,M` satisfy it, first shift `K` and rotate twice to
   `M → K[1] → L[1] → M[1]`. Steps 3--5 give `L[1]`; shifting back and using the shift
   isomorphism gives `L`. The rotation maps carry the usual signs, which do not change
   the vertex predicates. This proves all three cases of two-out-of-three.
7. The predicate defines a full subcategory of the ordinary triangulated derived category
   (`def-weil-abstract-derived-category`). Steps 1--6 give zero, all shifts, isomorphism
   closure and the middle-vertex condition. Apply `def-weil-triangulated-subcategory`:
   the inherited shifts and distinguished triangles make this full subcategory triangulated.

(blueprint: corollary-ambient-ind-derived--1). -/
theorem indConstructibleDerived_isTriangulated
    (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpl : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] :
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicSubfieldRingObj X ℓ E)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.continuousMapRingObj E) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) ∧
    ObjectProperty.IsTriangulated (fun K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (padicAlgClRingObj X ℓ)) ↦
      ∀ n : ℤ,
        ObjectProperty.ind.{u + 1}
          (IsConstantModelConstructible (Profinite.padicAlgClRingObj ℓ) X)
          ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  obtain ⟨hE, hQ⟩ := indHeart_kernelsCokernels ℓ p k hp hpl X
  exact ⟨indCohomology_triangulated _ X (hE E)
      (indConstructible_of_shortExact ℓ E X),
    indCohomology_triangulated _ X hQ
      (indConstructible_of_shortExact_padicAlgCl ℓ X)⟩

end AlgebraicGeometry.ProEtale
