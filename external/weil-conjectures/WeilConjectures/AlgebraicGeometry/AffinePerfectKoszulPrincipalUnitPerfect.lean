/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.ShiftedKoszulAugmentation
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import WeilConjectures.AlgebraicGeometry.AffineKoszulGeometricProperties

@[expose] public section

universe a b
open CategoryTheory
namespace AlgebraicGeometry

private theorem shifted_koszul_strictly_perfect (A : Type a) [CommRing A] (r : ℕ)
    (f : Fin r → A) (U : (Spec (.of A)).Opens) :
    let K := ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
      (shiftedKoszulComplex A r f))
    Scheme.IsStrictlyPerfect (Spec (.of A)) U
      (((SheafOfModules.overFunctor.{a}
        (moduleRings (Spec (.of A)).toRingedSpace) U).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) := by
  classical
  let L := shiftedKoszulChain A r f
  let T := tilde.functor (.of A)
  let : T.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let F := SheafOfModules.overFunctor.{a}
    (moduleRings (Spec (.of A)).toRingedSpace) U
  have hpos (n : ℤ) (hn : 0 < n) :
      Limits.IsZero (F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n))) := by
    apply F.map_isZero
    apply T.map_isZero
    apply L.isZero_extend_X
    intro q
    change -(q : ℤ) ≠ n
    omega
  have hneg (n : ℤ) (hn : n ≤ 0) : ∃ q : ℕ, -(q : ℤ) = n := by
    exact ⟨(-n).toNat, by omega⟩
  refine ⟨⟨-(r : ℤ), 0, ?_⟩, ?_⟩
  · intro n hn
    change Limits.IsZero (F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n)))
    by_cases hp : 0 < n
    · exact hpos n hp
    · obtain ⟨q, hq⟩ := hneg n (by omega)
      have hrq : r < q := by omega
      exact (F.map_isZero (T.map_isZero
        (isZero_exteriorPower_finsupp_of_lt A r (q + 1) (by omega)))).of_iso
        (F.mapIso (T.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)))
  · intro n
    change ∃ m : ℕ, ∃ (ι : F.obj (T.obj
        ((L.extend ComplexShape.embeddingDownNat).X n)) ⟶ _)
      (π : _ ⟶ F.obj (T.obj ((L.extend ComplexShape.embeddingDownNat).X n))),
        ι ≫ π = 𝟙 _
    by_cases hp : 0 < n
    · exact ⟨0, 0, 0, (hpos n hp).eq_of_src _ _⟩
    · obtain ⟨q, hq⟩ := hneg n (by omega)
      obtain ⟨m, ⟨e⟩⟩ := exists_tilde_exteriorPower_iso_free A r (q + 1) U
      let e' := F.mapIso (T.mapIso (L.extendXIso ComplexShape.embeddingDownNat hq)) ≪≫ e
      exact ⟨m, e'.hom, e'.inv, e'.hom_inv_id⟩

/-- The shifted Koszul complex on powers of a finite sequence gives a perfect affine object.
Source: Stacks Project, Tag 08CX and Definition 08CM.
(blueprint: lem-sc-affine-perfect-koszul-principal-unit-perfect).

Proof: In degree `-n` the complex is the exterior power of degree `n + 1` of `A^r`.
The exterior powers have the wedge bases indexed by subsets of the standard basis,
so they are finite free and vanish when `n + 1 > r`. Extension gives zero in positive
cochain degrees, and negating the differential does not change any term. Applying
associated sheaves termwise therefore gives a bounded complex of finite free structure
sheaf modules. Restrict this complex to the whole scheme, or any neighbourhood of a
point. Restriction preserves finite free modules and zero terms, and its derived
comparison identifies this strictly perfect model with the restricted derived object.
This is the definition of perfectness. For `r = 0` all terms are zero; if `A` is the
zero ring, the spectrum is empty and the pointwise conclusion is vacuous. -/
theorem affine_perfect_koszul_principal_unit_perfect
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    Scheme.IsPerfect (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
          (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))) := by
  classical
  let K := ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
    (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
    _ _ _ _ (tilde.functor (.of A))
    ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
    (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))
  change Scheme.IsPerfect (Spec (.of A)) (DerivedCategory.Q.obj K)
  intro x
  let F := SheafOfModules.overFunctor.{a}
    (moduleRings (Spec (.of A)).toRingedSpace) ⊤
  refine ⟨⊤, trivial, (F.mapHomologicalComplex (.up ℤ)).obj K,
    shifted_koszul_strictly_perfect A r (fun i ↦ f i ^ e) ⊤,
    ⟨F.mapDerivedCategoryFactors.app K⟩⟩

end AlgebraicGeometry
