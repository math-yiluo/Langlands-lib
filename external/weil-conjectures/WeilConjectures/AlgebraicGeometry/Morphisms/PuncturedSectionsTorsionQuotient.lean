/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsComplex
public import WeilConjectures.Algebra.Homology.IdealPowerTorsionCocomplexInclusion
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedInjectiveRestrictionExact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # The punctured sections complex is the torsion quotient

## References

* Stacks Project, Tag 0BK0, Lemma 51.8.2
* Tag 0A6T, Lemma 51.2.1
* Stacks Project, Tag 09T2
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- On the complement of the closed point, the complex of sections of associated
injective modules is the categorical quotient by maximal-ideal-power torsion.
-/
theorem nonempty_injective_quotient_iso_punctured_sections
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) :
    Nonempty (cokernel (ModuleCat.idealPowerTorsionCocomplexι
        (IsLocalRing.maximalIdeal R) I.cocomplex) ≅
      puncturedSectionsComplex R W I.cocomplex) := by
  classical
  let t := ModuleCat.idealPowerTorsionCocomplexι (IsLocalRing.maximalIdeal R) I.cocomplex
  let r := puncturedSectionsRestriction R W I.cocomplex
  have hr (k : ℕ) := injective_punctured_restriction_exact R W hW (I.cocomplex.X k)
  have hz : t ≫ r = 0 := by
    apply HomologicalComplex.hom_ext
    intro k
    change ModuleCat.ofHom (Ideal.primaryComponent (I.cocomplex.X k)
      (IsLocalRing.maximalIdeal R)).subtype ≫ tilde.toOpen (R := .of R) (I.cocomplex.X k) W = 0
    ext x
    have hx : x.val ∈ (tilde.toOpen (R := .of R) (I.cocomplex.X k) W).hom.ker := by
      rw [(hr k).1]
      exact x.property
    exact hx
  let S := ShortComplex.mk t r hz
  have hS : S.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro k
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2
      change LinearMap.range (Ideal.primaryComponent (I.cocomplex.X k)
        (IsLocalRing.maximalIdeal R)).subtype =
        (tilde.toOpen (R := .of R) (I.cocomplex.X k) W).hom.ker
      rw [Submodule.range_subtype, (hr k).1]
    · change Mono (t.f k)
      exact ModuleCat.idealPowerTorsionCocomplexι_f_mono _ _ _
    · change Epi (tilde.toOpen (R := .of R) (I.cocomplex.X k) W)
      exact (ModuleCat.epi_iff_surjective _).2 (hr k).2
  exact ⟨IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel t) hS.gIsCokernel⟩

end AlgebraicGeometry.Scheme
