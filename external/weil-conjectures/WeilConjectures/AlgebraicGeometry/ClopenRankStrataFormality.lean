/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
import WeilConjectures.AlgebraicGeometry.ClopenRankStrataHomologyLift
import WeilConjectures.AlgebraicGeometry.FiniteZeroDifferentialAssembly
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.DerivedCategory

/-! # Formality of modules on disjoint clopen rank strata

Source: Stacks Tag 0BQZ, single-degree truncation, and Tag 0AVW,
modules over the direct-image algebra.
-/

@[expose] public section

universe u wA

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry

/-- Arbitrary module sheaves on finitely many clopen rank strata can be
reconstructed from their cohomology in the assigned degrees. The family E
is arbitrary; no exterior-power or derived-direct-image computation occurs
in this assertion.

Source: Stacks Tags 0BQZ and 0AVW; reconstruction proof steps 2--4.
(blueprint: lem-sc-clopen-rank-strata-formality)

Proof: The clopen fibers of r partition Z. Glue 1 on each fiber and 0 on
its complement to obtain global sections e_n of O_Z. Their images in
 i_*O_Z are orthogonal idempotents with sum 1; only finitely many fibers
are nonempty. Multiplication by e_n splits each complex of algebra-module
sheaves into image subcomplexes. Differentials commute with scalar
multiplication, and the inclusions and projections exhibit the original
complex as their finite direct sum. The splitting preserves homology and
quasi-isomorphisms. The direct image of E_n from the clopen rank-n stratum
lies entirely in the e_n summand. The hypothesized cohomology isomorphisms
are algebra-linear, hence commute with these idempotents. Consequently
that summand of K has cohomology only in degree n, equal to the direct
image of E_n. Truncation above and below n identifies it with this module
in degree n. Apply the same truncations to the zero-differential comparison
complex. Sum these finitely many isomorphisms and compose with the splitting
isomorphisms. Off the closed image the algebra and all its modules are zero.
If Z is empty every summand is zero. Rank zero is the degree-zero case.
No stratum is required to be open in Y. -/
theorem clopenRankStrata_formality
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (r : LocallyConstant Z ℕ) (hfinite : (Set.range r).Finite)
    (E : ∀ n : ℕ, (Scheme.Modules.exteriorRankOpen r n).toScheme.Modules)
    (T : ℤ → Z.Modules)
    (hT : ∀ n : ℤ, T n = if 0 ≤ n then
      (Scheme.Modules.pushforward (Scheme.Modules.exteriorRankOpen r n.toNat).ι).obj
        (E n.toNat) else 0)
    (K : DerivedCategory (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
    (hK : ∀ n : ℤ, Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj K ≅
        (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj (T n))) :
    Nonempty (DerivedCategory.Q.obj
      (((RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (CochainComplex.of T (fun _ => 0) (fun _ => zero_comp))) ≅ K) := by
  classical
  let C := SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)
  let P := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CochainComplex.of T (fun _ => 0) (fun _ => zero_comp))
  let s : Finset ℤ := hfinite.toFinset.image (fun n : ℕ => (n : ℤ))
  have hzero (n : ℤ) (hn : n ∉ s) : IsZero (F.obj (T n)) := by
    rw [hT n]
    split_ifs with hnonneg
    · have hnot : n.toNat ∉ Set.range r := by
        intro hmem
        apply hn
        exact Finset.mem_image.mpr
          ⟨n.toNat, hfinite.mem_toFinset.mpr hmem, Int.toNat_of_nonneg hnonneg⟩
      have : IsEmpty (Scheme.Modules.exteriorRankOpen r n.toNat).toScheme :=
        ⟨fun x => hnot ⟨x.1, x.2⟩⟩
      exact F.map_isZero ((Scheme.Modules.pushforward
        (Scheme.Modules.exteriorRankOpen r n.toNat).ι).map_isZero
          (Scheme.Modules.isZero_of_isEmpty (E n.toNat)))
    · exact F.map_isZero (isZero_zero _)
  apply DerivedCategory.finiteZeroDifferentialAssembly P
    (fun a b => by simp [P, CochainComplex.of.d]) s
    (fun n hn => hzero n hn) K
    (fun n hn => (hzero n hn).of_iso (hK n).some)
  intro n hn
  obtain ⟨f, hf⟩ := clopenRankStrata_homology_lift i r E T hT K n
    (fun m _ => hK m) (hK n).some.inv
  refine ⟨f, ?_⟩
  have hiso : IsIso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app (F.obj (T n)) ≫
        (DerivedCategory.homologyFunctor C n).map f) := by
    rw [hf]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C n).inv.app (F.obj (T n))) _

end AlgebraicGeometry
