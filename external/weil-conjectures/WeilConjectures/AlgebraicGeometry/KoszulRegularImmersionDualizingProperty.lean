/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionDualizingTerm
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Quasi-coherence of the Koszul normal determinant

Source: Stacks Project, Tag 0BQZ and Tag 0BR0
(blueprint: lem-sc-koszul-normal-determinant-qcoherent).
-/

@[expose] public section

universe u wZ

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The explicit rank-stratified normal determinant has quasi-coherent cohomology.

Source: Stacks Project, Duality for Schemes, Tag 0BQZ and Tag 0BR0
(blueprint: lem-sc-koszul-normal-determinant-qcoherent).

Proof: Work on affine neighbourhoods of points of Z supplied by hregular. The
conormal sheaf is the sheaf associated to I/I² over B = A/I. Koszul-regularity
implies H₁-regularity. The classes of the generators are a basis of I/I²:
a relation modulo I² lifts to a first Koszul cycle after subtracting products of
generators, and H₁ = 0 expresses that cycle as a Koszul boundary; its coefficients
therefore lie in I. Surjectivity follows from generation of I. Thus the conormal
and its dual are finite locally free. The prescribed stalk finrank identifies r
with their local rank. On the clopen rank-n stratum the top exterior power is
finite locally free of rank one. Its direct image along the clopen inclusion is
locally that sheaf or zero, hence quasi-coherent. Negative terms are zero. Every
differential of locallyRankedExteriorComplex is zero, so its degree-n cohomology
is its degree-n term. Localization Q preserves this cohomology, proving the
assertion in every degree. The empty scheme and rank zero cause no exception:
the zero-rank determinant is the structure sheaf in degree zero. -/
theorem koszulRegularImmersion_dualizing_property {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))) :
    schemeDerivedQCohProperty Z ((DerivedCategory.Q (C :=
      SheafOfModules.{u} (moduleRings Z.toRingedSpace))).obj
        (Scheme.Modules.locallyRankedExteriorComplex
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r)) := by
  intro n
  let M := SheafOfModules.homObj (R := Z.sheaf)
    ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
    (SheafOfModules.unit Z.ringCatSheaf)
  let K : CochainComplex
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ :=
    Scheme.Modules.locallyRankedExteriorComplex M r
  have hterm : (Scheme.Modules.locallyRankedExteriorTerm M r n).IsQuasicoherent := by
    by_cases hn : 0 ≤ n
    · simpa only [Int.toNat_of_nonneg hn] using
        koszulRegularImmersion_dualizing_term i hregular r hr n.toNat
    · simp only [Scheme.Modules.locallyRankedExteriorTerm, ite_eq_right hn]
      have hzero : IsZero
          (SheafOfModules.free (R := Z.ringCatSheaf) PEmpty.{u + 1}) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply (SheafOfModules.freeHomEquiv _).injective
        funext j
        exact PEmpty.elim j
      exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso hzero.isoZero
        (SheafOfModules.isQuasicoherent_free PEmpty.{u + 1})
  let e : (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) n).obj
      (DerivedCategory.Q.obj K) ≅ Scheme.Modules.locallyRankedExteriorTerm M r n :=
    (DerivedCategory.homologyFunctorFactors _ n).app K ≪≫
      (ShortComplex.HomologyData.ofZeros (K.sc n)
        (by simp [K, Scheme.Modules.locallyRankedExteriorComplex,
        HomologicalComplex.sc, CochainComplex.of.d])
        (by simp [K, Scheme.Modules.locallyRankedExteriorComplex,
        HomologicalComplex.sc, CochainComplex.of.d])).left.homologyIso
  exact (SheafOfModules.isQuasicoherent Z.ringCatSheaf).prop_of_iso e.symm hterm

end AlgebraicGeometry
