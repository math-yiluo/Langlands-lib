/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.KoszulDualConormalRankStratum
import WeilConjectures.AlgebraicGeometry.Modules.Determinant
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! Per-degree quasi-coherence for the Koszul normal determinant.
Source: Stacks Project, Duality for Schemes, Tags 0BQZ and 0BR0
(blueprint: lem-sc-koszul-normal-determinant-term-qcoherent). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Each nonnegative term of the normal determinant complex is quasi-coherent.

Source: Stacks Project, Duality for Schemes, Tags 0BQZ and 0BR0
(blueprint: lem-sc-koszul-normal-determinant-term-qcoherent).

Proof: Around a point of Z choose the affine neighbourhood in hregular and write
A for its ring, I for the ideal and B for A/I. The pulled-back ideal sheaf is
associated to I/I². Koszul regularity implies vanishing of first Koszul homology.
Given a relation on the generator classes modulo I², subtract products of
generators to lift it to a Koszul cycle. Expressing that cycle as a boundary
shows that every coefficient lies in I. Together with generation of I this
proves that the generator classes form a B-basis of I/I². The conormal and
its internal dual are therefore finite locally free on Z. On the clopen
rank-n stratum hr identifies their rank with n. The sectionwise exterior-power
construction, followed by sheafification, gives the associated exterior power
on these affine trivializations, hence a line bundle on that stratum. Direct
image from a clopen subscheme is locally this line bundle or the zero sheaf,
so it is quasi-coherent. Since n is nonnegative, this is the prescribed term.
The empty stratum contributes zero; for n = 0 the empty wedge is the structure
sheaf. Thus rank zero and the empty scheme are included. -/
theorem koszulRegularImmersion_dualizing_term {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (n : ℕ) :
    (Scheme.Modules.locallyRankedExteriorTerm
      (SheafOfModules.homObj (R := Z.sheaf)
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
        (SheafOfModules.unit Z.ringCatSheaf)) r (n : ℤ)).IsQuasicoherent := by
  let U := Scheme.Modules.exteriorRankOpen r n
  let N := (Scheme.Modules.restrictFunctor U.ι).obj
    (SheafOfModules.homObj (R := Z.sheaf)
      ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
      (SheafOfModules.unit Z.ringCatSheaf))
  have : N.IsFiniteLocallyFreeOfRank n :=
    koszulRegularImmersion_dual_conormal_rank_stratum i hregular r hr n
  have : (Scheme.Modules.exteriorPower N n).IsQuasicoherent := inferInstance
  have : IsClosedImmersion U.ι := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [Scheme.Opens.range_ι]
    exact r.isLocallyConstant.isClosed_fiber n
  simpa only [Scheme.Modules.locallyRankedExteriorTerm, Int.natCast_nonneg,
    ite_true, Int.toNat_natCast] using
    Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion U.ι
      (Scheme.Modules.exteriorPower N n)

end AlgebraicGeometry
