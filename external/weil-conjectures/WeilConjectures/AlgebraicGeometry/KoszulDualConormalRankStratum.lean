/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.AffineConormalFrame
import WeilConjectures.RingTheory.KoszulConormalBasis
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Local rank of the dual conormal for a Koszul-regular immersion
Source: Stacks Project, Duality for Schemes, Tags 0BQZ and 0BR0.
(blueprint: lem-sc-koszul-dual-conormal-rank-stratum). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The dual conormal restricts to a finite locally free module of rank n on the rank-n
stratum. Source: Stacks Project, Duality for Schemes, Tags 0BQZ and 0BR0.
(blueprint: lem-sc-koszul-dual-conormal-rank-stratum).

Proof: On an affine neighbourhood supplied by hregular, put A = O_Y(U), I = ker(i),
and B = A/I. The pullback of the ideal sheaf is the associated sheaf of I/I².
For generators f of I, generation gives a surjection B^m → I/I². A relation on their
classes lifts to a relation modulo I². Subtract products of generators to turn it into
an actual first Koszul cycle. Koszul regularity gives H₁ = 0, so it is a boundary.
The boundary coefficients lie in I, proving injectivity of B^m → I/I². Thus the
conormal has a finite local basis. Internal Hom into the unit has the dual basis,
of the same size m; this description commutes with restriction. At every point of
such a chart its stalk finrank is m, since the stalk is a nonzero local ring and the
localized basis still has m elements. On the rank-n stratum hr therefore gives m = n.
Restricting the affine trivializations to that stratum yields local generators data
with n elements and invertible basis maps, which is IsFiniteLocallyFreeOfRank n.
For n = 0 these are empty bases and the dual is zero. An empty stratum satisfies
this local condition vacuously. -/
theorem koszulRegularImmersion_dual_conormal_rank_stratum {Z Y : Scheme.{u}} (i : Z ⟶ Y)
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
    ((Scheme.Modules.restrictFunctor (Scheme.Modules.exteriorRankOpen r n).ι).obj
      (SheafOfModules.homObj (R := Z.sheaf)
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
        (SheafOfModules.unit Z.ringCatSheaf))).IsFiniteLocallyFreeOfRank n := by
  classical
  let C := (Scheme.Modules.tensorPullback i).obj i.ker.toModules
  let D := SheafOfModules.homObj (R := Z.sheaf) C
    (SheafOfModules.unit Z.ringCatSheaf)
  let S := Scheme.Modules.exteriorRankOpen r n
  have frames (x : S.toScheme) : ∃ W : Z.Opens, x.1 ∈ W ∧
      Nonempty (D.over W ≅ SheafOfModules.free (ULift.{u} (Fin n))) := by
    obtain ⟨U, hxU, m, f, hf, hreg⟩ := hregular x.1
    obtain ⟨b, _⟩ := ExteriorAlgebra.exists_koszul_conormal_basis
      Γ(Y, U.1) (i.ker.ideal U) m f hreg hf
    obtain ⟨⟨e⟩, hdim⟩ := affine_conormal_frame i U m b
    have hm := hdim x.1 hxU
    let W := i ⁻¹ᵁ U.1
    have hmn : m = n := by
      calc
        m = r x.1 := (hr x.1 |>.trans hm).symm
        _ = n := x.2
    rw [hmn] at e
    refine ⟨W, hxU, ⟨?_⟩⟩
    exact SheafOfModules.overHomObjIso C (SheafOfModules.unit Z.ringCatSheaf) W ≪≫
      ((SheafOfModules.homFunctor (Z.sheaf.over W)).flip.obj
        (SheafOfModules.unit (Z.ringCatSheaf.over W))).mapIso e.symm.op ≪≫
      SheafOfModules.homObjFreeUnitIso (ULift.{u} (Fin n))
  choose W hxW e using frames
  let V : S.toScheme → S.toScheme.Opens := fun x ↦ S.ι ⁻¹ᵁ W x
  have hV : ⨆ x, V x = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxW x⟩
  apply Scheme.Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free
    ((Scheme.Modules.restrictFunctor S.ι).obj D) (fun x ↦ (V x).ι)
  · simpa only [Scheme.Opens.opensRange_ι] using hV
  · intro x
    let E := Scheme.Modules.overIsoFreeEquiv D (W x) (ULift.{u} (Fin n)) (e x).some
    refine ⟨(Scheme.Modules.restrictFunctorComp (V x).ι S.ι).symm.app D ≪≫
      (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι S.ι (W x)).symm).app D ≪≫
      (Scheme.Modules.restrictFunctorComp (S.ι ∣_ W x) (W x).ι).app D ≪≫
      (Scheme.Modules.restrictFunctor (S.ι ∣_ W x)).mapIso E ≪≫
      Scheme.Modules.restrictFreeIso (S.ι ∣_ W x) (ULift.{u} (Fin n))⟩

end AlgebraicGeometry
