import Langlands.GroupScheme.Quaternionic.SpinKernelAssembly
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.CocharacterDatum

/-! # Uniqueness of Levi lifts through a quaternionic spin cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  {S C : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- A spin cover can be cancelled on homomorphisms from any connected reductive source. -/
theorem cancel_of_connectedReductive (hπ : σ.IsSpinCover q π)
    (hC : IsConnectedReductive C) {a b : C ⟶ S} (hab : a ≫ π = b ≫ π) : a = b := by
  let := hπ.smooth
  obtain ⟨p, hp, hpp⟩ := hπ.exists_centralIsogeny
  apply hp.cancel_of_connectedReductive hC
  apply (cancel_mono (identityComponentι (σ.isometryGroup q))).mp
  simpa only [Category.assoc, hpp] using hab

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q} {e f : n → D} {h : σ.IsHyperbolicPair q e f}
  {mu mu' : (Gm (Spec (CommRingCat.of K))).toGrp ⟶ S}
  {psi psi' : CentralSimpleUnits.normOne K D ⟶ S}

/-- The scalar part of a Levi lift is uniquely determined by the Levi action. -/
theorem IsLeviLift.scalar_eq (hl : IsLeviLift h π mu psi)
    (hl' : IsLeviLift h π mu' psi') (hπ : σ.IsSpinCover q π) : mu = mu' := by
  apply hπ.cancel_of_connectedReductive isSplitTorus_gm.isConnectedReductive
  apply Grp.hom_ext
  apply (cancel_epi (CocharacterDatum.coordIso
    (Gm (Spec (CommRingCat.of K))).toGrp).hom).mp
  let A := CocharacterDatum.coordAlgebra (Gm (Spec (CommRingCat.of K))).toGrp
  let x := (CocharacterDatum.coordIso (Gm (Spec (CommRingCat.of K))).toGrp).hom
  obtain ⟨t, ht⟩ := (gmPoint A).surjective x
  change (x ≫ mu.hom.hom) ≫ π.hom.hom = (x ≫ mu'.hom.hom) ≫ π.hom.hom
  rw [← ht]
  exact (hl.1 A t).trans (hl'.1 A t).symm

/-- The norm-one part of a Levi lift is unique when its source is connected reductive. -/
theorem IsLeviLift.normOne_eq (hl : IsLeviLift h π mu psi)
    (hl' : IsLeviLift h π mu' psi') (hπ : σ.IsSpinCover q π)
    (hD : IsConnectedReductive (CentralSimpleUnits.normOne K D)) : psi = psi' := by
  apply hπ.cancel_of_connectedReductive hD
  exact hl.2.trans hl'.2.symm

/-- Both homomorphisms in a Levi lift are unique under the connected reductive hypothesis. -/
theorem IsLeviLift.unique (hl : IsLeviLift h π mu psi)
    (hl' : IsLeviLift h π mu' psi') (hπ : σ.IsSpinCover q π)
    (hD : IsConnectedReductive (CentralSimpleUnits.normOne K D)) : mu = mu' ∧ psi = psi' :=
  ⟨hl.scalar_eq hl' hπ, hl.normOne_eq hl' hπ hD⟩

end Langlands.GroupScheme.Quaternionic.SpinKernel
