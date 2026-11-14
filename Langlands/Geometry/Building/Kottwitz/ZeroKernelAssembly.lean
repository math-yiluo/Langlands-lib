import Langlands.Geometry.Building.Kottwitz.SimplyConnectedZeroKernelReduction
import Langlands.Geometry.Building.Kottwitz.CentralSurjectionZeroSurjectivity
import Langlands.Geometry.Building.Kottwitz.ZeroKernelReduction
import Langlands.Geometry.Building.Kottwitz.ZExtensionKernelStatement

/-! # Assembly of the Kottwitz zero-kernel reduction -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Geometry.Building.Kottwitz

/-- The unramified zero-kernel equality follows from the torus kernel,
the two map specifications and z-extension kernel surjectivity. -/
def UnramifiedZeroKernelReductionStatement : Prop :=
  TorusKottwitzKernelStatement.{u} →
  SimplyConnectedDerivedKottwitzStatement.{u} →
  ReductiveKottwitzExistenceStatement.{u} →
  ZExtensionKottwitzKernelSurjectivityStatement.{u} →
  UnramifiedZeroKernelStatement.{u}

/-- Subgroup images commute with the actual coefficient-point comparisons. -/
theorem map_comap_baseChangeCoeffEquiv
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    {H G : GroupScheme (Spec (CommRingCat.of k))}
    (p : H ⟶ G) (S : Subgroup (H.affinePoints (CommAlgCat.of k L))) :
    (S.comap (baseChangeCoeffEquiv k L H).toMonoidHom).map
        (rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map p)) =
      (S.map (H.affinePointsTarget p (CommAlgCat.of k L))).comap
        (baseChangeCoeffEquiv k L G).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨baseChangeCoeffEquiv k L H x, hx,
      (baseChangeCoeffEquiv_map k L p x).symm⟩
  · rintro ⟨x, hx, hxy⟩
    refine ⟨(baseChangeCoeffEquiv k L H).symm x, ?_, ?_⟩
    · change baseChangeCoeffEquiv k L H
        ((baseChangeCoeffEquiv k L H).symm x) ∈ S
      rw [MulEquiv.apply_symm_apply]
      exact hx
    · apply (baseChangeCoeffEquiv k L G).injective
      rw [baseChangeCoeffEquiv_map, MulEquiv.apply_symm_apply]
      exact hxy

/-- The full kernel of a z-extension is central and is a torus. -/
theorem zExtension_central_torus_kernel
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (z : ZExtension G) :
    IsCentral (kernelι z.p) ∧ IsTorus (kernel z.p) := by
  have hc : IsCentral (kernelι z.p) := by
    apply (isCentral_iff_range_le_center _).2
    rw [z.isZExtension.quotient.2.2.2]
    exact (isCentral_iff_range_le_center _).1 z.isZExtension.central
  have hZ : IsTorus z.Z.toGrp := by
    obtain ⟨L, hL, aL, _, _, hs, _⟩ := z.isZExtension.induced
    exact ⟨L, hL, aL, hs⟩
  let : IsClosedImmersion z.i.hom.hom.left := z.isZExtension.closed
  let : Mono z.i.hom.hom := Over.mono_of_mono_left _
  exact ⟨hc, IsTorus.of_iso
    (KernelRepresentative.iso z.p z.i z.isZExtension.quotient.2.2.2) hZ⟩

/-- The torus kernel input and z-extension kernel surjectivity give the
unramified kernel equality for every coefficient field of definition. -/
theorem unramifiedZeroKernel_of_torus_zExtension :
    UnramifiedZeroKernelReductionStatement.{u} := by
  intro htorus hscmap hred hzker F _ _ _ _ k _ _ _ _ _ _ G hG E
  obtain ⟨z⟩ := (hred F k G hG).1
  let B := GroupScheme.baseChange (baseMap k (UnramifiedClosure F))
  have hHK := connectedReductiveFieldExtensionStatement k (UnramifiedClosure F)
    z.H z.isZExtension.source_reductive
  obtain ⟨D, C, d, π, hcover⟩ :=
    simplyConnectedDerivedCoverExistence (UnramifiedClosure F)
      (baseChanged k (UnramifiedClosure F) z.H) hHK
  let EH := UnramifiedZeroDatum.ofDerivedCover d π hcover
  obtain ⟨hp, hk⟩ := zExtension_central_torus_kernel z
  have hpK : IsCentral (kernelι (B.map z.p)) := by
    have hc := (hp.baseChange (baseMap k (UnramifiedClosure F))).comp
      (kernelBaseChangeIso (baseMap k (UnramifiedClosure F)) z.p).inv
    simpa only [kernelBaseChangeIso_inv_ι] using hc
  have hkK : IsTorus (kernel (B.map z.p)) :=
    IsTorus.of_iso (kernelBaseChangeIso (baseMap k (UnramifiedClosure F)) z.p).symm
      hk.baseChange
  let : Surjective (B.map z.p).hom.hom.left :=
    (z.isZExtension.quotient.baseChange (baseMap k (UnramifiedClosure F))).2.1
  have hzero := map_zeroPoints_eq_of_centralSurjection EH E (B.map z.p) hpK hkK
  have hHker := simplyConnectedZeroKernel_of_torus htorus hscmap F k z.H
    z.isZExtension.source_reductive z.isZExtension.derived_simplyConnected EH
  have hmap :=
    (hred F k z.H z.isZExtension.source_reductive).2.2.2.2.1
      z.isZExtension.derived_simplyConnected
  rw [← hmap] at hHker
  rw [← hzero, hHker, map_comap_baseChangeCoeffEquiv, hzker.1 F k G hG z]

/-- Complete conditional reduction of KP Proposition 11.5.4 to the torus
kernel, map specifications, z-extension kernel surjectivity and descent. -/
theorem zeroKernel_of_torus_zExtension
    (htorus : TorusKottwitzKernelStatement.{u})
    (hscmap : SimplyConnectedDerivedKottwitzStatement.{u})
    (hred : ReductiveKottwitzExistenceStatement.{u})
    (hzker : ZExtensionKottwitzKernelSurjectivityStatement.{u})
    (hmap : ReductiveKottwitzDescentStatement.{u})
    (hzero : UnramifiedZeroDescentStatement.{u}) :
    ZeroKernelStatement.{u} :=
  zeroKernel_of_unramified hmap hzero
    (unramifiedZeroKernel_of_torus_zExtension htorus hscmap hred hzker)

end Langlands.Geometry.Building.Kottwitz
