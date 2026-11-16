import Langlands.GroupScheme.Reductive.IdentityComponentLocusProof
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.SplitSemisimpleRootSpanProof
import Langlands.GroupScheme.Torus.GeometricRootProfiles

/-! # Affine semisimple neighbourhoods from actual root supports -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A split maximal torus detects semisimplicity by the finite index of the
integral span of its actual roots, without a chosen root datum in the conclusion. -/
theorem isSemisimple_iff_finite_actualRootSpan {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) :
    haveI := hG.isAffineHom
    IsSemisimple G ↔ Finite (characterLattice T ⧸ Submodule.span ℤ (roots i)) := by
  have := hG.isAffineHom
  obtain ⟨J, hJ, P, hP, _⟩ := rootDatumExistence k G hG T hT i hi
  simpa only [RootPairing.rootSpan, hP.2.1] using
    splitSemisimpleRootSpan k G hG T hT i hi J P hP

namespace splitTorus

variable {r : Type u} [CommRing r] (I : Type u) [Fintype I] [DecidableEq I]
  (G : GroupScheme (Spec (CommRingCat.of r))) [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : splitTorus (Spec (CommRingCat.of r)) I ⟶ G)

local instance semisimpleAffine_smooth_geometricFiber (s : Spec (CommRingCat.of r)) :
    Smooth (geometricFiber G s).X.hom :=
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

local instance semisimpleAffine_affine_geometricFiber (s : Spec (CommRingCat.of r)) :
    IsAffineHom (geometricFiber G s).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (geometricPoint _ s)))

/-- The integral root span of the actual geometric identity component,
expressed in the common character coordinates of the standard split torus. -/
def geometricExponentRootSpan (s : Spec (CommRingCat.of r)) : Submodule ℤ (I → ℤ) :=
  Submodule.span ℤ (geometricExponentRoots I G i s)

omit [DecidableEq I] in
/-- On the reductive and self-centralizing loci, semisimplicity is detected
by finite index of the actual root support in common integral coordinates. -/
theorem mem_identityComponentSemisimpleLocus_iff_finite_rootSpan
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hs : s ∈ identityComponentReductiveLocus G)
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    IsSemisimple (identityComponent (geometricFiber G s)) ↔
      Finite ((I → ℤ) ⧸ geometricExponentRootSpan I G i s) := by
  let k := AlgebraicClosure ((Spec (CommRingCat.of r)).residueField s)
  let j := geometricIdentityComponentHom I G i s
  have hj : IsMaximalTorus (T := commGroupScheme _ I) j :=
    isMaximalTorus_geometricIdentityComponentHom_of_mem I G i hi s hself
  have hc := isSemisimple_iff_finite_actualRootSpan
    (identityComponent (geometricFiber G s)) hs (commGroupScheme _ I)
    (isSplitTorus_splitTorus I) j hj
  let e : (I → ℤ) ≃ₗ[ℤ] characterLattice (commGroupScheme (Spec (CommRingCat.of k)) I) :=
    (characterLatticeEquiv k I).symm.toIntLinearEquiv
  have hpreimage : geometricExponentRoots I G i s =
      e ⁻¹' roots (T := commGroupScheme (Spec (CommRingCat.of k)) I) j := by
    ext m
    change exponentCharacter (Spec (CommRingCat.of k)) I m ∈
      roots (T := commGroupScheme (Spec (CommRingCat.of k)) I) j ↔ e m ∈
        roots (T := commGroupScheme (Spec (CommRingCat.of k)) I) j
    rw [exponentCharacter_eq_characterLatticeEquiv_symm]
    rfl
  have hmap : (Submodule.span ℤ (geometricExponentRoots I G i s)).map
      e.toLinearMap = Submodule.span ℤ
        (roots (T := commGroupScheme (Spec (CommRingCat.of k)) I) j) := by
    rw [Submodule.map_span, hpreimage]
    congr 1
    ext χ
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact hm
    · intro hχ
      exact ⟨e.symm χ, by simpa only [Set.mem_preimage, e.apply_symm_apply] using hχ,
        e.apply_symm_apply χ⟩
  let q := Submodule.Quotient.equiv
    (Submodule.span ℤ (geometricExponentRoots I G i s))
    (Submodule.span ℤ (roots (T := commGroupScheme _ I) j)) e hmap
  refine hc.trans ?_
  constructor
  · intro h
    let := h
    exact Finite.of_equiv _ q.toEquiv.symm
  · intro h
    let : Finite ((I → ℤ) ⧸ Submodule.span ℤ (geometricExponentRoots I G i s)) := h
    exact Finite.of_equiv _ q.toEquiv

/-- A semisimple fibre with a supplied closed self-centralizing split torus
has an open neighbourhood of semisimple geometric identity components. -/
theorem exists_open_subset_identityComponentSemisimpleLocus
    (hi : IsClosedSubgroup i) (s : Spec (CommRingCat.of r))
    (hs : IsSemisimple (identityComponent (geometricFiber G s)))
    (hself : s ∈ geometricSelfCentralizingTorusLocus I G i) :
    ∃ U : Set (Spec (CommRingCat.of r)), IsOpen U ∧ s ∈ U ∧
      U ⊆ {t | IsSemisimple (identityComponent (geometricFiber G t))} := by
  let V := identityComponentReductiveLocus G ∩ geometricSelfCentralizingTorusLocus I G i
  let W := {t | geometricExponentRoots I G i t = geometricExponentRoots I G i s}
  have hV : IsOpen V :=
    (identityComponentReductiveLocusOpen _ G).inter
      (isOpen_geometricSelfCentralizingTorusLocus I G i hi)
  have hW : IsOpen W := (isLocallyConstant_geometricExponentRoots I G i).isOpen_fiber _
  have hsred : s ∈ identityComponentReductiveLocus G := hs.isConnectedReductive
  have hfinite := (mem_identityComponentSemisimpleLocus_iff_finite_rootSpan
    I G i hi s hsred hself).mp hs
  refine ⟨V ∩ W, hV.inter hW, ⟨⟨hsred, hself⟩, rfl⟩, ?_⟩
  rintro t ⟨⟨htred, htself⟩, ht⟩
  apply (mem_identityComponentSemisimpleLocus_iff_finite_rootSpan
    I G i hi t htred htself).mpr
  change geometricExponentRoots I G i t = geometricExponentRoots I G i s at ht
  simpa only [geometricExponentRootSpan, ht] using hfinite

end splitTorus

end Langlands.GroupScheme
