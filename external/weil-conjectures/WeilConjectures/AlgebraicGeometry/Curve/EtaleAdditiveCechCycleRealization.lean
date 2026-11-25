/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechNormalization
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechAlphaQuasiIso
import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveCechBetaClosed
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-! # Realizing additive Čech cycles in the augmented resolution total
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2. -/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every coefficient Čech cycle has a global-resolution representative with
matching augmentation classes. No edge equivalence or inverse image is involved.
Source: Stacks Project, Tag 01EQ, Lemma 20.11.2, the two augmentation arrows.
(blueprint: lem-pbc-etale-additive-cech-cycle-realization)

Proof: Identify unit module sections on an intersection with the lifted additive
structure-sheaf sections on its open subscheme, using restrictFunctorΓ. The
augmentation into I⁰ commutes with restrictions and has zero vertical differential.
It therefore defines the coefficient augmentation beta as a map of complexes
(after applying ULift). Thus beta of the supplied cycle is a total cycle tβ.
The restrictions from global sections define the augmentation alpha; the sign
in Čech degree zero is +1. Each resolution term is injective, so its augmented
open-cover Čech row is exact in positive degrees and computes global sections
in degree zero. The first-quadrant row filtration of the cone of alpha is finite
in each total degree and has acyclic rows, hence alpha is a quasi-isomorphism.
Choose the preimage of the class of tβ under H(alpha), then a global cycle s
representing that preimage (homologyπ is surjective). Let tα be alpha of s.
Naturality of homologyπ proves equality of the two total classes. Only the
covering condition is used, not affine acyclicity. In degree zero this is ordinary
sheaf gluing; an empty cover forces X empty and all these section groups zero.
Empty intersections and repeated opens are handled by the same restriction maps. -/
theorem etaleAdditiveCech_cycle_realization
    {X : Scheme.{u}} {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hcover : iSup U = ⊤)
    (I : InjectiveResolution X.etaleAdditiveSheaf) (n : ℕ)
    (z : (cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).cycles n) :
    ∃ (s : (additiveCechGlobal I).cycles n)
      (tα tβ : (additiveCechTotal U I).cycles n),
      (additiveCechTotal U I).iCycles n tα =
        additiveCechAlpha U I n ((additiveCechGlobal I).iCycles n s) ∧
      (additiveCechTotal U I).iCycles n tβ = additiveCechBeta U I n
        ((cechOver X.toSpecΓ U
          (SheafOfModules.unit X.ringCatSheaf)).iCycles n z) ∧
      (additiveCechTotal U I).homologyπ n tα =
        (additiveCechTotal U I).homologyπ n tβ := by
  classical
  obtain ⟨a, ha, hq⟩ := etaleAdditiveCech_alpha_quasiIso U hcover I
  have : QuasiIso a := hq
  let T := additiveCechTotal U I
  let G := additiveCechGlobal I
  let x := additiveCechBeta U I n
    ((cechOver X.toSpecΓ U (SheafOfModules.unit X.ringCatSheaf)).iCycles n z)
  have hx : (T.sc n).g x = 0 := by
    change T.d n ((ComplexShape.up ℕ).next n) x = 0
    rw [(ComplexShape.up ℕ).next_eq' (by simp : (ComplexShape.up ℕ).Rel n (n + 1))]
    exact etaleAdditiveCech_beta_closed U I n z
  let tβ : T.cycles n := (T.sc n).abCyclesIso.inv ⟨x, hx⟩
  have hβ : T.iCycles n tβ = x :=
    (T.sc n).abCyclesIso_inv_apply_iCycles ⟨x, hx⟩
  obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective
    (HomologicalComplex.homologyMap a n)).mp inferInstance (T.homologyπ n tβ)
  obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective
    (G.homologyπ n)).mp inferInstance c
  let tα := HomologicalComplex.cyclesMap a n s
  refine ⟨s, tα, tβ, ?_, hβ, ?_⟩
  · have h := ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i a n) s
    simpa only [ConcreteCategory.comp_apply, ha] using h
  · have h := ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality a n) s
    simp only [ConcreteCategory.comp_apply] at h
    exact h.symm.trans (by rw [hs, hc])

end AlgebraicGeometry.Scheme.Modules
