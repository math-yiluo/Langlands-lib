/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardOrdinaryModelCycles
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
import WeilConjectures.AlgebraicGeometry.PicardOrdinaryRawCoordinates

/-! # Scalar coordinates for ordinary pulled-back cycles

Source: Stacks Project, Tag 0BF2, degree-zero calculation; Tags 06Z0 and 0096.
(blueprint: lem-sc-picard-ordinary-scalar-coordinates)
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Scalar coordinates identify all ordinary residue morphisms with the residue
field. The residue differential vanishes, and every annihilating scalar on a smaller
open is an ordinary cycle with the prescribed evaluated coordinate. There is no
derived object or derived morphism in the conclusion.
Source: Stacks Project, Tag 0BF2, degree-zero calculation; Tags 06Z0 and 0096.
(blueprint: lem-sc-picard-ordinary-scalar-coordinates)

Proof: The terms of K are retracts of finite free modules, hence quasi-coherent on
affine U. Under the affine tilde/Gamma equivalence the section bases e0 and e1
therefore determine sheaf bases. In these bases hd says that the sheaf differential
is multiplication by d. Tensor pullback carries these bases to bases on every V
and on Spec κ(w). The source pulled back from W is the structure sheaf, via the
canonical tensor-unit comparison. Its maps to the degree-zero target are its global
sections. At the residue point the degree-zero coordinate is κ(w); denote the
resulting additive equivalence of raw morphisms by b. Each d_i evaluates to zero,
so postcomposition with the pulled-back differential kills every raw morphism.
On V the basis sends a to a morphism x, and its postcomposition has coordinates
a times d restricted to V; it vanishes by the scalar-cycle hypothesis. Pullback
of x to the residue point has coordinate a(w): the structure-sheaf map of the
residue lift is evaluation, and the tensor-unit and composition comparisons are
the canonical ones from the adjunction. These facts give precisely the final
equality. The argument works when m=0, when the outgoing module is zero, and for
arbitrary nonaffine V, since sheaf bases restrict to every open. -/
theorem picard_ordinary_scalar_coordinates
    (W : Scheme.{v}) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (m : ℕ) (d : Fin m → Γ(W, U))
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (e0 : (K.X 0).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] Γ(W, U))
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (hd : ∀ a : Γ(W, U), e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) (e0.symm a)) = a • d)
    (hdw : ∀ i, W.evaluation U w hwU (d i) = 0) :
    let p := picardResidueLift W w U hwU
    ∃ b : ((Modules.tensorPullback (W.fromSpecResidueField w)).obj
        (SheafOfModules.unit (moduleRings W.toRingedSpace)) ⟶
          (Modules.tensorPullback p).obj ((Modules.overEquiv U).functor.obj (K.X 0))) ≃+
            W.residueField w,
      (∀ f, f ∈ picardOrdinaryModelCycles W U K (W.fromSpecResidueField w) p) ∧
      ∀ (V : W.Opens) (hwV : w ∈ V) (hVU : V ≤ U)
        (hs : picardResidueLift W w V hwV ≫ W.homOfLE hVU = p) (a : Γ(W, V)),
        (a • (fun i ↦ W.presheaf.map (homOfLE hVU).op (d i)) = 0) →
        ∃ x : picardOrdinaryModelCycles W U K V.ι (W.homOfLE hVU),
          b (picardOrdinaryModelRestriction W U K (picardResidueLift W w V hwV)
            V.ι (W.fromSpecResidueField w) (W.homOfLE hVU) p
            (picardResidueLift_comp W w V hwV) hs x.val) =
              W.evaluation V w hwV a := by
  dsimp
  obtain ⟨b, b1, c, c1, hb, hc, hres⟩ :=
    picard_ordinary_raw_coordinates W w U hwU hU m d K hK e0 e1 hd
  refine ⟨b, ?_, ?_⟩
  · intro f
    change f ≫ (Modules.tensorPullback (picardResidueLift W w U hwU)).map
      ((Modules.overEquiv U).functor.map (K.d 0 1)) = 0
    apply b1.injective
    rw [hb, map_zero]
    ext i
    simp [hdw]
  · intro V hwV hVU hs a ha
    refine ⟨⟨(c V hVU).symm a, ?_⟩, ?_⟩
    · change (c V hVU).symm a ≫ (Modules.tensorPullback (W.homOfLE hVU)).map
        ((Modules.overEquiv U).functor.map (K.d 0 1)) = 0
      apply (c1 V hVU).injective
      rw [hc, map_zero]
      simpa using ha
    · simpa using hres V hwV hVU hs ((c V hVU).symm a)

end AlgebraicGeometry.Scheme
