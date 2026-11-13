import Langlands.AbelianScheme.Tate.ConnectedIntegralLatticeReflectionProof
import Mathlib.GroupTheory.OrderOfElement

/-! # Integral automorphisms from stabilizers of realized Tate lattices -/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.Tate

/-- A rational self-isogeny stabilizing an actually realized full Tate lattice
is conjugate to an integral automorphism on that same realizing scheme. -/
def RealizedLatticeStabilizerStatement : Prop :=
  ∀ (_htor : TorsionFiniteEtaleStatement.{u})
    (S : Scheme.{u}) [IsLocallyNoetherian S] [ConnectedSpace S]
    (_hu : ∀ k : GroupScheme.Tate.Index (fun _ => True), IsUnit (k.val : Γ(S, ⊤)))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (s : Spec (.of Ω) ⟶ S) (A B : AbelianScheme S)
    (e : Rationalization.of B ≅ Rationalization.of A)
    (L : AddSubgroup (Rational A (Over.mk s) (fun _ => True))),
    (∀ w : Rational A (Over.mk s) (fun _ => True),
      w ∈ L ↔ ∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk s),
        rationalHomMap (Over.mk s) (fun _ => True) e.hom
          (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x) = w) →
    ∀ a : Rationalization.of A ≅ Rationalization.of A,
      (∀ w : Rational A (Over.mk s) (fun _ => True),
        rationalHomMap (Over.mk s) (fun _ => True) a.hom w ∈ L ↔ w ∈ L) →
      ∃ g : B ≅ B,
        Rationalization.ofHom g.hom = e.hom ≫ a.hom ≫ e.inv ∧
        Rationalization.ofHom g.inv = e.hom ≫ a.inv ≫ e.inv

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) {A B : AbelianScheme S}
  (e : Rationalization.of B ≅ Rationalization.of A)
  (L : AddSubgroup (Rational A (Over.mk s) (fun _ => True)))
  (he : ∀ w : Rational A (Over.mk s) (fun _ => True),
    w ∈ L ↔ ∃ x : GroupScheme.Tate.Full B.toGrp (Over.mk s),
      rationalHomMap (Over.mk s) (fun _ => True) e.hom
        (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x) = w)

include he in
private theorem conjugate_carries_full_image
    (a : Rationalization.of A ≅ Rationalization.of A)
    (ha : ∀ w : Rational A (Over.mk s) (fun _ => True), w ∈ L →
      rationalHomMap (Over.mk s) (fun _ => True) a.hom w ∈ L) :
    ∀ x : GroupScheme.Tate.Full B.toGrp (Over.mk s),
      ∃ y : GroupScheme.Tate.Full B.toGrp (Over.mk s),
        rationalHomMap (Over.mk s) (fun _ => True)
            (e.hom ≫ a.hom ≫ e.inv)
            (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x) =
          GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) y := by
  intro x
  let r := rationalIso (Over.mk s) (fun _ => True) e
  have hx : r (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x) ∈ L :=
    (he _).mpr ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := (he _).mp (ha _ hx)
  refine ⟨y, r.injective ?_⟩
  change r (rationalIso (Over.mk s) (fun _ => True)
    (e.trans (a.trans e.symm))
    (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x)) = r _
  rw [rationalIso_trans, rationalIso_trans]
  change r (r.symm (rationalHomMap (Over.mk s) (fun _ => True) a.hom
    (r (GroupScheme.Tate.toRational B.toGrp (Over.mk s) (fun _ => True) x)))) = r _
  rw [LinearEquiv.apply_symm_apply]
  exact hy.symm

/-- Integral Tate reflection applied to the two actual conjugate arrows. -/
theorem realizedLatticeStabilizer : RealizedLatticeStabilizerStatement.{u} := by
  intro htor S _ _ hu Ω _ _ _ s A B e L he a ha
  let t := rationalIso (Over.mk s) (fun _ => True) a
  have hi : ∀ w : Rational A (Over.mk s) (fun _ => True), w ∈ L →
      rationalHomMap (Over.mk s) (fun _ => True) a.inv w ∈ L := by
    intro w hw
    apply (ha (t.symm w)).mp
    change t (t.symm w) ∈ L
    rwa [LinearEquiv.apply_symm_apply]
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc] using connectedIntegralLatticeReflection htor S hu Ω s B B
      (e.trans (a.trans e.symm))
      (by simpa only [Iso.trans_hom, Iso.symm_inv, Iso.symm_hom] using
        conjugate_carries_full_image s e L he a (fun w hw => (ha w).mpr hw))
      (by simpa only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Category.assoc] using
        conjugate_carries_full_image s e L he a.symm hi)

end Langlands.AbelianScheme.Tate
