import Langlands.Cohomology.Tate.ZeroTransferDefinitions
import Mathlib.RepresentationTheory.Invariants

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) [Fintype (G ⧸ H)]

/-- Trace of a subgroup-equivariant map, using the actual relative norm on the internal Hom. -/
def homTransfer (P A : Rep.{u} R G) :
    (Rep.res H.subtype P ⟶ Rep.res H.subtype A) →ₗ[R] (P ⟶ A) :=
  (Representation.linHom.invariantsEquivRepHom P A).toLinearMap ∘ₗ
    cosetNorm H (Rep.of (Representation.linHom P.ρ A.ρ)) ∘ₗ
      (Representation.linHom.invariantsEquivRepHom
        (Rep.res H.subtype P) (Rep.res H.subtype A)).symm.toLinearMap

/-- The genuine relative trace formula on a vector. -/
lemma homTransfer_apply (P A : Rep.{u} R G)
    (f : Rep.res H.subtype P ⟶ Rep.res H.subtype A) (x : P) :
    (homTransfer H P A f).hom x =
      ∑ q : G ⧸ H, A.ρ q.out (f.hom (P.ρ q.out⁻¹ x)) := by
  change (∑ q : G ⧸ H, cosetAction H (Rep.of (Representation.linHom P.ρ A.ρ))
    ((Representation.linHom.invariantsEquivRepHom
      (Rep.res H.subtype P) (Rep.res H.subtype A)).symm f) q) x = _
  rw [LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro q _
  rw [cosetAction_out]
  rfl

/-- Relative trace commutes with precomposition by an ambient equivariant map. -/
lemma homTransfer_precomp {P Q A : Rep.{u} R G}
    (d : Q ⟶ P) (f : Rep.res H.subtype P ⟶ Rep.res H.subtype A) :
    homTransfer H Q A ((Rep.resFunctor H.subtype).map d ≫ f) =
      d ≫ homTransfer H P A f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (homTransfer H Q A ((Rep.resFunctor H.subtype).map d ≫ f)).hom x =
    (homTransfer H P A f).hom (d.hom x)
  rw [homTransfer_apply, homTransfer_apply]
  apply Finset.sum_congr rfl
  intro q _
  change A.ρ q.out (f.hom (d.hom (Q.ρ q.out⁻¹ x))) =
    A.ρ q.out (f.hom (P.ρ q.out⁻¹ (d.hom x)))
  rw [Rep.hom_comm_apply]

/-- Relative trace commutes with postcomposition by an ambient equivariant map. -/
lemma homTransfer_postcomp {P A B : Rep.{u} R G}
    (f : Rep.res H.subtype P ⟶ Rep.res H.subtype A) (d : A ⟶ B) :
    homTransfer H P B (f ≫ (Rep.resFunctor H.subtype).map d) =
      homTransfer H P A f ≫ d := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change (homTransfer H P B (f ≫ (Rep.resFunctor H.subtype).map d)).hom x =
    d.hom ((homTransfer H P A f).hom x)
  rw [homTransfer_apply, homTransfer_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact (Rep.hom_comm_apply d q.out (f.hom (P.ρ q.out⁻¹ x))).symm

end Langlands.Tate
