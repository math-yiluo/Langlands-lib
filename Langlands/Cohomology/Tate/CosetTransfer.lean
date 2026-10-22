import Langlands.Cohomology.Tate.InverseCosetSum
import Mathlib.RepresentationTheory.Coinvariants

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G)

/-- The subgroup factor when a group element moves a chosen left-coset representative. -/
def schreierElement (g : G) (q : G ⧸ H) : H :=
  ⟨q.out⁻¹ * g * (g⁻¹ • q).out, by
    rw [mul_assoc]
    apply QuotientGroup.eq.mp
    change (QuotientGroup.mk q.out : G ⧸ H) =
      QuotientGroup.mk (g * (g⁻¹ • q).out)
    exact (Quotient.out_eq' q).trans
      ((smul_inv_smul g q).symm.trans
        (congrArg (fun x : G ⧸ H => g • x) (Quotient.out_eq' (g⁻¹ • q)).symm))⟩

/-- The equivariant coordinate map used to compare the two homogeneous resolutions. -/
def cosetCoordinate (g : G) : H :=
  ⟨g * (QuotientGroup.mk g⁻¹ : G ⧸ H).out, by
    simpa only [inv_inv] using
      (QuotientGroup.eq.mp (Quotient.out_eq' (QuotientGroup.mk g⁻¹ : G ⧸ H)).symm)⟩

lemma cosetCoordinate_subgroup_mul (h : H) (g : G) :
    cosetCoordinate H ((h : G) * g) = h * cosetCoordinate H g := by
  apply Subtype.ext
  simp only [cosetCoordinate, mul_inv_rev, Subgroup.coe_mul,
    QuotientGroup.mk_mul_of_mem _ (H.inv_mem h.property), mul_assoc]

lemma cosetCoordinate_inverse_out (q : G ⧸ H) :
    cosetCoordinate H q.out⁻¹ = 1 := by
  apply Subtype.ext
  simp only [cosetCoordinate, inv_inv, Quotient.out_eq', inv_mul_cancel, Subgroup.coe_one]

lemma cosetCoordinate_inverse_out_mul (q : G ⧸ H) (g : G) :
    cosetCoordinate H (q.out⁻¹ * g) = schreierElement H g q := by
  apply Subtype.ext
  change q.out⁻¹ * g * (QuotientGroup.mk (q.out⁻¹ * g)⁻¹ : G ⧸ H).out =
    q.out⁻¹ * g * (g⁻¹ • q).out
  congr 2
  simp only [mul_inv_rev, inv_inv]
  change g⁻¹ • (QuotientGroup.mk q.out : G ⧸ H) = g⁻¹ • q
  exact congrArg (fun x : G ⧸ H => g⁻¹ • x) (Quotient.out_eq' q)

lemma coinvariant_inverseCosetTerm (A : Rep.{u} R G) (g : G) (q : G ⧸ H) (a : A) :
    Representation.Coinvariants.mk (Rep.res H.subtype A).ρ (A.ρ q.out⁻¹ (A.ρ g a)) =
      Representation.Coinvariants.mk (Rep.res H.subtype A).ρ
        (A.ρ (g⁻¹ • q).out⁻¹ a) := by
  have he : A.ρ q.out⁻¹ (A.ρ g a) =
      (Rep.res H.subtype A).ρ (schreierElement H g q)
        (A.ρ (g⁻¹ • q).out⁻¹ a) := by
    change A.ρ q.out⁻¹ (A.ρ g a) =
      A.ρ (q.out⁻¹ * g * (g⁻¹ • q).out) (A.ρ (g⁻¹ • q).out⁻¹ a)
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right]
  rw [he, Representation.Coinvariants.mk_self_apply]

variable [Fintype (G ⧸ H)]

/-- The inverse-coset sum descends through the full coinvariant relations. -/
lemma coinvariant_inverseCosetSum_invariant (A : Rep.{u} R G) (g : G) :
    (Representation.Coinvariants.mk (Rep.res H.subtype A).ρ ∘ₗ inverseCosetSum H A) ∘ₗ
        A.ρ g =
      Representation.Coinvariants.mk (Rep.res H.subtype A).ρ ∘ₗ inverseCosetSum H A := by
  ext a
  simp only [LinearMap.comp_apply, inverseCosetSum_apply, map_sum]
  refine (Finset.sum_congr rfl (fun q _ =>
    coinvariant_inverseCosetTerm H A g q a)).trans ?_
  exact Equiv.sum_comp (MulAction.toPerm g⁻¹)
    (fun q : G ⧸ H =>
      Representation.Coinvariants.mk (Rep.res H.subtype A).ρ (A.ρ q.out⁻¹ a))

/-- The genuine relative norm on coinvariants, used termwise on resolutions. -/
def coinvariantsTransfer (A : Rep.{u} R G) :
    A.ρ.Coinvariants →ₗ[R] (Rep.res H.subtype A).ρ.Coinvariants :=
  Representation.Coinvariants.lift A.ρ
    (Representation.Coinvariants.mk (Rep.res H.subtype A).ρ ∘ₗ inverseCosetSum H A)
    (coinvariant_inverseCosetSum_invariant H A)

lemma coinvariantsTransfer_mk (A : Rep.{u} R G) (a : A) :
    coinvariantsTransfer H A (Representation.Coinvariants.mk A.ρ a) =
      Representation.Coinvariants.mk (Rep.res H.subtype A).ρ (inverseCosetSum H A a) := rfl

lemma coinvariantsTransfer_naturality {A B : Rep.{u} R G} (f : A ⟶ B) :
    Representation.Coinvariants.map (Rep.res H.subtype A).ρ (Rep.res H.subtype B).ρ
        ((Rep.resFunctor H.subtype).map f).hom ∘ₗ coinvariantsTransfer H A =
      coinvariantsTransfer H B ∘ₗ Representation.Coinvariants.map A.ρ B.ρ f.hom := by
  apply Representation.Coinvariants.hom_ext
  ext a
  change Representation.Coinvariants.mk (Rep.res H.subtype B).ρ
      (f.hom (inverseCosetSum H A a)) =
    Representation.Coinvariants.mk (Rep.res H.subtype B).ρ
      (inverseCosetSum H B (f.hom a))
  exact congrArg (Representation.Coinvariants.mk (Rep.res H.subtype B).ρ)
    (inverseCosetSum_naturality H f a)

end Langlands.Tate
