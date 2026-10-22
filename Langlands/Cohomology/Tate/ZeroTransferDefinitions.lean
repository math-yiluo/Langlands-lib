import Langlands.Cohomology.Tate.ZeroDefinitions
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index

noncomputable section

universe u

open CategoryTheory

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G]
variable (H : Subgroup G) (A : Rep R G)

/-- Restrict the actual coefficient pairing to a subgroup. -/
def Pairing.restrict {A B C : Rep R G} (φ : Pairing A B C) :
    Pairing (Rep.res H.subtype A) (Rep.res H.subtype B) (Rep.res H.subtype C) where
  bilinear := φ.bilinear
  equivariant h a b := φ.equivariant h a b

/-- The value of an invariant vector acted on by a left coset. -/
def cosetAction (a : (Rep.res H.subtype A).ρ.invariants) : G ⧸ H → A :=
  Quotient.lift (fun g => A.ρ g a) (by
    intro g k h
    have hm : g⁻¹ * k ∈ H := QuotientGroup.leftRel_apply.mp h
    have ha := a.property (⟨g⁻¹ * k, hm⟩ : H)
    change A.ρ (g⁻¹ * k) a = a at ha
    calc
      A.ρ g a = A.ρ g (A.ρ (g⁻¹ * k) a) := by rw [ha]
      _ = A.ρ k a := by simp [← Module.End.mul_apply, ← map_mul])

lemma cosetAction_mk (a : (Rep.res H.subtype A).ρ.invariants) (g : G) :
    cosetAction H A a (QuotientGroup.mk g) = A.ρ g a := rfl

lemma cosetAction_smul (a : (Rep.res H.subtype A).ρ.invariants) (g : G) (q : G ⧸ H) :
    cosetAction H A a (g • q) = A.ρ g (cosetAction H A a q) := by
  induction q using QuotientGroup.induction_on with
  | H k => simp [cosetAction_mk, ← Module.End.mul_apply, ← map_mul]

lemma cosetAction_out (a : (Rep.res H.subtype A).ρ.invariants) (q : G ⧸ H) :
    cosetAction H A a q = A.ρ q.out a := by
  exact congrArg (cosetAction H A a) (Quotient.out_eq' q).symm

variable [Fintype G] [Fintype H] [Fintype (G ⧸ H)]

/-- Sum over left cosets, independent of any representatives. -/
def cosetNorm : (Rep.res H.subtype A).ρ.invariants →ₗ[R] A.ρ.invariants where
  toFun a := ⟨∑ q : G ⧸ H, cosetAction H A a q, fun g => by
    simp only [map_sum, ← cosetAction_smul]
    exact Equiv.sum_comp (MulAction.toPerm g) (cosetAction H A a)⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Submodule.coe_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    induction q using QuotientGroup.induction_on with
    | H k => exact map_add (A.ρ k) (a : A) (b : A)
  map_smul' r a := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro q _
    induction q using QuotientGroup.induction_on with
    | H k => exact map_smul (A.ρ k) r (a : A)

omit [Fintype G] [Fintype H] [Fintype (G ⧸ H)] in
/-- The proved decomposition into a left-coset representative and a subgroup element. -/
def cosetDecomposition : (G ⧸ H) × H ≃ G :=
  Equiv.ofBijective (fun x => x.1.out * x.2) (by
    constructor
    · rintro ⟨q, h⟩ ⟨q', h'⟩ heq
      have hq : q = q' := by
        have := congrArg (QuotientGroup.mk (s := H)) heq
        simpa only [QuotientGroup.mk_mul_of_mem _ h.property,
          QuotientGroup.mk_mul_of_mem _ h'.property, Quotient.out_eq'] using this
      subst q'
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel heq))
    · intro g
      let q : G ⧸ H := QuotientGroup.mk g
      have hg : q.out⁻¹ * g ∈ H :=
        QuotientGroup.eq.mp (show (QuotientGroup.mk q.out : G ⧸ H) =
          QuotientGroup.mk g from Quotient.out_eq' q)
      exact ⟨(q, ⟨q.out⁻¹ * g, hg⟩), by simp⟩)

/-- Partition a finite group sum by left cosets. -/
lemma sum_left_cosets {M : Type*} [AddCommMonoid M] (f : G → M) :
    (∑ g : G, f g) = ∑ q : G ⧸ H, ∑ h : H, f (q.out * h) := by
  calc
    _ = ∑ x : (G ⧸ H) × H, f (x.1.out * x.2) :=
      (Equiv.sum_comp (cosetDecomposition H) f).symm
    _ = _ := Fintype.sum_prod_type _

/-- Partition a finite group sum by inverse left-coset representatives. -/
lemma sum_right_cosets {M : Type*} [AddCommMonoid M] (f : G → M) :
    (∑ g : G, f g) = ∑ q : G ⧸ H, ∑ h : H, f (h * q.out⁻¹) := by
  calc
    (∑ g : G, f g) = ∑ g : G, f g⁻¹ := Equiv.sum_comp (Equiv.inv G) f |>.symm
    _ = ∑ q : G ⧸ H, ∑ h : H, f (q.out * h)⁻¹ := sum_left_cosets H _
    _ = ∑ q : G ⧸ H, ∑ h : H, f (h * q.out⁻¹) := by
      apply Finset.sum_congr rfl
      intro q _
      simpa using Equiv.sum_comp (Equiv.inv H) (fun h : H => f (h * q.out⁻¹))

/-- The inclusion of group invariants into subgroup invariants. -/
def invariantRestriction : A.ρ.invariants →ₗ[R] (Rep.res H.subtype A).ρ.invariants :=
  { toFun a := ⟨a, fun h => a.property h⟩
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

/-- The full norm factors through the subgroup norm followed by the coset norm. -/
lemma cosetNorm_normToInvariants (a : A) :
    cosetNorm H A (normToInvariants (Rep.res H.subtype A) a) = normToInvariants A a := by
  apply Subtype.ext
  change (∑ q : G ⧸ H, cosetAction H A
    (normToInvariants (Rep.res H.subtype A) a) q) = A.ρ.norm a
  simp only [cosetAction_out, normToInvariants, LinearMap.codRestrict_apply,
    Representation.norm, LinearMap.sum_apply, map_sum]
  change (∑ q : G ⧸ H, ∑ h : H, A.ρ q.out (A.ρ h a)) = ∑ g : G, A.ρ g a
  simp only [← Module.End.mul_apply, ← map_mul]
  exact (sum_left_cosets H (fun g : G => A.ρ g a)).symm

/-- The inverse-coset sum is an explicit preimage under the subgroup norm. -/
lemma invariantRestriction_normToInvariants (a : A) :
    invariantRestriction H A (normToInvariants A a) =
      normToInvariants (Rep.res H.subtype A)
        (∑ q : G ⧸ H, A.ρ q.out⁻¹ a) := by
  apply Subtype.ext
  change A.ρ.norm a =
    (Rep.res H.subtype A).ρ.norm (∑ q : G ⧸ H, A.ρ q.out⁻¹ a)
  simp only [Representation.norm, LinearMap.sum_apply, map_sum]
  change (∑ g : G, A.ρ g a) =
    ∑ q : G ⧸ H, ∑ h : H, A.ρ h (A.ρ q.out⁻¹ a)
  simp only [← Module.End.mul_apply, ← map_mul]
  exact sum_right_cosets H (fun g : G => A.ρ g a)

/-- Invariant restriction preserves the actual norm images. -/
lemma invariantRestriction_normImage :
    normImage A ≤ (normImage (Rep.res H.subtype A)).comap (invariantRestriction H A) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨∑ q : G ⧸ H, A.ρ q.out⁻¹ a, (invariantRestriction_normToInvariants H A a).symm⟩

/-- Coset corestriction preserves the actual norm images. -/
lemma cosetNorm_normImage :
    normImage (Rep.res H.subtype A) ≤ (normImage A).comap (cosetNorm H A) := by
  rintro _ ⟨a, rfl⟩
  exact ⟨a, (cosetNorm_normToInvariants H A a).symm⟩

/-- Restriction on invariants modulo the actual norm image. -/
def quotientRestriction : InvariantsModNorm A →ₗ[R] InvariantsModNorm (Rep.res H.subtype A) :=
  (normImage A).mapQ (normImage (Rep.res H.subtype A))
    (invariantRestriction H A) (invariantRestriction_normImage H A)

/-- Corestriction on invariants modulo the actual norm image. -/
def quotientCorestriction : InvariantsModNorm (Rep.res H.subtype A) →ₗ[R] InvariantsModNorm A :=
  (normImage (Rep.res H.subtype A)).mapQ (normImage A)
    (cosetNorm H A) (cosetNorm_normImage H A)

/-- Degree-zero restriction on Mathlib's Tate cohomology, with its proved norm descent. -/
def restrictionZero : tateCohomology A 0 →ₗ[R] tateCohomology (Rep.res H.subtype A) 0 :=
  (zeroEquiv (Rep.res H.subtype A)).inv.hom.comp
    ((quotientRestriction H A).comp (zeroEquiv A).hom.hom)

/-- Degree-zero corestriction on Mathlib's Tate cohomology, with its proved norm descent. -/
def corestrictionZero : tateCohomology (Rep.res H.subtype A) 0 →ₗ[R] tateCohomology A 0 :=
  (zeroEquiv A).inv.hom.comp
    ((quotientCorestriction H A).comp (zeroEquiv (Rep.res H.subtype A)).hom.hom)

end Langlands.Tate
