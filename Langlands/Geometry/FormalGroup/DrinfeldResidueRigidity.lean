import Langlands.Geometry.FormalGroup.NilpotentReduction
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Etale.Field

/-! # Nilpotent rigidity of the actual Drinfeld residue coordinate -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.Nilp

open CategoryTheory

variable {O : Type u} [CommRing O] {π : O}
variable {A B : CommAlgCat.{v} O}

/-- An induced map on actual reductions is surjective if the coefficient map is. -/
theorem reductionMap_surjective (g : A →ₐ[O] B) (hg : Function.Surjective g) :
    Function.Surjective (reductionMap (π := π) g) := by
  intro x
  obtain ⟨b, rfl⟩ := reductionQuotient_surjective π B x
  obtain ⟨a, rfl⟩ := hg b
  exact ⟨reductionQuotient π A a, reductionMap_quotient g a⟩

private theorem ker_reductionMap_of_surjective (g : A →ₐ[O] B) (hg : Function.Surjective g) :
    RingHom.ker (reductionMap (π := π) g).toRingHom =
      (RingHom.ker g.toRingHom).map (reductionQuotient π A).toRingHom := by
  let q := (reductionQuotient π A).toRingHom
  let r := (reductionMap (π := π) g).toRingHom
  have hq : Function.Surjective q := reductionQuotient_surjective π A
  have hI : (reductionIdeal π A).map g.toRingHom = reductionIdeal π B := by
    simp only [reductionIdeal, Ideal.map_span, Set.image_singleton]
    change Ideal.span {g (algebraMap O A π)} = Ideal.span {algebraMap O B π}
    rw [g.commutes]
  have hcomap : (RingHom.ker r).comap q = (reductionIdeal π B).comap g.toRingHom := by
    ext a
    change reductionMap (π := π) g (reductionQuotient π A a) = 0 ↔
      g a ∈ reductionIdeal π B
    rw [reductionMap_quotient]
    exact Ideal.Quotient.eq_zero_iff_mem
  apply Ideal.comap_injective_of_surjective q hq
  change (RingHom.ker r).comap q = ((RingHom.ker g.toRingHom).map q).comap q
  rw [hcomap, ← hI, Ideal.comap_map_of_surjective g.toRingHom (show Function.Surjective g.toRingHom from hg),
    Ideal.comap_map_of_surjective q hq,
    ← RingHom.ker_eq_comap_bot, ← RingHom.ker_eq_comap_bot]
  have he : RingHom.ker q = reductionIdeal π A := Ideal.mk_ker
  rw [he, sup_comm]

/-- A nilpotent coefficient kernel stays nilpotent after actual reduction modulo pi. -/
theorem reductionMap_ker_isNilpotent (g : A →ₐ[O] B) (hg : Function.Surjective g)
    (hI : IsNilpotent (RingHom.ker g.toRingHom)) :
    IsNilpotent (RingHom.ker (reductionMap (π := π) g).toRingHom) := by
  rw [ker_reductionMap_of_surjective g hg]
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  change _ = ⊥
  rw [← Ideal.map_pow, show RingHom.ker g.toRingHom ^ n = ⊥ from hn, Ideal.map_bot]

section ResidueField

variable [IsDomain O] [IsDiscreteValuationRing O]

local notation "k" => IsLocalRing.ResidueField O

/-- The residue field acts on the actual quotient through the uniformizer ideal. -/
@[instance_reducible]
def reductionResidueFieldAlgebra (hπ : Irreducible π) (A : CommAlgCat.{v} O) :
    Algebra k (Reduction π A) :=
  ((algebraMap (ResidueRing O π) (Reduction π A)).comp
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toRingHom).toAlgebra

private theorem reductionResidueFieldTower (hπ : Irreducible π) (A : CommAlgCat.{v} O) :
    let _ := reductionResidueFieldAlgebra hπ A
    IsScalarTower O k (Reduction π A) := by
  let _ := reductionResidueFieldAlgebra hπ A
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change algebraMap O (Reduction π A) a =
    algebraMap (ResidueRing O π) (Reduction π A)
      (Ideal.quotEquivOfEq hπ.maximalIdeal_eq (IsLocalRing.residue O a))
  rw [IsLocalRing.residue_def, Ideal.quotEquivOfEq_mk]
  rfl

private def extendResidueField {P : Type v} {Q : Type w} [CommRing P] [CommRing Q]
    [Algebra O P] [Algebra O Q] [Algebra k P] [Algebra k Q]
    [IsScalarTower O k P] [IsScalarTower O k Q] (f : P →ₐ[O] Q) : P →ₐ[k] Q where
  toRingHom := f.toRingHom
  commutes' r := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := O) r
    change f (algebraMap k P (algebraMap O k a)) = algebraMap k Q (algebraMap O k a)
    rw [← IsScalarTower.algebraMap_apply O k P, ← IsScalarTower.algebraMap_apply O k Q, f.commutes]

variable {κ : Type w} [Field κ] [Algebra O κ] [Algebra (IsLocalRing.ResidueField O) κ]
  [IsScalarTower O (IsLocalRing.ResidueField O) κ] [Algebra.IsSeparable (IsLocalRing.ResidueField O) κ]

set_option backward.isDefEq.respectTransparency false in
/-- Postcomposition by the actual reduction map is bijective on residue coordinates. -/
theorem residueCoordinate_reductionMap_bijective (hπ : Irreducible π)
    (g : A →ₐ[O] B) (hg : Function.Surjective g) (hI : IsNilpotent (RingHom.ker g.toRingHom)) :
    Function.Bijective (fun ψ : κ →ₐ[O] Reduction π A => (reductionMap g).comp ψ) := by
  let _ := reductionResidueFieldAlgebra hπ A
  let _ := reductionResidueFieldAlgebra hπ B
  let _ := reductionResidueFieldTower hπ A
  let _ := reductionResidueFieldTower hπ B
  let _ := Algebra.FormallyEtale.of_isSeparable k κ
  let f : Reduction π A →ₐ[k] Reduction π B := extendResidueField (reductionMap g)
  have hf : Function.Surjective f := reductionMap_surjective g hg
  have hk : IsNilpotent (RingHom.ker f.toRingHom) := reductionMap_ker_isNilpotent g hg hI
  constructor
  · intro ψ ψ' he
    have he' : f.comp (extendResidueField ψ) = f.comp (extendResidueField ψ') := by
      ext x
      change reductionMap g (ψ x) = reductionMap g (ψ' x)
      exact AlgHom.congr_fun he x
    have h := Algebra.FormallyUnramified.lift_unique' f hk _ _ he'
    ext x
    change extendResidueField ψ x = extendResidueField ψ' x
    exact AlgHom.congr_fun h x
  · intro ψ
    let lift := Algebra.FormallySmooth.liftOfSurjective (extendResidueField ψ) f hf hk
    exact ⟨lift.restrictScalars O, AlgHom.ext (Algebra.FormallySmooth.liftOfSurjective_apply
      (extendResidueField ψ) f hf hk)⟩

/-- The residue coordinate equivalence uses the same quotient and postcomposition as the two functors. -/
def residueCoordinateReductionEquiv (hπ : Irreducible π)
    (g : A →ₐ[O] B) (hg : Function.Surjective g) (hI : IsNilpotent (RingHom.ker g.toRingHom)) :
    (κ →ₐ[O] Reduction π A) ≃ (κ →ₐ[O] Reduction π B) :=
  Equiv.ofBijective (fun ψ => (reductionMap g).comp ψ)
    (residueCoordinate_reductionMap_bijective hπ g hg hI)

@[simp]
theorem residueCoordinateReductionEquiv_apply (hπ : Irreducible π)
    (g : A →ₐ[O] B) (hg : Function.Surjective g) (hI : IsNilpotent (RingHom.ker g.toRingHom))
    (ψ : κ →ₐ[O] Reduction π A) :
    residueCoordinateReductionEquiv hπ g hg hI ψ = (reductionMap g).comp ψ := rfl

end ResidueField

end Langlands.FormalGroup.Nilp
