import Langlands.GroupScheme.GeometricComponentCanonicalBaseChange
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Fixed geometric components under purely inseparable extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.IdentityComponent

open GaloisPointComparison

private theorem galoisRestriction_surjective_of_purelyInseparable
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsPurelyInseparable k K]
    [Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
    [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)] :
    Function.Surjective (Field.absoluteGaloisGroup.mapOfAlgebra k K) := by
  let : Algebra.IsAlgebraic k K := IsPurelyInseparable.isAlgebraic k K
  let : Algebra.IsAlgebraic k (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans k K (AlgebraicClosure K)
  let : IsAlgClosure k (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  intro σ
  let τ : AlgebraicClosure K ≃ₐ[k] AlgebraicClosure K :=
    σ.liftNormal (AlgebraicClosure K)
  have hcomm (x : K) :
      τ (algebraMap K (AlgebraicClosure K) x) =
        algebraMap K (AlgebraicClosure K) x := by
    exact congrArg (fun f : K →ₐ[k] AlgebraicClosure K => f x)
      (Subsingleton.elim
        (τ.toAlgHom.comp (IsScalarTower.toAlgHom k K (AlgebraicClosure K)))
        (IsScalarTower.toAlgHom k K (AlgebraicClosure K)))
  let τ' : Field.absoluteGaloisGroup K :=
    { τ.toRingEquiv with commutes' := hcomm }
  refine ⟨τ', ?_⟩
  change (τ'.restrictScalars k).restrictNormal (AlgebraicClosure k) = σ
  have hs : τ'.restrictScalars k = τ := by
    ext x
    rfl
  rw [hs]
  exact σ.restrict_liftNormal (AlgebraicClosure K)

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [IsPurelyInseparable k K]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [Smooth H.X.hom] [IsAffineHom H.X.hom]

section SpecifiedEmbedding

variable [Algebra (AlgebraicClosure k) (AlgebraicClosure K)]
  [IsScalarTower k (AlgebraicClosure k) (AlgebraicClosure K)]

/-- Purely inseparable extension both preserves and reflects fixedness of an
actual geometric component. -/
theorem geometricComponentBaseChangeEquiv_purelyInseparable_mem_fixed_iff
    (c : GeometricComponents k H) :
    geometricComponentBaseChangeEquiv k K H c ∈
        geometricComponentFixedSubgroup K (baseChanged k K H) ↔
      c ∈ geometricComponentFixedSubgroup k H := by
  change (∀ τ : Field.absoluteGaloisGroup K,
      τ • geometricComponentBaseChangeEquiv k K H c =
        geometricComponentBaseChangeEquiv k K H c) ↔
    ∀ σ : Field.absoluteGaloisGroup k, σ • c = c
  constructor
  · intro hc σ
    obtain ⟨τ, hτ⟩ :=
      galoisRestriction_surjective_of_purelyInseparable k K σ
    apply (geometricComponentBaseChangeEquiv k K H).injective
    rw [← hτ, geometricComponentBaseChangeEquiv_restrict_smul]
    exact hc τ
  · intro hc
    exact (geometricComponentFixedBaseChange k K H ⟨c, hc⟩).property

end SpecifiedEmbedding

/-- Canonical purely inseparable extension reaches every Galois-fixed
geometric component of the actual base-changed group scheme. -/
theorem geometricComponentCanonicalBaseChange_purelyInseparable_surjective :
    Function.Surjective (geometricComponentCanonicalBaseChange k K H) := by
  let i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K := IsAlgClosed.lift
  let := i.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom i
  rw [geometricComponentCanonicalBaseChange_eq]
  intro d
  let e := geometricComponentBaseChangeEquiv k K H
  let c := e.symm d.val
  have hc : c ∈ geometricComponentFixedSubgroup k H :=
    (geometricComponentBaseChangeEquiv_purelyInseparable_mem_fixed_iff
      k K H c).mp (by
        change e (e.symm d.val) ∈ _
        rw [e.apply_symm_apply]
        exact d.property)
  refine ⟨⟨c, hc⟩, ?_⟩
  apply Subtype.ext
  exact e.apply_symm_apply d.val

/-- The actual canonical map is an equivalence on full fixed geometric
component groups for every purely inseparable field extension. -/
def geometricComponentFixedPurelyInseparableEquiv :
    geometricComponentFixedSubgroup k H ≃*
      geometricComponentFixedSubgroup K (baseChanged k K H) :=
  MulEquiv.ofBijective (geometricComponentCanonicalBaseChange k K H)
    ⟨geometricComponentCanonicalBaseChange_injective k K H,
      geometricComponentCanonicalBaseChange_purelyInseparable_surjective k K H⟩

@[simp]
theorem geometricComponentFixedPurelyInseparableEquiv_apply
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentFixedPurelyInseparableEquiv k K H c =
      geometricComponentCanonicalBaseChange k K H c := rfl

@[simp]
theorem geometricComponentFixedPurelyInseparableEquiv_toMonoidHom :
    (geometricComponentFixedPurelyInseparableEquiv k K H).toMonoidHom =
      geometricComponentCanonicalBaseChange k K H := rfl

/-- Any compatible closure embedding computes the underlying component of
the inverse equivalence. -/
theorem geometricComponentFixedPurelyInseparableEquiv_symm_val
    (i : AlgebraicClosure k →ₐ[k] AlgebraicClosure K)
    (d : geometricComponentFixedSubgroup K (baseChanged k K H)) :
    ((geometricComponentFixedPurelyInseparableEquiv k K H).symm d).val =
      (geometricComponentBaseChangeEquivOfEmbedding k K H i).symm d.val := by
  apply (geometricComponentBaseChangeEquivOfEmbedding k K H i).injective
  rw [MulEquiv.apply_symm_apply,
    ← geometricComponentCanonicalBaseChange_val k K H i]
  exact congrArg Subtype.val
    ((geometricComponentFixedPurelyInseparableEquiv k K H).apply_symm_apply d)

variable {H} {H' : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth H'.X.hom] [IsAffineHom H'.X.hom]

/-- The purely inseparable fixed-component equivalence is natural in actual
group-scheme homomorphisms. -/
theorem geometricComponentFixedPurelyInseparableEquiv_naturality (f : H ⟶ H')
    (c : geometricComponentFixedSubgroup k H) :
    geometricComponentFixedPurelyInseparableEquiv k K H'
        (geometricComponentFixedMap k f c) =
      geometricComponentFixedMap K ((GroupScheme.baseChange (baseMap k K)).map f)
        (geometricComponentFixedPurelyInseparableEquiv k K H c) :=
  geometricComponentCanonicalBaseChange_naturality k K f c

end Langlands.GroupScheme.IdentityComponent
