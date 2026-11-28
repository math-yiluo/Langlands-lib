import Langlands.Algebra.ReducedNormRegular
import Langlands.Global.AdelicGroupLocalPoints
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Norm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtinBaseEquiv

/-! # Prescribed local tensor norm classes from the Artin norm–restriction square -/

noncomputable section

open NumberField IsDedekindDomain Filter
open scoped NumberField TensorProduct

namespace Langlands.ClassFieldTheory.Global

open GlobalClassFieldTheory.Reciprocity

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section RelativeCoordinates

variable {F K : Type u} [Field F] [NumberField F] [Field K] [Algebra F K]
  [FiniteDimensional F K]

private def localTensorUnits (v : Langlands.Global.Place F) :
    RelativeIdeleGroup F K →* (Langlands.Global.placeCompletion F v ⊗[F] K)ˣ :=
  Units.map (Algebra.TensorProduct.map (Langlands.Global.adeleProjection F v)
    (AlgHom.id F K)).toMonoidHom

private theorem exists_relativeIdele_of_eventually_one
    (a : ∀ v : Langlands.Global.Place F, (Langlands.Global.placeCompletion F v ⊗[F] K)ˣ)
    (ha : ∀ᶠ w : Langlands.Global.FinitePlace F in cofinite, a (.inr w) = 1) :
    ∃ x : RelativeIdeleGroup F K, ∀ v, localTensorUnits v x = a v := by
  let d₁ := relativeIdeleToLocalData (1 : RelativeIdeleGroup F K)
  let d : RelativeLocalIdeleData (K := F) (L := K) :=
    { infinite := fun w => a (.inl w)
      finite := fun w => a (.inr w)
      eventually_integral := fun i => by
        filter_upwards [ha, d₁.eventually_integral i] with w hw hi
        change a (.inr w) = (1 : (w.adicCompletion F ⊗[F] K)ˣ) at hw
        simpa only [hw, d₁, relativeIdeleToLocalData_finite, map_one] using hi
      eventually_inverse_integral := fun i => by
        filter_upwards [ha, d₁.eventually_inverse_integral i] with w hw hi
        change a (.inr w) = (1 : (w.adicCompletion F ⊗[F] K)ˣ) at hw
        simpa only [hw, d₁, relativeIdeleToLocalData_finite, map_one] using hi }
  refine ⟨relativeIdeleOfLocalData d, ?_⟩
  rintro (w | w)
  · change RelativeIdeleGroup.infiniteComponent (K := F) (L := K) w _ = _
    exact relativeIdeleOfLocalData_infiniteComponent d w
  · change RelativeIdeleGroup.finiteComponent (K := F) (L := K) w _ = _
    exact relativeIdeleOfLocalData_finiteComponent d w

variable {P : Type u} [Field P] [Algebra K P] [FiniteDimensional K P]

private def relativeCoefficient (v : Langlands.Global.Place F) :
    RelativeAdeleRing F K →ₐ[K] K ⊗[F] Langlands.Global.placeCompletion F v where
  __ := (Algebra.TensorProduct.comm F (Langlands.Global.placeCompletion F v) K).toAlgHom.comp
    (Algebra.TensorProduct.map (Langlands.Global.adeleProjection F v) (AlgHom.id F K))
  commutes' k := by
    change k ⊗ₜ[F] Langlands.Global.adeleProjection F v (1 : NumberField.AdeleRing (𝓞 F) F) =
      k ⊗ₜ[F] (1 : Langlands.Global.placeCompletion F v)
    rw [map_one]

omit [FiniteDimensional F K] in
private theorem localTensorUnits_towerNorm (v : Langlands.Global.Place F)
    (z : TowerRelativeIdeleGroup F K P) :
    ∃ w : ((K ⊗[F] Langlands.Global.placeCompletion F v) ⊗[K] P)ˣ,
      Algebra.TensorProduct.comm F (Langlands.Global.placeCompletion F v) K
        (localTensorUnits v (TowerRelativeIdeleGroup.norm F K P z)) =
      Algebra.norm (K ⊗[F] Langlands.Global.placeCompletion F v)
        (w : (K ⊗[F] Langlands.Global.placeCompletion F v) ⊗[K] P) := by
  let j := relativeCoefficient (K := K) v
  refine ⟨Units.map (Algebra.TensorProduct.map j (AlgHom.id K P)).toMonoidHom z, ?_⟩
  exact (Langlands.CentralSimple.norm_baseChange_naturality (Module.finBasis K P) j _).symm

end RelativeCoordinates

/-- With injective Galois restriction in an abelian field diamond, a finitely supported
family of local units of the intermediate field with the prescribed scalar norm
condition comes from a single global element modulo the local norms of the top field. -/
def PrescribedTensorNormClassesStatement : Prop :=
  ∀ (F E K P : Type u) [Field F] [NumberField F] [Field E] [NumberField E]
    [Field K] [NumberField K] [Field P] [NumberField P]
    [Algebra F E] [Algebra F K] [Algebra E P] [Algebra K P] [Algebra F P]
    [IsScalarTower F E P] [IsScalarTower F K P]
    [FiniteDimensional F E] [FiniteDimensional F K] [FiniteDimensional K P]
    [IsAbelianGalois F E] [IsAbelianGalois K P],
    Function.Injective ((AlgEquiv.restrictNormalHom E).comp
      (AlgEquiv.restrictScalarsHom F : (P ≃ₐ[K] P) →* (P ≃ₐ[F] P))) →
    ∀ (d : Fˣ)
      (a : ∀ v : Langlands.Global.Place F, (Langlands.Global.placeCompletion F v ⊗[F] K)ˣ),
    (∀ᶠ w : Langlands.Global.FinitePlace F in cofinite, a (.inr w) = 1) →
    (∀ v : Langlands.Global.Place F,
      ∃ b : (Langlands.Global.placeCompletion F v ⊗[F] E)ˣ,
        Algebra.norm (Langlands.Global.placeCompletion F v)
          (b : Langlands.Global.placeCompletion F v ⊗[F] E) =
          algebraMap F (Langlands.Global.placeCompletion F v) (d : F) *
            Algebra.norm (Langlands.Global.placeCompletion F v)
              (a v : Langlands.Global.placeCompletion F v ⊗[F] K)) →
    ∃ x : Kˣ, ∀ v : Langlands.Global.Place F,
      ∃ z : ((K ⊗[F] Langlands.Global.placeCompletion F v) ⊗[K] P)ˣ,
        (x : K) ⊗ₜ[F] (1 : Langlands.Global.placeCompletion F v) =
          Algebra.TensorProduct.comm F (Langlands.Global.placeCompletion F v) K (a v) *
            Algebra.norm (K ⊗[F] Langlands.Global.placeCompletion F v)
              (z : (K ⊗[F] Langlands.Global.placeCompletion F v) ⊗[K] P)

/-- Apply the Artin norm–restriction square to the idèle given by the local family. -/
theorem prescribedTensorNormClasses : PrescribedTensorNormClassesStatement.{u} := by
  intro F E K P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinj d a ha hn
  obtain ⟨x, hx⟩ := exists_relativeIdele_of_eventually_one a ha
  let eK := relativeIdeleBaseChangeMulEquiv (K := F) (L := K)
  let eE := relativeIdeleBaseChangeMulEquiv (K := F) (L := E)
  let x₀ := eK x
  let y := IdeleGroup.principalIdele F d * IdeleGroup.norm F K x₀
  have hy : y ∈ (RelativeIdeleGroup.norm F E).range := by
    rw [mem_relativeIdeleNorm_range_iff_localTensorNorms]
    constructor
    · intro w
      obtain ⟨b, hb⟩ := hn (.inl w)
      refine ⟨b, ?_⟩
      apply Units.ext
      have h := hx (.inl w)
      change RelativeIdeleGroup.infiniteComponent (K := F) (L := K) w x = _ at h
      rw [map_mul, IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
        RelativeIdeleGroup.infiniteComponent_norm, h, Units.val_mul]
      rw [IdeleGroup.infiniteComponent_principalIdele]
      exact hb
    · intro w
      obtain ⟨b, hb⟩ := hn (.inr w)
      refine ⟨b, ?_⟩
      apply Units.ext
      have h := hx (.inr w)
      change RelativeIdeleGroup.finiteComponent (K := F) (L := K) w x = _ at h
      rw [map_mul, IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv,
        RelativeIdeleGroup.finiteComponent_norm, h, Units.val_mul]
      rw [IdeleGroup.finiteComponent_principalIdele]
      exact hb
  let cls (M : Type u) [Field M] [NumberField M] := QuotientGroup.mk' (IdeleGroup.principalSubgroup M)
  obtain ⟨b, hb⟩ := hy
  have hb' : _root_.ideleClassNorm F E (cls E (eE b)) = _root_.ideleClassNorm F K (cls K x₀) := by
    rw [ideleClassNorm_mk, ideleClassNorm_mk, IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv, hb]
    change cls F (IdeleGroup.principalIdele F d * IdeleGroup.norm F K x₀) = _
    have hd : cls F (IdeleGroup.principalIdele F d) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (show IdeleGroup.principalIdele F d ∈ IdeleGroup.principalSubgroup F from ⟨d, rfl⟩)
    rw [map_mul, hd]
    exact one_mul (cls F (IdeleGroup.norm F K x₀))
  have hl := (globalIdeleClassArtinMonoidHom_eq_one_iff (K := F) (L := E) _).mpr ⟨_, hb'⟩
  have hu : globalIdeleClassArtinMonoidHom (K := K) (L := P) (cls K x₀) = 1 := by
    apply hinj
    have hs := DFunLike.congr_fun
      (globalIdeleClassArtinMonoidHom_norm_restriction
        (K := F) (L := E) (M := K) (N := P)) (cls K x₀)
    rw [map_one]
    exact hs.trans hl
  obtain ⟨c, hc⟩ := (globalIdeleClassArtinMonoidHom_eq_one_iff (K := K) (L := P) _).mp hu
  obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup P) c
  have ht : cls K (IdeleGroup.norm K P t) = cls K x₀ := by
    rw [← ideleClassNorm_mk]
    exact hc
  have ht' : x₀ / IdeleGroup.norm K P t ∈ IdeleGroup.principalSubgroup K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change cls K (x₀ / IdeleGroup.norm K P t) = 1
    rw [map_div, ht, div_self']
  obtain ⟨k, hk⟩ := ht'
  let eP := relativeIdeleBaseChangeMulEquiv (K := K) (L := P)
  let eT := towerRelativeIdeleBaseChangeMulEquiv F K P
  let z := eT.symm (eP.symm t)
  have hz : eK (TowerRelativeIdeleGroup.norm F K P z) = IdeleGroup.norm K P t := by
    rw [towerRelativeIdeleBaseChangeMulEquiv_norm, ← IdeleGroup.norm_relativeIdeleBaseChangeMulEquiv]
    change IdeleGroup.norm K P (eP (eT z)) = _
    rw [show eT z = eP.symm t from eT.apply_symm_apply _, eP.apply_symm_apply]
  have hk' : RelativeIdeleGroup.principalIdele F K k =
      x * TowerRelativeIdeleGroup.norm F K P z⁻¹ := by
    apply eK.injective
    calc
      eK (RelativeIdeleGroup.principalIdele F K k) = IdeleGroup.principalIdele K k :=
        relativeIdeleBaseChangeMulEquiv_principalIdele k
      _ = x₀ / eK (TowerRelativeIdeleGroup.norm F K P z) := by rw [hz, hk]
      _ = eK (x * TowerRelativeIdeleGroup.norm F K P z⁻¹) := by
        rw [map_mul, map_inv (TowerRelativeIdeleGroup.norm F K P), map_inv eK, div_eq_mul_inv]
  refine ⟨k, fun v => ?_⟩
  obtain ⟨w, hw⟩ := localTensorUnits_towerNorm v z⁻¹
  refine ⟨w, ?_⟩
  let e := Algebra.TensorProduct.comm F (Langlands.Global.placeCompletion F v) K
  have hh := congrArg (fun u : RelativeIdeleGroup F K =>
    e (localTensorUnits v u)) hk'
  change e (localTensorUnits v (RelativeIdeleGroup.principalIdele F K k)) =
    e (localTensorUnits v (x * TowerRelativeIdeleGroup.norm F K P z⁻¹)) at hh
  rw [map_mul, Units.val_mul, map_mul e, hx, hw] at hh
  change (k : K) ⊗ₜ[F] Langlands.Global.adeleProjection F v 1 = _ at hh
  rwa [map_one] at hh

end Langlands.ClassFieldTheory.Global
