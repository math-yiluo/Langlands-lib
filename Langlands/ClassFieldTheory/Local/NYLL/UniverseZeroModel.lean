import Langlands.ClassFieldTheory.Local.FiniteArtinTransport
import Langlands.ClassFieldTheory.Local.FiniteArtinSystemUniquenessProof
import Langlands.LocalField.CanonicalTransport
import Mathlib.Algebra.Algebra.Shrink
import Mathlib.Algebra.Field.Shrink
import Mathlib.RingTheory.Finiteness.Small

/-! # Universe-zero models of p-adic fields and their transport maps

Every `F : PadicField.{u} p` has an explicit model in `Type 0`, namely
`Shrink.{0} F.Carrier` with the transported field and `Padic p`-algebra
structures, together with the actual algebra equivalence back to `F.Carrier`.
A field map `F.Carrier → E.Carrier` is transported to the models by
conjugation, so every field map of a tower has a compatible model.

The module also constructs the transported norm quotients and Galois groups,
and compares the arithmetic data of arbitrary supplied topological data along
an actual algebra equivalence. No reciprocity map is constructed or assumed.
-/

noncomputable section

namespace Langlands.LocalClassField.NYLL

universe u v w u'

variable {p : ℕ} [Fact p.Prime]

section Model

/-- A finite extension of `Padic p` is small in universe zero, since it is a
finite module over the universe-zero ring `Padic p`. -/
theorem padicField_small (F : PadicField.{u} p) : Small.{0} F.Carrier :=
  Module.Finite.small.{0} (Padic p) F.Carrier

/-- The universe-zero model of a p-adic field: `Shrink.{0} F.Carrier` with the
field and `Padic p`-algebra structures transported along `equivShrink`. -/
def universeZeroModel (F : PadicField.{u} p) : PadicField.{0} p :=
  letI := padicField_small F
  { Carrier := Shrink.{0} F.Carrier
    finiteDimensional :=
      Module.Finite.equiv (Shrink.algEquiv (Padic p) F.Carrier).toLinearEquiv.symm }

/-- The actual `Padic p`-algebra equivalence from the model to the field. -/
def universeZeroEquiv (F : PadicField.{u} p) :
    (universeZeroModel F).Carrier ≃ₐ[Padic p] F.Carrier :=
  letI := padicField_small F
  Shrink.algEquiv (Padic p) F.Carrier

variable (F : PadicField.{u} p) (E : PadicField.{v} p) (L : PadicField.{w} p)

/-- The field map between models obtained by conjugating the supplied field map
`F.Carrier → E.Carrier` with the two model equivalences. -/
@[instance_reducible]
def universeZeroAlgebra [Algebra F.Carrier E.Carrier] :
    Algebra (universeZeroModel F).Carrier (universeZeroModel E).Carrier :=
  ((universeZeroEquiv E).symm.toRingEquiv.toRingHom.comp
    ((algebraMap F.Carrier E.Carrier).comp
      (universeZeroEquiv F).toRingEquiv.toRingHom)).toAlgebra

section Algebra

variable [Algebra F.Carrier E.Carrier]

/-- The model equivalences intertwine the transported and supplied field maps. -/
theorem universeZeroEquiv_algebraMap (a : (universeZeroModel F).Carrier) :
    letI := universeZeroAlgebra F E
    universeZeroEquiv E
        (algebraMap (universeZeroModel F).Carrier (universeZeroModel E).Carrier a) =
      algebraMap F.Carrier E.Carrier (universeZeroEquiv F a) := by
  let := universeZeroAlgebra F E
  exact (universeZeroEquiv E).apply_symm_apply _

/-- The inverse model equivalences intertwine the supplied and transported field
maps. -/
theorem universeZeroEquiv_symm_algebraMap (b : F.Carrier) :
    letI := universeZeroAlgebra F E
    (universeZeroEquiv E).symm (algebraMap F.Carrier E.Carrier b) =
      algebraMap (universeZeroModel F).Carrier (universeZeroModel E).Carrier
        ((universeZeroEquiv F).symm b) := by
  let := universeZeroAlgebra F E
  apply (universeZeroEquiv E).injective
  rw [universeZeroEquiv_algebraMap, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- The intertwining relation in the ring-homomorphism form used by Mathlib and
by `FiniteArtinTransport`. -/
theorem universeZeroAlgebra_compatible :
    letI := universeZeroAlgebra F E
    (algebraMap F.Carrier E.Carrier).comp (universeZeroEquiv F).toRingEquiv.toRingHom =
      (universeZeroEquiv E).toRingEquiv.toRingHom.comp
        (algebraMap (universeZeroModel F).Carrier (universeZeroModel E).Carrier) := by
  let := universeZeroAlgebra F E
  ext a
  exact (universeZeroEquiv_algebraMap F E a).symm

/-- The inverse intertwining relation. -/
theorem universeZeroAlgebra_symm_compatible :
    letI := universeZeroAlgebra F E
    (algebraMap (universeZeroModel F).Carrier (universeZeroModel E).Carrier).comp
        (universeZeroEquiv F).toRingEquiv.symm.toRingHom =
      (universeZeroEquiv E).toRingEquiv.symm.toRingHom.comp
        (algebraMap F.Carrier E.Carrier) := by
  let := universeZeroAlgebra F E
  ext a
  apply (universeZeroEquiv E).injective
  change universeZeroEquiv E (algebraMap _ _ ((universeZeroEquiv F).symm a)) =
    universeZeroEquiv E ((universeZeroEquiv E).symm (algebraMap F.Carrier E.Carrier a))
  rw [universeZeroEquiv_algebraMap, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

/-- The transported field map is compatible with the base `Padic p`. -/
theorem universeZeroAlgebra_isScalarTower [IsScalarTower (Padic p) F.Carrier E.Carrier] :
    letI := universeZeroAlgebra F E
    IsScalarTower (Padic p) (universeZeroModel F).Carrier (universeZeroModel E).Carrier := by
  let := universeZeroAlgebra F E
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  apply (universeZeroEquiv E).injective
  rw [universeZeroEquiv_algebraMap, AlgEquiv.commutes, AlgEquiv.commutes,
    IsScalarTower.algebraMap_apply (Padic p) F.Carrier E.Carrier]

/-- Finite dimensionality is transported to the models. -/
theorem universeZeroAlgebra_finiteDimensional [FiniteDimensional F.Carrier E.Carrier] :
    letI := universeZeroAlgebra F E
    FiniteDimensional (universeZeroModel F).Carrier (universeZeroModel E).Carrier := by
  let := universeZeroAlgebra F E
  exact Module.Finite.of_equiv_equiv (universeZeroEquiv F).toRingEquiv.symm
    (universeZeroEquiv E).toRingEquiv.symm (universeZeroAlgebra_symm_compatible F E)

/-- The model degree equals the supplied degree. -/
theorem universeZeroAlgebra_finrank :
    letI := universeZeroAlgebra F E
    Module.finrank (universeZeroModel F).Carrier (universeZeroModel E).Carrier =
      Module.finrank F.Carrier E.Carrier := by
  let := universeZeroAlgebra F E
  exact (Algebra.finrank_eq_of_equiv_equiv (universeZeroEquiv F).toRingEquiv.symm
    (universeZeroEquiv E).toRingEquiv.symm (universeZeroAlgebra_symm_compatible F E)).symm

/-- Abelian Galois extensions are transported to the models. -/
theorem universeZeroAlgebra_isAbelianGalois [IsAbelianGalois F.Carrier E.Carrier] :
    letI := universeZeroAlgebra F E
    IsAbelianGalois (universeZeroModel F).Carrier (universeZeroModel E).Carrier := by
  let := universeZeroAlgebra F E
  have : IsGalois (universeZeroModel F).Carrier (universeZeroModel E).Carrier :=
    IsGalois.of_equiv_equiv (f := (universeZeroEquiv F).toRingEquiv.symm)
      (g := (universeZeroEquiv E).toRingEquiv.symm) (universeZeroAlgebra_symm_compatible F E)
  let g := FiniteArtinTransport.galoisEquiv (universeZeroEquiv F).toRingEquiv
    (universeZeroEquiv E).toRingEquiv (universeZeroAlgebra_compatible F E)
  exact { is_comm.comm σ τ := g.injective (by rw [map_mul, map_mul, mul_comm']) }

end Algebra

/-- The transported field maps of a tower again form a scalar tower. -/
theorem universeZeroAlgebra_isScalarTower_tower
    [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier] [Algebra E.Carrier L.Carrier]
    [IsScalarTower F.Carrier E.Carrier L.Carrier] :
    letI := universeZeroAlgebra F E
    letI := universeZeroAlgebra F L
    letI := universeZeroAlgebra E L
    IsScalarTower (universeZeroModel F).Carrier (universeZeroModel E).Carrier
      (universeZeroModel L).Carrier := by
  let := universeZeroAlgebra F E
  let := universeZeroAlgebra F L
  let := universeZeroAlgebra E L
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  apply (universeZeroEquiv L).injective
  rw [universeZeroEquiv_algebraMap F L, universeZeroEquiv_algebraMap E L,
    universeZeroEquiv_algebraMap F E,
    IsScalarTower.algebraMap_apply F.Carrier E.Carrier L.Carrier]

end Model

section Galois

variable (F : PadicField.{u} p) (E : PadicField.{v} p) (L : PadicField.{w} p)

/-- The actual Galois groups of the model extension and of the supplied
extension, identified by conjugation with the model equivalence of `E`. Both
Krull topologies are discrete because both extensions are finite. -/
def universeZeroGaloisEquiv
    [Algebra F.Carrier E.Carrier] [FiniteDimensional F.Carrier E.Carrier] :
    letI := universeZeroAlgebra F E
    Gal((universeZeroModel E).Carrier/(universeZeroModel F).Carrier) ≃ₜ*
      Gal(E.Carrier/F.Carrier) :=
  letI := universeZeroAlgebra F E
  haveI := universeZeroAlgebra_finiteDimensional F E
  { FiniteArtinTransport.galoisEquiv (universeZeroEquiv F).toRingEquiv
      (universeZeroEquiv E).toRingEquiv (universeZeroAlgebra_compatible F E) with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

section Apply

variable [Algebra F.Carrier E.Carrier] [FiniteDimensional F.Carrier E.Carrier]

/-- The transported automorphism acts by conjugation with the model equivalence. -/
theorem universeZeroGaloisEquiv_apply :
    letI := universeZeroAlgebra F E
    ∀ (σ : Gal((universeZeroModel E).Carrier/(universeZeroModel F).Carrier)) (x : E.Carrier),
      universeZeroGaloisEquiv F E σ x = universeZeroEquiv E (σ ((universeZeroEquiv E).symm x)) :=
  fun _ _ => rfl

/-- The inverse of a transported automorphism is the transported inverse. -/
theorem universeZeroGaloisEquiv_apply_symm :
    letI := universeZeroAlgebra F E
    ∀ (σ : Gal((universeZeroModel E).Carrier/(universeZeroModel F).Carrier)) (x : E.Carrier),
      (universeZeroGaloisEquiv F E σ).symm x =
        universeZeroEquiv E (σ.symm ((universeZeroEquiv E).symm x)) :=
  fun _ _ => rfl

/-- The inverse identification acts by conjugation with the inverse model
equivalence. -/
theorem universeZeroGaloisEquiv_symm_apply :
    letI := universeZeroAlgebra F E
    ∀ (σ : Gal(E.Carrier/F.Carrier)) (x : (universeZeroModel E).Carrier),
      (universeZeroGaloisEquiv F E).symm σ x =
        (universeZeroEquiv E).symm (σ (universeZeroEquiv E x)) :=
  fun _ _ => rfl

end Apply

/-- Transported Galois groups commute with restriction of scalars from the
middle field of a tower to its base. -/
theorem universeZeroGaloisEquiv_restrictScalars
    [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier] [Algebra E.Carrier L.Carrier]
    [IsScalarTower F.Carrier E.Carrier L.Carrier]
    [FiniteDimensional F.Carrier L.Carrier] [FiniteDimensional E.Carrier L.Carrier] :
    letI := universeZeroAlgebra F E
    letI := universeZeroAlgebra F L
    letI := universeZeroAlgebra E L
    letI := universeZeroAlgebra_isScalarTower_tower F E L
    ∀ τ : Gal((universeZeroModel L).Carrier/(universeZeroModel E).Carrier),
      universeZeroGaloisEquiv F L (τ.restrictScalars (universeZeroModel F).Carrier) =
        (universeZeroGaloisEquiv E L τ).restrictScalars F.Carrier := by
  intro τ
  ext x
  rfl

/-- Transported Galois groups commute with restriction to a normal middle
field of a tower. -/
theorem universeZeroGaloisEquiv_restrictNormalHom
    [Algebra F.Carrier E.Carrier] [Algebra F.Carrier L.Carrier] [Algebra E.Carrier L.Carrier]
    [IsScalarTower F.Carrier E.Carrier L.Carrier]
    [FiniteDimensional F.Carrier E.Carrier] [FiniteDimensional F.Carrier L.Carrier]
    [Normal F.Carrier E.Carrier] :
    letI := universeZeroAlgebra F E
    letI := universeZeroAlgebra F L
    letI := universeZeroAlgebra E L
    letI := universeZeroAlgebra_isScalarTower_tower F E L
    ∀ [Normal (universeZeroModel F).Carrier (universeZeroModel E).Carrier]
      (τ : Gal((universeZeroModel L).Carrier/(universeZeroModel F).Carrier)),
      AlgEquiv.restrictNormalHom (F := F.Carrier) (K₁ := L.Carrier) E.Carrier
          (universeZeroGaloisEquiv F L τ) =
        universeZeroGaloisEquiv F E
          (AlgEquiv.restrictNormalHom (F := (universeZeroModel F).Carrier)
            (K₁ := (universeZeroModel L).Carrier) (universeZeroModel E).Carrier τ) := by
  let := universeZeroAlgebra F E
  let := universeZeroAlgebra F L
  let := universeZeroAlgebra E L
  let := universeZeroAlgebra_isScalarTower_tower F E L
  intro _hN τ
  ext x
  apply (algebraMap E.Carrier L.Carrier).injective
  change algebraMap E.Carrier L.Carrier
      ((universeZeroGaloisEquiv F L τ).restrictNormal E.Carrier x) =
    algebraMap E.Carrier L.Carrier (universeZeroEquiv E
      ((τ.restrictNormal (universeZeroModel E).Carrier) ((universeZeroEquiv E).symm x)))
  rw [AlgEquiv.restrictNormal_commutes, universeZeroGaloisEquiv_apply F L,
    ← universeZeroEquiv_algebraMap E L, AlgEquiv.restrictNormal_commutes,
    universeZeroEquiv_symm_algebraMap E L]

end Galois

section NormQuotient

variable (F : PadicField.{u} p) (E : PadicField.{v} p) [Algebra F.Carrier E.Carrier]

/-- The model equivalences intertwine the actual field norms. -/
theorem universeZeroEquiv_norm :
    letI := universeZeroAlgebra F E
    ∀ x : (universeZeroModel E).Carrier,
      universeZeroEquiv F (Algebra.norm (universeZeroModel F).Carrier x) =
        Algebra.norm F.Carrier (universeZeroEquiv E x) := by
  let := universeZeroAlgebra F E
  intro x
  rw [Algebra.norm_eq_of_equiv_equiv (universeZeroEquiv F).toRingEquiv
    (universeZeroEquiv E).toRingEquiv (universeZeroAlgebra_compatible F E) x]
  exact (universeZeroEquiv F).toRingEquiv.apply_symm_apply _

/-- The units map of the model equivalence carries the model norm subgroup onto
the actual norm subgroup. -/
theorem universeZeroNormRange_map :
    letI := universeZeroAlgebra F E
    (Units.map (Algebra.norm (universeZeroModel F).Carrier
        (S := (universeZeroModel E).Carrier))).range.map
      (Units.mapEquiv (universeZeroEquiv F).toRingEquiv.toMulEquiv).toMonoidHom =
    (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range := by
  let := universeZeroAlgebra F E
  ext b
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨Units.mapEquiv (universeZeroEquiv E).toRingEquiv.toMulEquiv x, Units.ext ?_⟩
    exact (universeZeroEquiv_norm F E (x : (universeZeroModel E).Carrier)).symm
  · rintro ⟨x, rfl⟩
    refine ⟨_, ⟨Units.mapEquiv (universeZeroEquiv E).toRingEquiv.symm.toMulEquiv x, rfl⟩,
      Units.ext ?_⟩
    change universeZeroEquiv F (Algebra.norm (universeZeroModel F).Carrier
        ((universeZeroEquiv E).symm (x : E.Carrier))) = Algebra.norm F.Carrier (x : E.Carrier)
    rw [universeZeroEquiv_norm, AlgEquiv.apply_symm_apply]

/-- The model equivalence is continuous for the topologies of arbitrary
supplied topological data, since both are module topologies over `Padic p`. -/
theorem universeZeroEquiv_continuous
    (T₀ : (universeZeroModel F).TopologicalData) (T : F.TopologicalData) :
    letI := T₀.topology
    letI := T.topology
    Continuous (universeZeroEquiv F) ∧ Continuous (universeZeroEquiv F).symm := by
  let := T₀.topology
  let := T.topology
  have := T₀.moduleTopology
  have := T.moduleTopology
  have : ContinuousAdd F.Carrier := IsModuleTopology.toContinuousAdd (Padic p) F.Carrier
  have : ContinuousAdd (universeZeroModel F).Carrier :=
    IsModuleTopology.toContinuousAdd (Padic p) (universeZeroModel F).Carrier
  exact ⟨IsModuleTopology.continuous_of_linearMap (universeZeroEquiv F).toLinearEquiv.toLinearMap,
    IsModuleTopology.continuous_of_linearMap
      (universeZeroEquiv F).symm.toLinearEquiv.toLinearMap⟩

/-- The actual norm quotient of the model extension, with the quotient topology
of `T₀`, identified with the actual norm quotient of the supplied extension,
with the quotient topology of `T`, by the units map of the model equivalence. -/
def universeZeroNormQuotientEquiv
    (T₀ : (universeZeroModel F).TopologicalData) (T : F.TopologicalData) :
    letI := universeZeroAlgebra F E
    letI := T₀.topology
    letI := T.topology
    ((universeZeroModel F).Carrierˣ ⧸
        (Units.map (Algebra.norm (universeZeroModel F).Carrier
          (S := (universeZeroModel E).Carrier))).range) ≃ₜ*
      (F.Carrierˣ ⧸ (Units.map (Algebra.norm F.Carrier (S := E.Carrier))).range) :=
  letI := universeZeroAlgebra F E
  letI := T₀.topology
  letI := T.topology
  { QuotientGroup.congr _ _ (Units.mapEquiv (universeZeroEquiv F).toRingEquiv.toMulEquiv)
      (universeZeroNormRange_map F E) with
    continuous_toFun := by
      refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
      exact QuotientGroup.continuous_mk.comp
        (Continuous.units_map _ (universeZeroEquiv_continuous F T₀ T).1)
    continuous_invFun := by
      refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 ?_
      exact QuotientGroup.continuous_mk.comp
        (Continuous.units_map _ (universeZeroEquiv_continuous F T₀ T).2) }

/-- The quotient identification sends the class of a model unit to the class of
its image unit. -/
theorem universeZeroNormQuotientEquiv_mk
    (T₀ : (universeZeroModel F).TopologicalData) (T : F.TopologicalData) :
    letI := universeZeroAlgebra F E
    letI := T₀.topology
    letI := T.topology
    ∀ a : (universeZeroModel F).Carrierˣ,
      universeZeroNormQuotientEquiv F E T₀ T (QuotientGroup.mk a) =
        QuotientGroup.mk (Units.mapEquiv (universeZeroEquiv F).toRingEquiv.toMulEquiv a) :=
  fun _ => rfl

/-- The inverse quotient identification sends the class of a unit of `F` to the
class of its model unit. -/
theorem universeZeroNormQuotientEquiv_symm_mk
    (T₀ : (universeZeroModel F).TopologicalData) (T : F.TopologicalData) :
    letI := universeZeroAlgebra F E
    letI := T₀.topology
    letI := T.topology
    ∀ a : F.Carrierˣ,
      (universeZeroNormQuotientEquiv F E T₀ T).symm (QuotientGroup.mk a) =
        QuotientGroup.mk (Units.mapEquiv (universeZeroEquiv F).toRingEquiv.symm.toMulEquiv a) :=
  fun _ => rfl

end NormQuotient

section Arithmetic

variable {F : PadicField.{u} p} {F' : PadicField.{u'} p}

/-- Residue cardinalities of arbitrary supplied topological data agree along an
actual algebra equivalence over `Padic p`. -/
theorem residueCardinality_eq_of_algEquiv (e : F.Carrier ≃ₐ[Padic p] F'.Carrier)
    (T : F.TopologicalData) (T' : F'.TopologicalData) :
    T'.residueCardinality = T.residueCardinality := by
  rw [FiniteArtinSystemUniqueness.residueCardinality_eq_canonical F' T',
    FiniteArtinSystemUniqueness.residueCardinality_eq_canonical F T]
  exact PadicField.CanonicalTransport.residueCardinality_eq F F' e

/-- The normalized additive orders of arbitrary supplied topological data agree
along an actual algebra equivalence over `Padic p`, including at zero. -/
theorem ord_eq_of_algEquiv (e : F.Carrier ≃ₐ[Padic p] F'.Carrier)
    (T : F.TopologicalData) (T' : F'.TopologicalData) (x : F.Carrier) :
    T'.ord (e x) = T.ord x := by
  by_cases hx : x = 0
  · simp [hx, PadicField.TopologicalData.ord_zero]
  have he : e x ≠ 0 := by simpa only [map_zero] using e.injective.ne hx
  have h : T'.normalizedAbs (e x) = T.normalizedAbs x := by
    rw [T'.normalizedAbs_eq_canonicalNorm_pow_degree, T.normalizedAbs_eq_canonicalNorm_pow_degree,
      show F'.canonicalNorm (e x) = F.canonicalNorm x from
        Weil.Local.canonicalNorm_map F F' e.toAlgHom x,
      e.toLinearEquiv.finrank_eq]
  rw [T'.normalizedAbs_of_ne_zero he, T.normalizedAbs_of_ne_zero hx,
    residueCardinality_eq_of_algEquiv e T T'] at h
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  exact neg_injective (zpow_right_injective₀ (zero_lt_one.trans hq) (ne_of_gt hq) h)

/-- The normalized discrete valuations of arbitrary supplied topological data
agree along an actual algebra equivalence over `Padic p`, including at zero. -/
theorem discreteValuation_eq_of_algEquiv (e : F.Carrier ≃ₐ[Padic p] F'.Carrier)
    (T : F.TopologicalData) (T' : F'.TopologicalData) (x : F.Carrier) :
    T'.discreteValuation (e x) = T.discreteValuation x := by
  by_cases hx : x = 0
  · simp [hx]
  have he : e x ≠ 0 := by simpa only [map_zero] using e.injective.ne hx
  have h := congrArg Neg.neg (ord_eq_of_algEquiv e T T' x)
  simp only [PadicField.TopologicalData.ord, neg_neg] at h
  have he0 := (T'.discreteValuation.ne_zero_iff).mpr he
  have hx0 := (T.discreteValuation.ne_zero_iff).mpr hx
  simpa only [WithZero.exp_log he0, WithZero.exp_log hx0] using congrArg WithZero.exp h

end Arithmetic

end Langlands.LocalClassField.NYLL
