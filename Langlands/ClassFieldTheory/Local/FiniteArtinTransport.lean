import Langlands.ClassFieldTheory.Local.FiniteArtin
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Transport of finite Artin families through fixed field equivalences

All equivalences in this module are supplied field identifications. No Artin
homomorphism, norm-residue theorem or arithmetic existence is constructed.
-/

noncomputable section

namespace Langlands.LocalClassField.FiniteArtinTransport

universe u v w z

section Automorphisms

variable {K : Type u} {K' : Type v} {E : Type w} {E' : Type z}
  [Field K] [Field K'] [Field E] [Field E']
  [Algebra K E] [Algebra K' E']

/-- Conjugation of automorphisms through a compatible pair of field
equivalences, with independent universes for all four fields. -/
def galoisEquiv (eK : K ≃+* K') (eE : E ≃+* E')
    (h : (algebraMap K' E').comp eK.toRingHom =
      eE.toRingHom.comp (algebraMap K E)) :
    Gal(E/K) ≃* Gal(E'/K') where
  toFun σ :=
    { __ := eE.symm.trans (σ.toRingEquiv.trans eE)
      commutes' x := by
        have hx := DFunLike.congr_fun h (eK.symm x)
        have hx' : eE.symm (algebraMap K' E' x) =
            algebraMap K E (eK.symm x) := by
          apply eE.injective
          simpa using hx
        change eE (σ (eE.symm (algebraMap K' E' x))) = _
        rw [hx', σ.commutes]
        simpa using hx.symm }
  invFun σ :=
    { __ := eE.trans (σ.toRingEquiv.trans eE.symm)
      commutes' x := by
        have hx := DFunLike.congr_fun h x
        change algebraMap K' E' (eK x) = eE (algebraMap K E x) at hx
        change eE.symm (σ (eE (algebraMap K E x))) = _
        rw [← hx, σ.commutes]
        simpa using congrArg eE.symm hx }
  left_inv σ := by
    ext x
    change eE.symm (eE (σ (eE.symm (eE x)))) = σ x
    simp
  right_inv σ := by
    ext x
    change eE (eE.symm (σ (eE (eE.symm x)))) = σ x
    simp
  map_mul' σ τ := by
    ext x
    change eE ((σ * τ) (eE.symm x)) =
      eE (σ (eE.symm (eE (τ (eE.symm x)))))
    simp

@[simp] theorem galoisEquiv_apply
    (eK : K ≃+* K') (eE : E ≃+* E')
    (h : (algebraMap K' E').comp eK.toRingHom =
      eE.toRingHom.comp (algebraMap K E))
    (σ : Gal(E/K)) (x : E') :
    galoisEquiv eK eE h σ x = eE (σ (eE.symm x)) := rfl

@[simp] theorem galoisEquiv_symm_apply
    (eK : K ≃+* K') (eE : E ≃+* E')
    (h : (algebraMap K' E').comp eK.toRingHom =
      eE.toRingHom.comp (algebraMap K E))
    (σ : Gal(E'/K')) (x : E) :
    (galoisEquiv eK eE h).symm σ x = eE.symm (σ (eE x)) := rfl

end Automorphisms

section Norms

variable {K : Type u} {K' : Type v} {E : Type w} {E' : Type z}
  [Field K] [Field K'] [Field E] [Field E']
  [Algebra K E] [Algebra K' E']
  [FiniteDimensional K E] [FiniteDimensional K' E']

/-- Actual unit norms commute with a compatible pair of field equivalences. -/
theorem normUnits_map (eK : K ≃+* K') (eE : E ≃+* E')
    (h : (algebraMap K' E').comp eK.toRingHom =
      eE.toRingHom.comp (algebraMap K E)) (x : Eˣ) :
    normUnits K' E' (Units.mapEquiv eE.toMulEquiv x) =
      Units.mapEquiv eK.toMulEquiv (normUnits K E x) := by
  apply Units.ext
  have hn : eK (Algebra.norm K (x : E)) = Algebra.norm K' (eE (x : E)) := by
    simpa using congrArg eK (Algebra.norm_eq_of_equiv_equiv eK eE h (x : E))
  exact hn.symm

/-- Membership in the actual norm image is preserved and reflected. -/
theorem mem_normSubgroup_map_iff (eK : K ≃+* K') (eE : E ≃+* E')
    (h : (algebraMap K' E').comp eK.toRingHom =
      eE.toRingHom.comp (algebraMap K E)) (b : Kˣ) :
    Units.mapEquiv eK.toMulEquiv b ∈ normSubgroup K' E' ↔
      b ∈ normSubgroup K E := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(Units.mapEquiv eE.toMulEquiv).symm x, ?_⟩
    apply (Units.mapEquiv eK.toMulEquiv).injective
    rw [← normUnits_map eK eE h]
    rw [MulEquiv.apply_symm_apply]
    exact hx
  · rintro ⟨x, rfl⟩
    exact ⟨Units.mapEquiv eE.toMulEquiv x, normUnits_map eK eE h x⟩

end Norms

section Indices

variable {K : Type u} {K' : Type v} [Field K] [Field K']
  (eK : K ≃+* K')
  (eC : AlgebraicClosure K ≃+* AlgebraicClosure K')
  (h : (algebraMap K' (AlgebraicClosure K')).comp eK.toRingHom =
    eC.toRingHom.comp (algebraMap K (AlgebraicClosure K)))

/-- The actual image intermediate field under the fixed closure equivalence.
Membership is expressed by its inverse, so inclusions remain literal inclusions. -/
def intermediateField (L : IntermediateField K (AlgebraicClosure K)) :
    IntermediateField K' (AlgebraicClosure K') :=
  (L.toSubfield.comap eC.symm.toRingHom).toIntermediateField (by
    intro x
    change eC.symm (algebraMap K' (AlgebraicClosure K') x) ∈ L
    have hx := DFunLike.congr_fun h (eK.symm x)
    have heq : eC.symm (algebraMap K' (AlgebraicClosure K') x) =
        algebraMap K (AlgebraicClosure K) (eK.symm x) := by
      apply eC.injective
      simpa using hx
    rw [heq]
    exact L.algebraMap_mem _)

/-- Restriction of the same closure equivalence to an actual intermediate field. -/
def fieldEquiv (L : IntermediateField K (AlgebraicClosure K)) :
    L ≃+* intermediateField eK eC h L where
  toFun x := ⟨eC x, by
    change eC.symm (eC x) ∈ L
    simp only [RingEquiv.symm_apply_apply]
    exact x.property⟩
  invFun x := ⟨eC.symm x, x.property⟩
  left_inv x := Subtype.ext (eC.symm_apply_apply x)
  right_inv x := Subtype.ext (eC.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul eC (x : AlgebraicClosure K) y)
  map_add' x y := Subtype.ext (map_add eC (x : AlgebraicClosure K) y)

@[simp] theorem fieldEquiv_apply_coe
    (L : IntermediateField K (AlgebraicClosure K)) (x : L) :
    (fieldEquiv eK eC h L x : AlgebraicClosure K') = eC x := rfl

/-- The restricted equivalence and the base equivalence form the same
commuting algebra-map square as the supplied closure equivalence. -/
theorem fieldEquiv_compatible (L : IntermediateField K (AlgebraicClosure K)) :
    (algebraMap K' (intermediateField eK eC h L)).comp eK.toRingHom =
      (fieldEquiv eK eC h L).toRingHom.comp (algebraMap K L) := by
  ext x
  exact DFunLike.congr_fun h x

theorem intermediateField_mono
    {L M : IntermediateField K (AlgebraicClosure K)} (hLM : L ≤ M) :
    intermediateField eK eC h L ≤ intermediateField eK eC h M :=
  fun _ hx => hLM hx

/-- A finite Galois field remains finite Galois under the fixed field
identifications. The two certificates are transported, rather than assumed. -/
def finiteGaloisField (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    FiniteGaloisIntermediateField K' (AlgebraicClosure K') where
  toIntermediateField := intermediateField eK eC h L.toIntermediateField
  finiteDimensional := Module.Finite.of_equiv_equiv eK (fieldEquiv eK eC h _)
    (fieldEquiv_compatible eK eC h _)
  isGalois := IsGalois.of_equiv_equiv (f := eK) (g := fieldEquiv eK eC h _)
    (fieldEquiv_compatible eK eC h _)

/-- The actual finite automorphism groups are identified by conjugation. -/
def finiteGaloisEquiv (L : FiniteGaloisIntermediateField K (AlgebraicClosure K)) :
    Gal(L/K) ≃* Gal(finiteGaloisField eK eC h L/K') :=
  galoisEquiv eK (fieldEquiv eK eC h _) (fieldEquiv_compatible eK eC h _)

/-- Transport of the actual finite abelian index. Abelianity is deduced from
the induced isomorphism of the actual automorphism groups. -/
def extension (L : FiniteAbelianExtension K) : FiniteAbelianExtension K' :=
  ⟨finiteGaloisField eK eC h L.field, by
    let e := finiteGaloisEquiv eK eC h L.field
    refine ⟨⟨?_⟩⟩
    intro σ τ
    exact e.symm.injective (by
      rw [map_mul, map_mul]
      exact L.2.is_comm.comm (e.symm σ) (e.symm τ))⟩

/-- Conjugation is a homeomorphism for the finite discrete Krull topologies. -/
def extensionGaloisEquiv (L : FiniteAbelianExtension K) :
    L.galoisGroup ≃ₜ* (extension eK eC h L).galoisGroup :=
  { finiteGaloisEquiv eK eC h L.field with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

theorem extension_mono {L M : FiniteAbelianExtension K} (hLM : L.field ≤ M.field) :
    (extension eK eC h L).field ≤ (extension eK eC h M).field :=
  intermediateField_mono eK eC h hLM

@[simp] theorem extensionGaloisEquiv_apply_coe (L : FiniteAbelianExtension K)
    (σ : L.galoisGroup) (x : (extension eK eC h L).field) :
    (extensionGaloisEquiv eK eC h L σ x : AlgebraicClosure K') =
      eC (σ ⟨eC.symm x, x.property⟩) := rfl

/-- Coercing the actual restriction gives the same automorphism on an element
of the smaller intermediate field. -/
theorem restrictionOfLE_apply_coe (L M : FiniteAbelianExtension K)
    (hLM : L.field ≤ M.field) (σ : M.galoisGroup) (x : L.field) :
    (L.restrictionOfLE M hLM σ x : AlgebraicClosure K) =
      (σ ⟨x, hLM x.property⟩ : AlgebraicClosure K) := by
  let : Algebra L.field M.field := (Subsemiring.inclusion hLM).toAlgebra
  let : IsScalarTower K L.field M.field := IsScalarTower.of_algebraMap_eq' rfl
  exact congrArg (fun y : M.field => (y : AlgebraicClosure K))
    (AlgEquiv.restrictNormal_commutes σ L.field x)

/-- Conjugacy through the one supplied closure equivalence commutes with every
actual finite-field restriction. -/
theorem extensionGaloisEquiv_restriction (L M : FiniteAbelianExtension K)
    (hLM : L.field ≤ M.field) :
    (extensionGaloisEquiv eK eC h L : L.galoisGroup →ₜ*
      (extension eK eC h L).galoisGroup).comp (L.restrictionOfLE M hLM) =
    ((extension eK eC h L).restrictionOfLE (extension eK eC h M)
      (extension_mono eK eC h hLM)).comp
        (extensionGaloisEquiv eK eC h M) := by
  ext σ x
  change (extensionGaloisEquiv eK eC h L (L.restrictionOfLE M hLM σ) x :
      AlgebraicClosure K') =
    ((extension eK eC h L).restrictionOfLE (extension eK eC h M)
      (extension_mono eK eC h hLM) (extensionGaloisEquiv eK eC h M σ) x :
        AlgebraicClosure K')
  rw [restrictionOfLE_apply_coe]
  change eC ((L.restrictionOfLE M hLM σ) ⟨eC.symm x, x.property⟩ :
      AlgebraicClosure K) = eC (σ ⟨eC.symm x, hLM x.property⟩)
  rw [restrictionOfLE_apply_coe]

end Indices

section Families

variable {K : Type u} {K' : Type v} [Field K] [Field K']
  [TopologicalSpace K] [TopologicalSpace K']
  (eK : K ≃+* K')
  (eC : AlgebraicClosure K ≃+* AlgebraicClosure K')
  (h : (algebraMap K' (AlgebraicClosure K')).comp eK.toRingHom =
    eC.toRingHom.comp (algebraMap K (AlgebraicClosure K)))

/-- The unit homomorphism induced by the supplied continuous base equivalence. -/
def unitsHom (heK : Continuous eK) : Kˣ →ₜ* K'ˣ where
  toMonoidHom := (Units.mapEquiv eK.toMulEquiv).toMonoidHom
  continuous_toFun := heK.units_map _

/-- Pull one supplied family back at all actual indices simultaneously. -/
def pullback (heK : Continuous eK) (a' : FiniteArtinFamily K') :
    FiniteArtinFamily K :=
  fun L => ((extensionGaloisEquiv eK eC h L).symm :
    (extension eK eC h L).galoisGroup →ₜ* L.galoisGroup).comp
      ((a' (extension eK eC h L)).comp (unitsHom eK heK))

@[simp] theorem pullback_apply (heK : Continuous eK)
    (a' : FiniteArtinFamily K') (L : FiniteAbelianExtension K) (b : Kˣ) :
    pullback eK eC h heK a' L b =
      (extensionGaloisEquiv eK eC h L).symm
        (a' (extension eK eC h L) (Units.mapEquiv eK.toMulEquiv b)) := rfl

/-- The exact finite norm-residue relation is preserved at each image index. -/
theorem pullback_finiteNormResidueRelation (heK : Continuous eK)
    (a' : FiniteArtinFamily K') (L : FiniteAbelianExtension K)
    (ha : FiniteNormResidueRelation (extension eK eC h L)
      (a' (extension eK eC h L))) :
    FiniteNormResidueRelation L (pullback eK eC h heK a' L) := by
  constructor
  · ext b
    change ((extensionGaloisEquiv eK eC h L).symm
      (a' (extension eK eC h L) (Units.mapEquiv eK.toMulEquiv b)) = 1) ↔ _
    rw [EmbeddingLike.map_eq_one_iff]
    change Units.mapEquiv eK.toMulEquiv b ∈
      (a' (extension eK eC h L)).toMonoidHom.ker ↔ _
    rw [ha.1]
    exact @mem_normSubgroup_map_iff K K' L.field (extension eK eC h L).field
      _ _ _ _ _ _ L.field.finiteDimensional
      (extension eK eC h L).field.finiteDimensional
      eK (fieldEquiv eK eC h L.field.toIntermediateField)
      (fieldEquiv_compatible eK eC h L.field.toIntermediateField) b
  · intro σ
    obtain ⟨b', hb⟩ := ha.2 (extensionGaloisEquiv eK eC h L σ)
    refine ⟨(Units.mapEquiv eK.toMulEquiv).symm b', ?_⟩
    rw [pullback_apply, MulEquiv.apply_symm_apply, hb,
      ContinuousMulEquiv.symm_apply_apply]

/-- The same supplied family remains coherent under every actual restriction. -/
theorem pullback_finiteArtinRestrictionRelation (heK : Continuous eK)
    (a' : FiniteArtinFamily K') (ha : FiniteArtinRestrictionRelation a') :
    FiniteArtinRestrictionRelation (pullback eK eC h heK a') := by
  intro L M hLM
  apply ContinuousMonoidHom.ext
  intro b
  change L.restrictionOfLE M hLM (pullback eK eC h heK a' M b) =
    pullback eK eC h heK a' L b
  apply (extensionGaloisEquiv eK eC h L).injective
  calc
    extensionGaloisEquiv eK eC h L
        (L.restrictionOfLE M hLM (pullback eK eC h heK a' M b)) =
      (extension eK eC h L).restrictionOfLE (extension eK eC h M)
        (extension_mono eK eC h hLM)
          (extensionGaloisEquiv eK eC h M (pullback eK eC h heK a' M b)) :=
      DFunLike.congr_fun (extensionGaloisEquiv_restriction eK eC h L M hLM) _
    _ = (extension eK eC h L).restrictionOfLE (extension eK eC h M)
        (extension_mono eK eC h hLM)
          (a' (extension eK eC h M) (Units.mapEquiv eK.toMulEquiv b)) := by
      rw [pullback_apply, ContinuousMulEquiv.apply_symm_apply]
    _ = a' (extension eK eC h L) (Units.mapEquiv eK.toMulEquiv b) :=
      DFunLike.congr_fun (ha _ _ (extension_mono eK eC h hLM)) _
    _ = extensionGaloisEquiv eK eC h L (pullback eK eC h heK a' L b) := by
      rw [pullback_apply, ContinuousMulEquiv.apply_symm_apply]

/-- Transport of an unnormalized finite Artin system. This consumes a supplied
system and proves its norm and coherence properties on the source field. -/
theorem pullback_finiteArtinSystemRelation (heK : Continuous eK)
    (a' : FiniteArtinFamily K') (ha : FiniteArtinSystemRelation a') :
    FiniteArtinSystemRelation (pullback eK eC h heK a') :=
  ⟨fun L => pullback_finiteNormResidueRelation eK eC h heK a' L (ha.1 _),
    pullback_finiteArtinRestrictionRelation eK eC h heK a' ha.2⟩

end Families

end Langlands.LocalClassField.FiniteArtinTransport
