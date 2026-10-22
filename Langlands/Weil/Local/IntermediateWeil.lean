import Langlands.Weil.Local.ExtensionWeilRange
import Langlands.ClassFieldTheory.Local.ReciprocitySystem

/-!
# The Weil group of a prescribed intermediate field
-/

noncomputable section

namespace Langlands.Weil.Local

open LocalClassField

universe u

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
  (E : FiniteIntermediateExtension F.Carrier)

local notation "EP" => E.asPadicField (p := p)

local instance : Algebra (Padic p) E.field := (EP).algebra

/-- The actual base-field inclusion into the prescribed intermediate field. -/
def intermediateEmbedding : F.Carrier →ₐ[Padic p] E.field where
  toRingHom := algebraMap F.Carrier E.field
  commutes' _ := rfl

/-- A closure isomorphism extending the literal inclusion of `E` in the fixed closure. -/
def intermediateClosureEquiv : AlgebraicClosure E.field ≃ₐ[E.field]
    AlgebraicClosure F.Carrier := by
  have : Algebra.IsAlgebraic E.field (AlgebraicClosure F.Carrier) :=
    Algebra.IsAlgebraic.tower_top (K := F.Carrier) E.field
  exact AlgEquiv.ofBijective (IsAlgClosed.lift : AlgebraicClosure E.field →ₐ[E.field]
    AlgebraicClosure F.Carrier) (Algebra.IsAlgebraic.algHom_bijective₂
      (IsAlgClosed.lift : AlgebraicClosure E.field →ₐ[E.field] AlgebraicClosure F.Carrier)
      (IsAlgClosed.lift : AlgebraicClosure F.Carrier →ₐ[E.field] AlgebraicClosure E.field)).1

@[simp] theorem intermediateClosureEquiv_algebraMap (x : E.field) :
    intermediateClosureEquiv F E (algebraMap E.field (AlgebraicClosure E.field) x) =
      (x : AlgebraicClosure F.Carrier) :=
  (intermediateClosureEquiv F E).commutes x

/-- The automorphism correcting the published chosen lift to the prescribed inclusion. -/
def intermediateClosureCorrection : Field.absoluteGaloisGroup F.Carrier :=
  AlgEquiv.ofRingEquiv
    (f := (extensionClosureEquiv F EP (intermediateEmbedding F E)).trans
      (intermediateClosureEquiv F E).toRingEquiv) (fun x => by
        change intermediateClosureEquiv F E
          (extensionClosureEquiv F EP (intermediateEmbedding F E)
            (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x)) = _
        rw [extensionClosureEquiv_apply, extensionClosureLift_algebraMap,
          intermediateClosureEquiv_algebraMap]
        rfl)

/-- The correction sends the old chosen image of every field element to that same element. -/
theorem intermediateClosureCorrection_fieldEmbedding (x : E.field) :
    AlgEquiv.toAlgHom (intermediateClosureCorrection F E)
      (extensionFieldEmbedding F EP (intermediateEmbedding F E) x) =
      (x : AlgebraicClosure F.Carrier) := by
  change intermediateClosureEquiv F E
    (extensionClosureEquiv F EP (intermediateEmbedding F E)
      (extensionFieldEmbedding F EP (intermediateEmbedding F E) x)) = _
  rw [extensionClosureEquiv_apply, extensionClosureLift_fieldEmbedding,
    intermediateClosureEquiv_algebraMap]

/-- The Galois map induced by the closure isomorphism extending the prescribed inclusion. -/
def intermediateGaloisMap :
    Field.absoluteGaloisGroup E.field →ₜ* Field.absoluteGaloisGroup F.Carrier := by
  let c := intermediateClosureCorrection F E
  exact
    { toFun := fun τ => c * extensionGaloisMap F EP (intermediateEmbedding F E) τ * c⁻¹
      map_one' := by simp
      map_mul' := fun τ υ => by simp [mul_assoc]
      continuous_toFun := (continuous_const.mul
        (extensionGaloisMap F EP (intermediateEmbedding F E)).continuous).mul continuous_const }

/-- The induced Galois action commutes with the prescribed closure isomorphism. -/
theorem intermediateClosureEquiv_galoisMap (τ : Field.absoluteGaloisGroup E.field)
    (x : AlgebraicClosure E.field) :
    AlgEquiv.toAlgHom (intermediateGaloisMap F E τ) (intermediateClosureEquiv F E x) =
      intermediateClosureEquiv F E (AlgEquiv.toAlgHom τ x) := by
  obtain ⟨y, rfl⟩ := (extensionClosureEquiv F EP (intermediateEmbedding F E)).surjective x
  let c : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    intermediateClosureCorrection F E
  change c (AlgEquiv.toAlgHom (extensionGaloisMap F EP (intermediateEmbedding F E) τ)
    (c.symm (c y))) = _
  rw [AlgEquiv.symm_apply_apply]
  change intermediateClosureEquiv F E
    (extensionClosureLift F EP (intermediateEmbedding F E)
      (AlgEquiv.toAlgHom (extensionGaloisMap F EP (intermediateEmbedding F E) τ) y)) = _
  rw [extensionClosureLift_galoisMap]
  rfl

/-- Pointwise formula for the prescribed Galois map. -/
theorem intermediateGaloisMap_apply (τ : Field.absoluteGaloisGroup E.field)
    (x : AlgebraicClosure F.Carrier) :
    AlgEquiv.toAlgHom (intermediateGaloisMap F E τ) x =
      intermediateClosureEquiv F E
        (AlgEquiv.toAlgHom τ ((intermediateClosureEquiv F E).symm x)) := by
  rw [← intermediateClosureEquiv_galoisMap, AlgEquiv.apply_symm_apply]

/-- Conjugation by the correction carries the old image-field fixing condition to `E`. -/
theorem intermediateClosureCorrection_conj_mem (τ : Field.absoluteGaloisGroup F.Carrier) :
    intermediateClosureCorrection F E * τ * (intermediateClosureCorrection F E)⁻¹ ∈
        E.field.fixingSubgroup ↔
      τ ∈ (extensionIntermediateField F EP (intermediateEmbedding F E)).fixingSubgroup := by
  let c : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    intermediateClosureCorrection F E
  let t : AlgebraicClosure F.Carrier ≃ₐ[F.Carrier] AlgebraicClosure F.Carrier := τ
  have key (x : E.field) :
      AlgEquiv.toAlgHom (c * t * c⁻¹) (x : AlgebraicClosure F.Carrier) =
        c (t (extensionFieldEmbedding F EP (intermediateEmbedding F E) x)) := by
    rw [← intermediateClosureCorrection_fieldEmbedding F E x]
    change c (t (c.symm (c _))) = _
    rw [AlgEquiv.symm_apply_apply]
  change (c * t * c⁻¹ ∈ E.field.fixingSubgroup) ↔
    t ∈
      (extensionIntermediateField F EP (intermediateEmbedding F E)).fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F EP (intermediateEmbedding F E) y).mp hy
    apply c.injective
    exact (key x).symm.trans ((h x x.property).trans
      (intermediateClosureCorrection_fieldEmbedding F E x).symm)
  · intro h y hy
    let x : E.field := ⟨y, hy⟩
    have hx := h _ ((mem_extensionIntermediateField F EP (intermediateEmbedding F E) _).mpr
      ⟨x, rfl⟩)
    change AlgEquiv.toAlgHom (c * t * c⁻¹) (x : AlgebraicClosure F.Carrier) = _
    rw [key, hx]
    exact intermediateClosureCorrection_fieldEmbedding F E x

private theorem frobenius_central (z : ProfiniteIntegers) (n : Degree) :
    z * frobenius n = frobenius n * z := by
  have h : (fun z : ProfiniteIntegers => z * frobenius n) =
      fun z => frobenius n * z := by
    refine Continuous.ext_on
      (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree))
      (continuous_id.mul continuous_const) (continuous_const.mul continuous_id) ?_
    rintro _ ⟨m, rfl⟩
    change frobenius m * frobenius n = frobenius n * frobenius m
    rw [← map_mul, ← map_mul, mul_comm]
  exact congrFun h z

/-- Conjugation by an arbitrary absolute Galois element on the actual Weil pullback. -/
def galoisConjugationWeil (σ : Field.absoluteGaloisGroup F.Carrier) :
    localWeilGroup F ≃ₜ* localWeilGroup F := by
  let c (τ : Field.absoluteGaloisGroup F.Carrier) (w : localWeilGroup F) :
      localWeilGroup F := ⟨(τ * w.val.1 * τ⁻¹, w.val.2), by
    have hw : localResidueDegree F w.val.1 = frobenius w.val.2 := w.property
    change localResidueDegree F (τ * w.val.1 * τ⁻¹) = frobenius w.val.2
    rw [map_mul, map_mul, map_inv, hw, frobenius_central,
      mul_assoc, mul_inv_cancel, mul_one]⟩
  have hc (τ : Field.absoluteGaloisGroup F.Carrier) : Continuous (c τ) :=
    (((continuous_const.mul (continuous_fst.comp continuous_subtype_val)).mul
      continuous_const).prodMk (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  exact
    { toFun := c σ
      invFun := c σ⁻¹
      left_inv := fun w => by apply Subtype.ext; apply Prod.ext <;> simp [c, mul_assoc]
      right_inv := fun w => by apply Subtype.ext; apply Prod.ext <;> simp [c, mul_assoc]
      map_mul' := fun x y => by apply Subtype.ext; apply Prod.ext <;> simp [c, mul_assoc]
      continuous_toFun := hc σ
      continuous_invFun := hc σ⁻¹ }

@[simp] theorem localProjection_galoisConjugationWeil
    (σ : Field.absoluteGaloisGroup F.Carrier) (w : localWeilGroup F) :
    localProjection F (galoisConjugationWeil F σ w) =
      σ * localProjection F w * σ⁻¹ := rfl

@[simp] theorem localDegree_galoisConjugationWeil
    (σ : Field.absoluteGaloisGroup F.Carrier) (w : localWeilGroup F) :
    localDegree F (galoisConjugationWeil F σ w) = localDegree F w := rfl

/-- The continuous Weil map using the prescribed intermediate-field inclusion. -/
def intermediateWeilMap : localWeilGroup EP →ₜ* localWeilGroup F :=
  (galoisConjugationWeil F (intermediateClosureCorrection F E) : _ →ₜ* _).comp
    (extensionWeilMap F EP (intermediateEmbedding F E))

@[simp] theorem localProjection_intermediateWeilMap (w : localWeilGroup EP) :
    localProjection F (intermediateWeilMap F E w) =
      intermediateGaloisMap F E (localProjection EP w) := rfl

@[simp] theorem localDegree_intermediateWeilMap (w : localWeilGroup EP) :
    localDegree F (intermediateWeilMap F E w) =
      localDegree EP w ^ extensionResidueDegree F EP (intermediateEmbedding F E) := rfl

/-- The corrected Weil map has exactly the prescribed fixing subgroup as image. -/
theorem intermediateWeilMap_range :
    (intermediateWeilMap F E).toMonoidHom.range =
      pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) := by
  have mem_old (w : localWeilGroup F) :
      w ∈ (extensionWeilMap F EP (intermediateEmbedding F E)).toMonoidHom.range ↔
        localProjection F w ∈
          (extensionIntermediateField F EP (intermediateEmbedding F E)).fixingSubgroup := by
    rw [extensionWeilMap_range, extensionGaloisMap_range]
    rfl
  have mem_new (w : localWeilGroup F) :
      galoisConjugationWeil F (intermediateClosureCorrection F E) w ∈
          pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) ↔
        w ∈ (extensionWeilMap F EP (intermediateEmbedding F E)).toMonoidHom.range := by
    rw [mem_old]
    exact intermediateClosureCorrection_conj_mem F E (localProjection F w)
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    exact (mem_new _).mpr ⟨v, rfl⟩
  · intro hw
    let c := galoisConjugationWeil F (intermediateClosureCorrection F E)
    have hc : c (c.symm w) = w := c.apply_symm_apply w
    have hold := (mem_new (c.symm w)).mp (hc.symm ▸ hw)
    obtain ⟨v, hv⟩ := hold
    refine ⟨v, ?_⟩
    change c (extensionWeilMap F EP (intermediateEmbedding F E) v) = w
    have hv' : extensionWeilMap F EP (intermediateEmbedding F E) v = c.symm w := hv
    rw [hv', hc]

/-- Injectivity is preserved by the conjugacy correction. -/
theorem intermediateWeilMap_injective : Function.Injective (intermediateWeilMap F E) :=
  (galoisConjugationWeil F (intermediateClosureCorrection F E)).injective.comp
    (extensionWeilMap_injective F EP (intermediateEmbedding F E))

/-- The actual canonical topology on `W_E` is the topology induced from `W_F`. -/
theorem intermediateWeilMap_isEmbedding : Topology.IsEmbedding (intermediateWeilMap F E) :=
  (galoisConjugationWeil F (intermediateClosureCorrection F E)).toHomeomorph.isEmbedding.comp
    (extensionWeilMap_isEmbedding F EP (intermediateEmbedding F E))

/-- The standalone Weil group of the prescribed field as its actual fixing subgroup. -/
def intermediateWeilEquiv : localWeilGroup EP ≃ₜ*
    pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) := by
  let e : localWeilGroup EP ≃ₜ* (intermediateWeilMap F E).toMonoidHom.range :=
    { toMulEquiv := MonoidHom.ofInjective (f := (intermediateWeilMap F E).toMonoidHom)
        (intermediateWeilMap_injective F E)
      continuous_toFun := (intermediateWeilMap F E).continuous.subtype_mk _
      continuous_invFun := by
        rw [(intermediateWeilMap_isEmbedding F E).isInducing.continuous_iff]
        convert continuous_subtype_val using 1
        funext x
        exact MonoidHom.apply_ofInjective_symm (intermediateWeilMap_injective F E) x }
  exact e.trans
    { toMulEquiv := MulEquiv.subgroupCongr (intermediateWeilMap_range F E)
      continuous_toFun := continuous_subtype_val.subtype_mk _
      continuous_invFun := continuous_subtype_val.subtype_mk _ }

@[simp] theorem intermediateWeilEquiv_apply (w : localWeilGroup EP) :
    (intermediateWeilEquiv F E w : localWeilGroup F) = intermediateWeilMap F E w := rfl

@[simp] theorem intermediateWeilMap_equiv_symm
    (x : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    intermediateWeilMap F E ((intermediateWeilEquiv F E).symm x) = x :=
  congrArg Subtype.val ((intermediateWeilEquiv F E).apply_symm_apply x)

/-- Ambient projection agrees with the action through the prescribed closure isomorphism. -/
theorem intermediateWeilEquiv_projection (w : localWeilGroup EP) :
    localProjection F (intermediateWeilEquiv F E w : localWeilGroup F) =
      intermediateGaloisMap F E (localProjection EP w) := rfl

/-- The projection formula in the inverse direction. -/
theorem intermediateWeilEquiv_symm_projection
    (x : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    intermediateGaloisMap F E (localProjection EP ((intermediateWeilEquiv F E).symm x)) =
      localProjection F x := by
  rw [← localProjection_intermediateWeilMap, intermediateWeilMap_equiv_symm]

/-- Geometric integer degree scales by the actual relative residue degree. -/
theorem intermediateWeilEquiv_degree (w : localWeilGroup EP) :
    localDegreeInt F (intermediateWeilEquiv F E w : localWeilGroup F) =
      extensionResidueDegree F EP (intermediateEmbedding F E) * localDegreeInt EP w :=
  localDegreeInt_extensionWeilMap F EP (intermediateEmbedding F E) w

/-- The inverse element's degree recovers the ambient degree with the same residue factor. -/
theorem intermediateWeilEquiv_symm_degree
    (x : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    localDegreeInt F x = extensionResidueDegree F EP (intermediateEmbedding F E) *
      localDegreeInt EP ((intermediateWeilEquiv F E).symm x) := by
  rw [← intermediateWeilEquiv_degree, ContinuousMulEquiv.apply_symm_apply]

/-- The normalized norm is unchanged, using the actual residue cardinalities. -/
theorem intermediateWeilEquiv_normCharacter (w : localWeilGroup EP) :
    localNormCharacter F (intermediateWeilEquiv F E w : localWeilGroup F) =
      localNormCharacter EP w :=
  localNormCharacter_extensionWeilMap F EP (intermediateEmbedding F E) w

/-- The inverse comparison preserves the normalized norm. -/
theorem intermediateWeilEquiv_symm_normCharacter
    (x : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    localNormCharacter EP ((intermediateWeilEquiv F E).symm x) = localNormCharacter F x := by
  rw [← intermediateWeilEquiv_normCharacter, ContinuousMulEquiv.apply_symm_apply]

/-- The actual inclusion detects local inertia. -/
theorem intermediateWeilMap_mem_localInertia (w : localWeilGroup EP) :
    intermediateWeilMap F E w ∈ localInertia F ↔ w ∈ localInertia EP :=
  extensionWeilMap_mem_localInertia F EP (intermediateEmbedding F E) w

/-- The inverse image of ambient inertia is exactly the standalone inertia. -/
theorem localInertia_eq_comap_intermediateWeilMap :
    localInertia EP = (localInertia F).comap (intermediateWeilMap F E).toMonoidHom := by
  ext w
  exact (intermediateWeilMap_mem_localInertia F E w).symm

/-- Inertia inside the prescribed fixing subgroup, with its inherited topology. -/
abbrev intermediateInertia :
    Subgroup (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :=
  (localInertia F).comap
    (pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)).subtype

@[simp] theorem intermediateWeilEquiv_mem_inertia (w : localWeilGroup EP) :
    intermediateWeilEquiv F E w ∈ intermediateInertia F E ↔ w ∈ localInertia EP :=
  intermediateWeilMap_mem_localInertia F E w

@[simp] theorem intermediateWeilEquiv_symm_mem_inertia
    (x : pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) :
    (intermediateWeilEquiv F E).symm x ∈ localInertia EP ↔ x ∈ intermediateInertia F E := by
  rw [← intermediateWeilEquiv_mem_inertia, ContinuousMulEquiv.apply_symm_apply]

/-- The ambient inertia intersection is the image of the actual standalone inertia. -/
theorem localInertia_inf_intermediateFixing :
    localInertia F ⊓ pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F) =
      (localInertia EP).map (intermediateWeilMap F E).toMonoidHom := by
  rw [← intermediateWeilMap_range]
  ext x
  constructor
  · rintro ⟨hI, w, rfl⟩
    exact ⟨w, (intermediateWeilMap_mem_localInertia F E w).mp hI, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(intermediateWeilMap_mem_localInertia F E w).mpr hw, w, rfl⟩

/-- The induced topological group identification on inertia. -/
def intermediateInertiaEquiv : localInertia EP ≃ₜ* intermediateInertia F E := by
  let e := intermediateWeilEquiv F E
  exact
    { toFun := fun w => ⟨e w, (intermediateWeilEquiv_mem_inertia F E w).mpr w.property⟩
      invFun := fun x => ⟨e.symm x,
        (intermediateWeilEquiv_symm_mem_inertia F E x).mpr x.property⟩
      left_inv := fun w => Subtype.ext (e.symm_apply_apply w)
      right_inv := fun x => Subtype.ext (e.apply_symm_apply x)
      map_mul' := fun w v => Subtype.ext (e.map_mul w v)
      continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

@[simp] theorem intermediateInertiaEquiv_apply (w : localInertia EP) :
    (intermediateInertiaEquiv F E w :
      pullbackFixingSubgroup F.Carrier E.field (localResidueDegree F)) =
        intermediateWeilEquiv F E w := rfl

@[simp] theorem intermediateInertiaEquiv_symm_apply (x : intermediateInertia F E) :
    ((intermediateInertiaEquiv F E).symm x : localWeilGroup EP) =
      (intermediateWeilEquiv F E).symm x := rfl

end Langlands.Weil.Local
