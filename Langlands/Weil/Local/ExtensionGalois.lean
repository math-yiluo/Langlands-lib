import Langlands.LocalField.Definitions
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Absolute Galois groups along an embedding of p-adic fields

For an embedding `f : F →ₐ[Padic p] E`, the Galois map is exactly Mathlib's
`Field.absoluteGaloisGroup.map`. Its chosen closure embedding is shown to be an
isomorphism, the Galois map to be an injective closed embedding, and its image
to be the open fixing subgroup of the image of `E`, of index `[E : F]`.
-/

noncomputable section

namespace Langlands.Weil.Local

universe u v w

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
variable (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- The scalar structure on `E` over `F` given by the embedding. -/
abbrev extensionAlgebra : Algebra F.Carrier E.Carrier := f.toRingHom.toAlgebra

theorem extensionAlgebra_isScalarTower :
    letI := extensionAlgebra F E f
    IsScalarTower (Padic p) F.Carrier E.Carrier :=
  letI := extensionAlgebra F E f
  IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm

theorem extensionAlgebra_finiteDimensional :
    letI := extensionAlgebra F E f
    FiniteDimensional F.Carrier E.Carrier := by
  let := extensionAlgebra F E f
  have := extensionAlgebra_isScalarTower F E f
  exact Module.Finite.right (Padic p) F.Carrier E.Carrier

/-- The degree `[E : F]` of the embedding. -/
def extensionDegree : ℕ :=
  letI := extensionAlgebra F E f
  Module.finrank F.Carrier E.Carrier

theorem extensionDegree_pos : 0 < extensionDegree F E f := by
  let := extensionAlgebra F E f
  have := extensionAlgebra_finiteDimensional F E f
  exact Module.finrank_pos

/-- The tower law over the p-adic base. -/
theorem finrank_mul_extensionDegree :
    Module.finrank (Padic p) F.Carrier * extensionDegree F E f =
      Module.finrank (Padic p) E.Carrier := by
  let := extensionAlgebra F E f
  have := extensionAlgebra_isScalarTower F E f
  exact Module.finrank_mul_finrank (Padic p) F.Carrier E.Carrier

@[simp] theorem extensionDegree_id :
    extensionDegree F F (AlgHom.id (Padic p) F.Carrier) = 1 :=
  Module.finrank_self F.Carrier

/-- Degrees multiply in towers of embeddings. -/
theorem extensionDegree_comp (D : PadicField.{w} p)
    (g : E.Carrier →ₐ[Padic p] D.Carrier) :
    extensionDegree F D (g.comp f) = extensionDegree F E f * extensionDegree E D g := by
  let := extensionAlgebra F E f
  let := extensionAlgebra E D g
  let := extensionAlgebra F D (g.comp f)
  have : IsScalarTower F.Carrier E.Carrier D.Carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (Module.finrank_mul_finrank F.Carrier E.Carrier D.Carrier).symm

/-- Mathlib's chosen embedding of algebraic closures over `f`, the one used by
`Field.absoluteGaloisGroup.map`. -/
def extensionClosureLift : AlgebraicClosure F.Carrier →+* AlgebraicClosure E.Carrier :=
  letI := extensionAlgebra F E f
  (IsAlgClosed.lift : AlgebraicClosure F.Carrier →ₐ[F.Carrier]
    AlgebraicClosure E.Carrier).toRingHom

theorem extensionClosureLift_algebraMap (x : F.Carrier) :
    extensionClosureLift F E f (algebraMap F.Carrier (AlgebraicClosure F.Carrier) x) =
      algebraMap E.Carrier (AlgebraicClosure E.Carrier) (f x) := by
  let := extensionAlgebra F E f
  exact (IsAlgClosed.lift : AlgebraicClosure F.Carrier →ₐ[F.Carrier]
    AlgebraicClosure E.Carrier).commutes x

/-- Both closures are algebraic closures of `F`, so the chosen embedding is bijective. -/
theorem extensionClosureLift_bijective : Function.Bijective (extensionClosureLift F E f) := by
  let := extensionAlgebra F E f
  have := extensionAlgebra_finiteDimensional F E f
  have : Algebra.IsAlgebraic F.Carrier (AlgebraicClosure E.Carrier) :=
    Algebra.IsAlgebraic.trans F.Carrier E.Carrier (AlgebraicClosure E.Carrier)
  exact (Algebra.IsAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : AlgebraicClosure E.Carrier →ₐ[F.Carrier] AlgebraicClosure F.Carrier)
    (IsAlgClosed.lift : AlgebraicClosure F.Carrier →ₐ[F.Carrier]
      AlgebraicClosure E.Carrier)).2

/-- The chosen closure embedding as a ring isomorphism. -/
def extensionClosureEquiv : AlgebraicClosure F.Carrier ≃+* AlgebraicClosure E.Carrier :=
  RingEquiv.ofBijective (extensionClosureLift F E f) (extensionClosureLift_bijective F E f)

@[simp] theorem extensionClosureEquiv_apply (x : AlgebraicClosure F.Carrier) :
    extensionClosureEquiv F E f x = extensionClosureLift F E f x := rfl

/-- The continuous homomorphism `G_E → G_F`; it is exactly Mathlib's map for `f`. -/
def extensionGaloisMap :
    Field.absoluteGaloisGroup E.Carrier →ₜ* Field.absoluteGaloisGroup F.Carrier :=
  Field.absoluteGaloisGroup.map f.toRingHom

/-- The defining compatibility of the Galois map with the closure embedding. -/
theorem extensionClosureLift_galoisMap (σ : Field.absoluteGaloisGroup E.Carrier)
    (x : AlgebraicClosure F.Carrier) :
    extensionClosureLift F E f (AlgEquiv.toAlgHom (extensionGaloisMap F E f σ) x) =
      AlgEquiv.toAlgHom σ (extensionClosureLift F E f x) := by
  let := extensionAlgebra F E f
  let : Algebra (AlgebraicClosure F.Carrier) (AlgebraicClosure E.Carrier) :=
    (IsAlgClosed.lift : AlgebraicClosure F.Carrier →ₐ[F.Carrier]
      AlgebraicClosure E.Carrier).toRingHom.toAlgebra
  exact (AlgEquiv.restrictScalars F.Carrier σ).restrictNormal_commutes
    (AlgebraicClosure F.Carrier) x

theorem extensionGaloisMap_injective : Function.Injective (extensionGaloisMap F E f) := by
  intro σ τ h
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (extensionClosureLift_bijective F E f).2 y
  have hσ := extensionClosureLift_galoisMap F E f σ x
  have hτ := extensionClosureLift_galoisMap F E f τ x
  rw [h] at hσ
  exact hσ.symm.trans hτ

/-- The embedding of `E` into the closure of `F` through the closure isomorphism. -/
def extensionFieldEmbedding : E.Carrier →+* AlgebraicClosure F.Carrier :=
  (extensionClosureEquiv F E f).symm.toRingHom.comp
    (algebraMap E.Carrier (AlgebraicClosure E.Carrier))

theorem extensionClosureLift_fieldEmbedding (x : E.Carrier) :
    extensionClosureLift F E f (extensionFieldEmbedding F E f x) =
      algebraMap E.Carrier (AlgebraicClosure E.Carrier) x :=
  (extensionClosureEquiv F E f).apply_symm_apply _

theorem extensionFieldEmbedding_comp (x : F.Carrier) :
    extensionFieldEmbedding F E f (f x) =
      algebraMap F.Carrier (AlgebraicClosure F.Carrier) x := by
  apply (extensionClosureEquiv F E f).injective
  rw [extensionClosureEquiv_apply, extensionClosureEquiv_apply,
    extensionClosureLift_fieldEmbedding, extensionClosureLift_algebraMap]

/-- The embedding of `E` as an `F`-algebra homomorphism. -/
def extensionFieldAlgHom :
    letI := extensionAlgebra F E f
    E.Carrier →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
  letI := extensionAlgebra F E f
  { toRingHom := extensionFieldEmbedding F E f
    commutes' := extensionFieldEmbedding_comp F E f }

/-- The finite intermediate field of the closure of `F` determined by `E`. -/
def extensionIntermediateField : IntermediateField F.Carrier (AlgebraicClosure F.Carrier) :=
  letI := extensionAlgebra F E f
  (extensionFieldAlgHom F E f).fieldRange

theorem mem_extensionIntermediateField (y : AlgebraicClosure F.Carrier) :
    y ∈ extensionIntermediateField F E f ↔
      ∃ x : E.Carrier, extensionFieldEmbedding F E f x = y := by
  let := extensionAlgebra F E f
  exact AlgHom.mem_fieldRange

/-- The intermediate field is `F`-isomorphic to `E`. -/
def extensionIntermediateFieldEquiv :
    letI := extensionAlgebra F E f
    E.Carrier ≃ₐ[F.Carrier] extensionIntermediateField F E f :=
  letI := extensionAlgebra F E f
  AlgHom.equivFieldRange (extensionFieldAlgHom F E f)

instance extensionIntermediateField_finiteDimensional :
    FiniteDimensional F.Carrier (extensionIntermediateField F E f) := by
  let := extensionAlgebra F E f
  have := extensionAlgebra_finiteDimensional F E f
  exact (extensionIntermediateFieldEquiv F E f).toLinearEquiv.finiteDimensional

theorem extensionIntermediateField_finrank :
    Module.finrank F.Carrier (extensionIntermediateField F E f) = extensionDegree F E f := by
  let := extensionAlgebra F E f
  exact (extensionIntermediateFieldEquiv F E f).toLinearEquiv.finrank_eq.symm

/-- The image of `G_E` is the fixing subgroup of the image of `E`. -/
theorem extensionGaloisMap_range :
    (extensionGaloisMap F E f).toMonoidHom.range =
      (extensionIntermediateField F E f).fixingSubgroup := by
  ext τ
  rw [MonoidHom.mem_range]
  refine Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff
    (K := extensionIntermediateField F E f) τ).symm
  constructor
  · rintro ⟨σ, rfl⟩ y hy
    obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F E f y).mp hy
    apply (extensionClosureEquiv F E f).injective
    rw [extensionClosureEquiv_apply, extensionClosureEquiv_apply]
    refine (extensionClosureLift_galoisMap F E f σ _).trans ?_
    rw [extensionClosureLift_fieldEmbedding]
    exact AlgEquiv.commutes σ x
  · intro h
    let e := extensionClosureEquiv F E f
    let ρ : AlgebraicClosure E.Carrier ≃+* AlgebraicClosure E.Carrier :=
      (e.symm.trans (AlgEquiv.toRingEquiv τ)).trans e
    have hρ : ∀ x : E.Carrier, ρ (algebraMap E.Carrier _ x) = algebraMap E.Carrier _ x := by
      intro x
      have hfix : AlgEquiv.toAlgHom τ (extensionFieldEmbedding F E f x) =
          extensionFieldEmbedding F E f x :=
        h _ ((mem_extensionIntermediateField F E f _).mpr ⟨x, rfl⟩)
      calc ρ (algebraMap E.Carrier _ x)
          = e (AlgEquiv.toAlgHom τ (extensionFieldEmbedding F E f x)) := rfl
        _ = e (extensionFieldEmbedding F E f x) := by rw [hfix]
        _ = algebraMap E.Carrier _ x := extensionClosureLift_fieldEmbedding F E f x
    refine ⟨AlgEquiv.ofRingEquiv (f := ρ) hρ, ?_⟩
    apply AlgEquiv.ext
    intro y
    apply (extensionClosureLift_bijective F E f).1
    refine (extensionClosureLift_galoisMap F E f _ y).trans ?_
    change e (AlgEquiv.toAlgHom τ (e.symm (e y))) = e (AlgEquiv.toAlgHom τ y)
    rw [RingEquiv.symm_apply_apply]

/-- The image of `G_E` is open. -/
theorem extensionGaloisMap_range_isOpen :
    IsOpen ((extensionGaloisMap F E f).toMonoidHom.range :
      Set (Field.absoluteGaloisGroup F.Carrier)) := by
  rw [extensionGaloisMap_range]
  exact (extensionIntermediateField F E f).fixingSubgroup_isOpen

/-- The image of `G_E` has index `[E : F]`. -/
theorem extensionGaloisMap_range_index :
    (extensionGaloisMap F E f).toMonoidHom.range.index = extensionDegree F E f := by
  have : CharZero F.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) F.Carrier).injective
  rw [extensionGaloisMap_range, ← extensionIntermediateField_finrank]
  exact ((extensionIntermediateField F E f).finrank_eq_fixingSubgroup_index).symm

/-- The image of `G_E` as an open subgroup of `G_F`. -/
def extensionGaloisSubgroup : OpenSubgroup (Field.absoluteGaloisGroup F.Carrier) where
  toSubgroup := (extensionGaloisMap F E f).toMonoidHom.range
  isOpen' := extensionGaloisMap_range_isOpen F E f

/-- `G_E` is compact and `G_F` is Hausdorff, so the injective map is a closed embedding. -/
theorem extensionGaloisMap_isClosedEmbedding :
    Topology.IsClosedEmbedding (extensionGaloisMap F E f) := by
  have : CharZero E.Carrier :=
    charZero_of_injective_algebraMap (algebraMap (Padic p) E.Carrier).injective
  have : CompactSpace (Field.absoluteGaloisGroup E.Carrier) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure E.Carrier/E.Carrier))
  have : T2Space (Field.absoluteGaloisGroup F.Carrier) :=
    inferInstanceAs (T2Space Gal(AlgebraicClosure F.Carrier/F.Carrier))
  exact (extensionGaloisMap F E f).continuous.isClosedEmbedding
    (extensionGaloisMap_injective F E f)

/-- `G_E` is isomorphic, as a topological group, to its image in `G_F`. -/
def extensionGaloisEquivRange :
    Field.absoluteGaloisGroup E.Carrier ≃ₜ* (extensionGaloisMap F E f).toMonoidHom.range where
  toMulEquiv := MonoidHom.ofInjective (f := (extensionGaloisMap F E f).toMonoidHom)
    (extensionGaloisMap_injective F E f)
  continuous_toFun := (extensionGaloisMap F E f).continuous.subtype_mk _
  continuous_invFun := by
    rw [(extensionGaloisMap_isClosedEmbedding F E f).isEmbedding.continuous_iff]
    refine continuous_subtype_val.congr fun x => ?_
    exact (MonoidHom.apply_ofInjective_symm (f := (extensionGaloisMap F E f).toMonoidHom)
      (extensionGaloisMap_injective F E f) x).symm

@[simp] theorem extensionGaloisEquivRange_apply (σ : Field.absoluteGaloisGroup E.Carrier) :
    (extensionGaloisEquivRange F E f σ : Field.absoluteGaloisGroup F.Carrier) =
      extensionGaloisMap F E f σ := rfl

end Langlands.Weil.Local
