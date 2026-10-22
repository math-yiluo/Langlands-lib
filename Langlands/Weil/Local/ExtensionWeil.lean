import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Local.ExtensionResidue
import Langlands.Weil.Local.ExtensionGalois
import Langlands.LocalField.Normalization.Proof

/-!
# Local Weil groups along an embedding of p-adic fields
-/

noncomputable section

namespace Langlands.Weil.Local

open IsLocalRing
open scoped ValuativeRel

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
variable (f : F.Carrier →ₐ[Padic p] E.Carrier)

private theorem absoluteGaloisGroup_ext {K : Type*} [Field K]
    {σ τ : Field.absoluteGaloisGroup K}
    (h : ∀ x, AlgEquiv.toAlgHom σ x = AlgEquiv.toAlgHom τ x) : σ = τ :=
  AlgEquiv.ext h

/-- The integer ring of `E` is integral over that of `F` along the embedding. -/
theorem extensionIntegers_isIntegral :
    letI := (extensionIntegerMap F E f).toAlgebra
    Algebra.IsIntegral F.canonicalTopologicalData.Integers
      E.canonicalTopologicalData.Integers := by
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let A := (ValuativeRel.valuation (Padic p)).integer
  let := (extensionIntegerMap F E f).toAlgebra
  let := TF.integerAlgebra
  let := TE.integerAlgebra
  have : IsScalarTower A TF.Integers TE.Integers := IsScalarTower.of_algebraMap_eq fun a => by
    apply Subtype.ext
    exact (f.commutes (a : Padic p)).symm
  have := TE.integers_finite
  constructor
  intro y
  exact (Algebra.IsIntegral.isIntegral (R := A) y).tower_top

/-- The closure isomorphism over `f` matches the actual closure integer rings. -/
theorem extensionClosureEquiv_mem_closureIntegers (x : AlgebraicClosure F.Carrier) :
    extensionClosureEquiv F E f x ∈ E.closureIntegers E.canonicalTopologicalData ↔
      x ∈ F.closureIntegers F.canonicalTopologicalData := by
  let TF := F.canonicalTopologicalData
  let TE := E.canonicalTopologicalData
  let := TF.topology
  let := TF.valuativeRel
  let := TF.localField
  let := TE.topology
  let := TE.valuativeRel
  let := TE.localField
  let e := extensionClosureEquiv F E f
  have hF := LocalGalois.closureIntegers_integral F.Carrier x
  have hE := LocalGalois.closureIntegers_integral E.Carrier (e x)
  change e x ∈ LocalGalois.closureIntegers E.Carrier ↔ x ∈ LocalGalois.closureIntegers F.Carrier
  rw [← hF, ← hE]
  have hcomp : (algebraMap 𝒪[E.Carrier] (AlgebraicClosure E.Carrier)).comp
      (extensionIntegerMap F E f) =
      e.toRingHom.comp (algebraMap 𝒪[F.Carrier] (AlgebraicClosure F.Carrier)) := by
    ext a
    exact (extensionClosureLift_algebraMap F E f a).symm
  constructor
  · intro h
    let := (extensionIntegerMap F E f).toAlgebra
    have := extensionIntegers_isIntegral F E f
    let : Algebra 𝒪[F.Carrier] (AlgebraicClosure E.Carrier) :=
      ((algebraMap 𝒪[E.Carrier] (AlgebraicClosure E.Carrier)).comp
        (extensionIntegerMap F E f)).toAlgebra
    have : IsScalarTower 𝒪[F.Carrier] 𝒪[E.Carrier] (AlgebraicClosure E.Carrier) :=
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h' : IsIntegral 𝒪[F.Carrier] (e x) := isIntegral_trans (R := 𝒪[F.Carrier]) _ h
    have h'' := IsIntegral.map_of_comp_eq (RingHom.id 𝒪[F.Carrier]) e.symm.toRingHom ?_ h'
    · simpa using h''
    · ext a
      apply e.injective
      change e (algebraMap F.Carrier _ (a : F.Carrier)) =
        e (e.symm (algebraMap E.Carrier _ (f (a : F.Carrier))))
      rw [RingEquiv.apply_symm_apply]
      exact extensionClosureLift_algebraMap F E f a
  · intro h
    exact IsIntegral.map_of_comp_eq (extensionIntegerMap F E f) e.toRingHom hcomp h

/-- The closure isomorphism restricted to the actual closure integer rings. -/
def extensionClosureIntegerEquiv :
    F.closureIntegers F.canonicalTopologicalData ≃+*
      E.closureIntegers E.canonicalTopologicalData where
  toFun x := ⟨extensionClosureEquiv F E f x,
    (extensionClosureEquiv_mem_closureIntegers F E f x).mpr x.property⟩
  invFun y := ⟨(extensionClosureEquiv F E f).symm y, by
    rw [← extensionClosureEquiv_mem_closureIntegers F E f, RingEquiv.apply_symm_apply]
    exact y.property⟩
  left_inv x := Subtype.ext ((extensionClosureEquiv F E f).symm_apply_apply x)
  right_inv y := Subtype.ext ((extensionClosureEquiv F E f).apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul (extensionClosureEquiv F E f)
    (x : AlgebraicClosure F.Carrier) (y : AlgebraicClosure F.Carrier))
  map_add' x y := Subtype.ext (map_add (extensionClosureEquiv F E f)
    (x : AlgebraicClosure F.Carrier) (y : AlgebraicClosure F.Carrier))

@[simp] theorem extensionClosureIntegerEquiv_coe
    (x : F.closureIntegers F.canonicalTopologicalData) :
    (extensionClosureIntegerEquiv F E f x : AlgebraicClosure E.Carrier) =
      extensionClosureEquiv F E f x := rfl

/-- The induced isomorphism of the residue fields of the closure integer rings. -/
def extensionClosureResidueEquiv :
    ResidueField (F.closureIntegers F.canonicalTopologicalData) ≃+*
      ResidueField (E.closureIntegers E.canonicalTopologicalData) :=
  ResidueField.mapEquiv (extensionClosureIntegerEquiv F E f)

theorem extensionClosureResidueEquiv_residue
    (x : F.closureIntegers F.canonicalTopologicalData) :
    extensionClosureResidueEquiv F E f (residue _ x) =
      residue _ (extensionClosureIntegerEquiv F E f x) := rfl

/-- The comparison of the algebraic closures of the actual residue fields. -/
def extensionResidueClosureEquiv :
    AlgebraicClosure (localResidueField F) ≃+* AlgebraicClosure (localResidueField E) :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
  letI := E.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.valuativeRel
  letI := E.canonicalTopologicalData.localField
  ((LocalGalois.localResidueClosureEquiv F.Carrier).symm.trans
    (extensionClosureResidueEquiv F E f)).trans
      (LocalGalois.localResidueClosureEquiv E.Carrier)

/-- The comparison lies over the actual relative residue map. -/
theorem extensionResidueClosureEquiv_algebraMap (a : localResidueField F) :
    extensionResidueClosureEquiv F E f
        (algebraMap (localResidueField F) (AlgebraicClosure (localResidueField F)) a) =
      algebraMap (localResidueField E) (AlgebraicClosure (localResidueField E))
        (extensionResidueMap F E f a) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  obtain ⟨b, rfl⟩ := residue_surjective a
  have hF := LocalGalois.localResidueClosureEquiv_residue_base F.Carrier b
  have hE := LocalGalois.localResidueClosureEquiv_residue_base E.Carrier
    (extensionIntegerMap F E f b)
  have hb : extensionClosureIntegerEquiv F E f (LocalGalois.localIntegerMap F.Carrier b) =
      LocalGalois.localIntegerMap E.Carrier (extensionIntegerMap F E f b) :=
    Subtype.ext (extensionClosureLift_algebraMap F E f b)
  change LocalGalois.localResidueClosureEquiv E.Carrier
      (extensionClosureResidueEquiv F E f
        ((LocalGalois.localResidueClosureEquiv F.Carrier).symm
          (algebraMap _ _ (residue _ b)))) = _
  rw [← hF, RingEquiv.symm_apply_apply, extensionClosureResidueEquiv_residue, hb, hE]
  rfl

/-- The residue-field Galois map `G_{k_E} → G_{k_F}` along the residue-closure comparison. -/
def extensionResidueGaloisMap :
    Field.absoluteGaloisGroup (localResidueField E) →ₜ*
      Field.absoluteGaloisGroup (localResidueField F) :=
  letI : Algebra (localResidueField F) (localResidueField E) := extensionResidueAlgebra F E f
  letI : Algebra (AlgebraicClosure (localResidueField F))
      (AlgebraicClosure (localResidueField E)) :=
    (extensionResidueClosureEquiv F E f).toRingHom.toAlgebra
  letI : IsScalarTower (localResidueField F) (AlgebraicClosure (localResidueField F))
      (AlgebraicClosure (localResidueField E)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (extensionResidueClosureEquiv_algebraMap F E f a).symm
  Field.absoluteGaloisGroup.mapOfAlgebra (localResidueField F) (localResidueField E)

/-- The defining compatibility of the residue Galois map. -/
theorem extensionResidueClosureEquiv_galoisMap
    (τ : Field.absoluteGaloisGroup (localResidueField E))
    (y : AlgebraicClosure (localResidueField F)) :
    extensionResidueClosureEquiv F E f
        (AlgEquiv.toAlgHom (extensionResidueGaloisMap F E f τ) y) =
      AlgEquiv.toAlgHom τ (extensionResidueClosureEquiv F E f y) := by
  let : Algebra (localResidueField F) (localResidueField E) := extensionResidueAlgebra F E f
  let : Algebra (AlgebraicClosure (localResidueField F))
      (AlgebraicClosure (localResidueField E)) :=
    (extensionResidueClosureEquiv F E f).toRingHom.toAlgebra
  have : IsScalarTower (localResidueField F) (AlgebraicClosure (localResidueField F))
      (AlgebraicClosure (localResidueField E)) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (extensionResidueClosureEquiv_algebraMap F E f a).symm
  exact (AlgEquiv.restrictScalars (localResidueField F) τ).restrictNormal_commutes
    (AlgebraicClosure (localResidueField F)) y

theorem extensionResidueGaloisMap_injective :
    Function.Injective (extensionResidueGaloisMap F E f) := by
  intro τ₁ τ₂ h
  apply AlgEquiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (extensionResidueClosureEquiv F E f).surjective y
  have h₁ := extensionResidueClosureEquiv_galoisMap F E f τ₁ x
  have h₂ := extensionResidueClosureEquiv_galoisMap F E f τ₂ x
  rw [h] at h₁
  exact h₁.symm.trans h₂

/-- The actual residue actions commute with the Galois maps of `f`. -/
theorem localResidueMap_extensionGaloisMap (σ : Field.absoluteGaloisGroup E.Carrier) :
    localResidueMap F (extensionGaloisMap F E f σ) =
      extensionResidueGaloisMap F E f (localResidueMap E σ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := E.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.valuativeRel
  let := E.canonicalTopologicalData.localField
  apply absoluteGaloisGroup_ext
  intro y
  apply (extensionResidueClosureEquiv F E f).injective
  refine Eq.trans ?_
    (extensionResidueClosureEquiv_galoisMap F E f (localResidueMap E σ) y).symm
  obtain ⟨r, rfl⟩ := (LocalGalois.localResidueClosureEquiv F.Carrier).surjective y
  obtain ⟨x, rfl⟩ := residue_surjective r
  have hψ : ∀ z : F.closureIntegers F.canonicalTopologicalData,
      extensionResidueClosureEquiv F E f
          (LocalGalois.localResidueClosureEquiv F.Carrier (residue _ z)) =
        LocalGalois.localResidueClosureEquiv E.Carrier
          (residue _ (extensionClosureIntegerEquiv F E f z)) := by
    intro z
    change LocalGalois.localResidueClosureEquiv E.Carrier
        (extensionClosureResidueEquiv F E f
          ((LocalGalois.localResidueClosureEquiv F.Carrier).symm
            (LocalGalois.localResidueClosureEquiv F.Carrier (residue _ z)))) = _
    rw [RingEquiv.symm_apply_apply]
    rfl
  have h₁ : AlgEquiv.toAlgHom (localResidueMap F (extensionGaloisMap F E f σ))
      (LocalGalois.localResidueClosureEquiv F.Carrier (residue _ x)) = _ :=
    LocalGalois.absoluteResidueHom_residue F.Carrier (extensionGaloisMap F E f σ) x
  have h₂ : AlgEquiv.toAlgHom (localResidueMap E σ)
      (LocalGalois.localResidueClosureEquiv E.Carrier
        (residue _ (extensionClosureIntegerEquiv F E f x))) = _ :=
    LocalGalois.absoluteResidueHom_residue E.Carrier σ (extensionClosureIntegerEquiv F E f x)
  rw [h₁, hψ, hψ, h₂]
  congr 2
  exact Subtype.ext (extensionClosureLift_galoisMap F E f σ x)

private theorem toAlgHom_mul_apply {K : Type*} [Field K] (σ τ : Field.absoluteGaloisGroup K)
    (y : AlgebraicClosure K) :
    AlgEquiv.toAlgHom (σ * τ) y = AlgEquiv.toAlgHom σ (AlgEquiv.toAlgHom τ y) := rfl

private theorem arithmeticFrobenius_apply (k : Type*) [Field k] [Finite k]
    (y : AlgebraicClosure k) :
    AlgEquiv.toAlgHom (Galois.FiniteField.arithmeticFrobenius k) y = y ^ Nat.card k :=
  Galois.FiniteField.arithmetic_apply k (AlgebraicClosure k) y

private theorem arithmeticFrobenius_pow_apply (k : Type*) [Field k] [Finite k] (n : ℕ)
    (y : AlgebraicClosure k) :
    AlgEquiv.toAlgHom (Galois.FiniteField.arithmeticFrobenius k ^ n) y =
      y ^ Nat.card k ^ n := by
  induction n with
  | zero => simp only [pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ', toAlgHom_mul_apply, ih, arithmeticFrobenius_apply, ← pow_mul, ← pow_succ]

/-- Arithmetic Frobenius of `k_E` maps to the residue-degree power of that of `k_F`. -/
theorem extensionResidueGaloisMap_arithmetic :
    extensionResidueGaloisMap F E f
        (Galois.FiniteField.arithmeticFrobenius (localResidueField E)) =
      Galois.FiniteField.arithmeticFrobenius (localResidueField F) ^
        extensionResidueDegree F E f := by
  apply absoluteGaloisGroup_ext
  intro y
  apply (extensionResidueClosureEquiv F E f).injective
  rw [extensionResidueClosureEquiv_galoisMap, arithmeticFrobenius_apply,
    arithmeticFrobenius_pow_apply, map_pow]
  congr 1
  exact extensionResidueCardinality F E f

/-- Geometric Frobenius of `k_E` maps to the residue-degree power of that of `k_F`. -/
theorem extensionResidueGaloisMap_geometric :
    extensionResidueGaloisMap F E f
        (Galois.FiniteField.geometricFrobenius (localResidueField E)) =
      Galois.FiniteField.geometricFrobenius (localResidueField F) ^
        extensionResidueDegree F E f := by
  change extensionResidueGaloisMap F E f
      (Galois.FiniteField.arithmeticFrobenius (localResidueField E))⁻¹ =
    (Galois.FiniteField.arithmeticFrobenius (localResidueField F))⁻¹ ^ _
  rw [map_inv, extensionResidueGaloisMap_arithmetic, inv_pow]

private theorem profiniteEquivalence_geometric_zpow (k : Type*) [Field k] [Finite k] (m : ℤ) :
    Galois.FiniteField.profiniteEquivalence k
        (Galois.FiniteField.geometricFrobenius k ^ m) =
      frobenius (Multiplicative.ofAdd m) := by
  have h := Galois.FiniteField.profiniteEquivalence_symm_frobenius k (Multiplicative.ofAdd m)
  rw [toAdd_ofAdd] at h
  rw [← h, ContinuousMulEquiv.apply_symm_apply]

/-- On profinite integers the residue Galois map is multiplication by the residue degree. -/
theorem toProfiniteIntegers_extensionResidueGaloisMap
    (τ : Field.absoluteGaloisGroup (localResidueField E)) :
    Galois.FiniteField.toProfiniteIntegers (localResidueField F)
        (extensionResidueGaloisMap F E f τ) =
      Galois.FiniteField.toProfiniteIntegers (localResidueField E) τ ^
        extensionResidueDegree F E f := by
  let eE := Galois.FiniteField.profiniteEquivalence (localResidueField E)
  let eF := Galois.FiniteField.profiniteEquivalence (localResidueField F)
  have key : (fun x : ProfiniteIntegers => eF (extensionResidueGaloisMap F E f (eE.symm x))) =
      fun x => x ^ extensionResidueDegree F E f := by
    refine Continuous.ext_on
      (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of Degree)) ?_ ?_ ?_
    · exact eF.continuous.comp ((extensionResidueGaloisMap F E f).continuous.comp
        eE.symm.continuous)
    · exact continuous_pow _
    · rintro _ ⟨n, rfl⟩
      change eF (extensionResidueGaloisMap F E f (eE.symm (frobenius n))) = frobenius n ^ _
      rw [Galois.FiniteField.profiniteEquivalence_symm_frobenius, map_zpow,
        extensionResidueGaloisMap_geometric, ← zpow_natCast, ← zpow_mul,
        profiniteEquivalence_geometric_zpow, ← map_pow]
      congr 1
  have h := congrFun key (eE τ)
  simp only [ContinuousMulEquiv.symm_apply_apply] at h
  exact h

/-- Degree scaling: the profinite residue degree of `F` restricts to `r` times that of `E`,
where `r = extensionResidueDegree F E f`. -/
theorem localResidueDegree_extensionGaloisMap (σ : Field.absoluteGaloisGroup E.Carrier) :
    localResidueDegree F (extensionGaloisMap F E f σ) =
      localResidueDegree E σ ^ extensionResidueDegree F E f := by
  change Galois.FiniteField.toProfiniteIntegers (localResidueField F)
      (localResidueMap F (extensionGaloisMap F E f σ)) =
    Galois.FiniteField.toProfiniteIntegers (localResidueField E) (localResidueMap E σ) ^ _
  rw [localResidueMap_extensionGaloisMap, toProfiniteIntegers_extensionResidueGaloisMap]

/-- The local Weil map `W_E → W_F`, `(σ, m) ↦ (ι σ, r m)`,
with `r = extensionResidueDegree F E f`. -/
def extensionWeilMap : localWeilGroup E →ₜ* localWeilGroup F where
  toMonoidHom :=
    (((extensionGaloisMap F E f).toMonoidHom.prodMap
        (powMonoidHom (extensionResidueDegree F E f) : Degree →* Degree)).comp
      (pullbackSubgroup (localResidueDegree E)).subtype).codRestrict
      (pullbackSubgroup (localResidueDegree F)) (fun w => by
        have hw : localResidueDegree E w.val.1 = frobenius w.val.2 := w.property
        change localResidueDegree F (extensionGaloisMap F E f w.val.1) =
          frobenius (w.val.2 ^ extensionResidueDegree F E f)
        rw [localResidueDegree_extensionGaloisMap, map_pow, hw])
  continuous_toFun :=
    ((((extensionGaloisMap F E f).continuous.comp continuous_fst).prodMk
      ((continuous_pow (extensionResidueDegree F E f)).comp continuous_snd)).comp
        continuous_subtype_val).subtype_mk _

@[simp] theorem localProjection_extensionWeilMap (w : localWeilGroup E) :
    localProjection F (extensionWeilMap F E f w) =
      extensionGaloisMap F E f (localProjection E w) := rfl

@[simp] theorem localDegree_extensionWeilMap (w : localWeilGroup E) :
    localDegree F (extensionWeilMap F E f w) =
      localDegree E w ^ extensionResidueDegree F E f := rfl

theorem localDegreeInt_extensionWeilMap (w : localWeilGroup E) :
    localDegreeInt F (extensionWeilMap F E f w) =
      extensionResidueDegree F E f * localDegreeInt E w := by
  simp only [localDegreeInt, localDegree_extensionWeilMap, toAdd_pow, nsmul_eq_mul]

theorem extensionWeilMap_injective : Function.Injective (extensionWeilMap F E f) := by
  intro v w h
  apply projection_injective (localResidueDegree E)
  apply extensionGaloisMap_injective F E f
  change extensionGaloisMap F E f (localProjection E v) =
    extensionGaloisMap F E f (localProjection E w)
  rw [← localProjection_extensionWeilMap, ← localProjection_extensionWeilMap, h]

/-- The Weil map detects inertia: `j⁻¹(I_F) = I_E`. -/
theorem extensionWeilMap_mem_localInertia (w : localWeilGroup E) :
    extensionWeilMap F E f w ∈ localInertia F ↔ w ∈ localInertia E := by
  change localDegree F (extensionWeilMap F E f w) = 1 ↔ localDegree E w = 1
  rw [localDegree_extensionWeilMap]
  exact pow_eq_one_iff.trans (or_iff_left (extensionResidueDegree_pos F E f).ne')

/-- The norm character of `F` restricts to that of `E`. -/
theorem localNormCharacter_extensionWeilMap (w : localWeilGroup E) :
    localNormCharacter F (extensionWeilMap F E f w) = localNormCharacter E w := by
  apply Units.ext
  have hF : (localNormCharacter F (extensionWeilMap F E f w) : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^
        (-localDegreeInt F (extensionWeilMap F E f w)) :=
    residueNormCharacter_apply F.canonicalTopologicalData (localDegree F) _
  have hE : (localNormCharacter E w : ℂ) =
      (E.canonicalTopologicalData.residueCardinality : ℂ) ^ (-localDegreeInt E w) :=
    residueNormCharacter_apply E.canonicalTopologicalData (localDegree E) w
  rw [hF, hE, localDegreeInt_extensionWeilMap,
    extensionResidueCardinality F E f, Nat.cast_pow, ← zpow_natCast, ← zpow_mul]
  congr 1
  ring

/-- Unramified characters restrict to unramified characters, with the value raised to the
residue degree. -/
theorem localUnramifiedCharacter_extensionWeilMap (z : ℂˣ) (w : localWeilGroup E) :
    localUnramifiedCharacter F z (extensionWeilMap F E f w) =
      localUnramifiedCharacter E (z ^ extensionResidueDegree F E f) w := by
  change z ^ (localDegree F (extensionWeilMap F E f w)).toAdd =
    (z ^ extensionResidueDegree F E f) ^ (localDegree E w).toAdd
  rw [localDegree_extensionWeilMap, toAdd_pow, nsmul_eq_mul, ← zpow_natCast, ← zpow_mul]

/-- The residue field of `E` embedded in the closure of that of `F` over the residue map. -/
def extensionResidueFieldAlgHom :
    letI : Algebra (localResidueField F) (localResidueField E) := extensionResidueAlgebra F E f
    localResidueField E →ₐ[localResidueField F] AlgebraicClosure (localResidueField F) :=
  letI : Algebra (localResidueField F) (localResidueField E) := extensionResidueAlgebra F E f
  { toRingHom := (extensionResidueClosureEquiv F E f).symm.toRingHom.comp
      (algebraMap (localResidueField E) (AlgebraicClosure (localResidueField E)))
    commutes' := fun a => by
      apply (extensionResidueClosureEquiv F E f).injective
      change extensionResidueClosureEquiv F E f ((extensionResidueClosureEquiv F E f).symm
        (algebraMap _ _ (extensionResidueMap F E f a))) = _
      rw [RingEquiv.apply_symm_apply, extensionResidueClosureEquiv_algebraMap] }

/-- Every element in the image of the residue Galois map fixes the image of `k_E`. -/
theorem extensionResidueGaloisMap_fixes (τ : Field.absoluteGaloisGroup (localResidueField E))
    (y : localResidueField E) :
    AlgEquiv.toAlgHom (extensionResidueGaloisMap F E f τ)
        (extensionResidueFieldAlgHom F E f y) =
      extensionResidueFieldAlgHom F E f y := by
  apply (extensionResidueClosureEquiv F E f).injective
  rw [extensionResidueClosureEquiv_galoisMap]
  change AlgEquiv.toAlgHom τ (extensionResidueClosureEquiv F E f
      ((extensionResidueClosureEquiv F E f).symm (algebraMap _ _ y))) =
    extensionResidueClosureEquiv F E f
      ((extensionResidueClosureEquiv F E f).symm (algebraMap _ _ y))
  rw [RingEquiv.apply_symm_apply]
  exact AlgEquiv.commutes τ y

/-- Over an abstract finite field, a geometric Frobenius power fixing the image of a finite
extension has exponent divisible by the degree. -/
private theorem finrank_dvd_of_geometric_zpow_fixes {k : Type*} [Field k] [Finite k]
    {K : Type*} [Field K] [Algebra k K] [Finite K]
    (ε : K →ₐ[k] AlgebraicClosure k) (m : ℤ)
    (h : ∀ y : K, AlgEquiv.toAlgHom (Galois.FiniteField.geometricFrobenius k ^ m) (ε y) = ε y) :
    (Module.finrank k K : ℤ) ∣ m := by
  let L := ε.fieldRange
  have : FiniteDimensional k L := (AlgHom.equivFieldRange ε).toLinearEquiv.finiteDimensional
  have : Finite L := Module.finite_of_finite k
  have hres : Galois.FiniteField.finiteRestriction k L
      (Galois.FiniteField.geometricFrobenius k ^ m) = 1 := by
    generalize Galois.FiniteField.geometricFrobenius k ^ m = σ at h ⊢
    apply AlgEquiv.ext
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨ε y, y, rfl⟩).trans (h y)
  have hpow : Galois.FiniteField.geometric k L ^ m = 1 := by
    rw [← Galois.FiniteField.geometric_restrict, ← map_zpow]
    exact hres
  rw [← orderOf_dvd_iff_zpow_eq_one, Galois.FiniteField.geometric_order] at hpow
  rwa [← (AlgHom.equivFieldRange ε).toLinearEquiv.finrank_eq] at hpow

/-- A geometric Frobenius power in the image of `G_{k_E}` has exponent divisible by
`extensionResidueDegree F E f`. -/
theorem extensionResidueDegree_dvd_of_mem_range (m : ℤ)
    (h : Galois.FiniteField.geometricFrobenius (localResidueField F) ^ m ∈
      (extensionResidueGaloisMap F E f).toMonoidHom.range) :
    (extensionResidueDegree F E f : ℤ) ∣ m := by
  obtain ⟨τ, hτ⟩ := h
  let : Algebra (localResidueField F) (localResidueField E) := extensionResidueAlgebra F E f
  refine finrank_dvd_of_geometric_zpow_fixes (extensionResidueFieldAlgHom F E f) m ?_
  intro y
  rw [← hτ]
  exact extensionResidueGaloisMap_fixes F E f τ y

/-- The image of `W_E` is the full inverse image of the image of `G_E`. -/
theorem extensionWeilMap_range :
    (extensionWeilMap F E f).toMonoidHom.range =
      (extensionGaloisMap F E f).toMonoidHom.range.comap (localProjection F).toMonoidHom := by
  ext w'
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨localProjection E w, rfl⟩
  · rintro ⟨σ, hσ⟩
    have hσ' : extensionGaloisMap F E f σ = localProjection F w' := hσ
    have hw' : localResidueDegree F (localProjection F w') = frobenius (localDegree F w') :=
      w'.property
    rw [← hσ'] at hw'
    have hres : localResidueMap F (extensionGaloisMap F E f σ) =
        Galois.FiniteField.geometricFrobenius (localResidueField F) ^
          (localDegree F w').toAdd := by
      rw [← Galois.FiniteField.profiniteEquivalence_symm_frobenius]
      apply (Galois.FiniteField.profiniteEquivalence (localResidueField F)).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact hw'
    rw [localResidueMap_extensionGaloisMap] at hres
    obtain ⟨m, hm⟩ := extensionResidueDegree_dvd_of_mem_range F E f _ ⟨_, hres⟩
    have hrE : localResidueMap E σ =
        Galois.FiniteField.geometricFrobenius (localResidueField E) ^ m := by
      apply extensionResidueGaloisMap_injective F E f
      rw [hres, hm, map_zpow, extensionResidueGaloisMap_geometric, ← zpow_natCast, ← zpow_mul]
    refine ⟨⟨(σ, Multiplicative.ofAdd m), ?_⟩, ?_⟩
    · change Galois.FiniteField.profiniteEquivalence (localResidueField E)
          (localResidueMap E σ) = frobenius (Multiplicative.ofAdd m)
      rw [hrE, profiniteEquivalence_geometric_zpow]
    · apply Subtype.ext
      apply Prod.ext
      · exact hσ'
      · change Multiplicative.ofAdd m ^ extensionResidueDegree F E f = localDegree F w'
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← hm]

/-- Pulling back an open subgroup along a homomorphism with dense image preserves the index. -/
private theorem index_comap_of_denseRange {G' G : Type*} [Group G'] [Group G]
    [TopologicalSpace G] [ContinuousMul G] {φ : G' →* G} (hφ : DenseRange φ)
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    (H.comap φ).index = H.index := by
  have key : ∀ x y : G',
      QuotientGroup.leftRel (H.comap φ) x y ↔ QuotientGroup.leftRel H (φ x) (φ y) := by
    simp only [QuotientGroup.leftRel_apply]
    exact fun x y => iff_of_eq (congr_arg (· ∈ H) (by rw [φ.map_mul, φ.map_inv]))
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' φ fun x y => (key x y).mp) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun x => ?_
    have hopen : IsOpen ((fun g => x⁻¹ * g) ⁻¹' (H : Set G)) :=
      hH.preimage (continuous_const_mul _)
    obtain ⟨y, hy⟩ := hφ.exists_mem_open hopen ⟨x, by simp [H.one_mem]⟩
    refine ⟨Quotient.mk'' y, ?_⟩
    change Quotient.mk'' (φ y) = Quotient.mk'' x
    rw [Quotient.eq'', QuotientGroup.leftRel_apply]
    simpa using H.inv_mem hy

/-- The image of `W_E` is open in `W_F`. -/
theorem extensionWeilMap_range_isOpen :
    IsOpen ((extensionWeilMap F E f).toMonoidHom.range : Set (localWeilGroup F)) := by
  rw [extensionWeilMap_range, Subgroup.coe_comap]
  exact (extensionGaloisMap_range_isOpen F E f).preimage (localProjection F).continuous

/-- The image of `W_E` has index `[E : F]` in `W_F`. -/
theorem extensionWeilMap_range_index :
    (extensionWeilMap F E f).toMonoidHom.range.index = extensionDegree F E f := by
  rw [extensionWeilMap_range, index_comap_of_denseRange (localProjection_denseRange F) _
    (extensionGaloisMap_range_isOpen F E f), extensionGaloisMap_range_index]

theorem extensionWeilMap_range_finiteIndex :
    (extensionWeilMap F E f).toMonoidHom.range.FiniteIndex :=
  ⟨by rw [extensionWeilMap_range_index]; exact (extensionDegree_pos F E f).ne'⟩

/-- The local Weil map is a topological embedding. -/
theorem extensionWeilMap_isEmbedding : Topology.IsEmbedding (extensionWeilMap F E f) := by
  have hinj : Function.Injective (fun n : Degree => n ^ extensionResidueDegree F E f) := by
    intro a b h
    apply Multiplicative.toAdd.injective
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_pow, nsmul_eq_mul] at h'
    exact mul_left_cancel₀ (by exact_mod_cast (extensionResidueDegree_pos F E f).ne') h'
  have hpow : Topology.IsEmbedding (fun n : Degree => n ^ extensionResidueDegree F E f) := by
    refine ⟨Topology.isInducing_iff_nhds.mpr fun n => ?_, hinj⟩
    rw [nhds_discrete, Filter.comap_pure, ← Filter.principal_singleton]
    congr 1
    ext m
    simp [hinj.eq_iff]
  have hcomp : Topology.IsEmbedding
      (Subtype.val ∘ extensionWeilMap F E f :
        localWeilGroup E → Field.absoluteGaloisGroup F.Carrier × Degree) :=
    ((extensionGaloisMap_isClosedEmbedding F E f).isEmbedding.prodMap hpow).comp
      Topology.IsEmbedding.subtypeVal
  exact Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hcomp

/-- The local Weil map is an open embedding. -/
theorem extensionWeilMap_isOpenEmbedding :
    Topology.IsOpenEmbedding (extensionWeilMap F E f) :=
  ⟨extensionWeilMap_isEmbedding F E f, by
    have h := extensionWeilMap_range_isOpen F E f
    rw [MonoidHom.coe_range] at h
    exact h⟩

/-- The inertia subgroup of `E` is the pullback of that of `F`. -/
theorem localInertia_eq_comap_extensionWeilMap :
    localInertia E = (localInertia F).comap (extensionWeilMap F E f).toMonoidHom := by
  ext w
  exact (extensionWeilMap_mem_localInertia F E f w).symm

end Langlands.Weil.Local
