import Langlands.Representation.Plancherel.UnramifiedScalarDescent
import Langlands.Representation.Plancherel.ParabolicIntertwiningTopology
import Langlands.Representation.Plancherel.RationalTwistStabilizer

/-! # Rational scalar values on actual complex twist orbits -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u uG uI uV

section GenericOrbit

variable {H : Type uG} [Group H] [TopologicalSpace H] [NonarchimedeanGroup H]
  {I : Type uI} (ν : I → (H →* ℝ≥0ˣ))
  (π : SmoothRep.{0, uG, uV} ℂ H)

theorem unramifiedTwistOrbitMap_surjective :
    Function.Surjective (unramifiedTwistOrbitMap ν π) := by
  rintro ⟨c, χ, hχ⟩
  exact ⟨χ, Subtype.ext hχ⟩

theorem isOpenQuotientMap_unramifiedTwistOrbitMap :
    IsOpenQuotientMap (unramifiedTwistOrbitMap ν π) :=
  ⟨unramifiedTwistOrbitMap_surjective ν π, continuous_coinduced_rng,
    isOpenMap_unramifiedTwistOrbitMap ν π⟩

/-- The quotient by the full smooth-object stabilizer maps to the existing
actual orbit of isomorphism classes. -/
def unramifiedTwistOrbitQuotientMap :
    (unramifiedCharacters ν ⧸ smoothRepUnramifiedTwistStabilizer ν π) →
      UnramifiedTwistOrbit ν π :=
  Quotient.lift (unramifiedTwistOrbitMap ν π) (by
    intro χ ψ h
    apply Subtype.ext
    exact (unramifiedTwistClass_eq_iff ν π χ ψ).mpr
      (QuotientGroup.leftRel_apply.mp h))

@[simp]
theorem unramifiedTwistOrbitQuotientMap_mk (χ : unramifiedCharacters ν) :
    unramifiedTwistOrbitQuotientMap ν π (QuotientGroup.mk χ) =
      unramifiedTwistOrbitMap ν π χ := rfl

theorem unramifiedTwistOrbitQuotientMap_bijective :
    Function.Bijective (unramifiedTwistOrbitQuotientMap ν π) := by
  constructor
  · intro x y h
    obtain ⟨χ, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨ψ, rfl⟩ := QuotientGroup.mk_surjective y
    apply Quotient.sound
    exact QuotientGroup.leftRel_apply.mpr
      ((unramifiedTwistClass_eq_iff ν π χ ψ).mp (congrArg Subtype.val h))
  · intro x
    obtain ⟨χ, rfl⟩ := unramifiedTwistOrbitMap_surjective ν π x
    exact ⟨QuotientGroup.mk χ, rfl⟩

/-- The existing complex twist orbit is homeomorphic to the character
quotient by its actual full stabilizer. No finiteness is needed. -/
def unramifiedTwistOrbitQuotientHomeomorph :
    (unramifiedCharacters ν ⧸ smoothRepUnramifiedTwistStabilizer ν π) ≃ₜ
      UnramifiedTwistOrbit ν π where
  toEquiv := Equiv.ofBijective _ (unramifiedTwistOrbitQuotientMap_bijective ν π)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk
      (smoothRepUnramifiedTwistStabilizer ν π)).continuous_iff.mpr
        continuous_coinduced_rng
  continuous_invFun := by
    apply (isOpenQuotientMap_unramifiedTwistOrbitMap ν π).isQuotientMap.continuous_iff.mpr
    convert (QuotientGroup.continuous_mk :
      Continuous (QuotientGroup.mk :
        unramifiedCharacters ν →
          unramifiedCharacters ν ⧸ smoothRepUnramifiedTwistStabilizer ν π)) using 1
    funext χ
    exact (Equiv.ofBijective _
      (unramifiedTwistOrbitQuotientMap_bijective ν π)).symm_apply_apply (QuotientGroup.mk χ)

@[simp]
theorem unramifiedTwistOrbitQuotientHomeomorph_mk (χ : unramifiedCharacters ν) :
    unramifiedTwistOrbitQuotientHomeomorph ν π (QuotientGroup.mk χ) =
      unramifiedTwistOrbitMap ν π χ := rfl

@[simp]
theorem unramifiedTwistOrbitQuotientHomeomorph_symm_map (χ : unramifiedCharacters ν) :
    (unramifiedTwistOrbitQuotientHomeomorph ν π).symm
        (unramifiedTwistOrbitMap ν π χ) = QuotientGroup.mk χ :=
  (unramifiedTwistOrbitQuotientHomeomorph ν π).symm_apply_apply (QuotientGroup.mk χ)

/-- The stabilizer defined using all smooth isomorphism classes agrees
with the canonical smooth-dual stabilizer for an irreducible admissible object. -/
theorem smoothRepUnramifiedTwistStabilizer_eq
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := H)) :
    smoothRepUnramifiedTwistStabilizer ν A.obj =
      unramifiedTwistStabilizer ν (Quotient.mk _ A) := by
  ext χ
  change SmoothRep.isoClass (A.obj.twist χ.val.toMonoidHom
      (unramifiedCharacter_isOpen_ker ν χ)) = SmoothRep.isoClass A.obj ↔
    Quotient.mk _ (A.twist χ.val.toMonoidHom (unramifiedCharacter_isOpen_ker ν χ)) =
      Quotient.mk _ A
  rw [SmoothRep.isoClass_eq_iff, Quotient.eq]
  exact ⟨fun ⟨e⟩ => ⟨IrreducibleAdmissibleRep.isoMk e⟩,
    fun ⟨e⟩ => ⟨(irreducibleAdmissibleProperty (k := ℂ) (G := H)).ι.mapIso e⟩⟩

/-- Finiteness transfers from the proved central-quotient criterion to the
full stabilizer used by the actual smooth-object orbit. -/
theorem finite_smoothRepUnramifiedTwistStabilizer
    (C : Subgroup H) [C.Normal] (hC : C ≤ Subgroup.center H)
    [Finite (H ⧸ (commonNormKernel ν ⊔ C))]
    (A : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := H)) :
    Finite (smoothRepUnramifiedTwistStabilizer ν A.obj) := by
  rw [smoothRepUnramifiedTwistStabilizer_eq ν A]
  exact finite_unramifiedTwistStabilizer ν C hC (Quotient.mk _ A)

end GenericOrbit

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [TopologicalSpace (GroupScheme.rationalPoints L)]
  [NonarchimedeanGroup (GroupScheme.rationalPoints L)]
  (hp : Continuous (rationalValuationImageProjection L))
  (hL : GroupScheme.IsConnectedReductive L)
  (π : SmoothRep.{0, u, uV} ℂ (GroupScheme.rationalPoints L))

/-- Fraction-field fixedness under the actual full twist stabilizer gives
an invariant presentation whenever that stabilizer is finite. -/
theorem unramifiedTwistOrbitScalarPresentation_exists
    [Finite (smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) π)]
    (f : rationalUnramifiedFunctionField L hp hL)
    (hf : ∀ τ : smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) π,
      rationalUnramifiedFunctionFieldTranslation L hp hL τ.val f = f) :
    Nonempty (UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer
        (fun ψ => (rationalNormCharacters L ψ).toMul) π) f) := by
  classical
  let := Fintype.ofFinite (smoothRepUnramifiedTwistStabilizer
    (fun ψ => (rationalNormCharacters L ψ).toMul) π)
  exact unramifiedInvariantScalarPresentation_exists L hp hL _ f hf

namespace UnramifiedInvariantScalarPresentation

variable {L hp hL} {f : rationalUnramifiedFunctionField L hp hL}
  (p : UnramifiedInvariantScalarPresentation L hp hL
    (smoothRepUnramifiedTwistStabilizer (fun ψ => (rationalNormCharacters L ψ).toMul) π) f)

/-- The chosen invariant denominator's nonzero locus on the existing
actual complex orbit of the inducing smooth representation. -/
def orbitRegularRegion :
    Set (UnramifiedTwistOrbit (fun ψ => (rationalNormCharacters L ψ).toMul) π) :=
  (unramifiedTwistOrbitQuotientHomeomorph
    (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm ⁻¹' p.regularRegion

/-- Transport the regular scalar value to its actual representation class. -/
def orbitValue (x : p.orbitRegularRegion π) : ℂ :=
  p.value ⟨(unramifiedTwistOrbitQuotientHomeomorph
    (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm x.val, x.property⟩

@[simp]
theorem orbitRegularRegion_map
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul)) :
    unramifiedTwistOrbitMap (fun ψ => (rationalNormCharacters L ψ).toMul) π χ ∈ p.orbitRegularRegion π ↔
      p.denominator.val χ ≠ 0 := by
  simp [orbitRegularRegion]

@[simp]
theorem orbitValue_map
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters L ψ).toMul))
    (hχ : p.denominator.val χ ≠ 0) :
    p.orbitValue π ⟨unramifiedTwistOrbitMap (fun ψ => (rationalNormCharacters L ψ).toMul) π χ,
        (p.orbitRegularRegion_map π χ).mpr hχ⟩ =
      p.numerator.val χ / p.denominator.val χ := by
  simp [orbitValue, value]

theorem orbitRegularRegion_isOpen : IsOpen (p.orbitRegularRegion π) :=
  p.regularRegion_isOpen.preimage (unramifiedTwistOrbitQuotientHomeomorph
    (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm.continuous

theorem orbitRegularRegion_dense : Dense (p.orbitRegularRegion π) :=
  p.regularRegion_dense.preimage (unramifiedTwistOrbitQuotientHomeomorph
    (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm.isOpenMap

theorem orbitRegularRegion_nonempty : (p.orbitRegularRegion π).Nonempty := by
  obtain ⟨x, hx⟩ := p.regularRegion_nonempty
  exact ⟨unramifiedTwistOrbitQuotientHomeomorph
    (fun ψ => (rationalNormCharacters L ψ).toMul) π x, by
    simpa only [orbitRegularRegion, Set.mem_preimage, Homeomorph.symm_apply_apply] using hx⟩

theorem continuous_orbitValue : Continuous (p.orbitValue π) :=
  p.continuous_value.comp
    (((unramifiedTwistOrbitQuotientHomeomorph
      (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm.continuous.comp
      continuous_subtype_val).subtype_mk (fun x => x.property))

theorem orbitValue_eq
    (q : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer (fun ψ => (rationalNormCharacters L ψ).toMul) π) f)
    (x : UnramifiedTwistOrbit (fun ψ => (rationalNormCharacters L ψ).toMul) π)
    (hp' : x ∈ p.orbitRegularRegion π) (hq' : x ∈ q.orbitRegularRegion π) :
    p.orbitValue π ⟨x, hp'⟩ = q.orbitValue π ⟨x, hq'⟩ :=
  p.value_eq q ((unramifiedTwistOrbitQuotientHomeomorph
    (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm x) hp' hq'

theorem orbitRegularRegion_inter_dense
    (q : UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer (fun ψ => (rationalNormCharacters L ψ).toMul) π) f) :
    Dense (p.orbitRegularRegion π ∩ q.orbitRegularRegion π) :=
  (p.regularRegion_inter_dense q).preimage
    (unramifiedTwistOrbitQuotientHomeomorph
      (fun ψ => (rationalNormCharacters L ψ).toMul) π).symm.isOpenMap

end UnramifiedInvariantScalarPresentation

end ActualCharacters

section ActualFiniteStabilizer

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (L : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine L.X.left] [LocallyOfFiniteType L.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints L) :=
  rationalPointTopology F L.X

local instance : NonarchimedeanGroup (GroupScheme.rationalPoints L) :=
  rationalPoints_nonarchimedeanGroup L

variable {L} {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]

/-- The existing actual central-image finite-index theorem gives finiteness
of the full stabilizer of an irreducible admissible smooth object. -/
theorem finite_rationalSmoothRepUnramifiedTwistStabilizer
    (s : T.toGrp ⟶ L) (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (A : IrreducibleAdmissibleRep.{0, u, uV}
      (k := ℂ) (G := GroupScheme.rationalPoints L)) :
    Finite (smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) A.obj) := by
  rw [smoothRepUnramifiedTwistStabilizer_eq _ A]
  exact finite_rationalUnramifiedTwistStabilizer s hs hindex (Quotient.mk _ A)

/-- For canonical rational-point topology, the explicit central-image
finite-index premise supplies the finite stabilizer needed for scalar descent.
The fraction-field fixedness remains a separate premise. -/
theorem rationalUnramifiedTwistOrbitScalarPresentation_exists
    (hp : Continuous (rationalValuationImageProjection L))
    (hL : GroupScheme.IsConnectedReductive L)
    (s : T.toGrp ⟶ L) (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
    (A : IrreducibleAdmissibleRep.{0, u, uV}
      (k := ℂ) (G := GroupScheme.rationalPoints L))
    (f : rationalUnramifiedFunctionField L hp hL)
    (hf : ∀ τ : smoothRepUnramifiedTwistStabilizer
      (fun ψ => (rationalNormCharacters L ψ).toMul) A.obj,
      rationalUnramifiedFunctionFieldTranslation L hp hL τ.val f = f) :
    Nonempty (UnramifiedInvariantScalarPresentation L hp hL
      (smoothRepUnramifiedTwistStabilizer
        (fun ψ => (rationalNormCharacters L ψ).toMul) A.obj) f) := by
  let := finite_rationalSmoothRepUnramifiedTwistStabilizer s hs hindex A
  exact unramifiedTwistOrbitScalarPresentation_exists L hp hL A.obj f hf

end ActualFiniteStabilizer

end Langlands.Plancherel
