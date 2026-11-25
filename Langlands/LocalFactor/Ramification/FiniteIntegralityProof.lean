import Langlands.LocalFactor.Ramification.FiniteStatement
import Langlands.Representation.Finite.DegreeZeroBrauerProof
import Langlands.LocalFactor.Ramification.ConductorFunctional
import Langlands.LocalFactor.Ramification.InducedRankOneDifference

/-!
# Integrality of the Artin and Swan conductors of a finite Galois representation: proof

This module proves `Langlands.Ramification.Padic.FiniteGaloisConductorIntegralityStatement`:
for a finite Galois extension `F/K` of p-adic fields and a finite-dimensional complex
representation `ρ` of `G = Gal(F/K)`, the Artin and Swan expressions of `ρ` are natural numbers.

The Artin functional of the integer-ring action, composed with the character, is an additive
map on virtual representations of `G` whose value on a representation is its Artin expression
(`virtualArtin_ofClassOfRepresentation`). Its values on the induced rank-one differences are
integers (`exists_int_artinConductor_ind_sub`), and by Deligne's degree-zero form of Brauer's
theorem (`FiniteRep.DegreeZeroBrauer.finiteDegreeZeroBrauer`) these differences span the virtual
representations of degree zero, among them `[ρ] − dim ρ · [1]`. The functional vanishes on `[1]`,
so `a(ρ)` is an integer; it is non-negative. The Swan expression is `a(ρ)` minus the codimension
of the inertia invariants and is non-negative.
-/

noncomputable section

namespace Langlands.Ramification.Padic

open Module FiniteRep

universe uK uL uV

namespace FiniteIntegrality

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
  (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
  [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]

/-- The Artin functional of the integer-ring action, on virtual representations of the Galois
group. -/
def virtualArtin [Fintype (F.Carrier ≃ₐ[K] F.Carrier)] :
    VirtualRep ℂ (F.Carrier ≃ₐ[K] F.Carrier) →+ ℂ :=
  letI := integerAction T K
  (artinFunctional T.Integers (F.Carrier ≃ₐ[K] F.Carrier)).toAddMonoidHom.comp
    (virtualCharacter (k := ℂ) (G := F.Carrier ≃ₐ[K] F.Carrier)).toAddMonoidHom

theorem virtualArtin_ofClass [Fintype (F.Carrier ≃ₐ[K] F.Carrier)]
    (a : RepClass ℂ (F.Carrier ≃ₐ[K] F.Carrier)) :
    letI := integerAction T K
    virtualArtin T K (ofClass a) =
      artinFunctional T.Integers (F.Carrier ≃ₐ[K] F.Carrier) (character a) := by
  let := integerAction T K
  change artinFunctional T.Integers (F.Carrier ≃ₐ[K] F.Carrier)
    (virtualCharacter (k := ℂ) (G := F.Carrier ≃ₐ[K] F.Carrier) (ofClass a)) = _
  rw [virtualCharacter_ofClass]

/-- On the class of a representation, the functional is its Artin expression. -/
theorem virtualArtin_ofClassOfRepresentation [Fintype (F.Carrier ≃ₐ[K] F.Carrier)]
    {W : Type uV} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) W) :
    virtualArtin T K (ofClass (classOfRepresentation σ)) = ((artinConductor T K σ : ℚ) : ℂ) := by
  let := integerAction T K
  have := HerbrandBridge.integerAction_faithful T K
  have := LocalFactor.SpectralConductor.integerRing_noetherian' T
  rw [virtualArtin_ofClass, character_classOfRepresentation]
  exact artinFunctional_character T.Integers (F.Carrier ≃ₐ[K] F.Carrier) σ

/-- The functional vanishes on the trivial representation. -/
theorem virtualArtin_one [Fintype (F.Carrier ≃ₐ[K] F.Carrier)] :
    virtualArtin T K (ofClass (classOf (oneDimensional
      (1 : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ)))) = 0 := by
  let := integerAction T K
  rw [virtualArtin_ofClass, character_classOf]
  have h : (oneDimensional (1 : (F.Carrier ≃ₐ[K] F.Carrier) →* ℂˣ)).character =
      fun _ => (1 : ℂ) := by
    funext g
    rw [character_oneDimensional]
    rfl
  rw [h, artinFunctional_const]

/-- **The Artin expression is an integer** (Galois case). -/
theorem exists_int_artinConductor [IsGalois K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (F.Carrier ≃ₐ[K] F.Carrier) V) :
    ∃ z : ℤ, artinConductor T K ρ = (z : ℚ) := by
  classical
  have : FiniteDimensional K F.Carrier :=
    Module.Finite.of_restrictScalars_finite (Padic p) K F.Carrier
  let := Fintype.ofFinite (F.Carrier ≃ₐ[K] F.Carrier)
  let G := F.Carrier ≃ₐ[K] F.Carrier
  let integral : AddSubgroup (VirtualRep ℂ G) :=
    (Int.castAddHom ℂ).range.comap (virtualArtin T K)
  have hGen : degreeZeroBrauerGenerators G ⊆ (integral.toIntSubmodule : Set (VirtualRep ℂ G)) := by
    rintro _ ⟨S, χ, χ', rfl⟩
    obtain ⟨z, hz⟩ := exists_int_artinConductor_ind_sub T S χ χ'
    refine ⟨z, ?_⟩
    change (z : ℂ) = virtualArtin T K (virtualInduce S
      (ofClass (classOf (oneDimensional χ)) - ofClass (classOf (oneDimensional χ'))))
    rw [map_sub, virtualInduce, virtualMap_ofClass, virtualMap_ofClass, map_sub]
    change (z : ℂ) =
      virtualArtin T K (ofClass (classOfRepresentation
        (Representation.ind S.subtype (oneDimensional χ).ρ))) -
      virtualArtin T K (ofClass (classOfRepresentation
        (Representation.ind S.subtype (oneDimensional χ').ρ)))
    rw [virtualArtin_ofClassOfRepresentation, virtualArtin_ofClassOfRepresentation,
      ← Rat.cast_sub, hz, Rat.cast_intCast]
  have hdeg : ofClass (classOfRepresentation ρ) -
      (finrank ℂ V : ℤ) • ofClass (classOf (oneDimensional (1 : G →* ℂˣ))) ∈
        degreeZeroVirtualReps G := by
    refine LinearMap.mem_ker.mpr ?_
    simp only [virtualDegree, LinearMap.coe_comp, Function.comp_apply, map_sub, map_zsmul,
      virtualCharacter_ofClass, character_classOfRepresentation, character_classOf,
      LinearMap.proj_apply, Representation.char_one,
      character_oneDimensional, MonoidHom.one_apply, Units.val_one, zsmul_eq_mul, mul_one]
    push_cast
    ring
  have hle : Submodule.span ℤ (degreeZeroBrauerGenerators G) ≤ integral.toIntSubmodule :=
    Submodule.span_le.mpr hGen
  have hspan : degreeZeroBrauerSpan G = degreeZeroVirtualReps G :=
    DegreeZeroBrauer.finiteDegreeZeroBrauer G
  obtain ⟨z, hz⟩ := hle (hspan ▸ hdeg)
  change (z : ℂ) = virtualArtin T K _ at hz
  rw [map_sub, map_zsmul, virtualArtin_one, smul_zero, sub_zero,
    virtualArtin_ofClassOfRepresentation] at hz
  exact ⟨z, by exact_mod_cast hz.symm⟩

end FiniteIntegrality

open FiniteIntegrality

/-- **Integrality of the Artin and Swan conductors of a finite Galois representation.** For a
finite Galois extension `F/K` of p-adic fields and a finite-dimensional complex representation
`ρ` of `Gal(F/K)`, the Artin and Swan expressions of `ρ` are natural numbers (Serre, *Local
Fields*, VI §2, Theorem 1′; Deligne, §4.5). -/
theorem finiteGaloisConductorIntegrality {p : ℕ} [Fact p.Prime] {F : PadicField.{uL} p}
    (T : F.TopologicalData) (K : Type uK) [Field K] [Algebra (Padic p) K]
    [Algebra K F.Carrier] [IsScalarTower (Padic p) K F.Carrier]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] :
    FiniteGaloisConductorIntegralityStatement T K (V := V) := by
  intro _ ρ
  obtain ⟨z, hz⟩ := exists_int_artinConductor T K ρ
  have hz0 : 0 ≤ z := by
    have h := Langlands.Ramification.Padic.artinConductor_nonneg T K ρ
    rw [hz] at h
    exact_mod_cast h
  have ha : artinConductor T K ρ = (z.toNat : ℚ) := by
    rw [hz]
    exact_mod_cast (Int.toNat_of_nonneg hz0).symm
  refine ⟨⟨z.toNat, ha⟩, ?_⟩
  have htame := Langlands.Ramification.Padic.artinConductor_eq_tame_add_swan T K ρ
  have hs := Langlands.Ramification.Padic.swanConductor_nonneg T K ρ
  have hle : fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) ≤ z.toNat := by
    have h : (fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K) : ℚ) ≤ z.toNat := by
      rw [← ha, htame]
      linarith
    exact_mod_cast h
  refine ⟨z.toNat - fixedCodimension (F.Carrier ≃ₐ[K] F.Carrier) ρ (inertia T K), ?_⟩
  rw [Nat.cast_sub hle, ← ha, htame]
  ring

end Langlands.Ramification.Padic
