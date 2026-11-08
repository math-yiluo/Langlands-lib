import Langlands.Global.Arithmetic.HenniartGlobalizationStatement
import Langlands.Global.Factors.RelativeIsometryOperationStatement
import Langlands.Global.Factors.RelativeIsometryFactorStatement
import Langlands.Weil.Local.ExtensionWeilEquiv
import Langlands.VirtualRepresentation.Weil.GroupTransport
import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport

/-!
# Henniart's composite map at a p-adic field

Henniart (2000), §§3.7–3.8, page 451, in the relative form of the Library's
witnessed pairs. For a finite place `v` of `F`, a p-adic field `K` and a
`ℚ_p`-algebra isomorphism `f : K ≅ F_v`, the isometry `T` between the relative
Weil and automorphic images at `v` is transported to `K`. The composite
`henniartCompositeMap` pulls back along `f` on both sides. The properties of
Henniart's 3.8 (a)–(c) are stated for any such map of lattices over `K`, with
reciprocity candidates, characters, additive characters, measures and
local-constant systems of `K` itself. Proposition definitions only.
-/

noncomputable section

universe u uF uK uW uP uV uE

namespace Langlands.Correspondence.LatticeMap

open Langlands.VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)
  {W : Submodule ℤ (LocalWeil.UnitaryLattice.{uK, uW} K)}
  {A : Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{uK, uV} K)}

/-- `Φ` preserves the multiplicity pairings and the degrees. -/
def Isometry (Φ : W ≃ₗ[ℤ] A) : Prop :=
  (∀ x y : W, PadicSupercuspidal.unitaryPairing K (Φ x) (Φ y) =
    LocalWeil.unitaryPairing K x y) ∧
  ∀ x : W, PadicSupercuspidal.unitaryDegree K (Φ x) = LocalWeil.unitaryDegree K x

/-- `x` is the class of an irreducible unitary Weil representation exactly when
`Φ x` is the class of a unitary supercuspidal representation. -/
def GeneratorCompatibility (Φ : W ≃ₗ[ℤ] A) : Prop :=
  ∀ x : W, (∃ b : LocalWeil.UnitaryBasis.{uK, uW} K, (x : LocalWeil.UnitaryLattice K) =
      generator b) ↔
    ∃ b : PadicSupercuspidal.UnitaryBasis.{uK, uV} K,
      (Φ x : PadicSupercuspidal.UnitaryLattice K) = generator b

/-- `W` is closed under the actual contragredient, and `Φ` carries it to the
actual smooth contragredient. -/
def DualCompatibility (Φ : W ≃ₗ[ℤ] A) : Prop :=
  ∀ x : W, ∃ h : LocalWeil.unitaryDualLatticeEquiv K x.1 ∈ W,
    (Φ ⟨_, h⟩ : PadicSupercuspidal.UnitaryLattice K) =
      PadicSupercuspidal.unitaryContragredientLatticeEquiv K (Φ x).1

/-- `W` is closed under twisting by the modulus-one field character `χ` pulled
back along `e`, and `Φ` carries this twist to the twist by `χ ∘ det`. -/
def TwistCompatibility (Φ : W ≃ₗ[ℤ] A) (e : ReciprocityCandidate K)
    (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1) : Prop :=
  ∀ x : W, ∃ h : LocalWeil.unitaryFieldCharacterTwistLatticeEquiv K e χ hχ x.1 ∈ W,
    (Φ ⟨_, h⟩ : PadicSupercuspidal.UnitaryLattice K) =
      PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K χ hχ (Φ x).1

/-- The rank-one Weil class of `χ` pulled back along `e` lies in `W`, and `Φ`
sends it to the actual `GL₁` class of `χ`. -/
def CharacterCompatibility (Φ : W ≃ₗ[ℤ] A) (e : ReciprocityCandidate K)
    (χ : QuasiCharacter K) : Prop :=
  ∃ x : W,
    LocalWeil.includeUnitary K x.1 =
        generator (⟨1, rankOneWeilCharacterClass.{uK, uW} K e χ⟩ :
          LocalWeil.Basis.{uK, uW} K) ∧
      PadicSupercuspidal.includeUnitary K (Φ x).1 =
        generator (⟨1, rankOneSupercuspidalClass.{uK, uV} K χ⟩ :
          PadicSupercuspidal.Basis.{uK, uV} K)

/-- `det x = ω_(Φ x) ∘ rec`: the image of each class has a central character
whose pullback along the reciprocity candidate is its determinant. -/
def DeterminantCompatibility (Φ : W ≃ₗ[ℤ] A) (e : ReciprocityCandidate K) : Prop :=
  ∀ x : W, ∃ ω : K.Carrierˣ →* ℂˣ,
    PadicSupercuspidal.IsUnitaryCentralCharacter K (Φ x).1 ω ∧
      ∀ w : Weil.Local.localWeilGroup K,
        ω (reciprocityHom K e w) = Additive.toMul (LocalWeil.unitaryDeterminant K x.1) w

/-- `L(s, Φ x × Φ y) = L(s, x ⊗ y)` and `ε(s, Φ x × Φ y, ψ) = ε(s, x ⊗ y, ψ)`.
A self-dual measure exists; for every such measure the L-factors agree, and for
every local-constant system some `c q^(-ms)` is both epsilon factors. -/
def PairFactorCompatibility (Φ : W ≃ₗ[ℤ] A) (ψ : NontrivialAdditiveCharacter K) :
    Prop :=
  (∃ ν : LocalAdditiveHaarMeasure K, IsSelfDualMeasure K ψ ν) ∧
  ∀ ν : LocalAdditiveHaarMeasure K, IsSelfDualMeasure K ψ ν →
    ∀ x y : W,
      PadicSupercuspidal.IsUnitaryPairLFactor K ψ ν (Φ x).1 (Φ y).1
          (LocalWeil.unitaryPairLFactor K x.1 y.1) ∧
        ∀ (eC : LocalFactor.CommonClosure.ReciprocityFamily K)
          (ε : LocalFactor.NonabelianSystem.Assignment.{uK, uE} K)
          (hε : LocalFactor.NonabelianSystem.IsSystem K eC ε),
          ∃ c : ℂˣ × ℤ,
            LocalWeil.IsUnitaryPairEpsilonFactor K eC ε hε ψ x.1 y.1 c ∧
              PadicSupercuspidal.IsUnitaryPairEpsilonFactor K ψ ν (Φ x).1 (Φ y).1 c

/-- Henniart's 3.8 (a), degree, contragredient and twist clauses, and (c), together
with the preservation of pairings. Twist and character clauses use every geometric
reciprocity candidate and every modulus-one field character of `K`. -/
def OperationProperties (Φ : W ≃ₗ[ℤ] A) : Prop :=
  Isometry K Φ ∧ GeneratorCompatibility K Φ ∧ DualCompatibility K Φ ∧
    ∀ e : ReciprocityCandidate K, IsGeometricReciprocity K e →
      ∀ (χ : QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1),
        TwistCompatibility K Φ e χ hχ ∧ CharacterCompatibility K Φ e χ

/-- Henniart's 3.8 (a), determinant clause, and (b). The determinant clause uses
every geometric reciprocity candidate of `K`; the factor clauses use every
additive character of `K`. -/
def FactorProperties (Φ : W ≃ₗ[ℤ] A) : Prop :=
  (∀ e : ReciprocityCandidate K, IsGeometricReciprocity K e →
    DeterminantCompatibility K Φ e) ∧
    ∀ ψ : NontrivialAdditiveCharacter K, PairFactorCompatibility.{uK, uW, uV, uE} K Φ ψ

/-- All properties of Henniart's 3.8 (a)–(c) for a map of unitary lattices over `K`. -/
def HenniartProperties (Φ : W ≃ₗ[ℤ] A) : Prop :=
  OperationProperties K Φ ∧ FactorProperties.{uK, uW, uV, uE} K Φ

end Langlands.Correspondence.LatticeMap

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation

section Transport

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p)

/-- Prime transport of the canonical completion package leaves the unitary
supercuspidal lattice unchanged. -/
def padicFieldAtSupercuspidalLatticeEquiv :
    PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v) ≃ₗ[ℤ]
      PadicSupercuspidal.UnitaryLattice.{u, uV} (padicFieldAt v h) := by
  subst h
  exact LinearEquiv.refl ℤ _

variable (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- The local Weil map of `f : K ≅ F_v` as an isomorphism of topological groups. -/
def completionWeilEquiv : localWeilGroup K ≃ₜ* localWeilGroup (padicField v) :=
  letI := (padicFieldAt v h).algebra
  (extensionWeilEquiv (padicFieldAt v h) K f.symm).trans (padicFieldAtWeilEquiv v h)

theorem coe_completionWeilEquiv :
    (completionWeilEquiv v h K f : localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      completionWeilTransport v h K f :=
  rfl

/-- Pullback of unitary Weil classes from `F_v` to `K` along `completionWeilEquiv`. -/
def completionWeilLatticeEquiv :
    LocalWeil.UnitaryLattice.{u, uW} (padicField v) ≃ₗ[ℤ]
      LocalWeil.UnitaryLattice.{uK, uW} K :=
  Weil.restrictUnitaryLatticeEquiv (completionWeilEquiv v h K f)

/-- The comparison of `HenniartGlobalizationStatement`, in the exact Grothendieck
group of `W_K`, is equality after `completionWeilLatticeEquiv`. -/
theorem continuousRestrict_completionWeilTransport_eq_iff
    (y : LocalWeil.UnitaryLattice.{u, uW} (padicField v))
    (x : LocalWeil.UnitaryLattice.{uK, uW} K) :
    ExactGrothendieckGroup.continuousRestrict (completionWeilTransport v h K f)
        (LocalWeil.realizeExact (padicField v) (LocalWeil.includeUnitary (padicField v) y)) =
        LocalWeil.realizeExact K (LocalWeil.includeUnitary K x) ↔
      completionWeilLatticeEquiv v h K f y = x := by
  rw [← coe_completionWeilEquiv]
  exact Weil.continuousRestrict_realizeExact_includeUnitary_eq_iff _ y x

/-- Pullback of unitary supercuspidal classes from `F_v` to `K` along `f`. -/
def completionSupercuspidalLatticeEquiv :
    PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v) ≃ₗ[ℤ]
      PadicSupercuspidal.UnitaryLattice.{uK, uV} K :=
  letI := (padicFieldAt v h).algebra
  (padicFieldAtSupercuspidalLatticeEquiv v h).trans
    (PadicSupercuspidal.unitaryLatticeEquiv K (padicFieldAt v h) f)

end Transport

end Langlands.Global

namespace Langlands.Global.PoleComparison

open Langlands.VirtualRepresentation Langlands.VirtualRepresentation.RelativeGlobal
open Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality

variable (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
  (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- Henniart's composite `R(K) → R_A(K)` of §3.7: pull back from `K` to `F_v`
on the Weil side, apply `T`, and pull back from `F_v` to `K` on the
supercuspidal side. It is defined on the whole transported Weil image. -/
def henniartCompositeMap
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v) :
    (weilImage.{uF, uW, uP} F E c v).map
        (completionWeilLatticeEquiv v h K f : LocalWeil.UnitaryLattice (padicField v) →ₗ[ℤ]
          LocalWeil.UnitaryLattice K) ≃ₗ[ℤ]
      (automorphicImage.{uF, uW, uP} F E c v).map
        (completionSupercuspidalLatticeEquiv v h K f :
          PadicSupercuspidal.UnitaryLattice (padicField v) →ₗ[ℤ]
            PadicSupercuspidal.UnitaryLattice K) :=
  ((completionWeilLatticeEquiv v h K f).submoduleMap _).symm ≪≫ₗ T ≪≫ₗ
    (completionSupercuspidalLatticeEquiv v h K f).submoduleMap _

/-- On a transported class, the composite is the transport of `T`. -/
theorem henniartCompositeMap_apply
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v)
    (x : weilImage.{uF, uW, uP} F E c v) :
    (henniartCompositeMap F E c v h K f T
        ⟨completionWeilLatticeEquiv v h K f x, Submodule.mem_map_of_mem x.2⟩ :
          PadicSupercuspidal.UnitaryLattice K) =
      completionSupercuspidalLatticeEquiv v h K f (T x) := by
  have hx : ((completionWeilLatticeEquiv v h K f).submoduleMap
      (weilImage.{uF, uW, uP} F E c v)).symm
      ⟨completionWeilLatticeEquiv v h K f x, Submodule.mem_map_of_mem x.2⟩ = x := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  simp [henniartCompositeMap, hx]

/-- Transport of the operation clauses: if `T` is a generated positive isometry
with the contragredient, twist and character clauses at `F_v`, then the
composite at `K` has the operation properties of Henniart's 3.8 for the
conventions of `K`. -/
def HenniartCompositeOperationStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v),
    RelativeGeneratedPositiveIsometry F E c v T →
    RelativeIsometryOperations F E c v T →
    ∀ (p : ℕ) [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
      (f : letI := (padicFieldAt v h).algebra
        K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier),
      Correspondence.LatticeMap.OperationProperties K (henniartCompositeMap F E c v h K f T)

/-- Transport of the factor clauses: if `T` has the determinant and pair-factor
clauses at `F_v`, then the composite at `K` has the factor properties of
Henniart's 3.8 for the conventions of `K`. -/
def HenniartCompositeFactorStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}) (v : FinitePlace F)
    (T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v),
    RelativeIsometryFactors.{uF, uW, uP, uE} F E c v T →
    ∀ (p : ℕ) [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
      (f : letI := (padicFieldAt v h).algebra
        K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier),
      Correspondence.LatticeMap.FactorProperties.{uK, uW, uF, uE} K
        (henniartCompositeMap F E c v h K f T)

/-- Henniart (2000), 3.8: under the certified pole comparisons, for every
generated positive isometry `T` and every `ℚ_p`-algebra isomorphism `K ≅ F_v`,
the composite map at `K` has all properties of 3.8 (a)–(c). -/
def HenniartCompositeMapStatement : Prop :=
  ∀ (F E : Type uF) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [CompactSpace (AdeleQuotient F)]
    (c : FundamentalClass.ClassFamily.{uF}),
    RelativeWeilGroup.IsArithmeticClassFamily c →
  ∀ (v : FinitePlace F) (ψ : Correspondence.NontrivialAdditiveCharacter (padicField v)),
    RelativeCertifiedPoleComparisons.{uF, uW, uP} F E c v ψ →
    ∀ T : weilImage.{uF, uW, uP} F E c v ≃ₗ[ℤ] automorphicImage.{uF, uW, uP} F E c v,
      RelativeGeneratedPositiveIsometry F E c v T →
      ∀ (p : ℕ) [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
        (f : letI := (padicFieldAt v h).algebra
          K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier),
        Correspondence.LatticeMap.HenniartProperties.{uK, uW, uF, uE} K
          (henniartCompositeMap F E c v h K f T)

end Langlands.Global.PoleComparison
