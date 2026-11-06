import Langlands.Correspondence.AutomorphicPoleComparison
import Langlands.Correspondence.ZeroMonodromyExtension
import Langlands.Correspondence.AssemblySquareIntegrableStatement
import Langlands.Correspondence.AssemblyZeroMonodromyWitness
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Correspondence.AssemblyConstruction
import Langlands.Group.GL.SingleBlock

/-!
# Reducing the L-factor characterization of the assembly to its ingredients

Henniart 2002, Theorem 1.8, proof in §4.5. The theorem
`assemblyLCharacterization_of_ingredients` derives the published statement
`AssemblyLCharacterizationStatement` from the five statements bundled in
`AssemblyLCharacterizationIngredients`. None of these ingredients is proved here.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance assemblyReductionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyReductionGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

variable (F) in
/-- The ingredients of the reduction: well-definedness, bijectivity and
L-inheritance of the assembly, Henniart's Theorem 1.7(b), and the indecomposability
of parameters assembled to essentially square-integrable classes. -/
def AssemblyLCharacterizationIngredients : Prop :=
  AssemblyWellDefinedStatement.{uF, uP, uA} F ∧
    AssemblyBijectiveStatement.{uF, uP, uA} F ∧
    AssemblyLInheritanceStatement.{uF, uP, uA} F ∧
    RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement.{uF, uA, uA} ∧
    AssemblySquareIntegrablePreimageStatement.{uF, uP, uA} F

/-- Every irreducible admissible representation of `GL_1(F)` is supercuspidal: the
only block shape of rank one has one block, and its parabolic is the whole group. -/
theorem isSupercuspidal_rank_one (A : AutomorphicObject.{uF, uA} F (Nat.succPNat 0)) :
    GeneralLinear.IsSupercuspidal A.obj.representation := by
  refine ⟨A.property.2, fun B hB _ => ?_⟩
  exfalso
  apply hB
  refine B.singleBlock_parabolic_eq_top ?_ F.Carrier
  have hle : B.length ≤ 1 := B.length_le
  have hne : B.length ≠ 0 := by
    intro h0
    have hsum := B.sum_eq
    have : IsEmpty (Fin B.length) := by
      rw [h0]
      infer_instance
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
    exact absurd hsum (by simp)
  omega

/-- If an injective extension `c` of a surjective supercuspidal map sends `D` to the
class of a supercuspidal representation, then `D` is an irreducible Weil parameter. -/
theorem isIrreducibleWeilParameter_of_isSupercuspidal
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c : FullMap.{uF, uP, uA} F}
    (hc0 : SupercuspidalRankwiseBijective F c0) (hext : ExtendsSupercuspidal F c0 c)
    (hinj : ∀ n, Function.Injective (c n)) {n : ℕ+}
    {D : WeilDeligneClass.{uF, uP} F n} (A : AutomorphicObject.{uF, uA} F n)
    (hA : automorphicClassOf F A = c n D)
    (hsc : GeneralLinear.IsSupercuspidal A.obj.representation) :
    IsIrreducibleWeilParameter F D := by
  let S : GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := (n : ℕ)) :=
    ⟨A.obj, A.property.1, hsc⟩
  obtain ⟨σ, hσ⟩ := (hc0 n).2 S.isoClass
  obtain ⟨E, hE, hcE⟩ := hext n σ
  have hED : c n E = c n D := by
    rw [hcE, hσ, ← hA]
    rfl
  exact ⟨σ, hinj n hED ▸ hE⟩

/-- Under well-definedness, an assembly of `c0` extends `c0` as soon as some full map
`τ` does: `τ` supplies the zero-monodromy classes, and the single-block witness
`assembly_apply_of_isZeroMonodromyOf` gives the values of the assembly on them. -/
theorem extendsSupercuspidal_of_isAssemblyOf
    (hwd : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {c τ : FullMap.{uF, uP, uA} F}
    (hc : IsAssemblyOf F c0 c) (hτ : ExtendsSupercuspidal F c0 τ) :
    ExtendsSupercuspidal F c0 c := by
  intro n σ
  obtain ⟨E, hE, -⟩ := hτ n σ
  exact ⟨E, hE, assembly_apply_of_isZeroMonodromyOf F hwd hc hE⟩

/-- Henniart's induction (§4.5): under the ingredients, every assembly of `c0` equals
a full map `τ` that extends `c0` and satisfies the lower-rank pair L-factor identities
at `ψ`. -/
theorem assembly_eq_of_lowerRankPairL
    (hwd : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (hbij : AssemblyBijectiveStatement.{uF, uP, uA} F)
    (hinh : AssemblyLInheritanceStatement.{uF, uP, uA} F)
    (hpole : RankinSelberg.SquareIntegrablePoleOrderCharacterizationStatement.{uF, uA, uA})
    (hsq : AssemblySquareIntegrablePreimageStatement.{uF, uP, uA} F)
    {c0 : SupercuspidalMap.{uF, uP, uA} F} {τ : FullMap.{uF, uP, uA} F}
    {ψ : NontrivialAdditiveCharacter F}
    (hc0 : IsSupercuspidalCorrespondence F c0) (hτ : ExtendsSupercuspidal F c0 τ)
    (hL : ∀ k j : ℕ, j < k → ∀ (D : WeilDeligneClass.{uF, uP} F k.succPNat)
        (D' : WeilDeligneClass.{uF, uP} F j.succPNat),
      ¬ IsIrreducibleWeilParameter F D → IsIndecomposableParameterClass F D' →
        IsPairLCompatibleAt F ψ D D' (τ k.succPNat D) (τ j.succPNat D'))
    {c : FullMap.{uF, uP, uA} F} (hc : IsAssemblyOf F c0 c) : c = τ := by
  have hcext := extendsSupercuspidal_of_isAssemblyOf hwd hc hτ
  have hcbij := hbij c0 c hc0.1 hc
  have hcL := hinh c0 c hc0 hc ψ
  obtain ⟨ν, hν⟩ := hc0.exists_selfDualMeasure F ψ
  let νH : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ := ⟨ν, hν⟩
  have key : ∀ (k : ℕ) (D : WeilDeligneClass.{uF, uP} F k.succPNat),
      c k.succPNat D = τ k.succPNat D := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro D
      by_cases hD : IsIrreducibleWeilParameter F D
      · exact hcext.eq_on_irreducible hτ hD
      obtain ⟨A, hA⟩ := automorphicClass_has_representative F (c k.succPNat D)
      obtain ⟨B, hB⟩ := automorphicClass_has_representative F (τ k.succPNat D)
      have hAns : ¬ GeneralLinear.IsSupercuspidal A.obj.representation := fun hsc =>
        hD (isIrreducibleWeilParameter_of_isSupercuspidal hc0.1 hcext
          (fun n => (hcbij n).1) A hA hsc)
      cases k with
      | zero => exact absurd (isSupercuspidal_rank_one A) hAns
      | succ n =>
        rw [← hA, ← hB]
        apply automorphicClass_eq_of_pole_order_tests hpole ψ νH n A B hAns
        intro r hr R hR
        obtain ⟨D', hD'⟩ := (hcbij r.succPNat).2 (automorphicClassOf F R)
        have hind : IsIndecomposableParameterClass F D' :=
          hsq c0 r.succPNat D' R (hD' ▸ hc r.succPNat D') hR
        have hIH : c r.succPNat D' = τ r.succPNat D' := ih r (by omega) D'
        have h1 := hcL (n + 1) r D D'
        have h2 := hL (n + 1) r (by omega) D D' hD hind
        rw [hIH] at h1
        obtain ⟨P, Q, hP, hQ, hPQ⟩ := h1.same_pole_order h2 ν hν
        rw [← hA, ← hIH, hD'] at hP
        rw [← hB, ← hIH, hD'] at hQ
        exact ⟨P, Q, hP, hQ, hPQ⟩
  funext n D
  have hn : n = (n : ℕ).pred.succPNat := (PNat.succPNat_natPred n).symm
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k.succPNat := ⟨_, hn⟩
  exact key k D

/-- Henniart 2002, Theorem 1.8, conditional on its ingredients: the published
characterization statement follows from `AssemblyLCharacterizationIngredients`. -/
theorem assemblyLCharacterization_of_ingredients
    (h : AssemblyLCharacterizationIngredients.{uF, uP, uA} F) :
    AssemblyLCharacterizationStatement.{uF, uP, uA} F := by
  obtain ⟨hwd, hbij, hinh, hpole, hsq⟩ := h
  intro c0 τ ψ hc0 hτ hL
  have hc := assemblyOfWellDefined_isAssemblyOf F hwd c0
  have hcτ := assembly_eq_of_lowerRankPairL hwd hbij hinh hpole hsq hc0 hτ hL hc
  exact ⟨hcτ ▸ hc, fun c' hc' =>
    assembly_eq_of_lowerRankPairL hwd hbij hinh hpole hsq hc0 hτ hL hc'⟩

end Langlands.Correspondence
