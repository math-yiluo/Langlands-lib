import Langlands.Representation.Whittaker.MirabolicUnitTestProof
import Langlands.AllField.Representation.Whittaker.MirabolicUnitTestStatement
/-!
# Compact opposite-character mirabolic test functions: proof

A compact open ambient subgroup is chosen inside the determinant-norm-one
locus and inside a neighborhood on which the standard character is trivial.
Its mirabolic intersection is the right stabilizer, and the character values
on the corresponding `N`-cosets are extended by zero.
-/

noncomputable section

open Topology

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker

universe uF uG

namespace MirabolicUnitTest
open Langlands.Whittaker.MirabolicUnitTest
open Langlands.AllField.Whittaker.MirabolicUnitTest
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest
open Langlands.AllField.Whittaker



end MirabolicUnitTest

open Langlands.Whittaker.MirabolicUnitTest
open Langlands.AllField.Whittaker.MirabolicUnitTest

/-- Compact opposite-character mirabolic test functions exist for every supplied
p-adic realization, every unitary additive character and every rank. -/
theorem mirabolicUnitTest (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) : MirabolicUnitTestStatement F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  intro ψ G P N χ
  have hker : IsOpen (χ.ker : Set N) := by
    let := T.upperUnipotentNonarchimedean (n + 1)
    exact isOpen_ker_of_continuous_complex_character χ
      (standardCharacterContinuous ψ n).continuous
  have hK1 : (χ.ker : Set N) ∈ 𝓝 (1 : N) := hker.mem_nhds χ.ker.one_mem
  rw [Topology.IsInducing.subtypeVal.nhds_eq_comap, Filter.mem_comap] at hK1
  obtain ⟨O, hO, hOK⟩ := hK1
  have hU : O ∩ ((T.determinantNorm (n + 1)).ker : Set G) ∈ 𝓝 (1 : G) :=
    Filter.inter_mem hO ((T.isOpen_ker_determinantNorm (n + 1)).mem_nhds (one_mem _))
  obtain ⟨J₀, hJc, hJU⟩ := T.generalLinearCompactOpen (n + 1) _ hU
  let P₀ : OpenSubgroup P := OpenSubgroup.comap P.subtype continuous_subtype_val J₀
  let H : Subgroup G := J₀.toSubgroup ⊓ P
  have hθ : ∀ u : N, (u : G) ∈ H → χ u = 1 := fun u hu =>
    MonoidHom.mem_ker.mp (hOK (hJU (Subgroup.mem_inf.mp hu).1).1)
  have hθ' : ∀ u : N, (u : G) ∈ H → inverseStandardCharacter ψ n u = 1 := by
    intro u hu
    change (χ u)⁻¹ = 1
    rw [hθ u hu, inv_one]
  have hH (k : P₀) : k.val.val ∈ H := Subgroup.mem_inf.mpr ⟨k.property, k.val.property⟩
  let φ : RankinSelberg.WhittakerFunctions ψ n :=
    ⟨cosetExtension N H χ, fun u g => cosetExtension_left hθ u g⟩
  let φ' : RankinSelberg.InverseWhittakerFunctions ψ n :=
    ⟨cosetExtension N H (inverseStandardCharacter ψ n),
      fun u g => cosetExtension_left hθ' u g⟩
  refine ⟨P₀, φ, φ', J₀, ?_⟩
  intro C S
  refine ⟨?_, hJc, ?_, ?_, ?_, ?_, ?_⟩
  · exact (GeneralLinear.Mirabolic.isClosed (F := F) (n := n)).isClosedEmbedding_subtypeVal.isCompact_preimage hJc
  · intro k
    exact MonoidHom.mem_ker.mp (hJU k.property).2
  · intro j hj hP
    exact ⟨⟨j, hP⟩, hj, rfl⟩
  · intro u k
    exact ⟨cosetExtension_mul hθ u (hH k),
      (cosetExtension_mul hθ' u (hH k)).trans (Units.val_inv_eq_inv_val _)⟩
  · intro g hg
    have hg' : ¬ ∃ u : N, ∃ k ∈ H, g = u * k := by
      rintro ⟨u, k, hk, rfl⟩
      exact hg ⟨u, ⟨⟨k, (Subgroup.mem_inf.mp hk).2⟩, (Subgroup.mem_inf.mp hk).1⟩, rfl⟩
    exact ⟨cosetExtension_eq_zero hg', cosetExtension_eq_zero hg'⟩
  · intro g k
    exact ⟨cosetExtension_right hθ g (hH k), cosetExtension_right hθ' g (hH k)⟩

end Langlands.AllField.Whittaker
