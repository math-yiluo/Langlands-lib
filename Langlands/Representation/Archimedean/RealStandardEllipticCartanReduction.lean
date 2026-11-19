import Langlands.Representation.Archimedean.ComplexStandardOppositeOrderHomReduction
import Langlands.Representation.Archimedean.RealStandardEllipticCartanNumerator
import Langlands.Representation.Archimedean.RealStandardParameterUniqueStatement

/-! # Real standard parameter uniqueness from the elliptic Cartan comparison

This reduction uses equality of the finite Cartan numerators and the number of elliptic
slots of the two modules. See the paired Markdown.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

namespace RealStandardEllipticCartan

/-- A block list from enumerations of its induced blocks and real characters. -/
def ofBlockData {r s : ℕ} (d : Fin r → ComplexCharacterData)
    (c : Fin s → RealCharacterData) : List RealBlock :=
  (List.ofFn d).map RealBlock.induced ++ (List.ofFn c).map RealBlock.character

/-- The weight, parity and exponent coordinates read from the two enumerations. -/
def blockParameters {r s : ℕ} (d : Fin r → ComplexCharacterData)
    (c : Fin s → RealCharacterData) : Parameters r s :=
  (fun i => ((d i).weight, (d i).exponent), fun j => ((c j).parity, (c j).exponent))

private theorem realCharacterData_eq_of_parity_exponent {c d : RealCharacterData}
    (hp : c.parity = d.parity) (he : c.exponent = d.exponent) : c = d := by
  cases c with
  | mk χ p t h =>
    cases d with
    | mk ψ q u h' =>
      change p = q at hp
      change t = u at he
      subst q
      subst u
      have hc : χ = ψ := ContinuousMonoidHom.ext fun x => Units.ext (by rw [h x, h' x])
      subst ψ
      rfl

private theorem perm_of_cartan_numerator_eq {r s : ℕ} {d e : Fin r → ComplexCharacterData}
    {c b : Fin s → RealCharacterData}
    (hd : ∀ i, 0 < (d i).weight) (he : ∀ i, 0 < (e i).weight)
    (h : numerator (blockParameters d c) = numerator (blockParameters e b)) :
    (ofBlockData d c).Perm (ofBlockData e b) := by
  obtain ⟨π, σ, hπ, hσ⟩ := exists_perm_of_numerator_eq hd he h
  have heq : e = d ∘ π := by
    funext i
    exact complexCharacterData_eq_of_weight_exponent
      (congrArg Prod.fst (hπ i)).symm (congrArg Prod.snd (hπ i)).symm
  have hbeq : b = c ∘ σ := by
    funext j
    exact realCharacterData_eq_of_parity_exponent
      (congrArg Prod.fst (hσ j)).symm (congrArg Prod.snd (hσ j)).symm
  subst e
  subst b
  exact ((π.ofFn_comp_perm d).symm.map RealBlock.induced).append
    ((σ.ofFn_comp_perm c).symm.map RealBlock.character)

end RealStandardEllipticCartan

open RealStandardEllipticCartan

/-- Bijectively intertwined irreducible real standard modules with positive induced weights
have the same number of induced blocks, and their numerators on the Cartan subgroup of that
elliptic rank agree. The enumerations of the block data refer to the original lists. -/
def RealStandardEllipticCartanComparisonStatement : Prop :=
  ∀ (n : ℕ) (ds es : List RealBlock), realRank ds = n → realRank es = n →
    (∀ d : ComplexCharacterData, .induced d ∈ ds → 0 < d.weight) →
    (∀ d : ComplexCharacterData, .induced d ∈ es → 0 < d.weight) →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) →
    ∀ T : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
        kFiniteFunctions (realStandardModule n es) (unitaryCompact ℝ n),
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
      Function.Bijective T →
      ∃ (r s : ℕ) (d e : Fin r → ComplexCharacterData) (c b : Fin s → RealCharacterData),
        ds.Perm (ofBlockData d c) ∧ es.Perm (ofBlockData e b) ∧
          numerator (blockParameters d c) = numerator (blockParameters e b)

/-- The elliptic Cartan comparison suffices for positive-weight parameter uniqueness. -/
def RealStandardEllipticCartanReductionStatement : Prop :=
  RealStandardEllipticCartanComparisonStatement → RealPositiveWeightStandardUniqueStatement

theorem realStandardEllipticCartanReduction : RealStandardEllipticCartanReductionStatement := by
  intro hcartan n ds es hn hm hd he hds hes T hT hbij
  obtain ⟨r, s, d, e, c, b, hdp, hep, hnum⟩ :=
    hcartan n ds es hn hm hd he hds hes T hT hbij
  have hpos (f : Fin r → ComplexCharacterData) (g : Fin s → RealCharacterData)
      {xs : List RealBlock} (hp : xs.Perm (ofBlockData f g))
      (h : ∀ d : ComplexCharacterData, .induced d ∈ xs → 0 < d.weight) (i : Fin r) :
      0 < (f i).weight := by
    apply h
    exact hp.mem_iff.mpr (List.mem_append_left _ (List.mem_map_of_mem
      (List.mem_ofFn.mpr ⟨i, rfl⟩)))
  exact hdp.trans ((perm_of_cartan_numerator_eq (hpos d c hdp hd) (hpos e b hep he) hnum).trans
    hep.symm)

end Langlands.Archimedean
