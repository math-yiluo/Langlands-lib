import Langlands.GroupScheme.Rational.RelativeTitsSystemStatement
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.TitsStandardParabolic

/-! # Bruhat consequences for the actual relative Tits data -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [IsAffineHom G.X.hom] (ν : cocharacterLattice T)

/-- The Bruhat cell of an actual relative Weyl class for the actual minimal
standard parabolic, using all normalizer representatives. -/
def relativeTitsCell (w : relativeWeylGroup i) :
    Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :=
  Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))) w

/-- The kernel of the actual quotient lies in every standard parabolic,
without a Bruhat or reductivity hypothesis. -/
theorem relativeTits_ker_le :
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).ker ≤
      (standardParabolicPoints i ν ∅).subgroupOf (normalizerPoints i) := by
  rw [QuotientGroup.ker_mk']
  intro n hn
  exact centralizerPoints_le_standardParabolicPoints i ν ∅ hn

/-- Bruhat separation alone gives the exact kernel identity for the actual
minimal standard parabolic. The full endpoint equality is not needed. -/
theorem relativeTits_ker_eq_of_bruhat (hBr : HasRationalBruhatDecomposition i ν) :
    (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).ker =
      (standardParabolicPoints i ν ∅).subgroupOf (normalizerPoints i) := by
  apply le_antisymm (relativeTits_ker_le i ν)
  intro n hn
  have hnP := standardParabolic_empty_le i ν _ hn
  have hclass : (QuotientGroup.mk (1 : normalizerPoints i) : relativeWeylGroup i) =
      QuotientGroup.mk n :=
    (hBr.2 1 n).mp ⟨n.val, hnP, 1, Subgroup.one_mem _, by simp⟩
  rw [MonoidHom.mem_ker]
  exact hclass.symm

/-- The normalizing points in the minimal standard parabolic are precisely
the whole-torus centralizer points, under rational Bruhat separation. -/
theorem relativeTits_inf_eq_of_bruhat (hBr : HasRationalBruhatDecomposition i ν) :
    standardParabolicPoints i ν ∅ ⊓ normalizerPoints i = centralizerPoints i := by
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨hgB, hgN⟩
    have hker : (⟨g, hgN⟩ : normalizerPoints i) ∈
        (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).ker := by
      rw [relativeTits_ker_eq_of_bruhat i ν hBr]
      exact hgB
    rw [QuotientGroup.ker_mk'] at hker
    exact hker
  · intro hg
    exact ⟨centralizerPoints_le_standardParabolicPoints i ν ∅ hg,
      centralizerPoints_le_normalizerPoints i hg⟩

/-- Covering by rational Bruhat double cosets gives generation by the minimal
standard parabolic and normalizer, once the minimal endpoint is identified. -/
theorem relativeTits_sup_eq_of_bruhat
    (hB : standardParabolicPoints i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hBr : HasRationalBruhatDecomposition i ν) :
    standardParabolicPoints i ν ∅ ⊔ normalizerPoints i = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨n, hn, p, hp, q, hq, rfl⟩ := hBr.1 g
  have hpB : p ∈ standardParabolicPoints i ν ∅ := hB.symm ▸ hp
  have hqB : q ∈ standardParabolicPoints i ν ∅ := hB.symm ▸ hq
  have hBL : standardParabolicPoints i ν ∅ ≤
      standardParabolicPoints i ν ∅ ⊔ normalizerPoints i := le_sup_left
  have hNL : normalizerPoints i ≤
      standardParabolicPoints i ν ∅ ⊔ normalizerPoints i := le_sup_right
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (hBL hpB) (hNL hn)) (hBL hqB)

/-- Every rational point belongs to an actual relative Tits cell under the
minimal endpoint identity and rational Bruhat covering. -/
theorem exists_mem_relativeTitsCell_of_bruhat
    (hB : standardParabolicPoints i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hBr : HasRationalBruhatDecomposition i ν)
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ w : relativeWeylGroup i, g ∈ relativeTitsCell i ν w := by
  obtain ⟨n, hn, p, hp, q, hq, heq⟩ := hBr.1 g
  exact ⟨QuotientGroup.mk ⟨n, hn⟩, ⟨n, hn⟩, rfl, p, hB.symm ▸ hp,
    q, hB.symm ▸ hq, heq⟩

/-- The actual relative Tits cells are disjoint under Bruhat separation.
The one-sided inclusion of the minimal endpoint suffices. -/
theorem eq_of_mem_relativeTitsCell_of_bruhat
    (hBr : HasRationalBruhatDecomposition i ν)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {w w' : relativeWeylGroup i}
    (hg : g ∈ relativeTitsCell i ν w) (hg' : g ∈ relativeTitsCell i ν w') :
    w = w' := by
  obtain ⟨n, hn, p, hp, q, hq, heq⟩ := hg
  obtain ⟨n', hn', p', hp', q', hq', heq'⟩ := hg'
  have hpP := standardParabolic_empty_le i ν _ hp
  have hqP := standardParabolic_empty_le i ν _ hq
  have hpP' := standardParabolic_empty_le i ν _ hp'
  have hqP' := standardParabolic_empty_le i ν _ hq'
  have heqN : (n' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) =
      (p'⁻¹ * p) * n * (q * q'⁻¹) := by
    have h := congrArg (fun x => p'⁻¹ * x * q'⁻¹) (heq'.symm.trans heq)
    simpa [mul_assoc] using h
  have hclass := (hBr.2 n n').mp
    ⟨p'⁻¹ * p, Subgroup.mul_mem _ (Subgroup.inv_mem _ hpP') hpP,
      q * q'⁻¹, Subgroup.mul_mem _ hqP (Subgroup.inv_mem _ hqP'), heqN⟩
  exact hn.symm.trans (hclass.trans hn')

end Langlands.GroupScheme
