import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLeviDecompositionStatement
import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamicProof
import Langlands.GroupScheme.Dynamic.Decomposition
import Langlands.GroupScheme.Dynamic.Uniqueness

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

private theorem ordered_factorization {S : Scheme.{u}} {G : GroupScheme S}
    (χ : (Gm S).toGrp ⟶ G) [IsSeparated G.X.hom]
    {T : Over S} {g : T ⟶ G.X} (hg : g ∈ (Dynamic.parabolic χ).carrier T) :
    ∃! p : (T ⟶ G.X) × (T ⟶ G.X),
      p.1 ∈ (Dynamic.centralizer χ).carrier T ∧
      p.2 ∈ (Dynamic.unipotent χ).carrier T ∧ g = p.1 * p.2 := by
  obtain ⟨l, hl⟩ := Dynamic.exists_hasLimit χ hg
  have hz := hl.mem_centralizer χ
  have hv : l⁻¹ * g ∈ (Dynamic.unipotent χ).carrier T := by
    rw [Dynamic.mem_unipotent]
    have h := ((Dynamic.hasLimit_of_mem_centralizer χ hz).inv χ).mul χ hl
    simpa only [inv_mul_cancel] using h
  refine ⟨(l, l⁻¹ * g), ⟨hz, hv, (mul_inv_cancel_left l g).symm⟩, ?_⟩
  rintro ⟨z, v⟩ ⟨hz', hv', hgv⟩
  have hl' : Dynamic.HasLimit χ g z := by
    rw [hgv]
    simpa only [mul_one] using (Dynamic.hasLimit_of_mem_centralizer χ hz').mul χ hv'
  have hzl : z = l := hl'.unique χ hl
  apply Prod.ext hzl
  change v = l⁻¹ * g
  rw [hgv, ← hzl, inv_mul_cancel_left]

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

private theorem triangular_intersection :
    upperTriangular b c ⊓ lowerTriangular b c = diagonal b c := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, mem_upperTriangular,
    mem_lowerTriangular, mem_diagonal, and_comm]

private theorem opposite_unipotent_intersection :
    lowerUnipotent b c ⊓ upperTriangular b c = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  ext x
  simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf, mem_lowerUnipotent,
    mem_upperTriangular, SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · rintro ⟨⟨h01, h00, h11⟩, h10⟩
    apply (pointsEquiv b c T).injective
    apply Subtype.ext
    apply Units.ext
    change (matrixCoordinates b c T x).val = (matrixCoordinates b c T 1).val
    rw [map_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h00, h11, h10]
  · rintro rfl
    simp [map_one]

private theorem unitary_ordered_factorization
    {T : Over (Spec (CommRingCat.of F))} {g : T ⟶ (groupScheme b c).X}
    (hg : g ∈ (Dynamic.parabolic (cocharacter b c)).carrier T) :
    ∃! p : (T ⟶ (groupScheme b c).X) × (T ⟶ (groupScheme b c).X),
      p.1 ∈ (Dynamic.centralizer (cocharacter b c)).carrier T ∧
      p.2 ∈ (Dynamic.unipotent (cocharacter b c)).carrier T ∧ g = p.1 * p.2 := by
  exact ordered_factorization (cocharacter b c) hg

/-- Combine the dynamic matrix descriptions with separatedness of the unitary model. -/
theorem leviDecompositionStatement : LeviDecompositionStatement.{u} := by
  intro F E _ _ _ _ κ _ b c hc
  obtain ⟨hp, hz, hu, hp', hz', hu', hroots⟩ := dynamicStatement F E κ b c hc
  refine ⟨Dynamic.unipotent_isNormalizedBy_parabolic (cocharacter b c), ?_, ?_, ?_⟩
  · intro T g hg
    exact unitary_ordered_factorization b c hg
  · rw [hp, hp', hz]
    exact triangular_intersection b c
  · rw [hu', hp]
    exact opposite_unipotent_intersection b c

end Langlands.GroupScheme.QuasiSplitUnitary
