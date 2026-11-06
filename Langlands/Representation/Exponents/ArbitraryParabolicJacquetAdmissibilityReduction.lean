import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityStatement
import Langlands.Representation.Aubert.General.JacquetAdmissibility
import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisProof
import Langlands.GroupScheme.Rational.ParabolicLeviRealization

/-! # Actual Jacquet admissibility reduced to dynamic structure statements -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Jacquet

/-- An ambient-cofinal opposite contraction basis has arbitrarily small
intersections with the Levi subgroup in its induced topology. -/
theorem HasOppositeIwahoriContractionBasis.hasIwahoriContractionBasis
    {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    {N M Nbar : Subgroup Γ} {g : Γ}
    (h : HasOppositeIwahoriContractionBasis N M Nbar g) :
    HasIwahoriContractionBasis N M Nbar := by
  intro L
  obtain ⟨W, hW, hWL⟩ := isOpen_induced_iff.mp L.isOpen
  have h1 : (1 : Γ) ∈ W := by
    have : (1 : M) ∈ (Subtype.val : M → Γ) ⁻¹' W := by
      rw [hWL]
      exact L.one_mem
    exact this
  obtain ⟨K, hK, hKW, hKg, -⟩ := h W hW h1
  refine ⟨K, hK, ?_, g, hKg⟩
  intro m hm
  change m ∈ (L : Set M)
  rw [← hWL]
  exact hKW hm

end Langlands.Jacquet

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Every cocharacter of a connected reductive group over a nonarchimedean
local field supplies an ambient-cofinal opposite contraction basis for its
literal dynamic radical, centralizer and opposite radical. -/
theorem dynamic_hasOppositeIwahoriContractionBasis
    {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G),
      ∃ g : rationalPoints G,
        Jacquet.HasOppositeIwahoriContractionBasis
          ((Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)))
          ((Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)))
          ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _))) g := by
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := pointTopology
  intro _ _ χ
  have := hG.smooth
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨g, hgM, hcomm, hcontrU, hcontrO⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint (F := k) χ
  refine ⟨g, Jacquet.hasOppositeIwahoriContractionBasis_of_contraction
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints
      (Dynamic.inverseCocharacter χ))
    (BruhatTits.DynamicUnipotentContainment.isClosed_unipotentPoints χ)
    hgM hcomm ?_ ?_ (dynamic_opposite_factorization_unique χ) ?_ hcontrU hcontrO⟩
  · rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · have htop : (pointTopology : TopologicalSpace (rationalPoints G)) =
        rationalSchemeTopology k G.X :=
      rationalPointTopology_eq_rationalSchemeTopology k G.X
    rw [htop]
    exact Dynamic.opposite_cell_mem_nhds_one k G χ

end Langlands.Aubert.General.RationalPointFamily

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- A supplied geometric radical has literal point image equal to the dynamic
radical when the parabolic is realized by a cocharacter. -/
theorem pointImage_radical_eq_dynamic
    (hGUR : DynamicGeometricUnipotentRadicalStatement.{u})
    {k : Type u} [Field k] {G P U : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {p : P ⟶ G} (hp : IsParabolicSubgroup p)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic χ)
    {r : U ⟶ P} (hr : LeviSubgroup.IsGeometricUnipotentRadical r) :
    pointImage (r ≫ p) = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
  have : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  have : Mono p.hom.hom := Over.mono_of_mono_left _
  have hrep : (Dynamic.parabolic χ).IsRepresentedBy p := ⟨inferInstance, hP⟩
  apply Subgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    exact (DynamicLeviConjugacy.mem_range_radical_iff hGUR hG χ
      hp.isClosedSubgroup hrep hr (rationalPoints.map r y)).mp ⟨y, rfl⟩
  · intro hx
    have hxP : x ∈ (SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)) := by
      rw [hP]
      exact Dynamic.unipotent_le_parabolic χ _ hx
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hxP
    have hyU := (DynamicLeviConjugacy.mem_range_radical_iff hGUR hG χ
      hp.isClosedSubgroup hrep hr y).mpr (hy ▸ hx)
    obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hyU
    refine ⟨z, ?_⟩
    change (z ≫ r.hom.hom) ≫ p.hom.hom = x
    rw [hz, hy]

/-- The conditional reduction to the two dynamic structure statements. -/
def ArbitraryParabolicJacquetAdmissibilityReductionStatement : Prop :=
  ParabolicDynamicStatement.{u} →
    DynamicGeometricUnipotentRadicalStatement.{u} →
      ArbitraryParabolicJacquetAdmissibilityStatement.{u, v}

/-- The exact global admissibility proposition follows from the two explicit
dynamic structure statements. This does not prove those structural inputs. -/
theorem arbitraryParabolicJacquetAdmissibility_of_dynamic :
    ArbitraryParabolicJacquetAdmissibilityReductionStatement.{u, v} := by
  intro hPD hGUR k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul π hπ
  obtain ⟨χ, hP, hM⟩ :=
    DynamicLeviConjugacy.exists_cocharacter_parabolic_levi hPD hGUR hG hp hl
  have hN := pointImage_radical_eq_dynamic hGUR hG χ hp hP hr
  have hL : pointImage (l ≫ p) =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    exact congrArg (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _))) hM
  obtain ⟨g, hBasis⟩ := RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis G hG χ
  have hBasis' := hBasis.hasIwahoriContractionBasis
  rw [← hN, ← hL] at hBasis'
  exact isAdmissible_normalizedJacquetFunctor_obj_of_iwahoriContraction
    (pointImage (r ≫ p)) (pointImage (l ≫ p))
    ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (pointImage_le_normalizer p l r hr) hBasis' π hπ

end Langlands.Aubert.General.RepresentedParabolic
