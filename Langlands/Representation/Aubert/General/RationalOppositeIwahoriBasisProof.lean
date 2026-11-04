import Langlands.Representation.Aubert.General.RationalOppositeIwahoriBasisStatement
import Langlands.Representation.Jacquet.OppositeIwahoriBasisAbstract
import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.BruhatTits.Unipotent.CocharacterContraction

/-! # Proof: a Levi-central element with an opposite Iwahori basis on rational points

The element is the value of the standard cocharacter at one field unit whose
powers tend to zero. The compact open subgroups come from the abstract
contraction criterion, applied to the opposite radical, the dynamic Levi and the
dynamic radical of that cocharacter. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- For a separated affine group over a field and a cocharacter `χ`, a rational
point has at most one factorization `o * m * u` with `o` in `U(χ⁻¹)(k)`, `m` in
`Z(χ)(k)` and `u` in `U(χ)(k)`. -/
theorem dynamic_opposite_factorization_unique {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffine G.X.left] [IsSeparated G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    ∀ o ∈ (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)),
    ∀ m ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)),
    ∀ u ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)),
    ∀ o' ∈ (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)),
    ∀ m' ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)),
    ∀ u' ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)),
      o * m * u = o' * m' * u' → o = o' ∧ m = m' ∧ u = u' := by
  intro o ho m hm u hu o' ho' m' hm' u' hu' h
  have hP : o'⁻¹ * o ∈ (Dynamic.parabolic χ).carrier (Over.mk (𝟙 _)) := by
    have he : o'⁻¹ * o = m' * u' * u⁻¹ * m⁻¹ := by
      have ho : o = o' * m' * u' * u⁻¹ * m⁻¹ := by
        rw [← h]
        group
      rw [ho]
      group
    rw [he]
    exact mul_mem (mul_mem (mul_mem (Dynamic.centralizer_le_parabolic χ _ hm')
      (Dynamic.unipotent_le_parabolic χ _ hu'))
      (inv_mem (Dynamic.unipotent_le_parabolic χ _ hu)))
      (inv_mem (Dynamic.centralizer_le_parabolic χ _ hm))
  have hO : o'⁻¹ * o = 1 :=
    Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_parabolic χ (mul_mem (inv_mem ho') ho) hP
  have hoo : o = o' := (inv_mul_eq_one.mp hO).symm
  subst hoo
  have h2 : m * u = m' * u' := by
    rw [mul_assoc, mul_assoc] at h
    exact mul_left_cancel h
  have he : m'⁻¹ * m = u' * u⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h2, mul_inv_cancel_right]
  have h1 : m'⁻¹ * m = 1 :=
    Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent χ
      (fun _ _ _ _ hl hl' => hl.unique χ hl') (mul_mem (inv_mem hm') hm)
      (by rw [he]; exact mul_mem hu' (inv_mem hu))
  have hmm : m = m' := (inv_mul_eq_one.mp h1).symm
  subst hmm
  exact ⟨rfl, rfl, mul_left_cancel h2⟩

/-- **One Levi-central element and an opposite Iwahori basis.** For every
standard cocharacter there is one element commuting with the standard Levi for
which the standard radical, the standard Levi and the opposite radical admit an
ambient-cofinal opposite Iwahori contraction basis. The proof takes the
cocharacter's value at a field unit whose powers tend to zero. -/
theorem rationalOppositeIwahoriBasisStatement :
    RationalOppositeIwahoriBasisStatement.{u} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard I hU ζ hζ
  have := hG.smooth
  have := hG.isSeparated
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : T2Space k := Langlands.BruhatTits.localField_t2Space k
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = CommGroupScheme.groupHom ζ ≫ i := ⟨_, rfl⟩
  have hStd := (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).2 ζ hζ
  rw [← hχ] at hStd
  have hM : levi i ν I = (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    change (standardLevi i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) = _
    rw [hStd.2.1]
  have hUeq : unipotent i ν I = (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    change (standardUnipotent i ν (rootSet i ν I)).carrier (Over.mk (𝟙 _)) = _
    rw [hStd.2.2]
  have hOeq : oppositeUnipotent i ζ =
      (Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)) := by
    rw [hχ]
    rfl
  have hOc := isClosed_oppositeUnipotent_localField i ζ
  rw [hOeq] at hOc
  rw [hUeq] at hU
  obtain ⟨g, hgM, hcomm, hcontrU, hcontrO⟩ :=
    BruhatTits.DynamicUnipotentContainment.exists_central_contractingPoint (F := k) χ
  refine ⟨g, ?_, ?_⟩
  · rw [hM]
    exact hcomm
  rw [hM, hUeq, hOeq]
  have htop : (pointTopology : TopologicalSpace (RationalPoint k G.X)) =
      rationalSchemeTopology k G.X :=
    rationalPointTopology_eq_rationalSchemeTopology k G.X
  refine Jacquet.hasOppositeIwahoriContractionBasis_of_contraction hOc hU hgM hcomm ?_ ?_
    (dynamic_opposite_factorization_unique χ) ?_ hcontrU hcontrO
  · rw [← Dynamic.centralizer_inverseCocharacter χ]
    exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · exact Dynamic.centralizer_le_normalizer_unipotent _ _
  · rw [htop]
    exact Dynamic.opposite_cell_mem_nhds_one k G χ

end Langlands.Aubert.General.RationalPointFamily
