import Langlands.Representation.Geometric.RepresentedGeometricLemmaStatement
import Langlands.GroupScheme.Rational.ClosedSelfEmbedding
import Langlands.GroupScheme.Rational.FullParabolicLevi
import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Full self-intersections in the geometric lemma

For one represented parabolic `P = MN` and a double coset `P z P`, the intersection datum of
the geometric lemma (Renard VI.5.1) has `P' = M ∩ zPz⁻¹` and `Q' = M ∩ z⁻¹Pz`. When `P'` is all
of `M`, the conjugate `zMz⁻¹` contains `M`; since a closed self-embedding of a connected
reductive group is an isomorphism, all four intersection inclusions are then isomorphisms and
conjugation by `z` restricts to an automorphism of `M`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A closed-subgroup homomorphism `j` such that `i ≫ j` is an isomorphism is itself an
isomorphism: it is a monomorphism with a section. -/
theorem IsClosedSubgroup.isIso_of_isIso_comp {S : Scheme.{u}} {A B C : GroupScheme S}
    (i : A ⟶ B) {j : B ⟶ C} (hj : IsClosedSubgroup j) [IsIso (i ≫ j)] : IsIso j := by
  have : Mono j := by
    have : Mono ((Grp.forget (Over S) ⋙ Over.forget S).map j) := hj.mono
    exact (Grp.forget (Over S) ⋙ Over.forget S).mono_of_mono_map this
  have : IsSplitEpi j := ⟨⟨inv (i ≫ j) ≫ i, by simp⟩⟩
  exact isIso_of_mono_of_isSplitEpi j

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [TopologicalSpace k]
  {G : GroupScheme (Spec (CommRingCat.of k))} {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}

namespace GeometricLemmaIntersectionDatum

variable {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P} {hp : IsParabolicSubgroup p}
  {hr : LeviSubgroup.IsGeometricUnipotentRadical r} {hl : IsRationalLeviSubgroup l}
  {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q} {hq : IsParabolicSubgroup q}
  {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ} {hlQ : IsRationalLeviSubgroup lQ}
  {hmulQ : IsIso (subgroupMultiplication lQ rQ)} {z : rationalPoints G}

/-- If `P' = M ∩ zQz⁻¹` is all of `M`, its Levi `M' = M ∩ zLz⁻¹` is all of `P'`. -/
theorem isIso_l'_of_isIso_p'
    (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul q lQ rQ hq hrQ hlQ hmulQ z)
    [IsIso D.p'] : IsIso D.l' :=
  D.hl'.isIso_of_isIso_parabolic (p := D.p') hl.isConnectedReductive

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul p l r hp hr hl hmul z)

/-- For a self-intersection datum at `P z P` with `P' = M`, the closed embedding
`L' ⟶ Q' ⟶ M` of `M ∩ z⁻¹Mz` is an isomorphism. -/
theorem isIso_lQ'_comp_q'_of_isIso_p' [IsIso D.p'] : IsIso (D.lQ' ≫ D.q') := by
  have := D.isIso_l'_of_isIso_p'
  let f : M ⟶ M := inv (D.φ.hom ≫ D.l' ≫ D.p') ≫ D.lQ' ≫ D.q'
  have hf : IsClosedSubgroup f :=
    (IsClosedSubgroup.of_iso (asIso (D.φ.hom ≫ D.l' ≫ D.p')).symm).comp
      (D.hlQ'.isClosedSubgroup.comp D.hq'.isClosedSubgroup)
  have := hl.isConnectedReductive.isIso_of_isClosedSubgroup f hf
  have hcomp : D.lQ' ≫ D.q' = (D.φ.hom ≫ D.l' ≫ D.p') ≫ f := by
    simp only [f, IsIso.hom_inv_id_assoc]
  rw [hcomp]
  infer_instance

/-- For a self-intersection datum at `P z P` with `P' = M`, the parabolic `Q' = M ∩ z⁻¹Pz` is
all of `M`. -/
theorem isIso_q'_of_isIso_p' [IsIso D.p'] : IsIso D.q' := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'
  exact D.hq'.isClosedSubgroup.isIso_of_isIso_comp D.lQ'

/-- For a self-intersection datum at `P z P` with `P' = M`, the Levi `L' = M ∩ z⁻¹Mz` is all
of `Q'`. -/
theorem isIso_lQ'_of_isIso_p' [IsIso D.p'] : IsIso D.lQ' := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'
  have := D.isIso_q'_of_isIso_p'
  exact IsIso.of_isIso_comp_right D.lQ' D.q'

/-- Conjugation by `z` as an automorphism of `M`, for a self-intersection datum at `P z P`
with `P' = M`: the composite `M ≅ L' ≅ M' ≅ M` of the inverse of `L' ⟶ Q' ⟶ M`, the
intersection isomorphism `φ`, and `M' ⟶ P' ⟶ M`. -/
def selfConjugation [IsIso D.p'] : M ≅ M :=
  haveI := D.isIso_l'_of_isIso_p'
  haveI := D.isIso_lQ'_comp_q'_of_isIso_p'
  (asIso (D.lQ' ≫ D.q')).symm ≪≫ D.φ ≪≫ asIso (D.l' ≫ D.p')

theorem selfConjugation_hom [IsIso D.p'] :
    haveI := D.isIso_lQ'_comp_q'_of_isIso_p'
    D.selfConjugation.hom = inv (D.lQ' ≫ D.q') ≫ D.φ.hom ≫ D.l' ≫ D.p' := by
  simp only [selfConjugation, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom]

/-- The automorphism `selfConjugation` of `M` is conjugation by `z` inside `G`. -/
theorem selfConjugation_comp [IsIso D.p'] :
    D.selfConjugation.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso z).hom := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'
  rw [D.selfConjugation_hom]
  simp only [Category.assoc]
  rw [D.φ_comp, ← Category.assoc D.lQ' D.q', IsIso.inv_hom_id_assoc]

/-- On rational points, `selfConjugation` sends the image of `a ∈ L'(F)` in `M(F)` to the
image of `e a ∈ M'(F)`. -/
theorem selfConjugation_map_rationalPoints [IsIso D.p'] (a : rationalPoints D.L') :
    rationalPoints.map D.selfConjugation.hom (rationalPoints.map (D.lQ' ≫ D.q') a) =
      rationalPoints.map (D.l' ≫ D.p') (rationalPoints.map D.φ.hom a) := by
  have := D.isIso_lQ'_comp_q'_of_isIso_p'
  have hc : ∀ {A B C : GroupScheme (Spec (CommRingCat.of k))} (f : A ⟶ B) (g : B ⟶ C)
      (x : rationalPoints A),
      rationalPoints.map (f ≫ g) x = rationalPoints.map g (rationalPoints.map f x) := by
    intros
    simp only [rationalPoints.map_apply, Grp.comp_hom_hom, Category.assoc]
  have h : (D.lQ' ≫ D.q') ≫ D.selfConjugation.hom = D.φ.hom ≫ D.l' ≫ D.p' := by
    rw [D.selfConjugation_hom, IsIso.hom_inv_id_assoc]
  rw [← hc, ← hc, h]

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
