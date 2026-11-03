import Langlands.GroupScheme.Absolute.ParabolicNormalizerReduction
import Langlands.GroupScheme.Absolute.ParabolicBorelFactorization
import Langlands.GroupScheme.Rational.ParabolicNormalizerStatement
import Langlands.GroupScheme.Reductive.FieldExtensionStatement
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionStatement
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.ParabolicNormalizerSeparation

/-! # Conditional assembly of all-test parabolic self-normalization -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K]
  {P G : GroupScheme (Spec (CommRingCat.of k))}

/-- An arbitrary morphism of field spectra is covered by the field-extension statement. -/
theorem connectedReductive_baseChange_of_statement
    (hext : ConnectedReductiveFieldExtensionStatement.{u})
    (hG : IsConnectedReductive G)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    IsConnectedReductive ((GroupScheme.baseChange b).obj G) := by
  let _ : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k K)) = b :=
    Spec.map_preimage b
  simpa only [hb] using hext k K G hG

/-- Dynamic parabolics and connected-reductive extension imply parabolic extension.
Both exact structural statements remain hypotheses. -/
theorem parabolicFieldExtensionStatement_of_dynamic
    (hpar : ParabolicDynamicStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u}) :
    ParabolicFieldExtensionStatement.{u} := by
  intro k K _ _ _ G hG P i hi
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨χ, hχ⟩ := (hpar k G hG P i hi.isClosedSubgroup).mp hi
  apply (hpar K ((GroupScheme.baseChange b).obj G) (hext k K G hG)
    _ ((GroupScheme.baseChange b).map i) (hi.isClosedSubgroup.baseChange b)).mpr
  refine ⟨Dynamic.baseChangeCocharacter b χ, ?_⟩
  rw [SubgroupFunctor.range_baseChangeHom, hχ, Dynamic.parabolic_baseChange]

/-- Transfer the preceding parabolic extension conclusion to any map of field spectra. -/
theorem parabolic_baseChange_of_structural_statements
    (hpar : ParabolicDynamicStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u})
    (hG : IsConnectedReductive G) {i : P ⟶ G} (hi : IsParabolicSubgroup i)
    (b : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k)) :
    IsParabolicSubgroup ((GroupScheme.baseChange b).map i) := by
  let _ : Algebra k K := (Spec.preimage b).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k K)) = b :=
    Spec.map_preimage b
  have hh : IsParabolicSubgroup
      ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i) :=
    parabolicFieldExtensionStatement_of_dynamic hpar hext k K G hG P i hi
  rwa [hb] at hh

/-- The exact dynamic connectedness statement gives connectedness of a parabolic source. -/
theorem parabolic_connected_of_structural_statements
    (hpar : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    (hG : IsConnectedReductive G) {i : P ⟶ G} (hi : IsParabolicSubgroup i) :
    ConnectedSpace P.X.left := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hpar k G hG P i hi.isClosedSubgroup).mp hi
  exact ((hconn k G χ P i).2 hG.connectedSpace).1 ⟨inferInstance, hχ⟩

/-- Structural base-change and connectedness statements provide the geometric Borels. -/
theorem geometricBorelOvergroupCondition_of_structural_statements
    (hpar : ParabolicDynamicStatement.{u}) (hconn : DynamicConnectedStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u})
    (hG : IsConnectedReductive G) {i : P ⟶ G} (hi : IsParabolicSubgroup i) :
    GeometricBorelOvergroupCondition i := by
  intro L _ _ b
  have hGb := connectedReductive_baseChange_of_statement hext hG b
  have hib := parabolic_baseChange_of_structural_statements hpar hext hG hi b
  exact ⟨hGb.connectedSpace,
    parabolic_connected_of_structural_statements hpar hconn hGb hib,
    hib.exists_isBorelSubgroup_factor⟩

/-- The dynamic opposite cell supplies all-test normalization once geometric Borels are given. -/
theorem parabolic_normalizer_eq_of_geometric_borels
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hcell : OppositeCellStatement.{u})
    (hG : IsConnectedReductive G) {i : P ⟶ G} (hi : IsParabolicSubgroup i)
    (hgeom : GeometricBorelOvergroupCondition i) :
    (SubgroupFunctor.range i).normalizer = SubgroupFunctor.range i := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth P.X.hom := hi.smooth
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨χ, hχ⟩ := (hpar k G hG P i hi.isClosedSubgroup).mp hi
  let iU := Dynamic.Affine.unipotentHom (Dynamic.oppositeCocharacter χ)
  have hU := Dynamic.Affine.isRepresentedBy_unipotentHom (Dynamic.oppositeCocharacter χ)
  have hP : (Dynamic.parabolic χ).IsRepresentedBy i := ⟨inferInstance, hχ⟩
  apply normalizer_eq_of_geometric_borels_and_open_cell hconj hnorm iU i
    hi.isClosedSubgroup hgeom
  · intro T g hgU hgN
    rw [hU.2] at hgU
    rw [hχ] at hgN
    exact Dynamic.eq_one_of_mem_opposite_unipotent_of_mem_normalizer χ hgU hgN
  · exact hcell k G χ _ P iU i hU hP

/-- Conditional assembly of the exact existing all-test proposition.
Each of the six structural statements remains an explicit proof obligation. -/
theorem parabolicSelfNormalizerStatement_of_structural_statements
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hcell : OppositeCellStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u}) :
    ParabolicSelfNormalizerStatement.{u} := by
  intro k _ G hG P i hi
  exact parabolic_normalizer_eq_of_geometric_borels hconj hnorm hpar hcell hG hi
    (geometricBorelOvergroupCondition_of_structural_statements hpar hconn hext hG hi)

/-- Under the six exact structural statements, lift every normalizer test point
to the original parabolic source, preserving multiplication. -/
def normalizerPointsEquivOfStructuralStatements
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hcell : OppositeCellStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u})
    (hG : IsConnectedReductive G) (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (T : Over (Spec (CommRingCat.of k))) :
    (SubgroupFunctor.range i).normalizer.carrier T ≃* (T ⟶ P.X) := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact (MulEquiv.subgroupCongr
    (congrArg (fun F : SubgroupFunctor G => F.carrier T)
      (parabolicSelfNormalizerStatement_of_structural_statements
        hconj hnorm hpar hcell hconn hext k G hG P i hi))).trans
    ((show (SubgroupFunctor.range i).IsRepresentedBy i from
      ⟨inferInstance, rfl⟩).pointsEquiv T).symm

/-- The returned point composes with the given inclusion to the original normalizer point. -/
theorem normalizerPointsEquivOfStructuralStatements_comp
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    (hpar : ParabolicDynamicStatement.{u}) (hcell : OppositeCellStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hext : ConnectedReductiveFieldExtensionStatement.{u})
    (hG : IsConnectedReductive G) (i : P ⟶ G) (hi : IsParabolicSubgroup i)
    (T : Over (Spec (CommRingCat.of k)))
    (g : (SubgroupFunctor.range i).normalizer.carrier T) :
    normalizerPointsEquivOfStructuralStatements hconj hnorm hpar hcell hconn hext
      hG i hi T g ≫ i.hom.hom = g := by
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  exact (show (SubgroupFunctor.range i).IsRepresentedBy i from
    ⟨inferInstance, rfl⟩).pointsEquiv_symm_comp _

end Langlands.GroupScheme
