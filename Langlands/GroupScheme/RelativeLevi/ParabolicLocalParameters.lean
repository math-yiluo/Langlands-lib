import Langlands.GroupScheme.RelativeLevi.ParabolicUniformFieldTypes
import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleConjugacyProof
import Langlands.GroupScheme.ConjugacyBaseChange

/-! # Local parameters from uniform parabolic field types -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.ParabolicSubgroupModuli

open SubgroupFunctor TorusSubgroupModuli

section Transport

variable {S : Scheme.{u}} {G H P Q : GroupScheme S}

/-- Rational conjugacy of actual subgroup ranges is invariant under ambient
group-scheme isomorphisms. -/
theorem exists_range_innerIso_comp_iso_iff (i : P ⟶ H) (j : Q ⟶ H) (e : H ≅ G) :
    (∃ g : Over.mk (𝟙 S) ⟶ H.X,
      range (i ≫ (H.innerIso g).hom) = range j) ↔
    ∃ g : Over.mk (𝟙 S) ⟶ G.X,
      range ((i ≫ e.hom) ≫ (G.innerIso g).hom) = range (j ≫ e.hom) := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g ≫ e.hom.hom.hom, ?_⟩
    have he := (range_comp_iso_eq_iff _ _ e).mpr hg
    rwa [Category.assoc, innerIso_hom_comp, ← Category.assoc] at he
  · rintro ⟨g, hg⟩
    refine ⟨g ≫ e.inv.hom.hom, ?_⟩
    have he := (range_comp_iso_eq_iff _ _ e.symm).mpr hg
    simpa only [Category.assoc, Iso.symm_hom, innerIso_hom_comp,
      Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using he

variable {S' : Scheme.{u}} {I : Type u} {P : I → GroupScheme S}
    {G : GroupScheme S} (j : ∀ a, P a ⟶ G)

set_option maxHeartbeats 800000 in
/-- Uniform rational field-conjugacy types persist under arbitrary base change. -/
theorem HasUniformParabolicFieldTypes.baseChange
    (htypes : HasUniformParabolicFieldTypes j) (b : S' ⟶ S) :
    HasUniformParabolicFieldTypes (fun a => (GroupScheme.baseChange b).map (j a)) := by
  intro k _ x Q i hi
  let e := Descent.pullbackComparison b x (x ≫ b) rfl G
  have hiff (a : I) :
      (∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          ((GroupScheme.baseChange x).obj ((GroupScheme.baseChange b).obj G)).X,
        range (i ≫ (((GroupScheme.baseChange x).obj
          ((GroupScheme.baseChange b).obj G)).innerIso g).hom) =
          range ((GroupScheme.baseChange x).map ((GroupScheme.baseChange b).map (j a)))) ↔
      ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
          ((GroupScheme.baseChange (x ≫ b)).obj G).X,
        range ((i ≫ e.hom) ≫
          (((GroupScheme.baseChange (x ≫ b)).obj G).innerIso g).hom) =
          range ((GroupScheme.baseChange (x ≫ b)).map (j a)) := by
    rw [exists_range_innerIso_comp_iso_iff i _ e]
    simp only [e, Descent.pullbackComparison_naturality, range_iso_comp]
  obtain ⟨a, ha, huniq⟩ := htypes k (x ≫ b) Q (i ≫ e.hom) (hi.comp_iso e)
  exact ⟨a, (hiff a).mpr ha, fun c hc => huniq c ((hiff c).mp hc)⟩

/-- Inverting an actual rational conjugator reverses the range equality. -/
theorem range_innerIso_inv_of_eq {H P Q : GroupScheme S} (i : P ⟶ H) (j : Q ⟶ H)
    (g : Over.mk (𝟙 S) ⟶ H.X)
    (h : range (i ≫ (H.innerIso g).hom) = range j) :
    range (j ≫ (H.innerIso g⁻¹).hom) = range i := by
  have he := (range_comp_iso_eq_iff _ _ (H.innerIso g).symm).mpr h
  simpa only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id,
    innerIso_inv_hom] using he.symm

set_option maxHeartbeats 800000 in
/-- Uniform field types identify an actual inclusion with one representative
on an etale neighbourhood of any point. -/
theorem exists_etale_conjugacy_of_fieldTypes (hG : IsReductive G)
    (hj : ∀ a, IsRelativeParabolicSubgroup (j a))
    (htypes : HasUniformParabolicFieldTypes j) {Q : GroupScheme S}
    (i : Q ⟶ G) (hi : IsRelativeParabolicSubgroup i) (s : S) :
    ∃ (a : I) (U : Scheme.{u}) (f : U ⟶ S), Etale f ∧
      (∃ u : U, f u = s) ∧
      ∃ g : Over.mk (𝟙 U) ⟶ ((GroupScheme.baseChange f).obj G).X,
        range ((GroupScheme.baseChange f).map (j a) ≫
          (((GroupScheme.baseChange f).obj G).innerIso g).hom) =
          range ((GroupScheme.baseChange f).map i) := by
  let x := S.fromSpecResidueField s
  obtain ⟨a, ⟨g, hg⟩, _⟩ := htypes (S.residueField s) x _
    ((GroupScheme.baseChange x).map i) (hi.isParabolicSubgroup_baseChange hG x)
  exact ⟨a, relativeParabolicEtaleLocalConjugacyStatement S G _ Q (j a) i s
    hG (hj a) hi ⟨g⁻¹, range_innerIso_inv_of_eq _ _ g hg⟩⟩

/-- Transport an iterated-pullback conjugator to an actual parameter of the
original group. -/
def parameterOfIteratedConjugator {M T : Over S} (f : T ⟶ M)
    (g : Over.mk (𝟙 T.left) ⟶
      ((GroupScheme.baseChange f.left).obj ((GroupScheme.baseChange M.hom).obj G)).X) :
    T ⟶ G.X :=
  baseChangeBasePointsEquiv T.hom G
    (g ≫ (Descent.pullbackComparison M.hom f.left T.hom (Over.w f) G).hom.hom.hom)

set_option maxHeartbeats 800000 in
/-- The transported group parameter evaluates the given conjugacy equation. -/
theorem range_conjugateFamily_parameterOfIteratedConjugator
    {M T : Over S} {Q : GroupScheme M.left} (a : I)
    (i : Q ⟶ (GroupScheme.baseChange M.hom).obj G) (f : T ⟶ M)
    (g : Over.mk (𝟙 T.left) ⟶
      ((GroupScheme.baseChange f.left).obj ((GroupScheme.baseChange M.hom).obj G)).X)
    (h : range ((GroupScheme.baseChange f.left).map
        ((GroupScheme.baseChange M.hom).map (j a)) ≫
        (((GroupScheme.baseChange f.left).obj
          ((GroupScheme.baseChange M.hom).obj G)).innerIso g).hom) =
      range ((GroupScheme.baseChange f.left).map i)) :
    range (conjugateFamily (j a) (parameterOfIteratedConjugator f g)) = evaluate i f := by
  let e := Descent.pullbackComparison M.hom f.left T.hom (Over.w f) G
  have he := (range_comp_iso_eq_iff _ _ e).mpr h
  rw [Category.assoc, innerIso_hom_comp, ← Category.assoc,
    Descent.pullbackComparison_naturality, Category.assoc, range_iso_comp] at he
  simpa only [conjugateFamily, conjugatePullback, parameterOfIteratedConjugator,
    MulEquiv.symm_apply_apply, evaluate, familyHom, e] using he

end Transport

section Parameters

variable {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {I : Type u} {P : I → GroupScheme S} (j : ∀ a, P a ⟶ G)
    (hj : ∀ a, IsRelativeParabolicSubgroup (j a))

/-- An actual etale-local group-valued parameter of a supplied parabolic family
near a specified point of its test scheme. -/
structure EtaleParabolicParameter (T : Over S)
    (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G)) (t : T.left) where
  neighbourhood : Over S
  projection : neighbourhood ⟶ T
  etale : Etale projection.left
  point : neighbourhood.left
  point_over : projection.left point = t
  index : I
  lift : neighbourhood ⟶ G.X
  evaluates : conjugateParabolic hG (j index) (hj index) lift = restrict hG projection F

set_option maxHeartbeats 800000 in
/-- Uniform field types and the published etale-local conjugacy theorem give
an actual local parameter near every test-scheme point. -/
theorem nonempty_etaleParabolicParameter
    (htypes : HasUniformParabolicFieldTypes j) (T : Over S)
    (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G)) (t : T.left) :
    Nonempty (EtaleParabolicParameter hG j hj T F t) := by
  let r := parabolicRepresentative F
  obtain ⟨a, U, f, hf, ⟨u, hu⟩, g, hg⟩ := exists_etale_conjugacy_of_fieldTypes
    (fun a => (GroupScheme.baseChange T.hom).map (j a)) (hG.baseChange T.hom)
    (fun a => (hj a).baseChange hG T.hom) (HasUniformParabolicFieldTypes.baseChange j htypes T.hom)
    r.hom r.parabolic t
  let V : Over S := Over.mk (f ≫ T.hom)
  let q : V ⟶ T := Over.homMk f rfl
  let v : V ⟶ G.X := parameterOfIteratedConjugator q g
  refine ⟨⟨V, q, hf, u, hu, a, v, ?_⟩⟩
  apply Subtype.ext
  rw [restrict_eq_evaluate hG F r.hom r.represents.2 q]
  exact range_conjugateFamily_parameterOfIteratedConjugator j a r.hom q g hg

/-- Choose an actual etale-local group-valued parameter. -/
def etaleParabolicParameter (htypes : HasUniformParabolicFieldTypes j)
    (T : Over S) (F : ParabolicSubgroup ((GroupScheme.baseChange T.hom).obj G))
    (t : T.left) : EtaleParabolicParameter hG j hj T F t :=
  Classical.choice (nonempty_etaleParabolicParameter hG j hj htypes T F t)

end Parameters

end Langlands.GroupScheme.ParabolicSubgroupModuli
