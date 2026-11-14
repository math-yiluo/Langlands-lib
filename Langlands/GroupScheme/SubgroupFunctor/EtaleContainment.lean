import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Torus.IsomorphismLocusEtale

/-! # Descent of subgroup containment to an etale image -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SubgroupFunctor

variable {S S' S'' : Scheme.{u}} {G P Q : GroupScheme S}

/-- Containment in a monomorphically represented subgroup descends along
a surjective flat morphism locally of finite presentation. -/
theorem le_range_of_fppf_baseChange_le (b : S' ⟶ S)
    [LocallyOfFinitePresentation b] [Flat b] [Surjective b]
    {F : SubgroupFunctor G} (i : P ⟶ G) [Mono i.hom.hom]
    (h : F.baseChange b ≤ (range i).baseChange b) : F ≤ range i := by
  intro U x hx
  let V : Over S' := (Over.pullback b).obj U
  let q : (Over.map b).obj V ⟶ U :=
    Over.homMk (pullback.fst U.hom b) pullback.condition
  have : EffectiveEpi q.left := by
    change EffectiveEpi (pullback.fst U.hom b)
    infer_instance
  apply mem_range_of_comp_mem_range i q
  let x' := (baseChangePointsEquiv b G V).symm (q ≫ x)
  have hx' : x' ∈ (F.baseChange b).carrier V := by
    rw [mem_baseChange]
    change baseChangePointsEquiv b G V
      ((baseChangePointsEquiv b G V).symm (q ≫ x)) ∈ F.carrier _
    rw [MulEquiv.apply_symm_apply]
    exact F.comp_mem q hx
  have hi := h V hx'
  rw [mem_baseChange] at hi
  simpa only [x', MulEquiv.apply_symm_apply] using hi

/-- The canonical comparison of direct and iterated base change preserves
and reflects containment of the actual subgroup ranges. -/
theorem range_le_comp_baseChange_iff
    (b : S' ⟶ S) (c : S'' ⟶ S') (j : Q ⟶ G) (i : P ⟶ G) :
    range ((GroupScheme.baseChange (c ≫ b)).map j) ≤ range ((GroupScheme.baseChange (c ≫ b)).map i) ↔
      range ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map j)) ≤
        range ((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)) := by
  let eP := Descent.pullbackComparison b c (c ≫ b) rfl P
  let eQ := Descent.pullbackComparison b c (c ≫ b) rfl Q
  let eG := Descent.pullbackComparison b c (c ≫ b) rfl G
  have hi := Descent.pullbackComparison_naturality b c (c ≫ b) rfl i
  have hj := Descent.pullbackComparison_naturality b c (c ≫ b) rfl j
  symm
  calc
    _ ↔ range (((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map j)) ≫ eG.hom) ≤
        range (((GroupScheme.baseChange c).map ((GroupScheme.baseChange b).map i)) ≫ eG.hom) :=
      (range_comp_iso_le_iff _ _ eG).symm
    _ ↔ range (eQ.hom ≫ (GroupScheme.baseChange (c ≫ b)).map j) ≤
        range (eP.hom ≫ (GroupScheme.baseChange (c ≫ b)).map i) := by rw [hj, hi]
    _ ↔ _ := by rw [range_iso_comp, range_iso_comp]

/-- Containment after an etale base change descends to its open image.
Only the inclusion on the right must be monomorphic. -/
theorem range_le_etaleImage (b : S' ⟶ S) [Etale b]
    (j : Q ⟶ G) (i : P ⟶ G) [Mono i.hom.hom]
    (h : range ((GroupScheme.baseChange b).map j) ≤ range ((GroupScheme.baseChange b).map i)) :
    range ((GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).map j) ≤
      range ((GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).map i) := by
  let V := TorusIsomorphismLocus.etaleImage b
  let b' : S' ⟶ V := IsOpenImmersion.lift V.ι b (by simp [V,
    TorusIsomorphismLocus.etaleImage])
  have hb' : b' ≫ V.ι = b := IsOpenImmersion.lift_fac _ _ _
  have : Surjective b' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by
      apply V.ι.injective
      change (b' ≫ V.ι) y = x
      rw [hb']
      exact hy⟩⟩
  have : Etale (b' ≫ V.ι) := by rw [hb']; infer_instance
  have : Etale b' := Etale.of_comp b' V.ι
  have : Mono ((GroupScheme.baseChange V.ι).map i).hom.hom := by
    change Mono ((Over.pullback V.ι).map i.hom.hom)
    infer_instance
  apply le_range_of_fppf_baseChange_le b' ((GroupScheme.baseChange V.ι).map i)
  rw [← range_baseChangeHom, ← range_baseChangeHom]
  apply (range_le_comp_baseChange_iff V.ι b' j i).mp
  rwa [hb']

/-- The actual homomorphism of the two subgroup presentations over the open
etale image, obtained by descent of their range containment. -/
def factorOnEtaleImage (b : S' ⟶ S) [Etale b]
    (j : Q ⟶ G) (i : P ⟶ G) [Mono j.hom.hom] [Mono i.hom.hom]
    (h : range ((GroupScheme.baseChange b).map j) ≤ range ((GroupScheme.baseChange b).map i)) :
    (GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).obj Q ⟶
      (GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).obj P := by
  let V := TorusIsomorphismLocus.etaleImage b
  have : Mono ((GroupScheme.baseChange V.ι).map j).hom.hom := by
    change Mono ((Over.pullback V.ι).map j.hom.hom)
    infer_instance
  have : Mono ((GroupScheme.baseChange V.ι).map i).hom.hom := by
    change Mono ((Over.pullback V.ι).map i.hom.hom)
    infer_instance
  exact factorOfRangeLE (range_le_etaleImage b j i h)

/-- The descended homomorphism commutes with the actual subgroup inclusions. -/
theorem factorOnEtaleImage_comp (b : S' ⟶ S) [Etale b]
    (j : Q ⟶ G) (i : P ⟶ G) [Mono j.hom.hom] [Mono i.hom.hom]
    (h : range ((GroupScheme.baseChange b).map j) ≤ range ((GroupScheme.baseChange b).map i)) :
    factorOnEtaleImage b j i h ≫
        (GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).map i =
      (GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).map j := by
  have : Mono ((GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).map j).hom.hom := by
    change Mono ((Over.pullback (TorusIsomorphismLocus.etaleImage b).ι).map j.hom.hom)
    infer_instance
  have : Mono ((GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage b).ι).map i).hom.hom := by
    change Mono ((Over.pullback (TorusIsomorphismLocus.etaleImage b).ι).map i.hom.hom)
    infer_instance
  unfold factorOnEtaleImage
  exact factorOfRangeLE_comp _

/-- A point of an etale containment neighbourhood determines an open
containment neighbourhood of its image in the original base. -/
theorem exists_open_range_le_of_etale (b : S' ⟶ S) [Etale b]
    (j : Q ⟶ G) (i : P ⟶ G) [Mono i.hom.hom] (u : S')
    (h : range ((GroupScheme.baseChange b).map j) ≤ range ((GroupScheme.baseChange b).map i)) :
    ∃ V : S.Opens, b u ∈ V ∧
      range ((GroupScheme.baseChange V.ι).map j) ≤ range ((GroupScheme.baseChange V.ι).map i) :=
  ⟨TorusIsomorphismLocus.etaleImage b, ⟨u, rfl⟩, range_le_etaleImage b j i h⟩

end Langlands.GroupScheme.SubgroupFunctor
