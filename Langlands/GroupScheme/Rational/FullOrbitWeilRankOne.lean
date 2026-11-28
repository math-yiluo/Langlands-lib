import Langlands.GroupScheme.Rational.GaloisBorelFaceRankOne
import Langlands.GroupScheme.SimplyConnected.OrbitWeilFactorCover
import Langlands.GroupScheme.Reductive.TitsIndexExistenceProof

/-! # Actual Weil restriction from a full orbit of rank-one factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [IsGalois F E] [IsSepClosed E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]
  [Smooth ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
  [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap F E)).obj G).X.hom]
  (D : SimplyConnectedAlmostSimpleProduct ((GroupScheme.baseChange (algebraBaseMap F E)).obj G))

attribute [local instance] factorStabilizerDescent_isAffine
  factorStabilizerDescent_locallyOfFiniteType

/-- If the chosen orbit is the whole geometric factor set, its actual
Weil inclusion is an isomorphism over the original field. -/
theorem isIso_orbitWeilInclusion_of_full (i : D.Index)
    (h : D.galoisFactorOrbit i = Set.univ) :
    IsIso (D.orbitWeilInclusion i) := by
  let b := algebraBaseMap F E
  let f := D.orbitWeilInclusion i
  let : Surjective b := (fieldExtension_fpqc F E).1
  let : Flat b := (fieldExtension_fpqc F E).2.1
  let : QuasiCompact b := (fieldExtension_fpqc F E).2.2
  let : IsClosedImmersion f.hom.hom.left := D.isClosedSubgroup_orbitWeilInclusion i
  let : Mono f.hom.hom := Over.mono_of_mono_left _
  have htop : SubgroupFunctor.range f = ⊤ := by
    apply le_antisymm (fun _ _ _ => Subgroup.mem_top _)
    apply SubgroupFunctor.le_range_of_baseChange_le b f
    rw [SubgroupFunctor.top_baseChange, D.range_orbitWeilInclusion_baseChange, h]
    intro U x _
    exact (D.mem_range_subproductInclusion_iff Set.univ x).mpr
      (fun j hj => (hj (Set.mem_univ j)).elim)
  let rep : (SubgroupFunctor.range f).IsRepresentedBy f := ⟨inferInstance, rfl⟩
  have hf : SubgroupFunctor.range (𝟙 G) ≤ SubgroupFunctor.range f := by
    rw [htop]
    exact fun _ _ _ => Subgroup.mem_top _
  let g := rep.factorHom (𝟙 G) hf
  have hg : g ≫ f = 𝟙 G := rep.factorHom_comp (𝟙 G) hf
  exact ⟨⟨g, rep.hom_ext (by rw [Category.assoc, hg, Category.comp_id, Category.id_comp]),
    hg⟩⟩

local instance fullOrbitFactorAffine (i : D.Index) : IsAffineHom (D.factor i).X.hom :=
  (D.isAlmostSimple i).isSemisimple.isConnectedReductive.isAffineHom

/-- The selected stabilizer-field model has absolute rank one when the
geometric factor has a one-vertex pinning. The field is retained exactly
in the Weil-restriction isomorphism. -/
theorem exists_rankOneWeilRestriction_of_fullOrbit (i : D.Index)
    (h : D.galoisFactorOrbit i = Set.univ)
    (q : SplitPinning (D.factor i)) (eq : q.base.support ≃ Fin 1) :
    ∃ (A : GroupScheme (Spec (CommRingCat.of (D.factorStabilizerField i : Type u))))
      (_ : IsAffine A.X.left) (_ : IsAffineHom A.X.hom) (_ : LocallyOfFiniteType A.X.hom)
      (d : TitsIndexData A),
      IsSimplyConnected A ∧ IsAbsolutelyAlmostSimple A ∧ Nonempty (d.Vertex ≃ Fin 1) ∧
        Nonempty (AffineWeil.groupScheme F (D.factorStabilizerField i) A ≅ G) := by
  let K := D.factorStabilizerField i
  let A := (D.factorStabilizerDescent i).1
  have hA := D.isSimplyConnected_factorStabilizerDescent i
  let : IsAffineHom A.X.hom := hA.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine A.X.left := inferInstanceAs (IsAffine (D.factorStabilizerDescent i).1.X.left)
  let : LocallyOfFiniteType A.X.hom :=
    inferInstanceAs (LocallyOfFiniteType (D.factorStabilizerDescent i).1.X.hom)
  let : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.tower_top (K := F) K
  obtain ⟨d⟩ := titsIndexExistence K A hA.isSemisimple
  obtain ⟨e⟩ := d.nonempty_vertexEquiv_of_geometricPinning q
    (D.factorStabilizerDescent i).2.2.1
  let w := D.orbitWeilInclusion i
  let hw : IsIso w := D.isIso_orbitWeilInclusion_of_full i h
  let iso := @asIso _ _ _ _ w hw
  exact ⟨A, inferInstance, inferInstance, inferInstance, d, hA,
    D.isAbsolutelyAlmostSimple_factorStabilizerDescent_of_isSepClosed i,
    ⟨e.trans eq⟩, ⟨iso⟩⟩

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
