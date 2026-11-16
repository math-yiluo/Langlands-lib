import Langlands.GroupScheme.RelativeLevi.BaseChangeGeometry
import Langlands.GroupScheme.RelativeLevi.ModuliFunctorConstruction

/-! # Reducing the actual Levi presheaf to a field-extension assertion -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable
  (hfield : ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [IsAlgClosed k] [IsAlgClosed K]
    (P U : GroupScheme (Spec (CommRingCat.of k))) (r : U ⟶ P),
    Smooth P.X.hom → IsUnipotentRadical r →
      IsUnipotentRadical
        ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map r))

variable {S T : Scheme.{u}} {P U L : GroupScheme S}

include hfield

/-- The stated field-extension assertion preserves relative radicals in a smooth
ambient group. The field assertion remains an explicit premise. -/
theorem IsRelativeUnipotentRadical.baseChange_of_smooth_field_extension
    {r : U ⟶ P} (hr : IsRelativeUnipotentRadical r)
    (hP : Smooth P.X.hom) (b : T ⟶ S) :
    IsRelativeUnipotentRadical ((baseChange b).map r) := by
  apply hr.baseChange_of_geometric_extension b
  intro t
  let := RelativeLevi.residueFieldAlgebra b t
  let : Algebra (AlgebraicClosure (S.residueField (b t)))
      (AlgebraicClosure (T.residueField t)) :=
    (algebraicClosureEmbedding (S.residueField (b t))
      (T.residueField t)).toRingHom.toAlgebra
  have hgeom : Smooth (Langlands.GroupScheme.geometricFiber P (b t)).X.hom := by
    let : Smooth P.X.hom := hP
    change Smooth (pullback.snd P.X.hom (geometricPoint S (b t)))
    infer_instance
  exact hfield _ _ (Langlands.GroupScheme.geometricFiber P (b t))
    (Langlands.GroupScheme.geometricFiber U (b t))
    (RelativeLevi.geometricFiberHom r (b t)) hgeom (hr.geometricFiber (b t))

/-- Every actual relative Levi pulls back if the stated smooth-ambient field
assertion holds; the Levi witness itself supplies ambient smoothness. -/
theorem IsRelativeLeviSubgroup.baseChange_of_field_extension
    {l : L ⟶ P} (hl : IsRelativeLeviSubgroup l) (b : T ⟶ S) :
    IsRelativeLeviSubgroup ((baseChange b).map l) := by
  apply hl.baseChange_of_radical_preservation b
  intro V r hr
  exact hr.baseChange_of_smooth_field_extension hfield hl.smooth_ambient b

namespace RelativeLevi

/-- The field assertion implies closure of the actual Levi images under the
existing restriction maps, including the actual ambient pullback comparison. -/
theorem restrictionStable_of_field_extension (P : GroupScheme S) :
    RestrictionStable P := by
  intro M N a F
  obtain ⟨K, l, hl, hF⟩ := F.exists_presentation
  refine ⟨(baseChange a.left).obj K, TorusSubgroupModuli.familyHom l a, ?_, ?_⟩
  · exact (hl.baseChange_of_field_extension hfield a.left).comp_iso
      (Descent.pullbackComparison M.hom a.left N.hom (Over.w a) P)
  · rw [← hF, restrictImage_range]

/-- The actual Levi presheaf from the sufficient field-extension assertion.
This construction retains the field assertion as a parameter. -/
def moduliFunctorOfFieldExtension (P : GroupScheme S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  moduliFunctorOfStability (restrictionStable_of_field_extension hfield P)

end RelativeLevi
end Langlands.GroupScheme
