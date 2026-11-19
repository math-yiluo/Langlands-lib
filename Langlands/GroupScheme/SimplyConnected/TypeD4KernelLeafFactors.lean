import Langlands.GroupScheme.SimplyConnected.TypeD4KernelWeights
import Langlands.GroupScheme.SimplyConnected.TypeD4CubicLeafField
import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.SimplyConnected.DescendedComponentPinning

/-! # Actual descended leaf factors of the centrally marked D4 kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} (p : d.AnisotropicKernelIndex)

private theorem kernelGeometricSimplyConnected (hsc : IsSimplyConnected G) :
    IsSimplyConnected ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj p.kernel) :=
  isSimplyConnectedFieldExtension k (SeparableClosure k) p.kernel (p.isSimplyConnected hsc)

variable (hsc : IsSimplyConnected G)

private abbrev geometricProduct := (p.kernelGeometricSimplyConnected hsc).almostSimpleProduct

private abbrev geometricSemisimple := (p.kernelGeometricSimplyConnected hsc).isSemisimple

private abbrev geometricFactor (a : p.index.Vertex) :=
  p.index.geometricFactorIndex (p.geometricProduct hsc) (p.geometricSemisimple hsc) a

local instance kernelSmooth : Smooth p.kernel.X.hom :=
  p.index.isSemisimple.isConnectedReductive.smooth

local instance geometricKernelSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
      p.kernel).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd p.kernel.X.hom _)
  infer_instance

/-- The field of the actual geometric factor of the anisotropic kernel containing
this simple root, as an intermediate field in the original separable closure. -/
def componentField (a : p.index.Vertex) : IntermediateField k (SeparableClosure k) :=
  (p.geometricProduct hsc).factorStabilizerField (p.geometricFactor hsc a)

/-- Select the full actual component factor of the anisotropic kernel from
its geometric normal factor and the pinning descended to its stabilizer field. -/
def descendedComponentFactor (a : p.index.Vertex) : p.index.ComponentFactor a := by
  let D := p.geometricProduct hsc
  let hD := p.geometricSemisimple hsc
  exact p.index.componentFactorOfPinningComparison a D hD (p.isSimplyConnected hsc)
    (p.index.descendedComponentPinning D hD (p.isSimplyConnected hsc) a)

/-- The actual component model is over the selected geometric stabilizer field. -/
theorem descendedComponentFactor_extension (a : p.index.Vertex) :
    (p.descendedComponentFactor hsc a).extension = (p.componentField hsc a : Type u) :=
  rfl

/-- The inclusion of the selected factor in the original kernel extended to
the component field. -/
def descendedComponentInclusion (a : p.index.Vertex) :
    (p.descendedComponentFactor hsc a).factor ⟶ (GroupScheme.baseChange
      (algebraBaseMap k (p.componentField hsc a))).obj p.kernel :=
  ((p.geometricProduct hsc).factorStabilizerDescent (p.geometricFactor hsc a)).2.1

variable (q : d.Vertex ≃ Fin 4)
  (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)

include hq in
/-- A component of the centrally marked D4 kernel is defined over the exact
star vertex field of the corresponding ambient leaf. -/
theorem componentField_eq_starVertexField_D4 (a : p.index.Vertex) :
    p.componentField hsc a = d.starVertexField (p.comparison.vertexEquiv a).val := by
  change IntermediateField.fixedField
    ((p.geometricProduct hsc).galoisFactorStabilizer (p.geometricFactor hsc a)) = _
  have hstab := p.index.cartanComponentStabilizer_eq_geometricFactorStabilizer
    (p.geometricProduct hsc) (p.geometricSemisimple hsc) a
  rw [← hstab]
  apply congrArg IntermediateField.fixedField
  ext σ
  rw [p.index.mem_cartanComponentStabilizer, d.mem_starVertexStabilizer,
    p.cartanConnected_iff_eq_D4_central_mark q hq]
  have hstar := congrArg Subtype.val (p.comparison.vertexEquiv_star σ a)
  change (p.comparison.vertexEquiv (p.index.star σ a)).val =
    d.star σ (p.comparison.vertexEquiv a).val at hstar
  rw [← hstar]
  exact ⟨fun h => congrArg (fun b => (p.comparison.vertexEquiv b).val) h.symm,
    fun h => (p.comparison.vertexEquiv.injective (Subtype.ext h)).symm⟩

include hq in
/-- All the simple vertices of one selected factor belong to its one leaf. -/
theorem descendedComponentFactor_vertex_eq_D4 (a : p.index.Vertex)
    (b : (p.descendedComponentFactor hsc a).index.Vertex) :
    ((p.descendedComponentFactor hsc a).vertexEquiv b).val = a :=
  ((p.cartanConnected_iff_eq_D4_central_mark q hq _ _).mp
    ((p.descendedComponentFactor hsc a).vertexEquiv b).property).symm

include hq in
/-- The full actual index of the selected leaf factor is inner A1. -/
theorem descendedComponentFactor_hasInnerTypeA_one_D4 (a : p.index.Vertex) :
    (p.descendedComponentFactor hsc a).index.HasInnerTypeA 1 := by
  let F := p.descendedComponentFactor hsc a
  let e : F.index.Vertex ≃ Fin 1 := F.vertexEquiv.trans
    { toFun := fun _ => 0
      invFun := fun _ => ⟨a, p.index.cartanConnected_refl a⟩
      left_inv := fun b => Subtype.ext
        ((p.cartanConnected_iff_eq_D4_central_mark q hq _ _).mp b.property)
      right_inv := fun _ => Subsingleton.elim _ _ }
  refine ⟨by decide, ⟨e, ?_⟩, F.index.starIsTrivial_of_equiv_fin_one e⟩
  intro b c
  rw [← F.cartan_eq, p.descendedComponentFactor_vertex_eq_D4 hsc q hq a b,
    p.descendedComponentFactor_vertex_eq_D4 hsc q hq a c,
    p.cartan_D4_central_mark q hq]
  rw [Subsingleton.elim (e b) 0, Subsingleton.elim (e c) 0]
  simp [CartanMatrix.A]

include hq in
/-- The actual selected leaf factor has a norm-one presentation by a central
quaternion division algebra over its exact geometric stabilizer field. -/
theorem descendedComponentFactor_divisionModel_D4 (a : p.index.Vertex) :
    HasCentralDivisionNormOnePresentation (p.descendedComponentFactor hsc a).factor 2 := by
  let F := p.descendedComponentFactor hsc a
  exact centralDivisionNormOnePresentation_of_anisotropic_innerTypeA F.index 1
    F.simplyConnected (F.anisotropic p.anisotropic)
    (p.descendedComponentFactor_hasInnerTypeA_one_D4 hsc q hq a)

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
