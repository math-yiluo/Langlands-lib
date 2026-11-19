import Langlands.GroupScheme.SimplyConnected.TypeD4KernelLeafWeightInflation
import Langlands.GroupScheme.Rational.FundamentalRepresentationsAssembly

/-! # The actual Tits class of a D4 anisotropic-kernel leaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {d : TitsIndexData G} (p : d.AnisotropicKernelIndex) (hsc : IsSimplyConnected G)

variable (q : d.Vertex ≃ Fin 4)
  (hq : d.IsNumberingOf (CartanMatrix.D 4) (fun i => i.val = 1) q)

variable {E : IntermediateField k (SeparableClosure k)}

local instance extendedKernelFiniteType :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k E)).obj p.kernel).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd p.kernel.X.hom _)
  infer_instance

variable (S : GaloisPinningData.ScalarExtension (E := E) p.index.pinning)

/-- The fundamental weight at an original kernel vertex, transported to the
pinning with the same separable closure after extension of the ground field. -/
def transportedKernelFundamentalWeight (a : p.index.Vertex) :
    characterLattice S.pinning.toSplitPinning.torus :=
  S.rootEquiv.weightEquiv (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a)

/-- A based scalar-extension equivalence preserves dominance of the kernel
fundamental weight. -/
theorem transportedKernelFundamentalWeight_dominant (a : p.index.Vertex) :
    S.pinning.toSplitPinning.IsDominantWeight (p.transportedKernelFundamentalWeight hsc S a) := by
  have hdom := p.index.pinning.toSplitPinning.fundamentalWeightBasis_isDominant
    (p.index.pinning_corootSpan_eq_top (p.isSimplyConnected hsc)) a
  intro b
  obtain ⟨c, rfl⟩ := (S.rootEquiv.indexEquiv.subtypeEquiv S.base_eq).surjective b
  change 0 ≤ S.pinning.toSplitPinning.rootDatum.coroot' (S.rootEquiv.indexEquiv c.val)
    (S.rootEquiv.weightEquiv (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a))
  rw [S.rootEquiv.coroot'_weightEquiv c.val]
  exact hdom c

private theorem kernelVertex_fixed_of_leafField (a : p.index.Vertex)
    (hE : E = d.starVertexField (p.comparison.vertexEquiv a).val)
    (σ : SeparableClosure k ≃ₐ[E] SeparableClosure k) :
    p.index.star (σ.restrictScalars k) a = a := by
  have hfix : ∀ x ∈ d.starVertexField (p.comparison.vertexEquiv a).val,
      (σ.restrictScalars k) x = x := by
    intro x hx
    have hxE : x ∈ E := hE ▸ hx
    exact σ.commutes (⟨x, hxE⟩ : E)
  have h := (d.fixes_starVertexField_iff _ (σ.restrictScalars k)).mp hfix
  apply p.comparison.vertexEquiv.injective
  apply Subtype.ext
  exact (congrArg Subtype.val (p.comparison.vertexEquiv_star (σ.restrictScalars k) a)).trans h

/-- The transported kernel weight is fixed by the whole relative Galois group
over the field of the corresponding ambient vertex. -/
theorem transportedKernelFundamentalWeight_fixed (a : p.index.Vertex)
    (hE : E = d.starVertexField (p.comparison.vertexEquiv a).val) :
    S.pinning.IsStarFixedWeight (p.transportedKernelFundamentalWeight hsc S a) := by
  intro σ
  have h := congrArg
    (fun f => f.weightEquiv (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a))
    (S.star_eq σ)
  change S.rootEquiv.weightEquiv ((p.index.pinning.starAction (σ.restrictScalars k)).val.weightEquiv
    (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc) a)) =
    (S.pinning.starAction σ).val.weightEquiv (p.transportedKernelFundamentalWeight hsc S a) at h
  have hweight := p.index.absoluteFundamentalCharacter_star (p.isSimplyConnected hsc)
    (σ.restrictScalars k) a
  have hfixed := hweight.trans
    (congrArg (p.index.absoluteFundamentalCharacter (p.isSimplyConnected hsc))
      (p.kernelVertex_fixed_of_leafField a hE σ))
  exact h.symm.trans (congrArg S.rootEquiv.weightEquiv hfixed)

variable {H : GroupScheme (Spec (CommRingCat.of E))}
  [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
  {j : H ⟶ (GroupScheme.baseChange (algebraBaseMap k E)).obj p.kernel}

include hq in
/-- The dominant Tits class of the transported original kernel leaf weight
equals the actual class for its component pinning and projection. -/
theorem transportedKernelFundamentalWeight_titsClass_D4 (a : p.index.Vertex)
    (C : p.index.ComponentPinningWithProjection E a S j)
    (hE : E = d.starVertexField (p.comparison.vertexEquiv a).val)
    (b : C.comparison.pinning.base.support)
    (hspan : C.comparison.pinning.rootDatum.corootSpan ℤ = ⊤)
    (hinflate : C.projection.weightInflation
        (Langlands.RootDatum.fundamentalWeightBasis C.comparison.pinning.rootDatum
          C.comparison.pinning.base hspan b) = p.transportedKernelFundamentalWeight hsc S a) :
    let Q := C.comparison.pinning
    let μ := Langlands.RootDatum.fundamentalWeightBasis Q.rootDatum Q.base hspan b
    ∃ (hdom : Q.toSplitPinning.IsDominantWeight μ) (hfix : Q.IsStarFixedWeight μ),
      S.pinning.dominantTitsClass _
        (p.transportedKernelFundamentalWeight_dominant hsc S a)
        (p.transportedKernelFundamentalWeight_fixed hsc S a hE) =
      Q.dominantTitsClass μ hdom hfix := by
  let Q := C.comparison.pinning
  let μ := Langlands.RootDatum.fundamentalWeightBasis Q.rootDatum Q.base hspan b
  have hvertex (v : Q.base.support) : (C.comparison.vertices v).val = a :=
    ((p.cartanConnected_iff_eq_D4_central_mark q hq _ _).mp
      (C.comparison.vertices v).property).symm
  have hv (v : Q.base.support) : v = b := by
    apply C.comparison.vertices.injective
    apply Subtype.ext
    exact (hvertex v).trans (hvertex b).symm
  have hdom : Q.toSplitPinning.IsDominantWeight μ :=
    Q.toSplitPinning.fundamentalWeightBasis_isDominant hspan b
  have hfix : Q.IsStarFixedWeight μ := by
    intro σ
    exact Langlands.RootDatum.fundamentalWeightBasis_fixed_of_based
      Q.rootDatum Q.base hspan (Q.starAction σ).val (Q.starAction σ).property b
      (congrArg Subtype.val (hv (Q.simpleStar σ b)))
  have hweight : C.projection.weightInflation μ =
      p.transportedKernelFundamentalWeight hsc S a := hinflate
  refine ⟨hdom, hfix, ?_⟩
  have hpdom : S.pinning.toSplitPinning.IsDominantWeight (C.projection.weightInflation μ) :=
    hweight.symm ▸ p.transportedKernelFundamentalWeight_dominant hsc S a
  have hpfix : S.pinning.IsStarFixedWeight (C.projection.weightInflation μ) :=
    hweight.symm ▸ p.transportedKernelFundamentalWeight_fixed hsc S a hE
  simpa only [hweight] using C.projection.dominantTitsClass_inflation hdom hfix hpdom hpfix

local instance leafClassKernelSmooth : Smooth p.kernel.X.hom :=
  p.index.isSemisimple.isConnectedReductive.smooth

local instance leafClassGeometricKernelSmooth :
    Smooth ((GroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj
      p.kernel).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd p.kernel.X.hom _)
  infer_instance

attribute [local instance] SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_isAffine
  SimplyConnectedAlmostSimpleProduct.factorStabilizerDescent_locallyOfFiniteType

include hsc in
private theorem leafClassGeometricallySimplyConnected :
    IsSimplyConnected ((GroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj p.kernel) :=
  isSimplyConnectedFieldExtension k (SeparableClosure k) p.kernel (p.isSimplyConnected hsc)

private abbrev leafClassGeometricProduct := (p.leafClassGeometricallySimplyConnected hsc).almostSimpleProduct

private abbrev leafClassFactorIndex (a : p.index.Vertex) :=
  p.index.geometricFactorIndex (p.leafClassGeometricProduct hsc)
    (p.leafClassGeometricallySimplyConnected hsc).isSemisimple a

/-- The selected simply connected factor gives a full integral coroot span
for its compatible pinning over the original separable closure. -/
theorem descendedComponentProjection_corootSpan_eq_top (a : p.index.Vertex) :
    (p.descendedComponentProjection hsc a).comparison.pinning.rootDatum.corootSpan ℤ = ⊤ :=
  (p.descendedComponentProjection hsc a).comparison.pinning.corootSpan_eq_top_of_simplyConnected
    ((p.leafClassGeometricProduct hsc).isSimplyConnected_factorStabilizerDescent
      (p.leafClassFactorIndex hsc a))

include hq in
/-- The actual dominant Tits classes agree over the exact D4 leaf field for
the selected factor and the extended original kernel. -/
theorem transportedKernelFundamentalWeight_titsClass_descendedComponent_D4
    (a : p.index.Vertex)
    (b : (p.descendedComponentProjection hsc a).comparison.pinning.base.support) :
    type_of% (p.transportedKernelFundamentalWeight_titsClass_D4 hsc q hq _ a
      (p.descendedComponentProjection hsc a) (p.componentField_eq_starVertexField_D4 hsc q hq a) b
      (p.descendedComponentProjection_corootSpan_eq_top hsc a)
      (p.weightInflation_descendedComponent_D4 hsc q hq a b _)) :=
  p.transportedKernelFundamentalWeight_titsClass_D4 hsc q hq _ a
    (p.descendedComponentProjection hsc a) (p.componentField_eq_starVertexField_D4 hsc q hq a) b
    (p.descendedComponentProjection_corootSpan_eq_top hsc a)
    (p.weightInflation_descendedComponent_D4 hsc q hq a b _)

end Langlands.GroupScheme.TitsIndexData.AnisotropicKernelIndex
