import Langlands.GroupScheme.SimplyConnected.SplitCriterionStatement
import Langlands.GroupScheme.CentralIsogeny.SplitTorusLiftStatement
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumStatement
import Langlands.GroupScheme.Reductive.RootDatumStatement

/-! # Reduction of the coroot criterion to torus lifting and root-datum morphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace SplitCorootCriterion

variable {ι ι₂ R M N M₂ N₂ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
  {P : RootPairing ι R M N} {Q : RootPairing ι₂ R M₂ N₂}

/-- The coweight map of a morphism of root pairings `P ⟶ Q` is surjective when the coroots of
`P` span the coweight space of `P`. -/
theorem surjective_coweightMap (f : RootPairing.Hom P Q) (h : P.corootSpan R = ⊤) :
    Function.Surjective f.coweightMap := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← h]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨j, rfl⟩
  refine ⟨Q.coroot (f.indexEquiv j), ?_⟩
  rw [RootPairing.Hom.coroot_coweightMap_apply, Equiv.symm_apply_apply]

/-- If the coweight map of a morphism of root pairings is bijective, its weight map is
surjective: the weight map is the transpose of the coweight map under the perfect pairings. -/
theorem surjective_weightMap (f : RootPairing.Hom P Q) (h : Function.Bijective f.coweightMap) :
    Function.Surjective f.weightMap := by
  intro y
  let e := LinearEquiv.ofBijective f.coweightMap h
  refine ⟨P.toPerfPair.symm (Q.toPerfPair y ∘ₗ e.symm.toLinearMap), Q.toPerfPair.injective ?_⟩
  ext x
  have hx := LinearMap.congr_fun (f.weight_coweight_transpose_apply P Q x)
    (P.toPerfPair.symm (Q.toPerfPair y ∘ₗ e.symm.toLinearMap))
  simp only [LinearMap.dualMap_apply, LinearMap.toPerfPair_apply, RootPairing.flip_toLinearMap,
    LinearMap.flip_apply] at hx
  rw [LinearMap.toPerfPair_apply, LinearMap.toPerfPair_apply, hx,
    LinearMap.apply_symm_toPerfPair_self]
  simp [e]

end SplitCorootCriterion

set_option linter.defProp false in
open SplitCorootCriterion in
/-- **Reduction of the coroot criterion** (Milne, Proposition 23.29, via Proposition 23.5).
Sufficiency of coroot generation for simple connectedness follows from the existence of root
data for split maximal tori, the lifting of split maximal tori through central isogenies, and
the morphism of root data defined by a central isogeny. -/
def splitCorootSpanSimplyConnected_of_rootDatumHom
    (hex : RootDatumExistenceStatement.{u})
    (hlift : CentralIsogenySplitMaximalTorusLiftStatement.{u})
    (hhom : CentralIsogenyRootDatumHomStatement.{u}) :
    SplitCorootSpanSimplyConnectedStatement.{u} := by
  intro k _ G hG T hT i hi J P hP hspan
  refine ⟨hG, fun H π hH hπ => ?_⟩
  obtain ⟨S, j, t, hS, hj, hjt⟩ :=
    hlift k H G hH.isConnectedReductive hG.isConnectedReductive π hπ T i hT hi
  obtain ⟨J', -, P', hP', -⟩ := hex k H hH.isConnectedReductive S hS j hj
  obtain ⟨g, -, -, hwinj, hcinj, hiso⟩ := hhom k H G hH.isConnectedReductive
    hG.isConnectedReductive S T hS hT j i hj hi π t hπ hjt J' J P' P hP' hP
  exact hiso.mpr ⟨hwinj, surjective_weightMap g ⟨hcinj, surjective_coweightMap g hspan⟩⟩

end Langlands.GroupScheme
