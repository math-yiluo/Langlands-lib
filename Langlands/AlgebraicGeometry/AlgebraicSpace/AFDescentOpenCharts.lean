import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteAffineOpenRestriction
import Langlands.AlgebraicGeometry.AlgebraicSpace.CompactEtaleImages
import Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteSurjectiveQuasiAffineSourceAFStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.PointLiftedOpenCharts

/-! # Open AF models conditional on quasi-affine-source AF descent -/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts

open OpenSubspaceGeometry FiniteAffineUniversalNeighborhoods
  FiniteAffineOpenRestriction CompactEtaleImages

variable {R : Type u} [CommRing R]
variable {U : Over (Spec (CommRingCat.of R))}
  {Y : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- An actual AF model of a compact target open, conditional on the
quasi-affine-source descent proposition. -/
def openAFModel (hcore : FiniteSurjectiveQuasiAffineSourceAFStatement.{u})
    (π : (schemeYoneda _).obj U ⟶ Y.presheaf)
    (hπ : IsFinite π) (hs : IsSurjective π) (hY : IsQuasiSeparated Y)
    (A : Subfunctor Y.presheaf) (hA : IsOpenImmersion A.ι)
    (hAc : IsQuasiCompact (openSubspace Y A hA))
    (V : U.left.affineOpens) (hAV : A ≤ universalAffineOpen π V) :
    Σ P : {P : Over (Spec (CommRingCat.of R)) //
      PointTopology.HasFiniteAffineNeighborhoods P.left},
        (schemeYoneda _).obj P.val ≅ A.toFunctor :=
  let h := hcore R (sourceOverOpen π A hA) (openSubspace Y A hA)
    (homMk (toOpen π A hA)) hAc
    (isQuasiSeparated_openSubspace hY A hA)
    (sourceOverOpen_isQuasiAffine π hπ A hA hAc V hAV)
    (toOpen_isFinite π hπ A hA) (toOpen_isSurjective π hs A hA)
  ⟨⟨h.choose, h.choose_spec.1⟩, Classical.choice h.choose_spec.2⟩

/-- Every etale chart point has an open scheme chart after applying the
explicit quasi-affine-source descent premise. -/
theorem point_lifted_open_charts
    (hcore : FiniteSurjectiveQuasiAffineSourceAFStatement.{u})
    (π : (schemeYoneda _).obj U ⟶ Y.presheaf)
    (hπ : IsFinite π) (hs : IsSurjective π)
    (hU : PointTopology.HasFiniteAffineNeighborhoods U.left)
    (hY : IsQuasiSeparated Y)
    {T : Over (Spec (CommRingCat.of R))}
    (a : (schemeYoneda _).obj T ⟶ Y.presheaf) (ha : IsEtale a) :
    HasPointLiftedOpenCharts a := by
  intro x
  let p := OpenSubfunctorPoints.residueFieldPoint T x
  obtain ⟨V, hxV⟩ := exists_universalAffineOpen_of_field_test hπ hU
    (T.left.residueField x) (T.left.fromSpecResidueField x ≫ T.hom)
    ((schemeYoneda _).map p ≫ a)
  let A := universalAffineOpen π V
  have hA : IsOpenImmersion A.ι := universalAffineOpen_isOpenImmersion hπ V
  have hx : Y.presheaf.map p.op (uliftYonedaEquiv a) ∈
      A.obj (op (OpenSubfunctorPoints.residueFieldTest T x)) := by
    rw [uliftYonedaEquiv_naturality]
    exact hxV
  obtain ⟨D, j, d, hD, hj, hjd, hAV⟩ :=
    exists_affine_restriction_inside_open a A hA x hx
  let : IsAffine D.left := hD
  let : _root_.AlgebraicGeometry.IsOpenImmersion j.left := hj
  let b₀ := (schemeYoneda _).map j ≫ a
  have hb₀ : IsEtale b₀ := (isEtale_map j inferInstance).comp ha
  let B := imageSubfunctor b₀
  have hB : IsOpenImmersion B.ι :=
    OpenSubfunctorImages.sheafify_range_open b₀ hb₀
  have hBc : IsQuasiCompact (openSubspace Y B hB) :=
    etaleImage_isQuasiCompact b₀ hb₀
  let M := openAFModel hcore π hπ hs hY B hB hBc V hAV
  let e := M.2
  let b := e.hom ≫ B.ι
  let z : (schemeYoneda _).obj D ⟶ B.toFunctor :=
    Subfunctor.toRangeSheafify (fppfTopology _) b₀
  let c : D ⟶ M.1.val :=
    (schemeYoneda _).preimage (z ≫ e.inv)
  have hc : (schemeYoneda _).map c ≫ e.hom = z := by
    dsimp [c]
    rw [Functor.map_preimage]
    simp
  have hi : z ≫ B.ι = b₀ := by
    ext Q z
    rfl
  refine ⟨M.1.val, D, b, j, c, d, IsOpenImmersion.iso_comp e hB, ?_, hjd⟩
  change b₀ = (schemeYoneda _).map c ≫ (e.hom ≫ B.ι)
  rw [← Category.assoc, hc, hi]

/-- The full finite AF-source scheme-representability reduction, still
conditional on the explicit quasi-affine-source descent proposition. -/
theorem exists_representation
    (hcore : FiniteSurjectiveQuasiAffineSourceAFStatement.{u})
    (π : (schemeYoneda _).obj U ⟶ Y.presheaf)
    (hπ : IsFinite π) (hs : IsSurjective π)
    (hU : PointTopology.HasFiniteAffineNeighborhoods U.left)
    (hY : IsQuasiSeparated Y) :
    ∃ P : Over (Spec (CommRingCat.of R)),
      Nonempty ((schemeYoneda _).obj P ≅ Y.presheaf) := by
  obtain ⟨T, a, _, ha, has⟩ := Y.exists_atlas
  exact exists_representation_of_point_lifted_open_charts Y.toSheaf a ha has
    (point_lifted_open_charts hcore π hπ hs hU hY a ha)

end Langlands.AlgebraicGeometry.AlgebraicSpace.AFDescentOpenCharts
