import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.CentralIsogeny.SplitRootDatumProof
import Langlands.GroupScheme.CentralIsogeny.TorusRestriction

/-! # The integral cocharacter image of a simply connected central cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace IsCentralIsogeny

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {φ : G ⟶ G'} (hφ : IsCentralIsogeny φ)
  (hG : IsSimplyConnected G) (hG' : IsConnectedReductive G')
  (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
  (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
  (t : T ⟶ T') (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
  {J' : Type u} (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
  (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')

include hφ hG hG' hT hT' hi hi' ht hP'

/-- The integral cocharacter image of a simply connected central cover is the coroot span
of any supplied root datum of the target split maximal torus. -/
theorem range_cocharacterMapInt_eq_corootSpan :
    LinearMap.range (RealTorusSpace.cocharacterMapInt t) = P'.corootSpan ℤ := by
  let hGr := hG.isSemisimple.isConnectedReductive
  have := hGr.isAffineHom
  have := hG'.isAffineHom
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence k G hGr T hT i hi
  have := hJ
  obtain ⟨f, _, hf, _, _, _⟩ :=
    centralIsogenyRootDatumHom k G G' hGr hG' T T' hT hT' i i' hi hi' φ t hφ ht
      J J' P P' hP hP'
  have hspan : P.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan k G hG T hT i hi J P hP hred
  have hmap : (P.corootSpan ℤ).map f.coweightMap = P'.corootSpan ℤ := by
    rw [Submodule.map_span, ← Set.range_comp, f.coroot_coweightMap,
      f.indexEquiv.symm.surjective.range_comp]
  have hfmap : f.coweightMap = RealTorusSpace.cocharacterMapInt t := by
    ext ν
    exact hf ν
  simpa [hspan, hfmap] using hmap

/-- The actual cocharacter pushforward identifies the lattice of the simply connected source
with the target coroot span. -/
def cocharacterCorootSpanEquiv : cocharacterLattice T ≃ₗ[ℤ] P'.corootSpan ℤ :=
  (LinearEquiv.ofInjective (RealTorusSpace.cocharacterMapInt t)
    (hφ.cocharacterMapInt_injective_of_square hi.2.1 hi'.2.1 t ht)).trans
      (LinearEquiv.ofEq _ _
        (hφ.range_cocharacterMapInt_eq_corootSpan hG hG' hT hT' hi hi' t ht P' hP'))

@[simp]
theorem cocharacterCorootSpanEquiv_apply (ν : cocharacterLattice T) :
    (hφ.cocharacterCorootSpanEquiv hG hG' hT hT' hi hi' t ht P' hP' ν :
      cocharacterLattice T') = ν ≫ t := rfl

end IsCentralIsogeny

end Langlands.GroupScheme
