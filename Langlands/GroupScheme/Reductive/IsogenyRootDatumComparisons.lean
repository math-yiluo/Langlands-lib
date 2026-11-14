import Langlands.GroupScheme.CentralIsogeny.RootDatumHomConstruction
import Langlands.LinearAlgebra.RootDatumIsogeny

/-! # Central and isomorphism comparisons for actual root-datum isogenies -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.LinearAlgebra.RootDatumIsogeny

variable {p : ℕ} {J X Y J' X' Y' : Type*}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup X'] [AddCommGroup Y']
  [Finite J] [Finite J']
  [Module.Finite ℤ X] [Module.Finite ℤ Y]
  [Module.Finite ℤ X'] [Module.Finite ℤ Y']
  {P : RootDatum J X Y} {Q : RootDatum J' X' Y'} [P.IsReduced] [Q.IsReduced]

/-- A root-datum isogeny is central exactly when its weight map takes every root
to a root, rather than merely to a positive multiple of a root. -/
theorem isCentral_iff_mapsTo_roots (f : RootDatumIsogeny p P Q) :
    f.IsCentral ↔ Set.MapsTo f.weightMap (Set.range P.root) (Set.range Q.root) := by
  have : Module.IsReflexive ℤ X' := .of_isPerfPair Q.toLinearMap
  have : IsAddTorsionFree X' := .of_isTorsionFree ℤ X'
  constructor
  · intro hf x hx
    obtain ⟨j, rfl⟩ := hx
    rw [f.root_weightMap, hf j]
    simp
  · intro h j
    have hm := h (Set.mem_range_self j)
    rw [f.root_weightMap] at hm
    have hm' : f.rootFactor j • Q.root (f.indexEquiv j) ∈ Set.range Q.root := by
      simpa only [Nat.cast_smul_eq_nsmul] using hm
    by_contra hj
    have hn : 2 ≤ f.rootFactor j := by
      have hp := f.rootFactor_pos j
      omega
    have : (f.rootFactor j).AtLeastTwo := ⟨hn⟩
    exact Q.nsmul_notMem_range_root hm'

end Langlands.LinearAlgebra.RootDatumIsogeny

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
  [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H}
  {φ : G ⟶ H} {t : T ⟶ T'}
  {J : Type v} {J' : Type w} [Finite J] [Finite J']
  {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
  {Q : RootDatum J' (characterLattice T') (cocharacterLattice T')}
  [P.IsReduced] [Q.IsReduced] {p : ℕ}

/-- Any root-datum isogeny with the actual weight map of a central ambient
isogeny is central. No uniqueness of its supplied root correspondence is assumed. -/
theorem IsCentralIsogeny.isCentral_rootDatumIsogeny
    (hφ : IsCentralIsogeny φ)
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) : f.IsCentral := by
  apply f.isCentral_iff_mapsTo_roots.mpr
  have hr := hφ.roots_bijOn_of_torusRestriction hT hT' t hsquare ht
  intro χ hχ
  rw [hw, hP.2.1]
  rw [hQ.2.1] at hχ
  exact hr.1 hχ

/-- Recover the exact root-pairing morphism from any actual-map root-datum
isogeny of a central ambient isogeny, retaining its chosen root correspondence. -/
def IsCentralIsogeny.rootDatumHomOfActualIsogeny
    (hφ : IsCentralIsogeny φ)
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) : RootPairing.Hom Q P :=
  f.toHom (hφ.isCentral_rootDatumIsogeny hP hQ hT hT' ht hsquare f hw)

/-- The recovered exact morphism retains both lattice maps and the index
equivalence of the supplied root-datum isogeny. -/
theorem IsCentralIsogeny.rootDatumHomOfActualIsogeny_spec
    (hφ : IsCentralIsogeny φ)
    (hP : IsRootDatumOf i P) (hQ : IsRootDatumOf i' Q)
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ) :
    let g := hφ.rootDatumHomOfActualIsogeny hP hQ hT hT' ht hsquare f hw
    g.weightMap = f.weightMap ∧ g.coweightMap = f.coweightMap ∧
      g.indexEquiv = f.indexEquiv :=
  ⟨rfl, rfl, rfl⟩

omit [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
  [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] in
/-- Given the centrality comparison, the actual weight map gives the ambient
isomorphism comparison. Centrality remains an explicit conjunct. -/
theorem isIso_iff_central_bijective_rootDatumIsogeny
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (hsquare : i ≫ φ = CommGroupScheme.groupHom t ≫ i')
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p Q P)
    (hw : ∀ χ, f.weightMap χ = t ≫ χ)
    (hcentral : IsCentralIsogeny φ ↔ f.IsCentral) :
    IsIso φ ↔ f.IsCentral ∧ Function.Bijective f.weightMap := by
  have heq : (f.weightMap : characterLattice T' → characterLattice T) =
      fun χ => t ≫ χ := funext hw
  have hbij : Function.Bijective f.weightMap ↔ IsIso t := by
    rw [heq]
    exact (hT.isIso_iff_bijective_characterPullback hT' t).symm
  constructor
  · intro h
    have : IsIso φ := h
    have hc := isCentralIsogeny_of_isIso φ
    exact ⟨hcentral.mp hc, hbij.mpr
      ((hc.isIso_iff_torusRestriction_of_selfCentralizing
        hi hT'.isTorus hi' t hsquare hself).mp h)⟩
  · rintro ⟨hc, hb⟩
    exact ((hcentral.mpr hc).isIso_iff_torusRestriction_of_selfCentralizing
      hi hT'.isTorus hi' t hsquare hself).mpr (hbij.mp hb)

end Langlands.GroupScheme
