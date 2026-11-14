import Langlands.GroupScheme.Torus.MaximalLocus
import Langlands.GroupScheme.Reductive.BaseChange
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Openness of the maximal locus for relative tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

/-- The actual maximal locus pulls back under every scheme morphism. -/
theorem maximalTorusLocus_baseChange {S S' : Scheme.{u}} {G : GroupScheme S}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {T : CommGroupScheme S}
    (b : S' ⟶ S) (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    maximalTorusLocus (T := (CommGroupScheme.baseChange b).obj T)
      ((baseChange b).map i) = b ⁻¹' maximalTorusLocus i := by
  ext x
  let a := S.fromSpecResidueField (b x)
  let c := Spec.map (b.residueFieldMap x)
  let d := S'.fromSpecResidueField x
  let : Algebra (S.residueField (b x)) (S'.residueField x) :=
    (b.residueFieldMap x).hom.toAlgebra
  have hfac : c ≫ a = d ≫ b := b.SpecMap_residueFieldMap_fromSpecResidueField x
  have : Smooth ((baseChange a).obj G).X.hom :=
    inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd G.X.hom a))
  have : IsAffineHom ((baseChange a).obj G).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom a))
  change IsMaximalTorus
    (T := (CommGroupScheme.baseChange d).obj ((CommGroupScheme.baseChange b).obj T))
    ((baseChange d).map ((baseChange b).map i)) ↔
      IsMaximalTorus (T := (CommGroupScheme.baseChange a).obj T) ((baseChange a).map i)
  constructor
  · intro hx
    have h := isMaximalTorus_of_baseChange_comp b d T i hx
    rw [← hfac] at h
    have hc := isMaximalTorus_baseChange_comp a c T i h
    exact IsMaximalTorus.of_baseChange
      (k := S.residueField (b x)) (K := S'.residueField x) (hi.baseChange a) hc
  · intro hx
    have hc := (maximalTorusBaseChange (S.residueField (b x)) (S'.residueField x)
      ((baseChange a).obj G) ((CommGroupScheme.baseChange a).obj T)
      ((baseChange a).map i) hx.1 hx.2.1).mp hx
    have h := isMaximalTorus_of_baseChange_comp a c T i hc
    rw [hfac] at h
    exact isMaximalTorus_baseChange_comp (G := G) b d T i h

private theorem isOpen_of_cover_preimages {S : Scheme.{u}}
    {P : MorphismProperty Scheme.{u}}
    (𝒰 : Scheme.Cover (Scheme.precoverage P) S)
    (hopen : ∀ j, IsOpenMap (𝒰.f j)) (s : Set S)
    (hs : ∀ j, IsOpen ((𝒰.f j) ⁻¹' s)) : IsOpen s := by
  have he : s = ⋃ j, (𝒰.f j) '' ((𝒰.f j) ⁻¹' s) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
      exact Set.mem_iUnion.mpr ⟨j, y, (by change (𝒰.f j) y ∈ s; rwa [hy]), hy⟩
    · intro hx
      obtain ⟨j, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      exact hy
  rw [he]
  exact isOpen_iUnion (fun j => hopen j _ (hs j))

/-- A closed split torus in a reductive group has an open maximal locus on
an arbitrary scheme base. -/
theorem IsReductive.isOpen_maximalTorusLocus_of_isSplitTorus_scheme
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    IsOpen (maximalTorusLocus i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  refine isOpen_of_cover_preimages S.affineCover
    (fun j => (S.affineCover.f j).isOpenEmbedding.isOpenMap)
    (maximalTorusLocus (T := T) i) ?_
  intro j
  have he := maximalTorusLocus_baseChange (T := T) (G := G) (S.affineCover.f j) i hi
  rw [← he]
  exact IsReductive.isOpen_maximalTorusLocus_of_isSplitTorus
    (G := (GroupScheme.baseChange (S.affineCover.f j)).obj G)
    (hG.baseChange (S.affineCover.f j))
    (T := (CommGroupScheme.baseChange (S.affineCover.f j)).obj T)
    (hT.baseChange (S.affineCover.f j))
    ((GroupScheme.baseChange (S.affineCover.f j)).map i)
    (hi.baseChange (S.affineCover.f j))

/-- A closed relative torus in a reductive group has an open maximal locus. -/
theorem IsReductive.isOpen_maximalTorusLocus
    {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) :
    IsOpen (maximalTorusLocus i) := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨𝒰, h𝒰⟩ := hT
  refine isOpen_of_cover_preimages 𝒰 (fun j => (𝒰.f j).isOpenMap)
    (maximalTorusLocus (T := T) i) ?_
  intro j
  have he := maximalTorusLocus_baseChange (T := T) (G := G) (𝒰.f j) i hi
  rw [← he]
  exact IsReductive.isOpen_maximalTorusLocus_of_isSplitTorus_scheme
    (G := (GroupScheme.baseChange (𝒰.f j)).obj G)
    (hG.baseChange (𝒰.f j))
    (T := (CommGroupScheme.baseChange (𝒰.f j)).obj T)
    (h𝒰 j) ((GroupScheme.baseChange (𝒰.f j)).map i) (hi.baseChange (𝒰.f j))

/-- The actual open subscheme of the base where a closed relative torus is
maximal in a reductive ambient group. -/
def maximalTorusOpen {S : Scheme.{u}} {G : GroupScheme S} (hG : IsReductive G)
    {T : CommGroupScheme S} (hT : RelativeTorus.IsTorus T.toGrp)
    (i : T.toGrp ⟶ G) (hi : IsClosedSubgroup i) : S.Opens :=
  ⟨maximalTorusLocus i, hG.isOpen_maximalTorusLocus hT i hi⟩

end Langlands.GroupScheme
