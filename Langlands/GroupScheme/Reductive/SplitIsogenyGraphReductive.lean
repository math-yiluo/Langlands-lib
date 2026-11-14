import Langlands.GroupScheme.Reductive.SplitIsogenyGraphProjections

/-! # Reductivity of actual local-isogeny graphs over arbitrary fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

namespace LeviGluing.GraphEnvelope

variable {G G' T : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {A : I → GroupScheme (Spec (CommRingCat.of k))}
    {a : ∀ j, A j ⟶ G} {a' : ∀ j, A j ⟶ G'} {i : T ⟶ G} {i' : T ⟶ G'}
    (D : GraphEnvelope A a a' i i')

/-- A smooth connected affine graph with faithfully flat projections to two
connected reductive groups is connected reductive over the original field. -/
theorem isConnectedReductive_of_projection_geometry
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hflat : Flat D.first.hom.hom.left) (hsurj : Surjective D.first.hom.hom.left)
    (hflat' : Flat D.second.hom.hom.left) (hsurj' : Surjective D.second.hom.hom.left) :
    IsConnectedReductive D.group := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G'.X.hom := hG'.smooth
  let : IsAffineHom G'.X.hom := hG'.isAffineHom
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  let b := toAlgebraicClosure k
  let B := GroupScheme.baseChange b
  let : IsAffineHom (B.obj D.group).X.hom :=
    MorphismProperty.pullback_snd _ b (inferInstance : IsAffineHom D.group.X.hom)
  let : Smooth (B.obj G).X.hom := MorphismProperty.pullback_snd _ b hG.smooth
  let : IsAffineHom (B.obj G).X.hom := MorphismProperty.pullback_snd _ b hG.isAffineHom
  let : Smooth (B.obj G').X.hom := MorphismProperty.pullback_snd _ b hG'.smooth
  let : IsAffineHom (B.obj G').X.hom := MorphismProperty.pullback_snd _ b hG'.isAffineHom
  let : Flat (B.map D.first).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b D.first.hom.hom hflat
  let : Surjective (B.map D.first).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b D.first.hom.hom hsurj
  let : Flat (B.map D.second).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b D.second.hom.hom hflat'
  let : Surjective (B.map D.second).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b D.second.hom.hom hsurj'
  let : Epi (B.map D.first).hom.hom.left := Flat.epi_of_flat_of_surjective _
  let : Epi (B.map D.second).hom.hom.left := Flat.epi_of_flat_of_surjective _
  intro U j hj hs hc hu hn
  have h₁ := LeviGluing.normal_unipotent_comp_eq_one (B.map D.first)
    hG.hasTrivialGeometricUnipotentRadical j hj hs hc hu hn
  have h₂ := LeviGluing.normal_unipotent_comp_eq_one (B.map D.second)
    hG'.hasTrivialGeometricUnipotentRadical j hj hs hc hu hn
  have hj1 : j.hom.hom = 1 := by
    apply (baseChangePointsEquiv b D.group U.X).injective
    apply D.points_ext
    · rw [← baseChangePointsEquiv_comp, ← baseChangePointsEquiv_comp,
        h₁, MonObj.one_comp]
    · rw [← baseChangePointsEquiv_comp, ← baseChangePointsEquiv_comp,
        h₂, MonObj.one_comp]
  apply SubgroupFunctor.ext
  intro W
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change y ≫ j.hom.hom = 1
    rw [hj1, MonObj.comp_one]
  · rintro rfl
    exact Subgroup.one_mem _

end LeviGluing.GraphEnvelope

namespace RootDatumIsogenyRealization.LocalIsogenyGraphEnvelope

variable {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    {C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)}
    (D : LocalIsogenyGraphEnvelope C)

/-- A generic chamber in a split reductive group has the prescribed maximal
torus as its full dynamic centralizer. -/
theorem chamber_centralizer_eq_range
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (ζ : cocharacterLattice T)
    (hζ : haveI := hG.isAffineHom; IsGenericCocharacter i ζ) :
    Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) = SubgroupFunctor.range i := by
  have hself := maximalTorusCentralizer_of_structuralInputs dynamicCentralizerReductive
    noTorusUnipotent solvableTorusQuotient k G hG T i hi
  exact (genericCentralizer k G hG T i (hi.isMaximalSplitTorus hT) ζ hζ).trans hself

/-- Both simple-direction covering conditions imply connected reductivity of
the actual local-isogeny graph, with arbitrary fields retained. -/
theorem isConnectedReductive
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i')
    (ht : IsIsogeny (CommGroupScheme.groupHom t))
    {J J' : Type u}
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    (hP : haveI := hG.isAffineHom; IsRootDatumOf i P)
    (hP' : haveI := hG'.isAffineHom; IsRootDatumOf i' P')
    (ζ : cocharacterLattice T) (ζ' : cocharacterLattice T')
    (hζ : haveI := hG.isAffineHom; IsGenericCocharacter i ζ)
    (hζ' : haveI := hG'.isAffineHom; IsGenericCocharacter i' ζ')
    (hcover : haveI := hG.isAffineHom;
      ∀ α ∈ simpleRelativeRoots i ζ, ∃ j, latticePairing T α (ν j) = 0)
    (hcover' : haveI := hG'.isAffineHom;
      ∀ α ∈ simpleRelativeRoots i' ζ', ∃ j, latticePairing T' α (ν' j) = 0) :
    IsConnectedReductive D.group := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : Smooth G'.X.hom := hG'.smooth
  let : IsAffineHom G'.X.hom := hG'.isAffineHom
  let : ConnectedSpace G'.X.left := hG'.connectedSpace
  have hg := D.first_geometry hT hi.2.1 P hP ζ hζ hcover
    (chamber_centralizer_eq_range hG hT hi ζ hζ)
  have hg' := D.second_geometry hT' hi'.2.1 ht P' hP' ζ' hζ' hcover'
    (chamber_centralizer_eq_range hG' hT' hi' ζ' hζ')
  exact D.isConnectedReductive_of_projection_geometry hG hG' hg.1 hg.2.1 hg'.1 hg'.2.1

end RootDatumIsogenyRealization.LocalIsogenyGraphEnvelope


namespace RootDatumIsogenyRealization

/-- An actual local-isogeny graph certified connected reductive, retaining both
faithfully flat projections. -/
structure ReductiveLocalIsogenyGraphEnvelope
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    (C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)) where
  projections : FaithfullyFlatLocalIsogenyGraphEnvelope C
  reductive : IsConnectedReductive projections.graph.group

/-- Turn the certified faithfully flat graph into a certified reductive graph
using the actual ambient reductivity hypotheses. -/
def reductiveLocalIsogenyGraphEnvelope
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type v} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}
    {ν : I → cocharacterLattice T} {ν' : I → cocharacterLattice T'}
    {C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)}
    (E : FaithfullyFlatLocalIsogenyGraphEnvelope C)
    (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G') :
    ReductiveLocalIsogenyGraphEnvelope C :=
  ⟨E, E.graph.isConnectedReductive_of_projection_geometry hG hG'
    E.firstGeometry.1 E.firstGeometry.2.1 E.secondGeometry.1 E.secondGeometry.2.1⟩

end RootDatumIsogenyRealization

end Langlands.GroupScheme
