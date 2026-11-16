import Langlands.GroupScheme.Torus.IsomorphismLocus
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.HomImageEmbedding

/-! # Closed monomorphisms from split tori over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace SplitTorusMonomorphism

variable {S : Scheme.{u}} {T G : GroupScheme S}
    (hT : IsSplitTorus T) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (f : T ⟶ G) [Mono f.hom.hom]

include hT in
/-- Each base point has an open neighbourhood on which the split-torus
monomorphism is a closed immersion. -/
theorem exists_closed_neighbourhood (s : S) :
    ∃ (V : Scheme.{u}) (b : V ⟶ S), IsOpenImmersion b ∧
      s ∈ Set.range b ∧ IsClosedSubgroup ((baseChange b).map f) := by
  let c := S.fromSpecResidueField s
  let Tc := (baseChange c).obj T
  let Gc := (baseChange c).obj G
  let fc := (baseChange c).map f
  have hTc : IsSplitTorus Tc := hT.baseChange c
  let : Smooth Tc.X.hom := hTc.smooth
  let : ConnectedSpace Tc.X.left := hTc.connectedSpace
  let : IsAffineHom Tc.X.hom := hTc.isAffineHom
  let : IsAffineHom Gc.X.hom :=
    MorphismProperty.pullback_snd G.X.hom c inferInstance
  let : LocallyOfFiniteType Gc.X.hom :=
    MorphismProperty.pullback_snd G.X.hom c inferInstance
  have : Mono fc.hom.hom :=
    (inferInstance : Mono ((Over.pullback c).map f.hom.hom))
  have hc : IsClosedSubgroup fc := HomImage.isClosedSubgroup_of_mono fc
  obtain ⟨V, b, hb, x, hx, hf⟩ :=
    exists_open_isClosedImmersion_baseChange hT f (S.residueField s) c hc
  refine ⟨V, b, hb, ?_, hf⟩
  refine ⟨x (IsLocalRing.closedPoint (S.residueField s)), ?_⟩
  change (x ≫ b) (IsLocalRing.closedPoint (S.residueField s)) = s
  rw [hx]
  exact Scheme.fromSpecResidueField_apply _ _

/-- The actual base open cover of closed-immersion neighbourhoods of a
split-torus monomorphism. -/
def closedImmersionCover : S.OpenCover :=
  let V := fun s => (exists_closed_neighbourhood hT f s).choose
  let b := fun s => (exists_closed_neighbourhood hT f s).choose_spec.choose
  Scheme.Cover.mkOfCovers S V b
    (fun s => ⟨s, (exists_closed_neighbourhood hT f s).choose_spec.choose_spec.2.1⟩)
    (fun s => (exists_closed_neighbourhood hT f s).choose_spec.choose_spec.1)

/-- Every member of the constructed cover makes the original map a closed immersion. -/
theorem isClosedSubgroup_baseChange_cover (s : S) :
    IsClosedSubgroup ((baseChange ((closedImmersionCover hT f).f s)).map f) :=
  (exists_closed_neighbourhood hT f s).choose_spec.choose_spec.2.2

end SplitTorusMonomorphism

/-- A monomorphism from a split torus to an affine group locally of finite
type over any base scheme is a closed immersion. -/
theorem IsSplitTorus.isClosedSubgroup_of_mono
    {S : Scheme.{u}} {T G : GroupScheme S} (hT : IsSplitTorus T)
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (f : T ⟶ G) [Mono f.hom.hom] : IsClosedSubgroup f := by
  let C := SplitTorusMonomorphism.closedImmersionCover hT f
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion)
    (C.pullback₁ G.X.hom)
  intro s
  let b := C.f s
  have hp := TorusIsomorphismLocus.underlying_isPullback b f
  change IsClosedImmersion (pullback.snd f.hom.hom.left (pullback.fst G.X.hom b))
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    hp.isoPullback.hom, hp.isoPullback_hom_snd]
  exact SplitTorusMonomorphism.isClosedSubgroup_baseChange_cover hT f s

end Langlands.GroupScheme
