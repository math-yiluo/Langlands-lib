import Langlands.AbelianScheme.SemiabelianCocharacters
import Langlands.AlgebraicGeometry.ProperOfFibres.NoetherianCore
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.SmoothPureDimensionProof
import Langlands.GroupScheme.Absolute.ParabolicIntersectionTorusReduction
import Langlands.GroupScheme.Lie.SplitTorusCoordinates
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.RelativeIdentityComponent.OpenGeometry

/-! # Torus rank bounds for supplied Néron models -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.NeronModel

variable {V K : Type u} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  {B : AbelianScheme (Spec (CommRingCat.of K))} (N : NeronModel V K B)

/-- The supplied Néron model has the relative dimension of the abelian generic
fibre. Flatness and the irreducible generic fibre make its total space connected. -/
theorem smoothOfRelativeDimension {d : ℕ} (hB : B.HasRelativeDimension d) :
    SmoothOfRelativeDimension d N.group.X.hom := by
  let j := NeronModelInfra.specGenericFibreInclusion V K
  let F := (CommGroupScheme.baseChange j).obj N.group
  let e : B.X ≅ F.X := (Grp.forget (Over (Spec (CommRingCat.of K)))).mapIso
    (CommGroupScheme.groupIso N.genericIso)
  let : Smooth N.group.X.hom := N.property.smooth
  let : ConnectedSpace B.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := B.X.hom)
  let : IrreducibleSpace B.X.left :=
    Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected B.X.hom
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  let : IrreducibleSpace N.group.X.left := by
    apply Langlands.AlgebraicGeometry.ProperOfFibres.irreducibleSpace_of_flat N.group.X.hom
      (e.hom.left ≫ pullback.fst N.group.X.hom j)
    intro x hx
    have hmem : x ∈ Set.range (pullback.fst N.group.X.hom j) := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hx]
      exact Langlands.AlgebraicGeometry.ProperOfFibres.bot_mem_range_SpecMap_of_injective
        (algebraMap V K) (IsFractionRing.injective V K)
    obtain ⟨y, rfl⟩ := hmem
    obtain ⟨z, rfl⟩ := e.hom.left.surjective y
    exact ⟨z, Scheme.Hom.comp_apply _ _ _⟩
  obtain ⟨m, hm⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension
    _ _ N.group.X.hom N.property.smooth inferInstance
  let : SmoothOfRelativeDimension m F.X.hom :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension m) N.group.X.hom j hm
  let : SmoothOfRelativeDimension m B.X.hom := by
    rw [← Over.w e.hom]
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + m) (e.hom.left ≫ F.X.hom))
  let : SmoothOfRelativeDimension d B.X.hom := hB
  let x : B.X.left := Classical.arbitrary _
  have h := (Langlands.AlgebraicGeometry.fieldSmooth_topologicalKrullDimAt
    K B.X.left B.X.hom m x).symm.trans
    (Langlands.AlgebraicGeometry.fieldSmooth_topologicalKrullDimAt K B.X.left B.X.hom d x)
  have hm_eq : m = d := by exact_mod_cast h
  exact hm_eq ▸ hm

/-- The rank of a split toric kernel in the geometric special identity
component is bounded by the dimension of the original abelian variety. -/
theorem torusRank_le {d : ℕ} (hB : B.HasRelativeDimension d)
    {J : CommGroupScheme (Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField V))))}
    (i : J ⟶ N.geometricSpecialFibre)
    (hi : IsRelativeIdentityComponent N.geometricSpecialFibre.toGrp (CommGroupScheme.groupHom i))
    (P : SplitSemiabelianPresentation J) : P.torusRank ≤ d := by
  let k := AlgebraicClosure (IsLocalRing.ResidueField V)
  let S := Spec (CommRingCat.of k)
  let I := ULift.{u} (Fin P.torusRank)
  let T := splitTorus S I
  let G := N.geometricSpecialFibre
  let q := CommGroupScheme.groupHom P.quotientMap
  let e := CommGroupScheme.groupIso P.torusIso
  let a := e.hom ≫ GroupScheme.kernelι q ≫ CommGroupScheme.groupHom i
  let : IsAffineHom T.X.hom := isAffineHom_splitTorus_spec _ I
  let : Smooth T.X.hom := smooth_splitTorus I
  let : IsIso e.hom.hom.hom.left := ((Grp.forget (Over S)) ⋙ Over.forget S).map_isIso e.hom
  let : IsOpenImmersion (CommGroupScheme.groupHom i).hom.hom.left := hi.isOpenImmersion
  have ha : IsPreimmersion a.hom.hom.left := by
    change IsPreimmersion (e.hom.hom.hom.left ≫ (GroupScheme.kernelι q).hom.hom.left ≫
      (CommGroupScheme.groupHom i).hom.hom.left)
    infer_instance
  have hT := Lie.finrank_kernel_cast_le_topologicalKrullDim T
  have htorus : Module.finrank k (Additive (lieKernel T k)) = P.torusRank := by
    simpa [I] using splitTorus.finrank_lieKernel I k
  rw [htorus] at hT
  have hEmb : topologicalKrullDim T.X.left ≤ topologicalKrullDim G.X.left :=
    ha.isEmbedding.isInducing.topologicalKrullDim_le
  let : QuasiCompact N.group.X.hom := N.property.quasiCompact
  let : QuasiCompact G.X.hom := inferInstanceAs
    (QuasiCompact (pullback.snd N.group.X.hom (geometricSpecialPoint V)))
  let : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have hG : SmoothOfRelativeDimension d G.X.hom :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension d)
      N.group.X.hom (geometricSpecialPoint V) (N.smoothOfRelativeDimension hB)
  have h := hT.trans (hEmb.trans
    (Langlands.AlgebraicGeometry.fieldSmoothTopologicalKrullDim k _ G.X.hom d hG inferInstance))
  exact_mod_cast h

end Langlands.AbelianScheme.NeronModel
