import Langlands.GroupScheme.Reductive.IsogenyAdditiveImage
import Langlands.GroupScheme.Reductive.IsogenyImageAction
import Langlands.GroupScheme.Rational.VectorLineEquivariantMap
import Langlands.GroupScheme.Rational.TangentWeightTransport
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Actual root characters from finite equivariant additive-line images -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

namespace HomImage

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {V G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (t : T ⟶ T') (i : T'.toGrp ⟶ G)
    (a : AutomorphicAction T.toGrp V) {α : characterLattice T}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (he : RelativeRoot.IsWeightVectorCoordinates a α e)
    (x : V ⟶ G) [IsFinite x.hom.hom.left]
    (hx : ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ T.X) (v : U ⟶ V.X),
      a.act s v ≫ x.hom.hom =
        (AutomorphicAction.conjugation (CommGroupScheme.groupHom t ≫ i)).act
          s (v ≫ x.hom.hom))

include hT hT' he hx

/-- A finite equivariant map from an actual additive line of nonzero weight
produces a target root with the exact characteristic-power pullback equation. -/
theorem exists_root_expChar_factor (hα : α ≠ 0) :
    ∃ (β : characterLattice T') (_ : β ∈ roots i) (r : ℕ),
      t ≫ β = (ringExpChar k ^ r) • α := by
  let hV : RelativeRoot.IsVectorGroupOfDimension V 1 := ⟨e, he.1⟩
  let : IsAffineHom V.X.hom := hV.isAffineHom
  let : Smooth V.X.hom := hV.smooth
  let : ConnectedSpace V.X.left := hV.connectedSpace
  have : GeometricallyIntegral V.X.hom :=
    smoothConnectedAffineGeometry.1 k V inferInstance inferInstance inferInstance
  let : Flat (SchematicImage.projection x).hom.hom.left := flat_projection x
  let : Surjective (SchematicImage.projection x).hom.hom.left := surjective_projection x
  let : LocallyOfFinitePresentation (SchematicImage.projection x).hom.hom.left :=
    locallyOfFinitePresentation_projection x
  let : Epi (SchematicImage.projection x).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  let : Epi (SchematicImage.projection x).hom.hom := Over.epi_of_epi_left _
  let : Mono (SchematicImage.inclusion x).hom.hom := Over.mono_of_mono_left _
  let hImage := isVectorGroupOfDimension_image x hV
  let : IsAffineHom (SchematicImage.image x).X.hom := hImage.isAffineHom
  let : CommGroup (lieKernel (SchematicImage.image x) k) :=
    lieKernelCommGroup (SchematicImage.image x)
  let : Module k (Additive (lieKernel (SchematicImage.image x) k)) :=
    lieKernelModule (SchematicImage.image x)
  let b := AutomorphicAction.conjugation (CommGroupScheme.groupHom t ≫ i)
  let c := imageAction x a b hx
  obtain ⟨imageWeight, d, hd⟩ :=
    RelativeRoot.exists_weightVectorCoordinates_of_dimension_one hT
      hImage c
  let P := RelativeRoot.VectorLine.powerMonomial e d (SchematicImage.projection x)
    he hd (fun _ s v => imageAction_projection x a b hx s v) hT hα
  have hImageWeight : imageWeight ≠ 0 := by
    rw [P.character_eq]
    exact hT.nsmul_ne_zero hα (pow_ne_zero _ (expChar_ne_zero k (ringExpChar k)))
  let E : Additive (lieKernel (SchematicImage.image x) k) ≃ₗ[k] (Fin 1 → k) :=
    RelativeRoot.vectorLieCoordinates d hd.1 (CommAlgCat.of (CommRingCat.of k) k)
  let v : Additive (lieKernel (SchematicImage.image x) k) := E.symm (fun _ => 1)
  have hv : v ≠ 0 := by
    intro hz
    have h := congrArg (fun z => E z 0) hz
    exact one_ne_zero (by
      simpa only [v, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] using h)
  have hw : Lie.targetMapLinear (SchematicImage.inclusion x) k v ∈
      weightSpace (CommGroupScheme.groupHom t ≫ i) imageWeight := by
    have hvw : v ∈ RelativeRoot.actionWeightSpace c imageWeight := by
      rw [hd.actionWeightSpace_eq_top]
      trivial
    simpa only [b, RelativeRoot.actionWeightSpace_conjugation] using
      RelativeRoot.lieKernelTargetLinear_mem_actionWeightSpace b c
        (SchematicImage.inclusion x)
        (fun _ s v => imageAction_act_comp x a b hx s v) imageWeight hvw
  have hroot : imageWeight ∈ roots (CommGroupScheme.groupHom t ≫ i) := by
    refine ⟨hImageWeight, (Submodule.ne_bot_iff _).mpr ⟨_, hw, ?_⟩⟩
    intro hz
    apply hv
    apply Lie.targetMapLinear_injective (SchematicImage.inclusion x) k
    simpa only [map_zero] using hz
  obtain ⟨_, β, hβ, hBetaImageWeight⟩ := (mem_roots_comp_iff hT' hT t i imageWeight).mp hroot
  exact ⟨β, hβ, P.exponent, hBetaImageWeight.trans P.character_eq⟩

/-- A chosen target root and characteristic-power exponent for the actual
finite equivariant line map, together with their integral character equation. -/
def rootExpCharFactor (hα : α ≠ 0) :
    Σ β : roots i, {r : ℕ // t ≫ β.val = (ringExpChar k ^ r) • α} :=
  Classical.choice (by
    obtain ⟨β, hβ, r, h⟩ := exists_root_expChar_factor hT hT' t i a e he x hx hα
    exact ⟨⟨⟨β, hβ⟩, r, h⟩⟩)

end HomImage
end Langlands.GroupScheme
