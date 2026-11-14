import Langlands.GroupScheme.Reductive.IsogenyRootImage
import Langlands.GroupScheme.ElementaryOrbitLimit
import Langlands.GroupScheme.Rational.MonicRootParametrization

/-! # Monicity of finite additive maps of an indivisible root weight -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

namespace RelativeRoot.VectorLine

variable {k : Type u} [Field k]
    {V W : GroupScheme (Spec (CommRingCat.of k))}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (d : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ W.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (f : V ⟶ W)

/-- A unit scalar polynomial makes the actual map of naturally coordinated
lines monic, including on nonreduced tests. -/
theorem mono_of_polynomial_linear
    (he : IsNaturalVectorCoordinates e) (hd : IsNaturalVectorCoordinates d)
    (c : kˣ) (hf : polynomial e d f = C (c : k) * X) :
    Mono f.hom.hom := by
  have hinj (B : Type u) [CommRing B] [Algebra k B] :
      Function.Injective (fun x : Lie.AffinePoints V B => x ≫ f.hom.hom) := by
    intro x y hxy
    have hc := (polynomial_aeval e d f he hd x).trans
      ((congrArg (fun z => (vectorAffineCoordinates d B z).toAdd 0) hxy).trans
        (polynomial_aeval e d f he hd y).symm)
    rw [hf] at hc
    simp only [map_mul, aeval_C, aeval_X] at hc
    have hcoord := (c.isUnit.map (algebraMap k B)).mul_left_cancel hc
    apply (vectorAffineCoordinates e B).injective
    apply Multiplicative.toAdd.injective
    funext j
    simpa only [Subsingleton.elim j 0] using hcoord
  constructor
  intro U x y hxy
  apply OrbitLimit.hom_ext_of_algebraSpec
  intro B _ _ a
  apply hinj B
  simpa only [Category.assoc] using congrArg (a ≫ ·) hxy

end RelativeRoot.VectorLine

namespace HomImage

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {V G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom T.toGrp.X.hom] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (a : AutomorphicAction T.toGrp V) {α : characterLattice T}
    (e : ∀ U : Over (Spec (CommRingCat.of k)),
      (U ⟶ V.X) ≃* Multiplicative (Fin 1 → Γ(U.left, ⊤)))
    (he : RelativeRoot.IsWeightVectorCoordinates a α e)
    (x : V ⟶ G) [IsFinite x.hom.hom.left]
    (hx : ∀ (U : Over (Spec (CommRingCat.of k))) (s : U ⟶ T.X) (v : U ⟶ V.X),
      a.act s v ≫ x.hom.hom =
        (AutomorphicAction.conjugation i).act s (v ≫ x.hom.hom))

include hT he hx

/-- A finite equivariant additive line with a nonzero root weight and no higher
roots is monic. The finite image is differentiated, so no separability premise
on the original map is inserted. -/
theorem mono_of_noHigherRoots (hα : α ≠ 0)
    (hhigh : RelativeRoot.HasNoHigherRoots i α) : Mono x.hom.hom := by
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
  let b := AutomorphicAction.conjugation i
  let c := imageAction x a b hx
  obtain ⟨β, d, hd⟩ :=
    RelativeRoot.exists_weightVectorCoordinates_of_dimension_one hT hImage c
  let P := RelativeRoot.VectorLine.powerMonomial e d (SchematicImage.projection x)
    he hd (fun _ s v => imageAction_projection x a b hx s v) hT hα
  have hβ : β ≠ 0 := by
    rw [P.character_eq]
    exact hT.nsmul_ne_zero hα (pow_ne_zero _ (expChar_ne_zero k (ringExpChar k)))
  let E : Additive (lieKernel (SchematicImage.image x) k) ≃ₗ[k] (Fin 1 → k) :=
    RelativeRoot.vectorLieCoordinates d hd.1 (CommAlgCat.of k k)
  let v : Additive (lieKernel (SchematicImage.image x) k) := E.symm (fun _ => 1)
  have hv : v ≠ 0 := by
    intro hz
    have h := congrArg (fun z => E z 0) hz
    exact one_ne_zero (by
      simpa only [v, LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] using h)
  have hw : Lie.targetMapLinear (SchematicImage.inclusion x) k v ∈ weightSpace i β := by
    have hvw : v ∈ RelativeRoot.actionWeightSpace c β := by
      rw [hd.actionWeightSpace_eq_top]
      trivial
    simpa only [b, RelativeRoot.actionWeightSpace_conjugation] using
      RelativeRoot.lieKernelTargetLinear_mem_actionWeightSpace b c
        (SchematicImage.inclusion x)
        (fun _ s v => imageAction_act_comp x a b hx s v) β hvw
  have hroot : β ∈ roots i := by
    refine ⟨hβ, (Submodule.ne_bot_iff _).mpr ⟨_, hw, ?_⟩⟩
    intro hz
    apply hv
    apply Lie.targetMapLinear_injective (SchematicImage.inclusion x) k
    simpa only [map_zero] using hz
  have hpow : ringExpChar k ^ P.exponent = 1 := by
    have hn := pow_ne_zero P.exponent (expChar_ne_zero k (ringExpChar k))
    by_contra hne
    have hge : 2 ≤ ringExpChar k ^ P.exponent := by omega
    exact hhigh _ hge (P.character_eq ▸ hroot)
  let : Mono (SchematicImage.projection x).hom.hom :=
    RelativeRoot.VectorLine.mono_of_polynomial_linear e d (SchematicImage.projection x)
      he.1 hd.1 P.scalar (by simpa only [hpow, pow_one] using P.polynomial_eq)
  rw [← SchematicImage.projection_inclusion x]
  change Mono ((SchematicImage.projection x).hom.hom ≫
    (SchematicImage.inclusion x).hom.hom)
  infer_instance

end HomImage
end Langlands.GroupScheme
