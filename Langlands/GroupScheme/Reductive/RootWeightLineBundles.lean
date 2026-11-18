import Langlands.GroupScheme.Torus.RootWeightTestSystem
import Langlands.AlgebraicGeometry.Modules.AffineTestLineBundle
import Langlands.GroupScheme.Reductive.PicardRootWeightLines
import Langlands.GroupScheme.Reductive.GlobalPinningFrames

/-! # Actual root-weight line bundles and coherent affine root frames

For a reductive group `G` over an arbitrary scheme `S`, a fibrewise maximal coordinate torus `t`
and a global coordinate root datum `P` of `(G, t)`, each root `α` gives an actual line bundle
`rootLineBundle α` on `S`. For every affine test `a : Spec R ⟶ S` it comes with the canonical
isomorphism `a^* L_α ≅ (actual exponent-weight module)^~` (`rootFrame`), coherent under coefficient
extension (`rootFrame_hom_eq`). Under the hypothesis that all line bundles on `S` are trivial,
chosen trivializations give coherent affine root frames in the sense of
`CoordinateRootDatum.AffineRootFrames.IsCoherent` (`picardRootFrames_isCoherent`).
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- Affineness of the structure morphism is preserved by base change. -/
local instance rootLineAffine {X Y : Scheme.{u}} (H : GroupScheme X) [IsAffineHom H.X.hom]
    (a : Y ⟶ X) : IsAffineHom ((baseChange a).obj H).X.hom :=
  MorphismProperty.pullback_snd H.X.hom a inferInstance

/-- Smoothness of the structure morphism is preserved by base change. -/
local instance rootLineSmooth {X Y : Scheme.{u}} (H : GroupScheme X) [Smooth H.X.hom]
    (a : Y ⟶ X) : Smooth ((baseChange a).obj H).X.hom :=
  inferInstanceAs (Smooth (pullback.snd H.X.hom a))

namespace CoordinateRootDatum

variable {S : Scheme.{u}} {I J : Type u} [Fintype I] [DecidableEq I]
  {G : GroupScheme S} (hG : IsReductive G) (t : splitTorus S I ⟶ G)
  (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
  (P : RootDatum J (I → ℤ) (I → ℤ))
  (hP : letI := hG.isAffineHom; IsGlobalCoordinateRootDatumOf I G t P)

/-- The affine test system of actual root-weight modules of the root `α`. -/
def rootWeightSystem (α : J) : AffineTestSystem S :=
  letI := hG.isAffineHom
  letI := hG.smooth
  splitTorus.weightTestSystem I G t (P.root α)

include hmax hP in
/-- On every affine chart the associated sheaf of the root-weight module is locally free of
rank one. -/
theorem isLocallyFreeRankOne_rootWeight (α : J) (U : S.Opens) (hU : IsAffineOpen U) :
    IsLocallyFreeRankOne (tilde ((rootWeightSystem hG t P α).obj hU.fromSpec)) := by
  let := hG.isAffineHom
  let := hG.smooth
  have hGa := hG.baseChange hU.fromSpec
  have hmaxa := hmax.baseChange_coordinates hU.fromSpec
  have hPa := hP.affinePullback t P Γ(S, U) hU.fromSpec
  have : Module.Finite Γ(S, U) ((rootWeightSystem hG t P α).obj hU.fromSpec) :=
    splitTorus.finite_exponentWeightSpace I ((baseChange hU.fromSpec).obj G)
      ((splitTorus.baseChangeIso hU.fromSpec I).inv ≫ (baseChange hU.fromSpec).map t) (P.root α)
  have : Module.Projective Γ(S, U) ((rootWeightSystem hG t P α).obj hU.fromSpec) :=
    splitTorus.projective_exponentWeightSpace I ((baseChange hU.fromSpec).obj G)
      ((splitTorus.baseChangeIso hU.fromSpec I).inv ≫ (baseChange hU.fromSpec).map t) (P.root α)
  exact Langlands.Algebra.isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one
    ((rootWeightSystem hG t P α).obj hU.fromSpec)
    (rootWeightRank_eq_one I ((baseChange hU.fromSpec).obj G) hGa _ hmaxa P hPa α)

/-- **The actual root-weight line bundle** of the root `α`. -/
def rootLineBundle (α : J) : LineBundle S :=
  (rootWeightSystem hG t P α).toLineBundle (isLocallyFreeRankOne_rootWeight hG t hmax P hP α)

lemma rootLineBundle_obj (α : J) :
    (rootLineBundle hG t hmax P hP α).obj = (rootWeightSystem hG t P α).toModules :=
  rfl

/-- **The canonical affine comparison** `a^* L_α ≅ (exponent-weight module)^~` on an affine test
`a : Spec R ⟶ S`. -/
def rootFrame {R : CommRingCat.{u}} (α : J) (a : Spec R ⟶ S) :
    (Scheme.Modules.pullback a).obj (rootLineBundle hG t hmax P hP α).obj ≅
      tilde (letI := hG.isAffineHom
        ModuleCat.of R (splitTorus.exponentWeightSpace I ((baseChange a).obj G)
          ((splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t) (P.root α))) :=
  (rootWeightSystem hG t P α).frame a

/-- **Coherence of the affine comparisons** under coefficient extension along `R → A`: the
comparison on `b = Spec A ⟶ Spec R ⟶ S` is the pullback of the comparison on `a`, followed by
`tildePullbackAlgebraIso` and the actual exponent-weight base-change equivalence normalized by
`baseChangeCompIso` (`splitTorus.weightExt`), after the canonical scheme-module identification
`b^* ≅ p^* a^*`. -/
theorem rootFrame_hom_eq {R A : CommRingCat.{u}} [Algebra R A] (α : J) (a : Spec R ⟶ S)
    {b : Spec A ⟶ S} (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b) :
    (rootFrame hG t hmax P hP α b).hom =
      ((Scheme.Modules.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap R A))) a).app
          (rootLineBundle hG t hmax P hP α).obj ≪≫
          (Scheme.Modules.pullbackCongr h).app (rootLineBundle hG t hmax P hP α).obj).inv ≫
        (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
          (rootFrame hG t hmax P hP α a).hom ≫
          (tildePullbackAlgebraIso R A ((rootWeightSystem hG t P α).obj a)).hom ≫
            tilde.map ((rootWeightSystem hG t P α).extHom a h) :=
  (rootWeightSystem hG t P α).frame_hom_eq a h

lemma rootWeightSystem_ext {R A : CommRingCat.{u}} [Algebra R A] (α : J) {a : Spec R ⟶ S}
    {b : Spec A ⟶ S} (h : Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ a = b)
    (z : A ⊗[R] (rootWeightSystem hG t P α).obj a) :
    (rootWeightSystem hG t P α).ext h z =
      (letI := hG.isAffineHom; letI := hG.smooth; splitTorus.weightExt I G t (P.root α) h z) :=
  rfl

variable (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))

/-- **Coherent affine root frames from the Picard hypothesis.** Chosen trivializations of the
root-weight line bundles give, on every affine test, a linear equivalence from the coordinate ring
to the actual root-weight module. -/
def picardRootFrames : letI := hG.isAffineHom; AffineRootFrames t P :=
  fun _ _ a α => (rootWeightSystem hG t P α).picardFrame
    (isLocallyFreeRankOne_rootWeight hG t hmax P hP α) hPic a

/-- **Coherence of the Picard root frames**: after extending coefficients to the same affine
test ring, the actual root-vector dual-number points agree in the original group. -/
theorem picardRootFrames_isCoherent :
    letI := hG.isAffineHom; (picardRootFrames hG t hmax P hP hPic).IsCoherent := by
  let := hG.isAffineHom
  let := hG.smooth
  intro R A _ _ _ a α
  have hab : Spec.map (CommRingCat.ofHom (algebraMap (CommRingCat.of R) (CommRingCat.of A))) ≫ a =
      algebraBaseMap R A ≫ a := rfl
  have hext := (rootWeightSystem hG t P α).picardFrame_ext
    (isLocallyFreeRankOne_rootWeight hG t hmax P hP α) hPic a hab
  have hpt := splitTorus.weightExt_point I G t (P.root α) hab
    ((rootWeightSystem hG t P α).picardFrame
      (isLocallyFreeRankOne_rootWeight hG t hmax P hP α) hPic a 1)
  exact hpt.symm.trans (congrArg (fun z : splitTorus.testWeightSpace I G t (P.root α)
      (algebraBaseMap R A ≫ a) =>
    (z : Additive (lieKernel ((baseChange (algebraBaseMap R A ≫ a)).obj G) A)).toMul.val.left ≫
      pullback.fst G.X.hom (algebraBaseMap R A ≫ a)) hext).symm

end CoordinateRootDatum

end Langlands.GroupScheme
