import Langlands.GroupScheme.CentralIsogeny.CommonRefinementConstruction
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny
import Langlands.GroupScheme.CentralIsogeny.SemisimpleTransfer
import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Derived.SemisimplePerfectProof
import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Lifting a homomorphism from a simply connected group through a central isogeny -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SimplyConnectedHomLift

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {C H G : GroupScheme (Spec (CommRingCat.of k))}
  (f : C ⟶ G) (q : H ⟶ G) (hq : IsCentralIsogeny q)

section Graph

variable [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]

/-- The commutator of the source paired with its canonical lift to the cover. -/
private def graphCommutator : C.X ⊗ C.X ⟶ (C ⊗ H).X :=
  lift (commutatorMap (𝟙 C) (𝟙 C))
    ((f.hom.hom ⊗ₘ f.hom.hom) ≫ CommutatorDescent.hom q hq.isCentral_kernelι)

private theorem graphCommutator_fst :
    graphCommutator f q hq ≫ fst C.X H.X = commutatorMap (𝟙 C) (𝟙 C) :=
  lift_fst _ _

private theorem graphCommutator_snd :
    graphCommutator f q hq ≫ snd C.X H.X =
      (f.hom.hom ⊗ₘ f.hom.hom) ≫ CommutatorDescent.hom q hq.isCentral_kernelι :=
  lift_snd _ _

private theorem graphCommutator_comp :
    graphCommutator f q hq ≫ fst C.X H.X ≫ f.hom.hom =
      graphCommutator f q hq ≫ snd C.X H.X ≫ q.hom.hom := by
  rw [← Category.assoc, graphCommutator_fst, ← Category.assoc,
    graphCommutator_snd, Category.assoc, CommutatorDescent.hom_comp]
  exact (CommutatorDescent.tensorHom_commutatorMap f).symm

private theorem graphCommutator_one :
    lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C.X) 1 ≫
      graphCommutator f q hq = 1 := by
  apply (productPointsEquiv C H _).injective
  rw [map_one]
  apply Prod.ext
  · rw [productPointsEquiv_fst, Category.assoc, graphCommutator_fst,
      commutatorMap_lift]
    simp
  · rw [productPointsEquiv_snd, Category.assoc, graphCommutator_snd,
      ← Category.assoc]
    have hone :
        lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C.X) 1 ≫
          (f.hom.hom ⊗ₘ f.hom.hom) = lift (1 : _ ⟶ G.X) 1 := by
      ext <;> simp
    rw [hone, CommutatorDescent.one_hom]
    rfl

variable (D : GeneratedImage (graphCommutator f q hq))

private theorem factor_fst :
    D.factor ≫ (D.inclusion ≫ fst C H).hom.hom =
      commutatorMap (𝟙 C) (𝟙 C) := by
  rw [Grp.comp_hom_hom, Grp.fst_hom_hom, ← Category.assoc, D.factor_comp,
    graphCommutator_fst]

private theorem factor_comp_eq :
    D.factor ≫ ((D.inclusion ≫ fst C H) ≫ f).hom.hom =
      D.factor ≫ ((D.inclusion ≫ snd C H) ≫ q).hom.hom := by
  simp only [Grp.comp_hom_hom, Grp.fst_hom_hom, Grp.snd_hom_hom]
  rw [← Category.assoc, ← Category.assoc, D.factor_comp,
    ← Category.assoc, ← Category.assoc, D.factor_comp]
  exact graphCommutator_comp f q hq

private theorem projections_comp_eq [IsReduced D.group.X.left] [IsSeparated G.X.hom]
    (n : ℕ) (hn : IsDominant (D.powerMap n).left) :
    (D.inclusion ≫ fst C H) ≫ f = (D.inclusion ≫ snd C H) ≫ q := by
  have hpow :
      D.powerMap n ≫ ((D.inclusion ≫ fst C H) ≫ f).hom.hom =
        D.powerMap n ≫ ((D.inclusion ≫ snd C H) ≫ q).hom.hom := by
    rw [GeneratedImage.powerMap, orderedPowerMap_comp, orderedPowerMap_comp,
      factor_comp_eq]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated G.X.hom (by rw [Over.w, Over.w])
    (D.powerMap n).left (congrArg (fun z => z.left) hpow)

private theorem isDominant_fst
    (hC : derivedSubgroup C = ⊤)
    (E : GeneratedImage (commutatorMap (𝟙 C) (𝟙 C))) (m : ℕ)
    (hm : IsDominant (E.powerMap m).left) :
    IsDominant (D.inclusion ≫ fst C H).hom.hom.left := by
  have h := CommonRefinement.isDominant_orderedPowerMap_of_perfect hC E m hm
  have heq : D.powerMap m ≫ (D.inclusion ≫ fst C H).hom.hom =
      orderedPowerMap (commutatorMap (𝟙 C) (𝟙 C)) m := by
    rw [GeneratedImage.powerMap, orderedPowerMap_comp, factor_fst]
  rw [← heq, Over.comp_left] at h
  exact IsDominant.of_comp (H := h)

end Graph

include hq

private theorem exists_lift (hC : IsSimplyConnected C) (hH : IsConnectedReductive H)
    (hG : IsSeparated G.X.hom) :
    ∃ a : C ⟶ H, a ≫ q = f := by
  have := hq.isFinite
  have := hq.flat
  have := hq.surjective
  have := hG
  let hCr := hC.isSemisimple.isConnectedReductive
  obtain ⟨hVa, hVf, -, hVi⟩ := smoothConnectedAffineGeometry.2 k C C
    hCr.smooth hCr.isAffineHom hCr.connectedSpace hCr.smooth hCr.isAffineHom hCr.connectedSpace
  obtain ⟨hPa, -, -, -⟩ := smoothConnectedAffineGeometry.2 k C H
    hCr.smooth hCr.isAffineHom hCr.connectedSpace hH.smooth hH.isAffineHom hH.connectedSpace
  obtain ⟨D, hDs, hDa, hDc, n, -, hn⟩ := ImageGeneration.pointedImageGeneration k (C ⊗ H)
    (CommonRefinement.smooth_tensor hCr.smooth hH.smooth) hPa
    (C.X ⊗ C.X) hVa hVf hVi (lift 1 1)
    (graphCommutator f q hq) (graphCommutator_one f q hq)
  obtain ⟨E, -, -, -, m, -, hm⟩ := ImageGeneration.pointedImageGeneration k C
    hCr.smooth hCr.isAffineHom (C.X ⊗ C.X) hVa hVf hVi (lift 1 1)
    (commutatorMap (𝟙 C) (𝟙 C)) CommonRefinement.one_commutatorMap
  let : Smooth D.group.X.hom := hDs
  let : IsReduced D.group.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k
      D.group.X.left D.group.X.hom
  have hcomm := projections_comp_eq f q hq D n hn
  have hcomm' : D.inclusion ≫ fst C H ≫ f = D.inclusion ≫ snd C H ≫ q := by
    simpa only [Category.assoc] using hcomm
  have hdom := isDominant_fst f q hq D (semisimplePerfect k C hC.isSemisimple) E m hm
  have hp := isCentralIsogeny_fst_of_closedSubgroup hq hCr.smooth D.inclusion D.closed
    hcomm' hDs hDa hdom
  let : GeometricallyConnected D.group.X.hom := hDc
  have hDconn : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  have hD := IsSemisimple.of_isCentralIsogeny _ hp hC.isSemisimple hDs hDconn
  let p := D.inclusion ≫ fst C H
  have : IsIso p := hC.central_isogeny_isIso D.group p hD hp
  refine ⟨inv p ≫ D.inclusion ≫ snd C H, ?_⟩
  calc
    (inv p ≫ D.inclusion ≫ snd C H) ≫ q =
        inv p ≫ ((D.inclusion ≫ snd C H) ≫ q) := by simp only [Category.assoc]
    _ = inv p ≫ (p ≫ f) := by rw [← hcomm]
    _ = f := by simp

/-- The unique lift of a homomorphism from a simply connected group through a central
isogeny with connected reductive source and separated target. -/
def liftHom (hC : IsSimplyConnected C) (hH : IsConnectedReductive H)
    (hG : IsSeparated G.X.hom) : C ⟶ H :=
  Classical.choose (exists_lift f q hq hC hH hG)

/-- The constructed lift has precisely the prescribed composite. -/
theorem liftHom_comp (hC : IsSimplyConnected C) (hH : IsConnectedReductive H)
    (hG : IsSeparated G.X.hom) :
    liftHom f q hq hC hH hG ≫ q = f :=
  Classical.choose_spec (exists_lift f q hq hC hH hG)

/-- There is only one lift as an actual group-scheme homomorphism. -/
theorem liftHom_unique (hC : IsSimplyConnected C) (hH : IsConnectedReductive H)
    (hG : IsSeparated G.X.hom) (a : C ⟶ H) (ha : a ≫ q = f) :
    a = liftHom f q hq hC hH hG := by
  apply hq.cancel_of_connectedReductive hC.isSemisimple.isConnectedReductive
  rw [ha, liftHom_comp]

end Langlands.GroupScheme.SimplyConnectedHomLift
