import Langlands.Shimura.PEL.HarrisProjectiveEndomorphismFinitePieces
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.TensorPowerGauge
import Langlands.AlgebraicGeometry.Modules.PullbackMonoidal
import Langlands.AlgebraicGeometry.Modules.TensorPowerDistributivity
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleProof
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections

/-! # Section ranks of the graph of an endomorphism -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Langlands.AbelianScheme Langlands.GroupScheme.Cartier
open Langlands.AlgebraicGeometry.Modules
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.Modules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

-- Use the same monoidal product as the affine Hom graph calculation.
attribute [-instance] Langlands.Scheme.Modules.tensorMonoidalCategory
  Langlands.Scheme.Modules.tensorSymmetricCategory

namespace Langlands.Shimura.PEL.ProjectiveEndomorphismGraphPieces

variable {R K : Type u} [CommRing R] [Field K]
    {B : AbelianScheme (Spec (CommRingCat.of R))}
    {s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)}
    (χ : RelativeHom B.toCommGroupScheme B.toCommGroupScheme (Over.mk s))
    (L : B.X.left.Modules)
    {Y : Scheme.{u}} (c : Y ⟶ pullback B.X.hom s) (v : Y ⟶ Y)

local notation "π" => pullback.fst B.X.hom s
local notation "M₁" => (Scheme.Modules.pullback (π)).obj L
local notation "M₂" => (Scheme.Modules.pullback (fstMap χ)).obj L
local notation "pb" => Scheme.Modules.pullback
local notation "tensorSheaf" => Langlands.Scheme.Modules.tensorObj

/-- Transport the graph tensor power along a comparison of the fibre and of the
endomorphism. A power of the chosen line bundle scales the exponent by `q`. -/
def fibreGraphPowerIso
    (hv : v ≫ c ≫ (π) = c ≫ fstMap χ)
    (M : Y.Modules) (q : ℕ) (e : (pb (c ≫ (π))).obj L ≅ tensorPow M q) (k : ℕ) :
    (pb c).obj ((M₁ ⊗ M₂).tensorPowFLT k) ≅
      tensorPow (tensorSheaf ((pb v).obj M) M) (q * k) := by
  let e₂ : (pb c).obj M₂ ≅ tensorPow ((pb v).obj M) q :=
    (Scheme.Modules.pullbackComp c (fstMap χ)).app L ≪≫
      (Scheme.Modules.pullbackCongr hv.symm).app L ≪≫
      (Scheme.Modules.pullbackComp v (c ≫ (π))).symm.app L ≪≫
      (pb v).mapIso e ≪≫ actualPullbackTensorPowIso v M q
  let e₁ := (Scheme.Modules.pullbackComp c (π)).app L ≪≫ e
  let t : (pb c).obj (M₁ ⊗ M₂) ≅ tensorPow (tensorSheaf ((pb v).obj M) M) q :=
    (pb c).mapIso (monoidalTensorIso M₁ M₂) ≪≫
      pullbackTensorIso c M₁ M₂ ≪≫ tensorComm ((pb c).obj M₁) ((pb c).obj M₂) ≪≫
      tensorMapIso e₂ e₁ ≪≫ (tensorPowTensorIso ((pb v).obj M) M q).symm
  exact (pb c).mapIso (TensorPowerGauge.tensorPowComparison (M₁ ⊗ M₂) k) ≪≫
    actualPullbackTensorPowIso c (M₁ ⊗ M₂) k ≪≫ tensorPowIso t k ≪≫
    tensorPowMulIso (tensorSheaf ((pb v).obj M) M) q k

/-- The geometric rank in the affine endomorphism graph test is the rank
of sections on an isomorphic fibre with the corresponding graph bundle. -/
theorem fibreGraphSectionRank_eq_finrank
    (f : Y ⟶ Spec (CommRingCat.of K)) [IsProper f] [IsIso c]
    (hc : c ≫ pullback.snd B.X.hom s = f)
    (hv : v ≫ c ≫ (π) = c ≫ fstMap χ)
    (M : LineBundle Y) (q : ℕ) (e : (pb (c ≫ (π))).obj L ≅ tensorPow M.obj q)
    (k : ℕ) :
    fibreGraphSectionRank (L := L) s χ K (RingHom.id K) k =
      Module.finrank K ((relativeGlobalSections f).obj
        (tensorPow (tensorSheaf ((pb v).obj M.obj) M.obj) (q * k))) := by
  let N := LineBundle.tensor pullbackTensorComparisonIsIso ((LineBundle.pullback v).obj M) M
  let Nk := tensorPow N.obj (q * k)
  have hNk := isInvertible_of_isLocallyFreeRankOne
    (tensorPow_isLocallyFreeRankOne Y N (q * k))
  have hsq : IsPullback c f (pullback.snd B.X.hom s)
      (Spec.map (CommRingCat.ofHom (RingHom.id K))) := by
    change IsPullback c f (pullback.snd B.X.hom s) (Spec.map (𝟙 _))
    rw [Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using hc⟩
  have hr := Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback
    (RingHom.id K) _ f c hsq ((M₁ ⊗ M₂).tensorPowFLT k) Nk
      (fibreGraphPowerIso χ L c v hv M.obj q e k) K (RingHom.id K)
  rw [RingHom.id_comp] at hr
  have hpower (n : ℕ) :
      Nat.rec (motive := fun _ => (pullback B.X.hom s).Modules)
        (𝟙_ (pullback B.X.hom s).Modules) (fun _ M' => M' ⊗ (M₁ ⊗ M₂)) n =
        (M₁ ⊗ M₂).tensorPowFLT n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change (_ ⊗ (M₁ ⊗ M₂)) = ((M₁ ⊗ M₂).tensorPowFLT n ⊗ (M₁ ⊗ M₂))
      rw [ih]
  rw [fibreGraphSectionRank, hpower, ← hr,
    Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections K f Nk hNk]
  change (letI : Module K Γ(Nk, ⊤) :=
    Module.compHom Γ(Nk, ⊤) (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      f.appLE ⊤ ⊤ le_top).hom); Module.finrank K Γ(Nk, ⊤)) = _
  have happ : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f (U := ⊤)
  rw [happ]
  exact ((relativeGlobalSectionsIso f).app Nk).toLinearEquiv.finrank_eq

end Langlands.Shimura.PEL.ProjectiveEndomorphismGraphPieces
