import Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPowerFibreCohomology
import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingBaseChange
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.HilbertClassifying
import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundleTensorPow
import Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof
import Langlands.AlgebraicGeometry.Picard.NoetherianLineBundleSeesawProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_id_eq_finrank_sections

/-! # Hilbert-polynomial values of frame-normalized cubic embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

-- Use the monoidal structure of the published Hilbert-family statement for its input powers.
attribute [-instance] Langlands.Scheme.Modules.tensorMonoidalCategory
  Langlands.Scheme.Modules.tensorSymmetricCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.Scheme.Modules (tensorPow tensorPowIso tensorFunctor tensorComm
  pullbackTensorPowIso pullbackUnitIso tensorRightUnitor)

/-- The polynomial of the cubic embedding of a dimension `g` abelian scheme with
polarization degree `d²`. -/
def cubicHilbertPolynomial (g d : ℕ) : Polynomial ℚ :=
  Polynomial.C ((6 : ℚ) ^ g * d) * Polynomial.X ^ g

private abbrev hilbertPower {Y : Scheme.{u}} (M : Y.Modules) (k : ℕ) : Y.Modules :=
  Nat.rec (motive := fun _ => Y.Modules) (𝟙_ Y.Modules) (fun _ L => L ⊗ M) k

private def hilbertPowerIso {Y : Scheme.{u}} (M : Y.Modules) :
    ∀ k, hilbertPower M k ≅ tensorPow M k
  | 0 => Iso.refl _
  | k + 1 => (Scheme.Modules.tensorIsoSheafify (hilbertPower M k) M).symm ≪≫
      tensorComm (hilbertPower M k) M ≪≫
      (tensorFunctor Y).mapIso ((Iso.refl M).prod (hilbertPowerIso M k))

private lemma geomFibreH0Finrank_id_eq_relativeH0 {K : Type u} [Field K] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of K)) [IsProper f] (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertibleFLT M) :
    Scheme.Modules.geomFibreH0Finrank f M K (RingHom.id K) =
      Module.finrank K ((relativeCohomology f 0).obj M) := by
  rw [Scheme.Modules.geomFibreH0Finrank_id_eq_finrank_sections K f M hM]
  have h : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f (U := ⊤)
  change (letI : Module K Γ(M, ⊤) :=
    Module.compHom Γ(M, ⊤) (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      f.appLE ⊤ ⊤ le_top).hom); Module.finrank K Γ(M, ⊤)) = _
  rw [h]
  exact (((relativeGlobalSectionsIso f).app M) ≪≫
    ((relativeCohomologyZeroIso f).app M).symm).toLinearEquiv.finrank_eq

variable {P : Prerequisites.{u}} {g d n m : ℕ}

private def frameTwistOverFieldIso {K : Type u} [Field K]
    {a : Datum P (Spec (CommRingCat.of K)) g d n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of K)) m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (hψ : a.IsFrameEmbedding ρ ψ) :
    (Scheme.Modules.pullback (ψ ≫ RelativeProjectiveSpace.toIntegral _ m)).obj
      (twistOne (ULift.{u} ℤ) m) ≅ a.cubicBundle.obj := by
  let N := hψ.cubic.choose
  let i := hψ.cubic.choose_spec.some
  let iN := (fieldLineBundleTriviality K N).some
  exact ((Scheme.Modules.pullbackComp ψ (RelativeProjectiveSpace.toIntegral _ m)).app _).symm ≪≫
    (LineBundle.forget _).mapIso i ≪≫
    (tensorFunctor _).mapIso ((Iso.refl a.cubicBundle.obj).prod
      ((Scheme.Modules.pullback a.abelian.X.hom).mapIso iN ≪≫ pullbackUnitIso _)) ≪≫
    tensorRightUnitor _

/-- For the closed subscheme cut out by a frame embedding in the fibre-product model of
projective space, the power of the actual projective twist has the prescribed number of
sections on every geometric fibre, in all positive exponents. -/
theorem Datum.IsFrameEmbedding.geomFibreH0Finrank_eq_cubicHilbertPolynomial
    {B : Type u} [CommRing B] {a : Datum P (Spec (CommRingCat.of B)) g d n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of B)) m}
    {ρ : Fin (m + 2) → Fin (2 * g) → ZMod n} (hψ : a.IsFrameEmbedding ρ ψ)
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ)))
    (J : (Limits.pullback (projectiveSpaceToSpec (ULift.{u} ℤ) m) s).IdealSheafData)
    (hJ : (ψ ≫ (RelativeProjectiveSpace.isoPullbackSpec m s).hom).ker = J)
    (K : Type u) [Field K] [IsAlgClosed K] (sk : B →+* K) (k : ℕ) (hk : 0 < k) :
    ((Scheme.Modules.geomFibreH0Finrank (J.subschemeι ≫ pullback.snd _ _)
      (Nat.rec (motive := fun _ => J.subscheme.Modules) (𝟙_ J.subscheme.Modules)
        (fun _ M => M ⊗ (Scheme.Modules.pullback
          (J.subschemeι ≫ pullback.fst _ _)).obj (twistOne (ULift.{u} ℤ) m)) k) K sk : ℕ) : ℚ) =
      (cubicHilbertPolynomial g d).eval (k : ℚ) := by
  let q := ψ ≫ (RelativeProjectiveSpace.isoPullbackSpec m s).hom
  have := hψ.isClosedImmersion
  have : IsClosedImmersion q := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  have hker : J.subschemeι.ker = q.ker := J.ker_subschemeι.trans hJ.symm
  let j := IsClosedImmersion.lift J.subschemeι q hker.le
  have hj : j ≫ J.subschemeι = q := IsClosedImmersion.lift_fac _ _ _
  have : IsIso j := IsClosedImmersion.isIso_lift _ _ hker
  let t := Spec.map (CommRingCat.ofHom sk)
  let aK := a.pullback t
  let c := pullback.fst a.abelian.X.hom t ≫ j
  have hjbase : j ≫ (J.subschemeι ≫ pullback.snd _ _) = a.abelian.X.hom := by
    rw [← Category.assoc, hj]
    simpa only [q, Category.assoc, RelativeProjectiveSpace.isoPullbackSpec, pullback.lift_snd]
      using hψ.toBase
  have hc : IsPullback c aK.abelian.X.hom (J.subschemeι ≫ pullback.snd _ _) t := by
    exact (IsPullback.of_hasPullback a.abelian.X.hom t).of_iso
      (Iso.refl _) (asIso j) (Iso.refl _) (Iso.refl _)
      (by simp [c]) ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simpa using hjbase.symm) (by simp)
  have hcπ : c ≫ (J.subschemeι ≫ pullback.fst _ _) =
      a.pullbackEmbedding t ψ ≫ RelativeProjectiveSpace.toIntegral _ m := by
    rw [Datum.pullbackEmbedding, RelativeProjectiveSpace.lift_toIntegral]
    simp only [c, Category.assoc, reassoc_of% hj]
    simp only [q, Category.assoc, RelativeProjectiveSpace.isoPullbackSpec, pullback.lift_fst]
  let L := twistOne (ULift.{u} ℤ) m
  let M := (Scheme.Modules.pullback (J.subschemeι ≫ pullback.fst _ _)).obj L
  let e : (Scheme.Modules.pullback c).obj (hilbertPower M k) ≅ (aK.cubicPowerBundle k).obj :=
    (Scheme.Modules.pullback c).mapIso (hilbertPowerIso M k) ≪≫
      pullbackTensorPowIso c M k ≪≫
      tensorPowIso ((Scheme.Modules.pullbackComp c _).app L ≪≫
        (Scheme.Modules.pullbackCongr hcπ).app L ≪≫
        frameTwistOverFieldIso (hψ.pullback (f := t))) k ≪≫
      (aK.cubicPowerBundleIso k).symm
  have hr := Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback sk _ _ c hc
    (hilbertPower M k) _ e K (RingHom.id K)
  rw [RingHom.id_comp] at hr
  have : IsProper aK.abelian.X.hom := aK.abelian.proper
  rw [geomFibreH0Finrank_id_eq_relativeH0 _ _
    (isInvertible_of_isLocallyFreeRankOne (aK.cubicPowerBundle k).property),
    (aK.cubicPowerFibreCohomology k hk).2] at hr
  change ((Scheme.Modules.geomFibreH0Finrank _ (hilbertPower M k) K sk : ℕ) : ℚ) = _
  rw [← hr, cubicHilbertPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, mul_pow]
  push_cast
  ring

end Langlands.AbelianScheme.PolarizedFiniteLevel
