import Langlands.AbelianScheme.PolarizedFiniteLevel.FrameEmbeddingHilbertPolynomial
import Langlands.AlgebraicGeometry.RelativeProjectiveSpace.HilbertPieceBoundedEquations

/-! # The common equation bound for cubic embeddings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory

attribute [-instance] Langlands.Scheme.Modules.tensorMonoidalCategory
  Langlands.Scheme.Modules.tensorSymmetricCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry RelativeProjectiveSpace ProjectiveSpace
open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.Scheme.Modules (tensorPow tensorPowIso tensorFunctor tensorComm pullbackTensorPowIso)

variable {P : Prerequisites.{u}} {S : Scheme.{u}} {g d n m : ℕ}

/-- An embedding over the base pulling back the relative projective twist to the actual
cubic bundle. No choice or normalization of a projective frame is required. -/
structure Datum.IsCubicEmbedding (a : Datum P S g d n)
    (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace S m) : Prop where
  toBase : ψ ≫ RelativeProjectiveSpace.toBase S m = a.abelian.X.hom
  isClosedImmersion : IsClosedImmersion ψ
  cubic : Nonempty ((Scheme.Modules.pullback ψ).obj
    (RelativeProjectiveSpace.twistOne S m).obj ≅ a.cubicBundle.obj)

private def recursiveTensorIso {Y : Scheme.{u}} (M : Y.Modules) :
    ∀ k, (Nat.rec (motive := fun _ => Y.Modules) (𝟙_ Y.Modules)
      (fun _ L => L ⊗ M) k) ≅ tensorPow M k
  | 0 => Iso.refl _
  | k + 1 => (Scheme.Modules.tensorIsoSheafify _ M).symm ≪≫
      tensorComm _ M ≪≫ (tensorFunctor Y).mapIso ((Iso.refl M).prod (recursiveTensorIso M k))

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

/-- The image of a cubic embedding satisfies the geometric section-rank test for the
cubic Hilbert polynomial, with threshold one on each geometric fibre. -/
theorem Datum.IsCubicEmbedding.hasGeometricFibreHilbertPolynomial
    {B : Type u} [CommRing B] {a : Datum P (Spec (CommRingCat.of B)) g d n}
    {ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of B)) m}
    (hψ : a.IsCubicEmbedding ψ)
    (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) :
    HasGeometricFibreHilbertPolynomial m (ψ ≫ (isoPullbackSpec m s).hom).ker
      (cubicHilbertPolynomial g d) := by
  intro K _ _ sk
  refine ⟨1, fun k hk => ?_⟩
  let q := ψ ≫ (isoPullbackSpec m s).hom
  let J := q.ker
  have := hψ.isClosedImmersion
  have : IsClosedImmersion q := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  let j := q.toImage
  let t := Spec.map (CommRingCat.ofHom sk)
  let aK := a.pullback t
  let l := pullback.fst a.abelian.X.hom t
  let c := l ≫ j
  have hj : j ≫ J.subschemeι = q := q.toImage_imageι
  have hjbase : j ≫ (J.subschemeι ≫ pullback.snd _ _) = a.abelian.X.hom := by
    rw [← Category.assoc, hj]
    simpa only [q, Category.assoc, isoPullbackSpec, pullback.lift_snd] using hψ.toBase
  have hc : IsPullback c aK.abelian.X.hom (J.subschemeι ≫ pullback.snd _ _) t := by
    exact (IsPullback.of_hasPullback a.abelian.X.hom t).of_iso
      (Iso.refl _) (asIso j) (Iso.refl _) (Iso.refl _)
      (by simp [c, l]) ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by simpa using hjbase.symm) (by simp)
  have hcπ : c ≫ (J.subschemeι ≫ pullback.fst _ _) =
      l ≫ ψ ≫ RelativeProjectiveSpace.toIntegral _ m := by
    simp only [c, Category.assoc, reassoc_of% hj, q, isoPullbackSpec, pullback.lift_fst]
  let L := Langlands.AlgebraicGeometry.twistOne (ULift.{u} ℤ) m
  let M := (Scheme.Modules.pullback (J.subschemeι ≫ pullback.fst _ _)).obj L
  let eL : (Scheme.Modules.pullback c).obj M ≅ aK.cubicBundle.obj :=
    (Scheme.Modules.pullbackComp c _).app L ≪≫
      (Scheme.Modules.pullbackCongr hcπ).app L ≪≫
      ((Scheme.Modules.pullbackComp l (ψ ≫ RelativeProjectiveSpace.toIntegral _ m)).app L).symm ≪≫
      (Scheme.Modules.pullback l).mapIso (((Scheme.Modules.pullbackComp ψ
        (RelativeProjectiveSpace.toIntegral _ m)).app L).symm ≪≫ hψ.cubic.some) ≪≫
      ((LineBundle.forget _).mapIso (a.cubicBundlePullbackIso t)).symm
  let e : (Scheme.Modules.pullback c).obj (hilbertTwistPower m J k) ≅
      (aK.cubicPowerBundle k).obj :=
    (Scheme.Modules.pullback c).mapIso (recursiveTensorIso M k) ≪≫
      pullbackTensorPowIso c M k ≪≫ tensorPowIso eL k ≪≫ (aK.cubicPowerBundleIso k).symm
  have hr := Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback sk _ _ c hc
    (hilbertTwistPower m J k) _ e K (RingHom.id K)
  rw [RingHom.id_comp] at hr
  have : IsProper aK.abelian.X.hom := aK.abelian.proper
  rw [geomFibreH0Finrank_id_eq_relativeH0 _ _
    (isInvertible_of_isLocallyFreeRankOne (aK.cubicPowerBundle k).property),
    (aK.cubicPowerFibreCohomology k (by omega)).2] at hr
  change ((Scheme.Modules.geomFibreH0Finrank _ (hilbertTwistPower m J k) K sk : ℕ) : ℚ) = _
  rw [← hr, cubicHilbertPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, mul_pow]
  push_cast
  ring

private lemma ker_comap_iso {X Y Z : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (e : Y ≅ Z) : (i ≫ e.hom).ker.comap e.hom = i.ker := by
  have h : IsPullback i (𝟙 X) e.hom (i ≫ e.hom) :=
    IsPullback.of_vert_isIso ⟨(Category.id_comp _).symm⟩
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  simpa only [Scheme.Hom.ker_comp_of_isIso] using congrArg Scheme.Hom.ker h.isoPullback_hom_fst

/-- A bound depending only on `g`, `d`, and `m` in the given universe works for all cubic
embeddings over local rings, in particular all fields, with arbitrary datum and level. -/
theorem exists_boundedEquations_cubicEmbedding (g d m : ℕ) :
    ∃ D : ℕ, ∀ (P : Prerequisites.{u}) (n : ℕ) (B : Type u) [CommRing B] [IsLocalRing B]
      (a : Datum P (Spec (CommRingCat.of B)) g d n)
      (ψ : a.abelian.X.left ⟶ RelativeProjectiveSpace (Spec (CommRingCat.of B)) m),
      a.IsCubicEmbedding ψ →
      HasBoundedHomogeneousEquations (ψ ≫ (polynomialIsoSpec B m).inv).ker D := by
  obtain ⟨D, hD⟩ := exists_uniformBoundedHomogeneousEquations_of_hilbertPolynomial.{u}
    m (cubicHilbertPolynomial g d)
  refine ⟨D, fun P n B _ _ a ψ hψ => ?_⟩
  let s := specULiftZIsTerminal.from (Spec (CommRingCat.of B))
  let q := ψ ≫ (isoPullbackSpec m s).hom
  let J := q.ker
  let e := polynomialIsoSpec B m ≪≫ isoPullbackSpec m s
  let i := ψ ≫ (polynomialIsoSpec B m).inv
  have := hψ.isClosedImmersion
  have : IsClosedImmersion q := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (_ ≫ _))
  have hq : q ≫ pullback.snd _ s = a.abelian.X.hom := by
    simpa only [q, Category.assoc, isoPullbackSpec, pullback.lift_snd] using hψ.toBase
  have hJ : J.subschemeι = inv q.toImage ≫ q :=
    (IsIso.eq_inv_comp q.toImage).mpr q.toImage_imageι
  have hflat : Flat (J.subschemeι ≫ pullback.snd _ s) := by
    rw [hJ, Category.assoc, hq]
    infer_instance
  have hlfp : LocallyOfFinitePresentation (J.subschemeι ≫ pullback.snd _ s) := by
    rw [hJ, Category.assoc, hq]
    infer_instance
  have hiq : i ≫ e.hom = q := by simp [i, e, q]
  have hEq := ker_comap_iso i e
  rw [hiq] at hEq
  change HasBoundedHomogeneousEquations i.ker D
  rw [← hEq]
  exact hD B s J hflat hlfp (hψ.hasGeometricFibreHilbertPolynomial s)

end Langlands.AbelianScheme.PolarizedFiniteLevel
