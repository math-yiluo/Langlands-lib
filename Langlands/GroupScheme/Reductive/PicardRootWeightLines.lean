import Langlands.GroupScheme.Torus.RootWeightTrivialization
import Langlands.GroupScheme.Reductive.FibrewiseRootDatum
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.AlgebraicGeometry.Picard.LineBundleLocusRestriction
import Langlands.AlgebraicGeometry.Modules.TildePullback

/-! # Actual root-weight lines from triviality of scheme line bundles -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Algebra

/-- A finite projective module of rank one at every prime gives an actual
locally free rank-one associated sheaf. -/
theorem isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1) :
    Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne (tilde M) := by
  intro p
  obtain ⟨r, hr, hline⟩ := exists_principal_tensorLine_of_rankAtStalk_eq_one p (hrank p)
  let A : CommRingCat.{u} := .of (Localization.Away r)
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  obtain ⟨e⟩ := hline A (IsLocalization.Away.algebraMap_isUnit r)
  let t : (Scheme.Modules.pullback f).obj (tilde M) ≅
      SheafOfModules.unit (Spec A).ringCatSheaf :=
    Langlands.Scheme.Modules.tildePullbackAlgebraIso R A M ≪≫
      (tilde.functor A).mapIso e.toModuleIso ≪≫ tildeSelf
  have hp : p ∈ f.opensRange := by
    rw [Scheme.Hom.opensRange_localizationAway]
    exact hr
  obtain ⟨q, hq⟩ := hp
  let t' : (tilde M).restrict f ≅ SheafOfModules.unit (Spec A).ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback f).app (tilde M) ≪≫ t
  have h : Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne
      ((tilde M).restrict f) :=
    (Langlands.AlgebraicGeometry.Picard.LineBundle.trivial _).property.of_iso t'.symm
  have hq' : q ∈ Langlands.AlgebraicGeometry.Picard.rankOneLocus ((tilde M).restrict f) :=
    (Langlands.AlgebraicGeometry.Picard.mem_rankOneLocus _ q).mpr (h q)
  rw [Langlands.AlgebraicGeometry.Picard.rankOneLocus_restrict] at hq'
  apply (Langlands.AlgebraicGeometry.Picard.mem_rankOneLocus _ p).mp
  change f q ∈ Langlands.AlgebraicGeometry.Picard.rankOneLocus (tilde M) at hq'
  simpa only [hq] using hq'

/-- Triviality of actual scheme line bundles makes every finite projective
module of constant rank one free over the original affine coordinate ring. -/
theorem nonempty_linearEquiv_of_lineBundlesTrivial_of_rankAtStalk_eq_one
    {R : CommRingCat.{u}}
    (hPic : ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle (Spec R),
      Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial (Spec R)))
    (M : ModuleCat.{u} R) [Module.Finite R M] [Module.Projective R M]
    (hrank : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = 1) :
    Nonempty (M ≃ₗ[R] R) := by
  let L : Langlands.AlgebraicGeometry.Picard.LineBundle (Spec R) :=
    ⟨tilde M, isLocallyFreeRankOne_tilde_of_rankAtStalk_eq_one M hrank⟩
  obtain ⟨e⟩ := hPic L
  let t : tilde M ≅ tilde (ModuleCat.of R R) :=
    (Langlands.AlgebraicGeometry.Picard.LineBundle.forget (Spec R)).mapIso e ≪≫
      tildeSelf.symm
  exact ⟨(tilde.fullyFaithfulFunctor.preimageIso t).toLinearEquiv⟩

end Langlands.Algebra

namespace Langlands.GroupScheme

/-- Every actual root-weight summand in a full fibrewise datum has rank one
at every prime of the affine base. -/
theorem rootWeightRank_eq_one
    {R : Type u} [CommRing R]
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : letI := hG.isAffineHom; IsFibrewiseRootDatumOf I G i P)
    (α : J) (p : Spec (CommRingCat.of R)) :
    letI := hG.isAffineHom
    letI := hG.smooth
    splitTorus.exponentWeightRank I G i (P.root α) p = 1 := by
  let := hG.isAffineHom
  let := hG.smooth
  let k := (Spec (CommRingCat.of R)).residueField p
  let φ := Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField p)
  let : Algebra R k := φ.hom.toAlgebra
  have hb : algebraBaseMap R k = (Spec (CommRingCat.of R)).fromSpecResidueField p :=
    Spec.map_preimage _
  have hp : (algebraBaseMap R k) (IsLocalRing.closedPoint k) = p := by
    rw [hb]
    exact Scheme.fromSpecResidueField_apply _ _
  let Gk := (baseChange (algebraBaseMap R k)).obj G
  have : IsAffineHom Gk.X.hom :=
    inferInstanceAs (IsAffineHom (pullback.snd G.X.hom (algebraBaseMap R k)))
  have hroot : splitTorus.exponentCharacter (Spec (CommRingCat.of k)) I (P.root α) ∈
      roots (splitTorus.baseChangeHom (K := k) G I i) :=
    (hP.mem_roots_iff k (P.root α)).mpr ⟨α, rfl⟩
  obtain ⟨e⟩ := splitRootLieLine k Gk (hG.isConnectedReductive_algebraMap k)
    (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I)
    (isSplitTorus_splitTorus I) _
    (splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax k) _ hroot
  have he := e.finrank_eq
  rw [Module.finrank_self] at he
  rw [← hp, ← splitTorus.finrank_exponentWeightSpace_fieldBaseChange,
    splitTorus.exponentWeightSpace_eq_weightSpace_exponentCharacter]
  exact he.symm

/-- Triviality of actual scheme line bundles trivializes every actual
root-weight module of a supplied full fibrewise split root datum. -/
theorem rootWeightSpace_nonempty_linearEquiv_of_lineBundlesTrivial
    {R : Type u} [CommRing R]
    (hPic : ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle (Spec (CommRingCat.of R)),
      Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial
        (Spec (CommRingCat.of R))))
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : letI := hG.isAffineHom; IsFibrewiseRootDatumOf I G i P)
    (α : J) :
    letI := hG.isAffineHom
    Nonempty (splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R) := by
  let := hG.isAffineHom
  let := hG.smooth
  let M : ModuleCat (CommRingCat.of R) :=
    ModuleCat.of (CommRingCat.of R) (splitTorus.exponentWeightSpace I G i (P.root α))
  let : Module.Finite (CommRingCat.of R) M :=
    splitTorus.finite_exponentWeightSpace I G i (P.root α)
  let : Module.Projective (CommRingCat.of R) M :=
    splitTorus.projective_exponentWeightSpace I G i (P.root α)
  exact Langlands.Algebra.nonempty_linearEquiv_of_lineBundlesTrivial_of_rankAtStalk_eq_one
    (R := CommRingCat.of R) hPic M (rootWeightRank_eq_one I G hG i hmax P hP α)


/-- Choose a trivialization of an actual root-weight module over the original
ring from triviality of all actual scheme line bundles. -/
def rootWeightSpaceEquivOfLineBundlesTrivial
    {R : Type u} [CommRing R]
    (hPic : ∀ L : Langlands.AlgebraicGeometry.Picard.LineBundle (Spec (CommRingCat.of R)),
      Nonempty (L ≅ Langlands.AlgebraicGeometry.Picard.LineBundle.trivial
        (Spec (CommRingCat.of R))))
    (I : Type u) [Fintype I] [DecidableEq I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    {J : Type v} (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : letI := hG.isAffineHom; IsFibrewiseRootDatumOf I G i P) (α : J) :
    letI := hG.isAffineHom
    splitTorus.exponentWeightSpace I G i (P.root α) ≃ₗ[CommRingCat.of R]
      CommRingCat.of R := by
  let := hG.isAffineHom
  exact Classical.choice
    (rootWeightSpace_nonempty_linearEquiv_of_lineBundlesTrivial hPic I G hG i hmax P hP α)

end Langlands.GroupScheme
