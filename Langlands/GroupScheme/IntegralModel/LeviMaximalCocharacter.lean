import Langlands.GroupScheme.IntegralModel.DynamicCentralizer
import Langlands.GroupScheme.Torus.HenselianCocharacterLifting
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.GroupScheme.Rational.QuasiSplitCentralizerTorus
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Reductive.GenericSpreadingAssembly
import Langlands.AlgebraicGeometry.DvrSmoothFibers
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction

/-! # A cocharacter of the integral model with a torus centralizer, and Levi maximality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A torus stays a torus after base change along the spectrum of any ring map of fields. -/
theorem IsTorus.baseChange_specMap {k K : Type u} [Field k] [Field K]
    (φ : CommRingCat.of k ⟶ CommRingCat.of K) {T : GroupScheme (Spec (CommRingCat.of k))}
    (hT : IsTorus T) : IsTorus ((GroupScheme.baseChange (Spec.map φ)).obj T) := by
  let : Algebra k K := φ.hom.toAlgebra
  exact hT.baseChange (K := K)

namespace IntegralModel

open Langlands.AlgebraicGeometry.PointTopology

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ↥𝒪[F] F G)

local instance leviMaximalModelAffine : IsAffine M.group.X.left :=
  isAffine_of_isAffineHom M.group.X.hom

/-- **A cocharacter with torus special centralizer.** If `G` and the special fibre of the
model are connected reductive, the model has a cocharacter whose integral dynamic centralizer
has a torus as special fibre. -/
theorem exists_cocharacter_isTorus_specialCentralizer (hG : IsConnectedReductive G)
    (hspecial : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj M.group)) :
    ∃ χ : (Gm (Spec (CommRingCat.of ↥𝒪[F]))).toGrp ⟶ M.group,
      IsTorus ((GroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] 𝓀[F])).obj
        (Dynamic.Affine.centralizerScheme χ)) := by
  classical
  let : HenselianLocalRing ↥𝒪[F] :=
    Langlands.BruhatTits.IntegralModels.henselianLocalRing_integer
  have : Smooth M.group.X.hom := M.isSmooth_of_reductive_localField hG hspecial
  -- The fibre at the closed point is connected reductive.
  have hclosed : (Spec.algebraMap ↥𝒪[F] 𝓀[F]) (IsLocalRing.closedPoint 𝓀[F]) =
      IsLocalRing.closedPoint ↥𝒪[F] := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap ↥𝒪[F] 𝓀[F]) (IsLocalRing.maximalIdeal 𝓀[F]) =
      IsLocalRing.maximalIdeal ↥𝒪[F]
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact IsLocalRing.ker_residue (R := ↥𝒪[F])
  have hk₀ : IsConnectedReductive ((GroupScheme.baseChange
      ((Spec (CommRingCat.of ↥𝒪[F])).fromSpecResidueField
        (IsLocalRing.closedPoint ↥𝒪[F]))).obj M.group) := by
    have h := residueReductive_of_fieldReductive M.group (Spec.algebraMap ↥𝒪[F] 𝓀[F]) hspecial
    rw [hclosed] at h
    exact h
  let := hk₀.isAffineHom
  let := hk₀.smooth
  -- The residue field at the closed point is finite.
  have : Finite ((Spec (CommRingCat.of ↥𝒪[F])).residueField
      (IsLocalRing.closedPoint ↥𝒪[F])) := by
    let e₁ : IsLocalRing.ResidueField ↥𝒪[F] ≃+*
        (IsLocalRing.maximalIdeal ↥𝒪[F]).ResidueField :=
      RingEquiv.ofBijective (algebraMap (↥𝒪[F] ⧸ IsLocalRing.maximalIdeal ↥𝒪[F]) _)
        (Ideal.bijective_algebraMap_quotient_residueField _)
    let e₂ := (Scheme.Spec.residueFieldIso (CommRingCat.of ↥𝒪[F])
      (IsLocalRing.closedPoint ↥𝒪[F])).commRingCatIsoToRingEquiv
    exact Finite.of_equiv _ (e₁.trans e₂.symm).toEquiv
  -- A maximal split torus of the quasi-split closed fibre with torus centralizer.
  have hQS := finiteFieldQuasiSplit
    ((Spec (CommRingCat.of ↥𝒪[F])).residueField (IsLocalRing.closedPoint ↥𝒪[F])) _ hk₀
  obtain ⟨A, a, ha, C, c, hc, -, hCt⟩ :=
    hQS.exists_maximalSplitTorus_with_torusCentralizer dynamicCentralizerReductive
      parabolicDynamic
  have hν := centralizingCocharacter_spec ha.1.1 a
  -- Lift a centralizing cocharacter to the model.
  obtain ⟨χ, B, hχB⟩ := exists_cocharacter_baseChange_eq_comp_iso ↥𝒪[F] M.group a ha.1.1 ha.1.2
    (centralizingCocharacter ha.1.1 a)
  refine ⟨χ, ?_⟩
  let f₀ := (Spec (CommRingCat.of ↥𝒪[F])).fromSpecResidueField (IsLocalRing.closedPoint ↥𝒪[F])
  let : IsAffine ((GroupScheme.baseChange f₀).obj M.group).X.left :=
    isAffine_of_isAffineHom ((GroupScheme.baseChange f₀).obj M.group).X.hom
  have hcent : Dynamic.centralizer (Dynamic.baseChangeCocharacter f₀ χ) =
      (torusCentralizer a).comap B.inv := by
    rw [Dynamic.centralizer_eq_comap_of_iso (Dynamic.baseChangeCocharacter f₀ χ) B.symm,
      ← hν, hχB]
    simp only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  have hrep : (Dynamic.centralizer (Dynamic.baseChangeCocharacter f₀ χ)).IsRepresentedBy
      (c ≫ B.hom) := by
    rw [hcent]
    exact hc.comp_iso B
  have hZ₀ : IsTorus (Dynamic.Affine.centralizerScheme (Dynamic.baseChangeCocharacter f₀ χ)) :=
    IsTorus.of_iso ((Dynamic.Affine.isRepresentedBy_centralizerHom _).isoOfIsRepresentedBy hrep)
      hCt
  have hZf₀ : IsTorus ((GroupScheme.baseChange f₀).obj (Dynamic.Affine.centralizerScheme χ)) :=
    IsTorus.of_iso (Dynamic.affineCentralizerBaseChangeIso χ f₀) hZ₀
  -- Transport from the scheme residue field to `𝓀[F]`.
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ =
      (Langlands.AlgebraicGeometry.closedPointResidueSpecIso ↥𝒪[F]).hom :=
    ⟨_, Spec.map_preimage _⟩
  have hc' : Spec.map φ ≫ f₀ = Spec.algebraMap ↥𝒪[F] 𝓀[F] := by
    rw [hφ]
    exact Langlands.AlgebraicGeometry.closedPointResidueSpecIso_hom_fromSpecResidueField _
  refine IsTorus.of_iso
    (eqToIso (congrArg (fun f => (GroupScheme.baseChange f).obj
        (Dynamic.Affine.centralizerScheme χ)) hc'.symm) ≪≫
      baseChangeCompIso f₀ (Spec.map φ) (Dynamic.Affine.centralizerScheme χ)) ?_
  exact IsTorus.baseChange_specMap φ hZf₀

/-- **Levi maximality from openness.** If the integral points of every supplied model of a
connected reductive group over a nonarchimedean local field are open in its rational points,
then `LeviMaximalCocharacterStatement` holds. -/
theorem leviMaximalCocharacterStatement_of_isOpen
    (hopen : ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
      [IsAffine G.X.left] (M : IntegralModel ↥𝒪[F] F G),
      letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
      IsOpen (M.integralPoints : Set (rationalPoints G))) :
    LeviMaximalCocharacterStatement.{u} := by
  intro F _ _ _ _ G hG M hspecial
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨χ, hχ⟩ := M.exists_cocharacter_isTorus_specialCentralizer hG hspecial
  refine ⟨χ, fun C hC hCZ _ => ?_⟩
  exact M.leviMaximal_of_isTorus_specialCentralizer χ hG hspecial hχ (hopen F G M) C hC hCZ

end IntegralModel

end Langlands.GroupScheme
