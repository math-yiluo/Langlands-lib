import Langlands.Representation.Aubert.General.RationalLeviFiniteLength
import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Aubert.General.FirstAdjointness
import Langlands.Representation.Induction.CompactLocalSection
import Mathlib.RepresentationTheory.Subrepresentation

/-! # Finite length of Jacquet modules inside a standard Levi -/

noncomputable section

open scoped MonoidAlgebra

universe u v uG uV uH uK uW

namespace Langlands.Aubert.General

open SmoothRep

section Descent

variable {H : Type uH} {K : Type uK} [Group H] [Group K]
  {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]
  (ρ : Representation ℂ H V) (τ : Representation ℂ K W)
  (j : H → K) (φ : V →ₗ[ℂ] W)

/-- Pull back a subrepresentation along a linear map sending each `ρ h x` to
a scalar multiple of `τ (j h) (φ x)`. -/
def comapSubrepresentation
    (hj : ∀ (h : H) (x : V), ∃ c : ℂ, φ (ρ h x) = c • τ (j h) (φ x))
    (S : Subrepresentation τ) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.comap φ
  apply_mem_toSubmodule h x hx := by
    obtain ⟨c, hc⟩ := hj h x
    change φ (ρ h x) ∈ S.toSubmodule
    rw [hc]
    exact S.toSubmodule.smul_mem c (S.apply_mem_toSubmodule (j h) hx)

/-- Along a surjective map, the pullback reflects inclusions. -/
def comapSubrepresentationOrderEmbedding (hφ : Function.Surjective φ)
    (hj : ∀ (h : H) (x : V), ∃ c : ℂ, φ (ρ h x) = c • τ (j h) (φ x)) :
    Subrepresentation τ ↪o Subrepresentation ρ :=
  OrderEmbedding.ofMapLEIff (comapSubrepresentation ρ τ j φ hj) (by
    intro S T
    constructor
    · intro hST w hw
      obtain ⟨x, rfl⟩ := hφ w
      exact hST hw
    · intro hST x hx
      exact hST hx)

/-- Finite length descends along a surjective linear map that intertwines up
to scalars. -/
theorem isFiniteLength_of_surjective_of_smul (hφ : Function.Surjective φ)
    (hj : ∀ (h : H) (x : V), ∃ c : ℂ, φ (ρ h x) = c • τ (j h) (φ x))
    (hfl : IsFiniteLength ℂ[H] ρ.asModule) : IsFiniteLength ℂ[K] τ.asModule := by
  let e : Submodule ℂ[K] τ.asModule ↪o Submodule ℂ[H] ρ.asModule :=
    Subrepresentation.subrepresentationSubmoduleOrderIso.symm.toOrderEmbedding |>.trans
      (comapSubrepresentationOrderEmbedding ρ τ j φ hφ hj) |>.trans
      Subrepresentation.subrepresentationSubmoduleOrderIso.toOrderEmbedding
  obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  let := hN
  let := hA
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_iff.mpr e.wellFoundedGT, e.wellFoundedLT⟩

end Descent

section Modulus

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]

/-- A half modulus is trivial on the image of a continuous homomorphism from a
compact group: the modulus has open kernel, so the image is a finite subgroup of
the positive reals. -/
theorem closedHalfCharacter_eq_one_of_compact (U M : Subgroup G)
    (hU : IsClosed (U : Set G)) (hMU : M ≤ Subgroup.normalizer (U : Set G))
    {C : Type uK} [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C]
    (ι : C →* M) (hι : Continuous ι) (c : C) :
    HaarModulus.closedHalfCharacter U hU M hMU (ι c) = 1 := by
  let χ := (HaarModulus.closedRestrictCharacter U hU M hMU).comp ι
  have hopen : IsOpen (χ.ker : Set C) :=
    (HaarModulus.isOpen_ker_closedRestrictCharacter U hU M hMU).preimage hι
  have : Finite (C ⧸ χ.ker) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hc : c ^ Nat.card (C ⧸ χ.ker) ∈ χ.ker := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  have hpow : ((χ c : NNReal)) ^ Nat.card (C ⧸ χ.ker) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, MonoidHom.mem_ker.mp hc, Units.val_one]
  have h1 : (χ c : NNReal) = 1 :=
    (pow_eq_one_iff_of_nonneg (by positivity) Nat.card_pos.ne').mp hpow
  have hu : HaarModulus.closedRestrictCharacter U hU M hMU (ι c) = 1 := Units.ext h1
  simp only [HaarModulus.closedHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, MonoidHom.comp_apply, hu, map_one]

end Modulus

section LeviJacquet

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G]
  {PJ MJ UJ P' M' U' : Subgroup G}
  (hJ : IsSemidirectDecomposition PJ MJ UJ) (hUJ : IsClosed (UJ : Set G))
  (h' : IsSemidirectDecomposition P' M' U') (hU' : IsClosed (U' : Set G))

/-- If `U'` lies in `P_J` and is a limit of compact subgroups, the half
modulus of `P_J` on `U_J` is trivial on `U'`. -/
theorem closedHalfCharacter_eq_one_of_isLimitOfCompactSubgroups (hU'PJ : U' ≤ PJ)
    (hU'c : Jacquet.Localization.IsLimitOfCompactSubgroups U') (u : U') :
    HaarModulus.closedHalfCharacter UJ hUJ PJ hJ.le_normalizer ⟨u, hU'PJ u.2⟩ = 1 := by
  obtain ⟨K, hK, huK⟩ := hU'c {u} isCompact_singleton
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ι : K →* PJ :=
    { toFun := fun k => ⟨((k : U') : G), hU'PJ (k : U').2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Continuous ι := by
    change Continuous fun k : K => (⟨((k : U') : G), hU'PJ (k : U').2⟩ : PJ)
    exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  exact closedHalfCharacter_eq_one_of_compact UJ PJ hUJ hJ.le_normalizer ι hι ⟨u, huK rfl⟩

/-- With a continuous Levi projection, evaluation at the identity on actual
normalized induction is surjective. -/
theorem evaluation_id_surjective (hprojJ : Continuous hJ.projection)
    (X : SmoothRep.{0, uG, uV} ℂ MJ) :
    Function.Surjective (FirstAdjointness.evaluation hJ hUJ
      ((normalizedInductionFunctor hJ hUJ).obj X) X (Representation.IntertwiningMap.id _)) := by
  intro x
  have hsm : IsSmooth (inducingRepresentation hJ hUJ X) :=
    (isSmooth_twist_iff _ _
      (HaarModulus.isOpen_ker_closedHalfCharacter UJ hUJ PJ hJ.le_normalizer)).mpr
      (isSmooth_comp hJ.projection hprojJ X.isSmooth)
  exact ⟨(Induction.compactLocalSection PJ (inducingRepresentation hJ hUJ X) hsm 1 x
      Set.univ isOpen_univ (Set.mem_univ _)).val,
    Induction.compactLocalSection_apply PJ (inducingRepresentation hJ hUJ X) hsm 1 x
      Set.univ isOpen_univ (Set.mem_univ _)⟩

/-- The scalar factors of two multiples of one vector. -/
private theorem exists_smul_eq_smul {W : Type uW} [AddCommGroup W] [Module ℂ W]
    {x y w : W} (a : ℂ) (b : ℂˣ) (hx : x = a • w) (hy : y = (b : ℂ) • w) :
    ∃ c : ℂ, x = c • y :=
  ⟨a * ((b⁻¹ : ℂˣ) : ℂ), by
    rw [hx, hy, smul_smul, mul_assoc, Units.inv_mul, mul_one]⟩

variable [LocallyCompactSpace MJ]
  (hL : IsSemidirectDecomposition (P'.subgroupOf MJ) (M'.subgroupOf MJ) (U'.subgroupOf MJ))

/-- Jacquet restriction inside `M_J` along `P' ∩ M_J = (M' ∩ M_J)(U' ∩ M_J)`
preserves finiteness of length relative to the ambient pair: if the ambient
Jacquet module of the normalized induction of `X` has finite length, so does the
inside-Levi Jacquet module of `X`. -/
theorem hasFiniteLength_leviJacquet_of_induction
    (hM'J : M' ≤ MJ) (hUJU' : UJ ≤ U') (hU'PJ : U' ≤ PJ)
    (hprojJ : Continuous hJ.projection)
    (hU'c : Jacquet.Localization.IsLimitOfCompactSubgroups U')
    (X : SmoothRep.{0, uG, uV} ℂ MJ)
    (hfl : ((jacquetFunctor.{uG, max uG uV} h' hU').obj
      ((normalizedInductionFunctor.{uG, uV} hJ hUJ).obj X)).HasFiniteLength) :
    ((jacquetFunctor.{uG, uV} hL (hU'.preimage continuous_subtype_val)).obj
      X).HasFiniteLength := by
  let Y := (normalizedInductionFunctor.{uG, uV} hJ hUJ).obj X
  let ev := FirstAdjointness.evaluation hJ hUJ Y X (Representation.IntertwiningMap.id _)
  let mkX := Jacquet.Localization.mk X.representation (U'.subgroupOf MJ) 1
  have hrel : ∀ (u : U') (f : Y), (mkX ∘ₗ ev) (Y.representation u f) =
      (((1 : U' →* ℂˣ) u : ℂˣ) : ℂ) • (mkX ∘ₗ ev) f := by
    intro u f
    have hcov := FirstAdjointness.evaluation_covariance hJ hUJ Y X
      (Representation.IntertwiningMap.id _) ⟨u, hU'PJ u.2⟩ f
    rw [closedHalfCharacter_eq_one_of_isLimitOfCompactSubgroups hJ hUJ hU'PJ hU'c u,
      Units.val_one, one_smul] at hcov
    have hn : ((hJ.projection ⟨u, hU'PJ u.2⟩ : MJ) : G) ∈ U' := by
      have h1 := hUJU' (hJ.projection_inv_mul_mem ⟨u, hU'PJ u.2⟩)
      have h2 : ((hJ.projection ⟨u, hU'PJ u.2⟩ : MJ) : G) =
          (u : G) * (((hJ.projection ⟨u, hU'PJ u.2⟩ : MJ) : G)⁻¹ * (u : G))⁻¹ := by
        group
      rw [h2]
      exact U'.mul_mem u.2 (U'.inv_mem h1)
    simp only [LinearMap.comp_apply, MonoidHom.one_apply, Units.val_one, one_smul]
    change mkX (ev (Y.representation ((⟨u, hU'PJ u.2⟩ : PJ) : G) f)) = mkX (ev f)
    rw [hcov]
    have hk := Jacquet.Localization.mk_apply_subgroup X.representation (U'.subgroupOf MJ) 1
      ⟨hJ.projection ⟨u, hU'PJ u.2⟩, hn⟩ (ev f)
    simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using hk
  let φ := Jacquet.Localization.lift Y.representation U' 1 (mkX ∘ₗ ev) hrel
  have hφ : Function.Surjective φ := by
    intro c
    obtain ⟨x, rfl⟩ := Jacquet.Localization.mk_surjective X.representation (U'.subgroupOf MJ) 1 c
    obtain ⟨f, rfl⟩ := evaluation_id_surjective hJ hUJ hprojJ X x
    exact ⟨Jacquet.Localization.mk Y.representation U' 1 f, rfl⟩
  let j : M' → M'.subgroupOf MJ := fun m => ⟨⟨m, hM'J m.2⟩, m.2⟩
  apply isFiniteLength_of_surjective_of_smul
    ((jacquetFunctor.{uG, max uG uV} h' hU').obj Y).representation
    ((jacquetFunctor.{uG, uV} hL (hU'.preimage continuous_subtype_val)).obj X).representation
    j φ hφ ?_ hfl
  intro m c
  obtain ⟨f, rfl⟩ := Jacquet.Localization.mk_surjective Y.representation U' 1 c
  have hcov := FirstAdjointness.evaluation_covariance hJ hUJ Y X
    (Representation.IntertwiningMap.id _) ⟨m, hJ.levi_le (hM'J m.2)⟩ f
  rw [hJ.projection_levi ⟨m, hM'J m.2⟩] at hcov
  let a₁ : ℂ := ((HaarModulus.closedInverseHalfCharacter U' hU' M' h'.levi_le_normalizer m :
    ℂˣ) : ℂ)
  let a₂ : ℂ := ((HaarModulus.closedHalfCharacter UJ hUJ PJ hJ.le_normalizer
    ⟨m, hJ.levi_le (hM'J m.2)⟩ : ℂˣ) : ℂ)
  refine exists_smul_eq_smul (w := mkX (X.representation ⟨(m : G), hM'J m.2⟩ (ev f)))
    (a₁ * a₂) (HaarModulus.closedInverseHalfCharacter (U'.subgroupOf MJ)
      (hU'.preimage continuous_subtype_val) (M'.subgroupOf MJ) hL.levi_le_normalizer (j m))
    ?_ rfl
  calc φ (((jacquetFunctor.{uG, max uG uV} h' hU').obj Y).representation m
        (Jacquet.Localization.mk Y.representation U' 1 f))
      = a₁ • φ (Jacquet.Localization.mk Y.representation U' 1 (Y.representation m f)) := by
        rw [← map_smul]
        rfl
    _ = a₁ • mkX (ev (Y.representation ((⟨m, hJ.levi_le (hM'J m.2)⟩ : PJ) : G) f)) := rfl
    _ = (a₁ * a₂) • mkX (X.representation ⟨(m : G), hM'J m.2⟩ (ev f)) := by
        rw [hcov, map_smul, smul_smul]

end LeviJacquet

end Langlands.Aubert.General

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hInter hG hi hν in
/-- The containments between the standard subgroups of `J` and of a standard
index inside `J`: the Levi point clause gives `M_{I'} ≤ M_J`, and the product
clause `U_{I'} = (M_J ⊓ U_{I'}) U_J` gives `U_J ≤ U_{I'} ≤ P_J`. -/
theorem leviIndex_containments (J : Finset (SimpleRoot i ν)) (I : Finset J) :
    levi i ν (leviIndex J I) ≤ levi i ν J ∧
      unipotent i ν J ≤ unipotent i ν (leviIndex J I) ∧
      unipotent i ν (leviIndex J I) ≤ parabolic i ν J := by
  have hincl : rootSet i ν (leviIndex J I) ⊆ rootSet i ν J :=
    (rootSet_subset_iff i ν _ J).mpr (leviIndex_subset J I)
  have hJI := hInter k G hG T i hi ν hν (rootSet i ν (leviIndex J I)) (rootSet i ν J)
    (rootSet_subset i ν _) (rootSet_subset i ν J) hincl
  obtain ⟨-, hMP, -, -⟩ := hJI.1 (Over.mk (𝟙 _))
  have hMP' : levi i ν (leviIndex J I) ≤ levi i ν J ⊓ parabolic i ν (leviIndex J I) := hMP
  have hprod : ((unipotent i ν (leviIndex J I) : Subgroup (RationalPoint k G.X)) :
      Set (RationalPoint k G.X)) =
      ((levi i ν J ⊓ unipotent i ν (leviIndex J I) : Subgroup (RationalPoint k G.X)) :
        Set (RationalPoint k G.X)) *
        ((unipotent i ν J : Subgroup (RationalPoint k G.X)) : Set (RationalPoint k G.X)) :=
    hJI.2
  refine ⟨fun m hm => (Subgroup.mem_inf.mp (hMP' hm)).1, fun u hu => ?_, fun u hu => ?_⟩
  · rw [← SetLike.mem_coe, hprod]
    simpa using Set.mul_mem_mul
      (SetLike.mem_coe.mpr (one_mem (levi i ν J ⊓ unipotent i ν (leviIndex J I)))) hu
  · rw [← SetLike.mem_coe, hprod] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hu
    exact (parabolic i ν J).mul_mem
      (levi_le_parabolic i ν J (Subgroup.mem_inf.mp ha).1) (unipotent_le_parabolic i ν J hb)

variable [TopologicalSpace k]

local instance rationalLeviJacquetPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]

/-- Jacquet restriction inside the closed standard Levi `M_J` preserves finite
length, given the ambient finite-length preservation of normalized induction
and of Jacquet restriction for the standard decompositions. -/
theorem standardLeviJacquet_preservesFiniteLength
    (hStandard : StandardCocharacterStatement.{u})
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
    (hproj : ∀ I, Continuous
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν I).projection)
    (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
    (hiFl : ∀ I, PreservesFiniteLength
      (normalizedInductionFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)))
    (hrFl : ∀ I, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I) (hU I)))
    (J : Finset (SimpleRoot i ν))
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X))) :
    letI := hM.locallyCompactSpace
    ∀ I : Finset J, PreservesFiniteLength
      (jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        ((hU (leviIndex J I)).preimage continuous_subtype_val)) := by
  let _ := hM.locallyCompactSpace
  intro I X hX
  obtain ⟨hMJ, hUJ, hUP⟩ := leviIndex_containments i ν hInter hG hi hν J I
  exact hasFiniteLength_leviJacquet_of_induction
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
    (hU J)
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (leviIndex J I))
    (hU (leviIndex J I)) (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
    hMJ hUJ hUP (hproj J) (hUc (leviIndex J I)) X
    (hrFl (leviIndex J I) _ (hiFl J X hX))

end Langlands.Aubert.General.RationalPointFamily
