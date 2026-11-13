import Langlands.Automorphic.OperatorScalarCentralCharacter

/-! # Central characters of cuspidal realizations from the top Satake coefficient

Let `T` be an irreducible cuspidal operator realization of rank `r + 1` with a spectral
presentation `P`, and let `δ` be a Hecke character. Suppose that at almost every finite
place `v` the character `δ` is unramified, `v` is not exceptional for `P`, and `δ_v(ϖ_v)`
is the top elementary coefficient (the product of the Satake parameters) of `P` at `v`.
Then `T` has central character `δ`.

At such a place, `T` has a nonzero spherical vector. The scalar matrices of integral units
fix it and `δ_v` is trivial on integral units, while the scalar matrix of `ϖ_v` acts on it
as the top standard Hecke operator, by the top elementary coefficient. By irreducibility
these scalar matrices act by `δ_v` on all of `T`, so `F_v^×` lies in the closed subgroup of
ideles whose scalar matrices act by `δ`. That subgroup contains the principal ideles, hence
is the whole idele group by weak approximation.
-/

noncomputable section
universe uF uP

set_option autoImplicit false

open Filter

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.Unramified

variable {F : Type uF} [Field F] [NumberField F]

open ContinuousRationalFunctions

local instance topCoefficientRationalAddCommGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance topCoefficientContinuousAddCommGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance topCoefficientSmoothAddCommGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance topCoefficientFormsAddCommGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance topCoefficientStableAddCommGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance topCoefficientRealizationAddCommGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

section Local

variable (v : FinitePlace F)

local instance scalarCentralTopology (m : ℕ) : TopologicalSpace (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology m
local instance scalarCentralTopologicalGroup (m : ℕ) :
    IsTopologicalGroup (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup m
local instance scalarCentralT2 (m : ℕ) : T2Space (FiniteLocalGL F m v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearT2Space m
local instance scalarCentralMeasurable (m : ℕ) : MeasurableSpace (FiniteLocalGL F m v) :=
  borel _
local instance scalarCentralBorel (m : ℕ) : BorelSpace (FiniteLocalGL F m v) := ⟨rfl⟩

/-- At a place where `δ` is unramified and the presentation is unramified, the scalar
matrices of the integral units act on `T` by `δ`, that is, trivially. -/
theorem finiteIdeleInclusion_units_mem_centralCharacterSubgroup
    (T : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uP} T)
    (δ : HeckeCharacter F) (hδ : δ.IsUnramifiedAt v) (hv : v ∉ P.exceptional)
    (u : (FiniteCompletion F v)ˣ)
    (hu : u ∈ (Submonoid.ofClass (v.adicCompletionIntegers F)).units) :
    finiteIdeleInclusion F v u ∈ T.realization.centralCharacterSubgroup δ := by
  obtain ⟨b, hb⟩ := P.exists_spherical_ne_zero v hv
  have hb0 : (b : T.realization.Space) ≠ 0 := fun h0 => hb (Subtype.ext h0)
  refine (T.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff δ v u).mpr ?_
  refine T.realization.localScalar_eq_smul_of_ne_zero T.irreducible v u _ hb0 ?_
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u ∈
      (sphericalOpenSubgroup (CompletionPadic.padicField v) r).toSubgroup := by
    rw [sphericalOpenSubgroup_toSubgroup, ← localIntegral_eq_sphericalSubgroup F v r]
    change Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u ∈ localIntegral F (r + 1) v
    rw [mem_localIntegral]
    have hu1 : (u : FiniteCompletion F v) ∈ v.adicCompletionIntegers F := hu.1
    have hu2 : ((u⁻¹ : (FiniteCompletion F v)ˣ) : FiniteCompletion F v) ∈
        v.adicCompletionIntegers F := hu.2
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · change Matrix.scalar (Fin (r + 1)) (u : FiniteCompletion F v) i j ∈ _
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact hu1
      · exact (v.adicCompletionIntegers F).zero_mem
    · have hinv : (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u)⁻¹ =
          Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u⁻¹ := (map_inv _ u).symm
      rw [hinv]
      change Matrix.scalar (Fin (r + 1))
        ((u⁻¹ : (FiniteCompletion F v)ˣ) : FiniteCompletion F v) i j ∈ _
      rw [Matrix.scalar_apply, Matrix.diagonal_apply]
      split_ifs
      · exact hu2
      · exact (v.adicCompletionIntegers F).zero_mem
  have hfix : T.realization.localRepresentation v
      (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) u) (b : T.realization.Space) = b :=
    b.property ⟨_, hmem⟩
  have h1 : (δ.finiteComponent v u : ℂ) = 1 := by
    rw [hδ u hu, Units.val_one]
  exact hfix.trans ((one_smul ℂ (b : T.realization.Space)).symm.trans
    (congrArg (fun c : ℂ => c • (b : T.realization.Space)) h1.symm))

/-- At a place where the presentation is unramified and `δ_v(ϖ_v)` is the top elementary
coefficient of the presented spectrum, the scalar matrix of the uniformizer acts on `T`
by `δ`. -/
theorem finiteIdeleInclusion_uniformizer_mem_centralCharacterSubgroup
    (T : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uP} T)
    (δ : HeckeCharacter F) (hv : v ∉ P.exceptional)
    (he : (δ.finiteUniformizerValue v : ℂ) =
      elementaryCoefficient (P.spectralSystem.eigenvalues v hv) (r + 1)) :
    finiteIdeleInclusion F v
        (LocalFactor.PadicAbelian.uniformizerUnit
          (CompletionPadic.padicField v).canonicalTopologicalData) ∈
      T.realization.centralCharacterSubgroup δ := by
  obtain ⟨b, hb⟩ := P.exists_spherical_ne_zero v hv
  have hb0 : (b : T.realization.Space) ≠ 0 := fun h0 => hb (Subtype.ext h0)
  refine (T.realization.finiteIdeleInclusion_mem_centralCharacterSubgroup_iff δ v _).mpr ?_
  refine T.realization.localScalar_eq_smul_of_ne_zero T.irreducible v _ _ hb0 ?_
  have hcorner := congrArg Subtype.val (P.corner_eq_smul v hv b (Fin.last (r + 1)))
  have htop := standardHecke_cornerAction_last (CompletionPadic.padicField v)
    (T.realization.localRepresentation v)
    (T.realization.localRepresentation_isSmooth_canonical v) b
  have hdiag := standardDiagonal_last (CompletionPadic.padicField v) (r := r)
  have hscalar : standardHeckeScalar (CompletionPadic.padicField v)
      (P.spectralSystem.eigenvalues v hv) (Fin.last (r + 1)) =
        (δ.finiteUniformizerValue v : ℂ) :=
    (standardHeckeScalar_last _ _).trans he.symm
  exact (congrArg (fun g => T.realization.localRepresentation v g (b : T.realization.Space))
    hdiag.symm).trans (htop.symm.trans (hcorner.trans
      ((Submodule.coe_smul _ b).trans
        (congrArg (fun c : ℂ => c • (b : T.realization.Space)) hscalar))))

/-- At a place where `δ` and the presentation are unramified and `δ_v(ϖ_v)` is the top
elementary coefficient of the presented spectrum, every local idele at `v` acts on `T`
through its scalar matrix by `δ`. -/
theorem finiteIdeleInclusion_mem_centralCharacterSubgroup (T : CuspidalOperatorRealization F r)
    (P : CuspidalSpectralPresentation.{uF, uP} T) (δ : HeckeCharacter F)
    (hδ : δ.IsUnramifiedAt v) (hv : v ∉ P.exceptional)
    (he : (δ.finiteUniformizerValue v : ℂ) =
      elementaryCoefficient (P.spectralSystem.eigenvalues v hv) (r + 1))
    (a : (FiniteCompletion F v)ˣ) :
    finiteIdeleInclusion F v a ∈ T.realization.centralCharacterSubgroup δ := by
  have hG := CompletionPadic.subgroup_eq_top_of_uniformizer_mem F v
    ((T.realization.centralCharacterSubgroup δ).comap (finiteIdeleInclusion F v).toMonoidHom)
    (finiteIdeleInclusion_units_mem_centralCharacterSubgroup v T P δ hδ hv)
    (finiteIdeleInclusion_uniformizer_mem_centralCharacterSubgroup v T P δ hv he)
  have ha : a ∈ (T.realization.centralCharacterSubgroup δ).comap
      (finiteIdeleInclusion F v).toMonoidHom := hG ▸ Subgroup.mem_top a
  exact ha

end Local

/-- If, at almost every finite place, the Hecke character `δ` is unramified and its value
at the uniformizer is the top elementary coefficient (the product of the Satake
parameters) of a spectral presentation of `T`, then `T` has central character `δ`. -/
theorem hasCentralCharacter_of_eventually_elementaryCoefficient
    (T : CuspidalOperatorRealization F r) (P : CuspidalSpectralPresentation.{uF, uP} T)
    (δ : HeckeCharacter F)
    (h : ∀ᶠ v in Filter.cofinite, δ.IsUnramifiedAt v ∧
      ∃ hs : v ∉ P.spectralSystem.exceptional,
        (δ.finiteUniformizerValue v : ℂ) =
          elementaryCoefficient (P.spectralSystem.eigenvalues v hs) (r + 1)) :
    T.HasCentralCharacter δ := by
  have hfin := Filter.eventually_cofinite.mp h
  apply T.realization.hasCentralCharacter_of_centralCharacterSubgroup_eq_top δ
  refine IdeleDensity.eq_top_of_isClosed _ hfin.toFinset
    (T.realization.isClosed_centralCharacterSubgroup δ)
    (T.realization.diagonalUnits_mem_centralCharacterSubgroup δ) ?_
  intro v hv a
  have hgood : δ.IsUnramifiedAt v ∧ ∃ hs : v ∉ P.spectralSystem.exceptional,
      (δ.finiteUniformizerValue v : ℂ) =
        elementaryCoefficient (P.spectralSystem.eigenvalues v hs) (r + 1) := by
    by_contra hc
    exact hv (hfin.mem_toFinset.mpr hc)
  obtain ⟨hδ, hs, he⟩ := hgood
  exact finiteIdeleInclusion_mem_centralCharacterSubgroup v T P δ hδ hs he a

end CuspidalOperatorRealization

end Langlands.Automorphic
