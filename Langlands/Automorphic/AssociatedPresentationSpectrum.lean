import Langlands.Automorphic.Unramified.RelativeWeilAssociationEuler
import Langlands.Representation.Unramified.TwistedHeckeScalars
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.LocalSphericalHecke
import Langlands.Automorphic.Unramified.RelativeWeilAssociation
import Langlands.Representation.Unramified.SphericalSpectrumUniquenessProof

noncomputable section

namespace Langlands.Hecke

open MeasureTheory Langlands.CompactSplitting

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A scalar corner action extends from a representation whose intertwiner
images span the target. Neither representation need be irreducible. -/
theorem cornerAction_scalar_of_isotypicPart_eq_top
    (μ : Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (htop : isotypicPart ρ σ = ⊤)
    (a : HeckeAlgebra.Corner μ K hK) (c : ℂ)
    (hc : ∀ v : fixedVectors ρ K.toSubgroup, cornerAction μ ρ hρ K hK a v = c • v)
    (w : fixedVectors σ K.toSubgroup) :
    cornerAction μ σ hσ K hK a w = c • w := by
  let Pρ := fixedProjection μ ρ hρ K hK
  let Pσ := fixedProjection μ σ hσ K hK
  let Aσ := cornerAction μ σ hσ K hK a
  let L := Aσ.comp Pσ - c • Pσ
  have hz : isotypicPart ρ σ ≤ LinearMap.ker L := by
    apply iSup_le
    intro T x hx
    obtain ⟨v, rfl⟩ := hx
    change Aσ (Pσ (T v)) - c • Pσ (T v) = 0
    have he := fixedProjection_intertwiner μ ρ hρ K hK hσ T v
    have ha := cornerAction_intertwiner μ ρ hρ K hK hσ T a (Pρ v)
    change fixedVectorsMap T K.toSubgroup (Pρ v) = Pσ (T v) at he
    change fixedVectorsMap T K.toSubgroup (cornerAction μ ρ hρ K hK a (Pρ v)) =
      Aσ (fixedVectorsMap T K.toSubgroup (Pρ v)) at ha
    rw [← he, ← ha, hc, map_smul, sub_self]
  have hw : (w : W) ∈ isotypicPart ρ σ := by
    rw [htop]
    exact Submodule.mem_top
  have hL := hz hw
  change Aσ (Pσ (w : W)) - c • Pσ (w : W) = 0 at hL
  change Aσ (fixedProjection μ σ hσ K hK (w : W)) -
    c • fixedProjection μ σ hσ K hK (w : W) = 0 at hL
  rw [fixedProjection_fixed] at hL
  exact sub_eq_zero.mp hL

end Langlands.Hecke

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.CompactSplitting

universe u uP uQ

variable {F : Type u} [Field F] [NumberField F]

local instance associatedSpectrumRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance associatedSpectrumContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance associatedSpectrumSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance associatedSpectrumFormsGroup (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance associatedSpectrumStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance associatedSpectrumOperatorGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance associatedSpectrumLocalGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace LocalRealization

/-- Uniqueness of the spectrum on an actual local fixed space needs neither
irreducibility nor admissibility of the local component. -/
theorem sphericalHeckeSpectrum_unique {r : ℕ} {v : FinitePlace F}
    (L : LocalRealization F (r + 1) v) {s t : Unramified.Eigenvalues (r + 1)}
    (hs : L.HasSphericalHeckeSpectrum s) (ht : L.HasSphericalHeckeSpectrum t) :
    s = t := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs.1
  have hw' : (⟨w, hw⟩ : L.SphericalVectors) ≠ 0 :=
    fun h0 => hw0 (congrArg Subtype.val h0)
  apply Unramified.eq_of_standardHeckeScalar_eq (CompletionPadic.padicField v)
  intro i
  exact smul_left_injective ℂ hw' ((hs.2 i ⟨w, hw⟩).symm.trans (ht.2 i ⟨w, hw⟩))

end LocalRealization

namespace CuspidalSpectralPresentation

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}
  {S : CuspidalOperatorRealization F r}

/-- Even a reducible local component generates the whole local restriction
through its intertwiner images. -/
theorem localComponent_isotypicPart_eq_top (P : CuspidalSpectralPresentation.{u, uP} S)
    (v : FinitePlace F) :
    isotypicPart (P.localComponent v).representation
      (S.realization.localRepresentation v) = ⊤ := by
  have : S.realization.IsIrreducible := S.irreducible
  apply S.realization.isotypicPart_eq_top_of_ne_bot v
  intro hbot
  have hn : (P.localComponent v).toSubmodule ≠ ⊥ := fun h =>
    P.localComponent_ne_bot v (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  let f := S.realization.localSubspaceInclusion v _ (P.localComponent_le_full v)
  have hf := S.realization.localSubspaceInclusion_injective v _
    (P.localComponent_le_full v)
  have hm := range_le_isotypicPart (P.localComponent v).representation
    (S.realization.localRepresentation v) f
    (show f ⟨x, hx⟩ ∈ LinearMap.range f.toLinearMap from ⟨⟨x, hx⟩, rfl⟩)
  rw [hbot, Submodule.mem_bot] at hm
  exact hx0 (congrArg Subtype.val (hf (hm.trans (map_zero f).symm)))

section Spherical

variable (v : FinitePlace F)

local instance associatedSpectrumLocalTopology :
    TopologicalSpace (FiniteLocalGL F (r + 1) v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopology (r + 1)
local instance associatedSpectrumLocalTopologicalGroup :
    IsTopologicalGroup (FiniteLocalGL F (r + 1) v) :=
  (CompletionPadic.padicField v).canonicalGeneralLinearTopologicalGroup (r + 1)
local instance associatedSpectrumLocalMeasurableSpace :
    MeasurableSpace (FiniteLocalGL F (r + 1) v) := borel _
local instance associatedSpectrumLocalBorelSpace :
    BorelSpace (FiniteLocalGL F (r + 1) v) := ⟨rfl⟩

/-- A witness spectrum's scalar equations hold on every other local component,
without any local irreducibility or admissibility assumptions. -/
theorem localComponent_standardHeckeOperator_eq
    (P : CuspidalSpectralPresentation.{u, uP} S)
    (Q : CuspidalSpectralPresentation.{u, uQ} S)
    (s : Unramified.Eigenvalues (r + 1))
    (hs : (P.localComponent v).HasSphericalHeckeSpectrum s)
    (i : Fin (r + 2)) (w : (Q.localComponent v).SphericalVectors) :
    (Q.localComponent v).standardHeckeOperator i w =
      Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i • w := by
  let K := Unramified.sphericalOpenSubgroup (CompletionPadic.padicField v) r
  have hK := Unramified.sphericalOpenSubgroup_isCompact (CompletionPadic.padicField v) r
  let μ := Unramified.sphericalHaar (CompletionPadic.padicField v) r
  have : μ.IsHaarMeasure :=
    Unramified.sphericalHaar_isHaar (CompletionPadic.padicField v) r
  let σ := S.realization.localRepresentation v
  have hσ : Langlands.IsSmooth σ :=
    Langlands.isSmooth_of_injective (S.realization.localFormEquiv v).toIntertwiningMap
      (S.realization.localFormEquiv v).injective
      (S.realization.toFiniteRealization.toLocal F (r + 1) v).isSmooth_canonical
  let a := Unramified.standardHeckeElement (CompletionPadic.padicField v) r i
  let c := Unramified.standardHeckeScalar (CompletionPadic.padicField v) s i
  have hfull : ∀ z : Langlands.fixedVectors σ K.toSubgroup,
      Hecke.cornerAction μ σ hσ K hK a z = c • z :=
    Hecke.cornerAction_scalar_of_isotypicPart_eq_top μ
      (P.localComponent v).representation (P.localComponent v).isSmooth_canonical
      σ hσ K hK (P.localComponent_isotypicPart_eq_top v) a c (hs.2 i)
  let g := S.realization.localSubspaceInclusion v _ (Q.localComponent_le_full v)
  have hg := S.realization.localSubspaceInclusion_injective v _
    (Q.localComponent_le_full v)
  apply Langlands.fixedVectorsMap_injective g hg K.toSubgroup
  exact (Hecke.cornerAction_intertwiner μ (Q.localComponent v).representation
    (Q.localComponent v).isSmooth_canonical K hK hσ g a w).trans
      ((hfull _).trans ((Langlands.fixedVectorsMap g K.toSubgroup).map_smul c w).symm)

/-- Outside both exceptional sets, the witness's entire spectrum also holds
on the compared component, even if either component is reducible. -/
theorem localComponent_hasSpectrum_of_other
    (P : CuspidalSpectralPresentation.{u, uP} S)
    (Q : CuspidalSpectralPresentation.{u, uQ} S)
    (hP : v ∉ P.exceptional) (hQ : v ∉ Q.exceptional) :
    (Q.localComponent v).HasSphericalHeckeSpectrum (P.spectralSystem.eigenvalues v hP) :=
  ⟨(Q.hasSpectrum v hQ).1,
    fun i w => P.localComponent_standardHeckeOperator_eq v Q _ (P.hasSpectrum v hP) i w⟩

end Spherical

/-- Any two supplied presentations of the same actual cuspidal realization have
equal numerical spectra at every place outside both exceptional sets. -/
theorem spectralSystem_eigenvalues_eq
    (P : CuspidalSpectralPresentation.{u, uP} S)
    (Q : CuspidalSpectralPresentation.{u, uQ} S)
    (v : FinitePlace F) (hP : v ∉ P.exceptional) (hQ : v ∉ Q.exceptional) :
    P.spectralSystem.eigenvalues v hP = Q.spectralSystem.eigenvalues v hQ :=
  (Q.localComponent v).sphericalHeckeSpectrum_unique
    (P.localComponent_hasSpectrum_of_other v Q hP hQ) (Q.hasSpectrum v hQ)

/-- The numerical systems attached to arbitrary presentations agree in Euler
polynomials wherever both systems are defined. -/
theorem spectralSystem_sameEulerPolynomials
    (P : CuspidalSpectralPresentation.{u, uP} S)
    (Q : CuspidalSpectralPresentation.{u, uQ} S) :
    P.spectralSystem.SameEulerPolynomials Q.spectralSystem :=
  Filter.Eventually.of_forall fun v hP hQ =>
    congrArg Unramified.Eigenvalues.eulerPolynomial (P.spectralSystem_eigenvalues_eq Q v hP hQ)

end CuspidalSpectralPresentation

end Langlands.Automorphic

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Unramified

universe u uV uP uQ

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- A class-level witness supplies weak association for every supplied actual
presentation, with independent witness and compared presentation universes. -/
theorem IsWeaklyAssociatedClass.presentation
    [CompactSpace (AdeleQuotient F)] {r : ℕ}
    {R : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {T : Automorphic.CuspidalOperatorRealization F r}
    (h : IsWeaklyAssociatedClass.{u, uV, uP} R T.isoClass)
    (Q : Automorphic.CuspidalSpectralPresentation.{u, uQ} T) :
    IsWeaklyAssociated R Q.spectralSystem := by
  obtain ⟨P, hP⟩ := (isWeaklyAssociatedClass_isoClass_iff R T).mp h
  exact hP.of_sameEulerPolynomials (P.spectralSystem_sameEulerPolynomials Q)

end Langlands.ClassField.Global.RelativeWeilGroup
