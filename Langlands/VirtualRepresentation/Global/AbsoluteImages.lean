import Langlands.ClassField.Global.AbsoluteWeilGroupStatement
import Langlands.VirtualRepresentation.Global.RelativeImages
import Langlands.Weil.Representation.UnitaryProof

/-!
# Integral images of witnessed absolute global pairs

Henniart's two generating images over the projective limit `W_F` of a supplied transitive
system of Weil maps. The index retains actual irreducible unitary representations of `W_F`,
actual cuspidal objects, local-to-global Weil maps `W_{F_v} → W_F` and expansions of the full
local components. The images are compared with the relative images of the finite Galois
layers under explicit hypotheses. No generator, local map or system is constructed.
-/

noncomputable section

universe u uW uP

namespace Langlands.VirtualRepresentation.AbsoluteGlobal

open Langlands.Global Langlands.Global.CompletionPadic Langlands.ClassField.Global
open Langlands.Global.AdelicFunctoriality
open Langlands.Automorphic

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h) (v : FinitePlace F)

/-- The actual full local restriction along a map `W_{F_v} → W_F`, in continuous exact K0. -/
def localExactClass (A : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup) (hA : A.IsContinuous)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) :
    LocalWeil.ContinuousExactGroup.{u, uW} (padicField v) :=
  ExactGrothendieckGroup.ofRepresentation _
    ⟨S.localComponent A θ, S.localComponent_isContinuous θ hA⟩

/-- Restriction retains the whole carrier and its dimension. -/
@[simp]
theorem localExactClass_degree (A : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup)
    (hA : A.IsContinuous) (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) :
    ExactGrothendieckGroup.degree _ (localExactClass S v A hA θ) = (A.rank : ℤ) := by
  rw [localExactClass, ExactGrothendieckGroup.degree_ofRepresentation]
  rfl

section Conjugation

variable {S v}

/-- If `φ g = x⁻¹ * ψ g * x` for every `g`, then `A(x)` is an equivalence from the
restriction of `A` along `φ` to the restriction of `A` along `ψ`. -/
def restrictConjEquiv {H : Type*} [Monoid H] {G : Type*} [Group G]
    (A : FiniteRepresentation.{0, _, uW} ℂ G) {φ ψ : H →* G} (x : G)
    (hx : ∀ g, φ g = x⁻¹ * ψ g * x) :
    FiniteRepresentation.Equiv (FiniteRepresentation.restrict φ A)
      (FiniteRepresentation.restrict ψ A) :=
  Representation.Equiv.mk
    (show A ≃ₗ[ℂ] A from LinearEquiv.ofLinearMap (A.representation x) (A.representation x⁻¹)
      (LinearMap.ext fun y => by
        change A.representation x (A.representation x⁻¹ y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply])
      (LinearMap.ext fun y => by
        change A.representation x⁻¹ (A.representation x y) = y
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]))
    (fun g => by
      have hc : A.representation x * A.representation (φ g) =
          A.representation (ψ g) * A.representation x := by
        rw [← map_mul, ← map_mul, hx g]
        congr 1
        group
      exact hc)

/-- Equivalent representations of `W_F` have equal full local classes along `θ`. -/
theorem localExactClass_eq_of_equiv {A B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup}
    (hA : A.IsContinuous) (hB : B.IsContinuous)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup)
    (e : FiniteRepresentation.Equiv A B) :
    localExactClass S v A hA θ = localExactClass S v B hB θ := by
  unfold localExactClass
  exact ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
    (FiniteRepresentation.restrictEquiv θ.toMonoidHom e)

/-- The full local class of an inflation along `θ` equals the relative full local class along
any map `ι` with `S.toLevel K (θ g) = x⁻¹ * ι g * x`. -/
theorem localExactClass_inflate {K : FiniteGaloisIntermediateField F Ω}
    {B : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F K)} (hB : B.IsContinuous)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup)
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K)
    (x : RelativeWeilGroup c F K) (hx : ∀ g, S.toLevel K (θ g) = x⁻¹ * ι g * x) :
    localExactClass S v (S.inflate K B) (S.isContinuous_inflate hB) θ =
      RelativeGlobal.localExactClass F K c v B hB ι :=
  ExactGrothendieckGroup.ofRepresentation_eq_of_equiv _
    (restrictConjEquiv B (φ := (S.levelHom K).comp θ.toMonoidHom) (ψ := ι.toMonoidHom) x hx)

end Conjugation

variable [CompactSpace (AdeleQuotient F)]

/-- Actual associated objects over `W_F` together with a local-to-global Weil map at `v` and
full local expansion witnesses. The automorphic support carriers have the universe of the
actual form space; the Weil and presentation-factor carriers have independent universes. -/
structure WitnessedGenerator where
  rankIndex : ℕ
  weil : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup
  weil_irreducible : weil.IsIrreducible
  weil_unitary : weil.IsUnitary
  cuspidal : CuspidalOperatorRealization F rankIndex
  presentation : CuspidalSpectralPresentation.{u, uP} cuspidal
  associated : S.IsWeaklyAssociated weil presentation.spectralSystem
  localMap : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup
  localMap_spec : S.IsLocalWeilMap v localMap
  local_irreducible : (presentation.localComponent v).IsIrreducible
  local_admissible : (presentation.localComponent v).IsAdmissible
  weilElement : LocalWeil.UnitaryLattice.{u, uW} (padicField v)
  weil_effective : weilElement ∈ effective
  weil_expansion : LocalWeil.ExactExpansion (padicField v)
    (localExactClass S v weil associated.1 localMap)
    (LocalWeil.includeUnitary (padicField v) weilElement)
  automorphicElement : PadicSupercuspidal.UnitaryLattice.{u, u} (padicField v)
  automorphic_support : PadicSupercuspidal.IsUnitaryLatticeSupport (padicField v)
    ((presentation.localComponent v).padicObject local_irreducible local_admissible).obj
    automorphicElement

namespace WitnessedGenerator

variable {S v}
variable (d : WitnessedGenerator.{u, uW, uP} S v)

/-- Weak association retains the actual full cuspidal class. -/
theorem associatedClass : S.IsWeaklyAssociatedClass.{u, uW, uP} d.weil d.cuspidal.isoClass :=
  ⟨d.presentation.spectralSystem,
    (CuspidalOperatorRealization.IsoClass.hasSpectralSystem_iff d.cuspidal _).mpr
      ⟨d.presentation, rfl⟩,
    d.associated⟩

/-- An explicit full exact expansion has the global representation's rank. -/
theorem weil_degree :
    LocalWeil.unitaryDegree (padicField v) d.weilElement =
      ((d.rankIndex + 1 : ℕ) : ℤ) := by
  calc
    LocalWeil.unitaryDegree (padicField v) d.weilElement =
        ExactGrothendieckGroup.degree _
          (LocalWeil.realizeExact (padicField v)
            (LocalWeil.includeUnitary (padicField v) d.weilElement)) :=
      (LocalWeil.degree_realizeExact _ _).symm
    _ = ExactGrothendieckGroup.degree _
        (localExactClass S v d.weil d.associated.1 d.localMap) :=
      congrArg _ d.weil_expansion
    _ = (d.weil.rank : ℤ) := localExactClass_degree _ _ _ _ _
    _ = ((d.rankIndex + 1 : ℕ) : ℤ) := congrArg (fun n : ℕ => (n : ℤ)) d.associated.2.1

/-- Actual normalized-induction support has the general linear group rank. -/
theorem automorphic_degree :
    PadicSupercuspidal.unitaryDegree (padicField v) d.automorphicElement =
      ((d.rankIndex + 1 : ℕ) : ℤ) :=
  d.automorphic_support.degree

theorem degrees_eq :
    LocalWeil.unitaryDegree (padicField v) d.weilElement =
      PadicSupercuspidal.unitaryDegree (padicField v) d.automorphicElement :=
  d.weil_degree.trans d.automorphic_degree.symm

theorem automorphic_effective : d.automorphicElement ∈ effective :=
  d.automorphic_support.effective

end WitnessedGenerator

/-- The integral span of all actual witnessed absolute pairs at this place. -/
def pairedLattice :
    Submodule ℤ (LocalWeil.UnitaryLattice.{u, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{u, u} (padicField v)) :=
  generatedPairs
    (fun d : WitnessedGenerator.{u, uW, uP} S v => d.weilElement)
    (fun d => d.automorphicElement)

/-- The Weil image generated by the full witnessed local restrictions. -/
def weilImage : Submodule ℤ (LocalWeil.UnitaryLattice.{u, uW} (padicField v)) :=
  generated (fun d : WitnessedGenerator.{u, uW, uP} S v => d.weilElement)

/-- The automorphic image generated by actual unitary supercuspidal supports. -/
def automorphicImage :
    Submodule ℤ (PadicSupercuspidal.UnitaryLattice.{u, u} (padicField v)) :=
  generated (fun d : WitnessedGenerator.{u, uW, uP} S v => d.automorphicElement)

/-- Projection retains membership in the actual Weil generated span. -/
def weilProjection :
    pairedLattice.{u, uW, uP} S v →ₗ[ℤ] weilImage.{u, uW, uP} S v :=
  pairLeft _ _

/-- Projection retains membership in the actual support generated span. -/
def automorphicProjection :
    pairedLattice.{u, uW, uP} S v →ₗ[ℤ] automorphicImage.{u, uW, uP} S v :=
  pairRight _ _

variable {S v}

theorem witnessed_pair_mem (d : WitnessedGenerator.{u, uW, uP} S v) :
    (d.weilElement, d.automorphicElement) ∈ pairedLattice.{u, uW, uP} S v :=
  Submodule.subset_span (Set.mem_range_self d)

theorem witnessed_weil_mem (d : WitnessedGenerator.{u, uW, uP} S v) :
    d.weilElement ∈ weilImage.{u, uW, uP} S v :=
  Submodule.subset_span (Set.mem_range_self d)

theorem witnessed_automorphic_mem (d : WitnessedGenerator.{u, uW, uP} S v) :
    d.automorphicElement ∈ automorphicImage.{u, uW, uP} S v :=
  Submodule.subset_span (Set.mem_range_self d)

/-- Equal generator degrees extend to every signed integral pair in the span. -/
theorem degrees_eq_of_mem
    {x : LocalWeil.UnitaryLattice.{u, uW} (padicField v) ×
      PadicSupercuspidal.UnitaryLattice.{u, u} (padicField v)}
    (hx : x ∈ pairedLattice.{u, uW, uP} S v) :
    LocalWeil.unitaryDegree (padicField v) x.1 =
      PadicSupercuspidal.unitaryDegree (padicField v) x.2 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    exact d.degrees_eq
  | zero => simp
  | add x y hx hy ihx ihy => simp only [Prod.fst_add, Prod.snd_add, map_add, ihx, ihy]
  | smul a x hx ih =>
    change LocalWeil.unitaryDegree (padicField v) (a • x.1) =
      PadicSupercuspidal.unitaryDegree (padicField v) (a • x.2)
    rw [map_smul, map_smul, ih]

/-- Every Weil image element lifts to a pair in the actual paired span. -/
theorem exists_pair_of_mem_weilImage
    {x : LocalWeil.UnitaryLattice.{u, uW} (padicField v)}
    (hx : x ∈ weilImage.{u, uW, uP} S v) :
    ∃ y, (x, y) ∈ pairedLattice.{u, uW, uP} S v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, rfl⟩ := hx
    exact ⟨d.automorphicElement, witnessed_pair_mem d⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, Submodule.add_mem _ ha hb⟩
  | smul a x hx ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨a • b, Submodule.smul_mem _ a hb⟩

/-- Every support image element lifts to a pair in the actual paired span. -/
theorem exists_pair_of_mem_automorphicImage
    {y : PadicSupercuspidal.UnitaryLattice.{u, u} (padicField v)}
    (hy : y ∈ automorphicImage.{u, uW, uP} S v) :
    ∃ x, (x, y) ∈ pairedLattice.{u, uW, uP} S v := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, rfl⟩ := hy
    exact ⟨d.weilElement, witnessed_pair_mem d⟩
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨a, ha⟩ := ihx
    obtain ⟨b, hb⟩ := ihy
    exact ⟨a + b, Submodule.add_mem _ ha hb⟩
  | smul a x hx ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨a • b, Submodule.smul_mem _ a hb⟩

theorem weilProjection_surjective :
    Function.Surjective (weilProjection.{u, uW, uP} S v) := by
  intro x
  obtain ⟨y, hy⟩ := exists_pair_of_mem_weilImage x.property
  exact ⟨⟨(x.val, y), hy⟩, Subtype.ext rfl⟩

theorem automorphicProjection_surjective :
    Function.Surjective (automorphicProjection.{u, uW, uP} S v) := by
  intro y
  obtain ⟨x, hx⟩ := exists_pair_of_mem_automorphicImage y.property
  exact ⟨⟨(x, y.val), hx⟩, Subtype.ext rfl⟩

section Comparison

/-- A witnessed relative pair at a finite Galois layer `K` gives a witnessed absolute pair with
the same lattice elements. The inputs are surjectivity of `S.toLevel K`, local-to-global Weil
maps at cofinitely many places, and a local-to-global Weil map `θ` at `v` whose composite with
`S.toLevel K` is conjugate to the relative local map. -/
def WitnessedGenerator.ofRelative {K : FiniteGaloisIntermediateField F Ω}
    (d : RelativeGlobal.WitnessedGenerator.{u, uW, uP} F K c v)
    (hK : Function.Surjective (S.toLevel K))
    (hθ : ∀ᶠ v' in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v') →ₜ* S.WeilGroup, S.IsLocalWeilMap v' θ)
    (θ : Weil.Local.localWeilGroup (padicField v) →ₜ* S.WeilGroup) (hθv : S.IsLocalWeilMap v θ)
    (x : RelativeWeilGroup c F K) (hx : ∀ g, S.toLevel K (θ g) = x⁻¹ * d.localMap g * x) :
    WitnessedGenerator.{u, uW, uP} S v where
  rankIndex := d.rankIndex
  weil := S.inflate K d.weil
  weil_irreducible := S.isIrreducible_inflate hK d.weil_irreducible
  weil_unitary := S.isUnitary_inflate d.weil_unitary
  cuspidal := d.cuspidal
  presentation := d.presentation
  associated := S.isWeaklyAssociated_inflate d.associated hθ
  localMap := θ
  localMap_spec := hθv
  local_irreducible := d.local_irreducible
  local_admissible := d.local_admissible
  weilElement := d.weilElement
  weil_effective := d.weil_effective
  weil_expansion :=
    d.weil_expansion.trans (localExactClass_inflate d.associated.1 θ d.localMap x hx).symm
  automorphicElement := d.automorphicElement
  automorphic_support := d.automorphic_support

/-- Lifting of the local data of every relative generator at `K` and `v`. -/
theorem exists_ofRelative {K : FiniteGaloisIntermediateField F Ω}
    (hK : Function.Surjective (S.toLevel K))
    (hθ : ∀ᶠ v' in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v') →ₜ* S.WeilGroup, S.IsLocalWeilMap v' θ)
    (hlift : ∀ (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹)
    (d : RelativeGlobal.WitnessedGenerator.{u, uW, uP} F K c v) :
    ∃ d' : WitnessedGenerator.{u, uW, uP} S v,
      d'.weilElement = d.weilElement ∧ d'.automorphicElement = d.automorphicElement := by
  obtain ⟨θ, hθv, x, hx⟩ := hlift d.placeOver d.reciprocity d.localMap d.localMap_spec
  refine ⟨WitnessedGenerator.ofRelative d hK hθ θ hθv x⁻¹ fun g => ?_, rfl, rfl⟩
  rw [hx, inv_inv]

/-- A witnessed absolute pair comes from a witnessed relative pair at some finite Galois layer,
with the same lattice elements. The inputs are: factorization of continuous representations
of `W_F` through finite levels, surjectivity of every projection `S.toLevel K`, lifting of
every local-to-relative Weil map to a local-to-global one up to conjugation, and existence of
local-to-relative Weil maps at all places above cofinitely many finite places of `F`. -/
theorem WitnessedGenerator.exists_relative (d : WitnessedGenerator.{u, uW, uP} S v)
    (hfact : ∀ A : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup, A.IsContinuous →
      ∃ (K : FiniteGaloisIntermediateField F Ω)
        (B : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F K)),
        B.IsContinuous ∧ Nonempty (FiniteRepresentation.Equiv A (S.inflate K B)))
    (hsurj : ∀ K : FiniteGaloisIntermediateField F Ω, Function.Surjective (S.toLevel K))
    (hlift : ∀ (v' : FinitePlace F) (K : FiniteGaloisIntermediateField F Ω)
      (w : FinitePlacesAbove K v')
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v' w.1))
      (ι : Weil.Local.localWeilGroup (padicField v') →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v' w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v' θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹)
    (hrel : ∀ K : FiniteGaloisIntermediateField F Ω, ∀ᶠ v' in Filter.cofinite,
      ∀ w : FinitePlacesAbove K v',
        ∃ (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v' w.1))
          (ι : Weil.Local.localWeilGroup (padicField v') →ₜ* RelativeWeilGroup c F K),
          RelativeWeilGroup.IsLocalRelativeWeilMap v' w.1 e ι) :
    ∃ (K : FiniteGaloisIntermediateField F Ω)
      (d' : RelativeGlobal.WitnessedGenerator.{u, uW, uP} F K c v),
      d'.weilElement = d.weilElement ∧ d'.automorphicElement = d.automorphicElement := by
  obtain ⟨K, B, hB, ⟨e⟩⟩ := hfact d.weil d.associated.1
  obtain ⟨w, r, x, ι, hι, hθι⟩ := d.localMap_spec.exists_level K
  have hirr : B.IsIrreducible :=
    (OrderIso.isSimpleOrder_iff (WeilMapSystem.subrepresentationCompOrderIso B.representation
      (S.levelHom K) (hsurj K))).mpr
      ((Weil.IsomorphismInvariance.irreducible_iff e).mp d.weil_irreducible)
  have hunit : B.IsUnitary := by
    obtain ⟨b, hb⟩ := FiniteRepresentation.isUnitary_of_equiv e.symm d.weil_unitary
    refine ⟨b, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := hsurj K y
    exact hb x
  have hassoc : RelativeWeilGroup.IsWeaklyAssociated B d.presentation.spectralSystem := by
    obtain ⟨-, hn, hA⟩ := d.associated
    refine ⟨hB, (FiniteRepresentation.rank_eq_of_equiv e).symm.trans hn, ?_⟩
    filter_upwards [hA, hrel K] with v' hv' hex
    obtain ⟨hs, hm⟩ := hv'
    have hm' := hm.of_equiv S e
    refine ⟨hs, fun w' => ⟨hex w', fun r' ι' hι' => ?_⟩⟩
    obtain ⟨θ', hθ', y, hy⟩ := hlift v' K w' r' ι' hι'
    obtain ⟨hu, hp⟩ := hm'.2 θ' hθ'
    refine ⟨fun i => ?_, ?_⟩
    · have hi : B.representation (S.toLevel K (θ' i)) = 1 := hu i
      rw [hy] at hi
      change B.representation (ι' i) = 1
      have hconj : ι' i = y⁻¹ * (y * ι' i * y⁻¹) * y := by group
      rw [hconj, map_mul, map_mul, hi, mul_one, ← map_mul, inv_mul_cancel, map_one]
    · have hconj := WeilMapSystem.eulerPolynomial_representation_conj (A := B) y⁻¹
        (ι' (Weil.Local.localGeometricFrobenius (padicField v')))
      rw [inv_inv] at hconj
      have hp' : LocalFactor.eulerPolynomial (B.representation
          (S.toLevel K (θ' (Weil.Local.localGeometricFrobenius (padicField v'))))) =
          d.presentation.spectralSystem.eulerPolynomial v' hs := hp
      rw [hy, hconj] at hp'
      exact hp'
  have hexp : LocalWeil.ExactExpansion (padicField v)
      (RelativeGlobal.localExactClass F K c v B hassoc.1 ι)
      (LocalWeil.includeUnitary (padicField v) d.weilElement) := by
    refine d.weil_expansion.trans ?_
    rw [← localExactClass_inflate hB d.localMap ι x hθι]
    exact localExactClass_eq_of_equiv _ _ _ e
  exact ⟨K,
    { rankIndex := d.rankIndex
      weil := B
      weil_irreducible := hirr
      weil_unitary := hunit
      cuspidal := d.cuspidal
      presentation := d.presentation
      associated := hassoc
      placeOver := w
      reciprocity := r
      localMap := ι
      localMap_spec := hι
      local_irreducible := d.local_irreducible
      local_admissible := d.local_admissible
      weilElement := d.weilElement
      weil_effective := d.weil_effective
      weil_expansion := hexp
      automorphicElement := d.automorphicElement
      automorphic_support := d.automorphic_support }, rfl, rfl⟩

end Comparison

section Lattices

variable {K : FiniteGaloisIntermediateField F Ω}

/-- The relative paired lattice of one finite Galois layer lies in the absolute one, under the
hypotheses of `exists_ofRelative`. -/
theorem relative_pairedLattice_le (hK : Function.Surjective (S.toLevel K))
    (hθ : ∀ᶠ v' in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v') →ₜ* S.WeilGroup, S.IsLocalWeilMap v' θ)
    (hlift : ∀ (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹) :
    RelativeGlobal.pairedLattice.{u, uW, uP} F K c v ≤ pairedLattice.{u, uW, uP} S v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, rfl⟩
  obtain ⟨d', h1, h2⟩ := exists_ofRelative hK hθ hlift d
  have hd := witnessed_pair_mem d'
  rw [h1, h2] at hd
  exact hd

/-- The relative Weil image of one finite Galois layer lies in the absolute one, under the
hypotheses of `exists_ofRelative`. -/
theorem relative_weilImage_le (hK : Function.Surjective (S.toLevel K))
    (hθ : ∀ᶠ v' in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v') →ₜ* S.WeilGroup, S.IsLocalWeilMap v' θ)
    (hlift : ∀ (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹) :
    RelativeGlobal.weilImage.{u, uW, uP} F K c v ≤ weilImage.{u, uW, uP} S v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, rfl⟩
  obtain ⟨d', h1, -⟩ := exists_ofRelative hK hθ hlift d
  have hd := witnessed_weil_mem d'
  rw [h1] at hd
  exact hd

/-- The relative automorphic image of one finite Galois layer lies in the absolute one, under
the hypotheses of `exists_ofRelative`. -/
theorem relative_automorphicImage_le (hK : Function.Surjective (S.toLevel K))
    (hθ : ∀ᶠ v' in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v') →ₜ* S.WeilGroup, S.IsLocalWeilMap v' θ)
    (hlift : ∀ (w : FinitePlacesAbove K v)
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w.1))
      (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹) :
    RelativeGlobal.automorphicImage.{u, uW, uP} F K c v ≤ automorphicImage.{u, uW, uP} S v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, rfl⟩
  obtain ⟨d', -, h2⟩ := exists_ofRelative hK hθ hlift d
  have hd := witnessed_automorphic_mem d'
  rw [h2] at hd
  exact hd

variable (S v) in
/-- For the arithmetic fundamental-class family, the existence statements for the absolute
global Weil group put every relative paired lattice in the absolute one. -/
theorem iSup_relative_pairedLattice_le_of_statements
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hsurj : WeilLevelSurjectiveStatement.{u}) (hex : LocalWeilMapExistenceStatement.{u})
    (hlift : LocalWeilMapLiftStatement.{u}) :
    ⨆ K : FiniteGaloisIntermediateField F Ω, RelativeGlobal.pairedLattice.{u, uW, uP} F K c v ≤
      pairedLattice.{u, uW, uP} S v :=
  iSup_le fun K => relative_pairedLattice_le (hsurj c hc h F Ω S K)
    (Filter.Eventually.of_forall fun v' => hex c hc h F Ω S v')
    (fun w e ι hι => hlift c hc h F Ω S v K w e ι hι)

variable (S v) in
/-- For the arithmetic fundamental-class family, the existence statements for the absolute
global Weil group put every relative Weil image in the absolute one. -/
theorem iSup_relative_weilImage_le_of_statements
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hsurj : WeilLevelSurjectiveStatement.{u}) (hex : LocalWeilMapExistenceStatement.{u})
    (hlift : LocalWeilMapLiftStatement.{u}) :
    ⨆ K : FiniteGaloisIntermediateField F Ω, RelativeGlobal.weilImage.{u, uW, uP} F K c v ≤
      weilImage.{u, uW, uP} S v :=
  iSup_le fun K => relative_weilImage_le (hsurj c hc h F Ω S K)
    (Filter.Eventually.of_forall fun v' => hex c hc h F Ω S v')
    (fun w e ι hι => hlift c hc h F Ω S v K w e ι hι)

variable (S v) in
/-- For the arithmetic fundamental-class family, the existence statements for the absolute
global Weil group put every relative automorphic image in the absolute one. -/
theorem iSup_relative_automorphicImage_le_of_statements
    (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hsurj : WeilLevelSurjectiveStatement.{u}) (hex : LocalWeilMapExistenceStatement.{u})
    (hlift : LocalWeilMapLiftStatement.{u}) :
    ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.automorphicImage.{u, uW, uP} F K c v ≤
      automorphicImage.{u, uW, uP} S v :=
  iSup_le fun K => relative_automorphicImage_le (hsurj c hc h F Ω S K)
    (Filter.Eventually.of_forall fun v' => hex c hc h F Ω S v')
    (fun w e ι hι => hlift c hc h F Ω S v K w e ι hι)

end Lattices

section Converse

variable
    (hfact : ∀ A : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup, A.IsContinuous →
      ∃ (K : FiniteGaloisIntermediateField F Ω)
        (B : FiniteRepresentation.{0, u, uW} ℂ (RelativeWeilGroup c F K)),
        B.IsContinuous ∧ Nonempty (FiniteRepresentation.Equiv A (S.inflate K B)))
    (hsurj : ∀ K : FiniteGaloisIntermediateField F Ω, Function.Surjective (S.toLevel K))
    (hlift : ∀ (v' : FinitePlace F) (K : FiniteGaloisIntermediateField F Ω)
      (w : FinitePlacesAbove K v')
      (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v' w.1))
      (ι : Weil.Local.localWeilGroup (padicField v') →ₜ* RelativeWeilGroup c F K),
      RelativeWeilGroup.IsLocalRelativeWeilMap v' w.1 e ι →
        ∃ θ, S.IsLocalWeilMap v' θ ∧
          ∃ x : RelativeWeilGroup c F K, ∀ g, S.toLevel K (θ g) = x * ι g * x⁻¹)
    (hrel : ∀ K : FiniteGaloisIntermediateField F Ω, ∀ᶠ v' in Filter.cofinite,
      ∀ w : FinitePlacesAbove K v',
        ∃ (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v' w.1))
          (ι : Weil.Local.localWeilGroup (padicField v') →ₜ* RelativeWeilGroup c F K),
          RelativeWeilGroup.IsLocalRelativeWeilMap v' w.1 e ι)
include hfact hsurj hlift hrel

/-- Under the hypotheses of `WitnessedGenerator.exists_relative`, the absolute paired lattice
lies in the join of the relative ones. -/
theorem pairedLattice_le_iSup_relative :
    pairedLattice.{u, uW, uP} S v ≤
      ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.pairedLattice.{u, uW, uP} F K c v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, rfl⟩
  obtain ⟨K, d', h1, h2⟩ := d.exists_relative hfact hsurj hlift hrel
  have hd := RelativeGlobal.witnessed_pair_mem d'
  rw [h1, h2] at hd
  exact le_iSup (fun K : FiniteGaloisIntermediateField F Ω =>
    RelativeGlobal.pairedLattice.{u, uW, uP} F K c v) K hd

/-- Under the hypotheses of `WitnessedGenerator.exists_relative`, the absolute Weil image lies
in the join of the relative ones. -/
theorem weilImage_le_iSup_relative :
    weilImage.{u, uW, uP} S v ≤
      ⨆ K : FiniteGaloisIntermediateField F Ω, RelativeGlobal.weilImage.{u, uW, uP} F K c v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, rfl⟩
  obtain ⟨K, d', h1, -⟩ := d.exists_relative hfact hsurj hlift hrel
  have hd := RelativeGlobal.witnessed_weil_mem d'
  rw [h1] at hd
  exact le_iSup (fun K : FiniteGaloisIntermediateField F Ω =>
    RelativeGlobal.weilImage.{u, uW, uP} F K c v) K hd

/-- Under the hypotheses of `WitnessedGenerator.exists_relative`, the absolute automorphic
image lies in the join of the relative ones. -/
theorem automorphicImage_le_iSup_relative :
    automorphicImage.{u, uW, uP} S v ≤
      ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.automorphicImage.{u, uW, uP} F K c v := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨d, rfl⟩
  obtain ⟨K, d', -, h2⟩ := d.exists_relative hfact hsurj hlift hrel
  have hd := RelativeGlobal.witnessed_automorphic_mem d'
  rw [h2] at hd
  exact le_iSup (fun K : FiniteGaloisIntermediateField F Ω =>
    RelativeGlobal.automorphicImage.{u, uW, uP} F K c v) K hd

variable
    (hθ : ∀ᶠ v' in Filter.cofinite,
      ∃ θ : Weil.Local.localWeilGroup (padicField v') →ₜ* S.WeilGroup, S.IsLocalWeilMap v' θ)
include hθ

/-- The absolute paired lattice is the join of the relative ones, under the hypotheses of both
comparisons. -/
theorem pairedLattice_eq_iSup_relative :
    pairedLattice.{u, uW, uP} S v =
      ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.pairedLattice.{u, uW, uP} F K c v :=
  le_antisymm (pairedLattice_le_iSup_relative hfact hsurj hlift hrel)
    (iSup_le fun K => relative_pairedLattice_le (hsurj K) hθ (hlift v K))

/-- The absolute Weil image is the join of the relative ones, under the hypotheses of both
comparisons. -/
theorem weilImage_eq_iSup_relative :
    weilImage.{u, uW, uP} S v =
      ⨆ K : FiniteGaloisIntermediateField F Ω, RelativeGlobal.weilImage.{u, uW, uP} F K c v :=
  le_antisymm (weilImage_le_iSup_relative hfact hsurj hlift hrel)
    (iSup_le fun K => relative_weilImage_le (hsurj K) hθ (hlift v K))

/-- The absolute automorphic image is the join of the relative ones, under the hypotheses of
both comparisons. -/
theorem automorphicImage_eq_iSup_relative :
    automorphicImage.{u, uW, uP} S v =
      ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.automorphicImage.{u, uW, uP} F K c v :=
  le_antisymm (automorphicImage_le_iSup_relative hfact hsurj hlift hrel)
    (iSup_le fun K => relative_automorphicImage_le (hsurj K) hθ (hlift v K))

end Converse

section Statements

variable (S v)
variable (hc : RelativeWeilGroup.IsArithmeticClassFamily c)
    (hsurj : WeilLevelSurjectiveStatement.{u}) (hex : LocalWeilMapExistenceStatement.{u})
    (hlift : LocalWeilMapLiftStatement.{u})
    (hfact : WeilRepresentationFactorizationStatement.{u, uW})
    (hrel : ∀ K : FiniteGaloisIntermediateField F Ω, ∀ᶠ v' in Filter.cofinite,
      ∀ w : FinitePlacesAbove K v',
        ∃ (e : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v' w.1))
          (ι : Weil.Local.localWeilGroup (padicField v') →ₜ* RelativeWeilGroup c F K),
          RelativeWeilGroup.IsLocalRelativeWeilMap v' w.1 e ι)
include hc hsurj hex hlift hfact hrel

/-- For the arithmetic fundamental-class family, the existence statements for the absolute
global Weil group and the existence of local-to-relative Weil maps above cofinitely many
places identify the absolute paired lattice with the join of the relative ones. -/
theorem pairedLattice_eq_iSup_relative_of_statements :
    pairedLattice.{u, uW, uP} S v =
      ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.pairedLattice.{u, uW, uP} F K c v :=
  pairedLattice_eq_iSup_relative (hfact c hc h F Ω S) (hsurj c hc h F Ω S)
    (hlift c hc h F Ω S) hrel (Filter.Eventually.of_forall fun v' => hex c hc h F Ω S v')

/-- For the arithmetic fundamental-class family, the existence statements for the absolute
global Weil group and the existence of local-to-relative Weil maps above cofinitely many
places identify the absolute Weil image with the join of the relative ones. -/
theorem weilImage_eq_iSup_relative_of_statements :
    weilImage.{u, uW, uP} S v =
      ⨆ K : FiniteGaloisIntermediateField F Ω, RelativeGlobal.weilImage.{u, uW, uP} F K c v :=
  weilImage_eq_iSup_relative (hfact c hc h F Ω S) (hsurj c hc h F Ω S)
    (hlift c hc h F Ω S) hrel (Filter.Eventually.of_forall fun v' => hex c hc h F Ω S v')

/-- For the arithmetic fundamental-class family, the existence statements for the absolute
global Weil group and the existence of local-to-relative Weil maps above cofinitely many
places identify the absolute automorphic image with the join of the relative ones. -/
theorem automorphicImage_eq_iSup_relative_of_statements :
    automorphicImage.{u, uW, uP} S v =
      ⨆ K : FiniteGaloisIntermediateField F Ω,
        RelativeGlobal.automorphicImage.{u, uW, uP} F K c v :=
  automorphicImage_eq_iSup_relative (hfact c hc h F Ω S) (hsurj c hc h F Ω S)
    (hlift c hc h F Ω S) hrel (Filter.Eventually.of_forall fun v' => hex c hc h F Ω S v')

end Statements

end Langlands.VirtualRepresentation.AbsoluteGlobal
