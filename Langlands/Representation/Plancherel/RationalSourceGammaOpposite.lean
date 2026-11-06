import Langlands.Representation.Plancherel.RationalSourceGammaIndex
import Langlands.Representation.Plancherel.ParabolicPointUniformNumerator

/-! # Actual auxiliary subgroups and opposite symmetry of source gamma -/

noncomputable section

namespace Langlands.Plancherel

universe v

private theorem mem_levi_first_iff_of_unique_factorization
    {A : Type v} [Group A] {M U V H : Subgroup A}
    (hMU : M ≤ Subgroup.normalizer (U : Set A))
    (hunique : ∀ u ∈ U, ∀ m ∈ M, ∀ v ∈ V,
      ∀ u' ∈ U, ∀ m' ∈ M, ∀ v' ∈ V,
        u * m * v = u' * m' * v' → u = u' ∧ m = m' ∧ v = v')
    (hfactor : ∀ h ∈ H, ∃ u ∈ H ⊓ U, ∃ m ∈ H ⊓ M,
      ∃ v ∈ H ⊓ V, h = u * m * v)
    (m : M) (u : U) (v : V) :
    (m : A) * u * (v : A) ∈ H ↔
      (m : A) ∈ H ∧ (u : A) ∈ H ∧ (v : A) ∈ H := by
  constructor
  · intro hh
    let u' : U := ⟨(m : A) * u * (m : A)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hMU m.property) (u : A)).mp u.property⟩
    obtain ⟨a, ha, b, hb, c, hc, he⟩ := hfactor _ hh
    have heq : (u' : A) * m * (v : A) = a * b * c := by
      calc
        _ = (m : A) * u * (v : A) := by dsimp [u']; group
        _ = _ := he
    obtain ⟨hua, hmb, hvc⟩ := hunique u' u'.property m m.property v v.property
      a ha.2 b hb.2 c hc.2 heq
    have hmH : (m : A) ∈ H := hmb.symm ▸ hb.1
    have huH' : (u' : A) ∈ H := hua.symm ▸ ha.1
    have huH : (u : A) ∈ H := by
      have hh' := H.mul_mem (H.mul_mem (H.inv_mem hmH) huH') hmH
      simpa [u', mul_assoc] using hh'
    exact ⟨hmH, huH, hvc.symm ▸ hc.1⟩
  · rintro ⟨hm, hu, hv⟩
    exact H.mul_mem (H.mul_mem hm hu) hv

end Langlands.Plancherel

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj NNReal ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
local instance : MeasurableSpace (RationalPoint F G.X) := borel (RationalPoint F G.X)
local instance : BorelSpace (RationalPoint F G.X) := ⟨rfl⟩
local instance : T2Space F := BruhatTits.localField_t2Space F
local instance : IsTopologicalGroup (RationalPoint F G.X) :=
  rationalPoint_isTopologicalGroup F G
local instance : T2Space (RationalPoint F G.X) := rationalPoint_t2Space F G
local instance : LocallyCompactSpace (RationalPoint F G.X) :=
  rationalPoint_locallyCompactSpace F G
local instance : NonarchimedeanGroup (RationalPoint F G.X) :=
  RationalPointFamily.affineRationalPoint_nonarchimedeanGroup G
local instance : SecondCountableTopology F := localField_secondCountableTopology F
local instance : SecondCountableTopology (RationalPoint F G.X) :=
  Aubert.General.rationalPoint_secondCountableTopology F G
local instance subgroupSecondCountableGammaOpposite (H : Subgroup (RationalPoint F G.X)) :
    SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set (RationalPoint F G.X))

variable (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))
local notation "P" => SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀
local notation "Q" => SubgroupFunctor.carrier (Dynamic.parabolic (oppositeCocharacter χ)) X₀
local notation "M" => SubgroupFunctor.carrier (Dynamic.centralizer χ) X₀
local notation "U" => unipotentPoints χ
local notation "V" => unipotentPoints (oppositeCocharacter χ)

/-- The already proved actual opposite Iwahori basis supplies one compact
open subgroup below any prescribed open subgroup, with recoverable local
factors in both Levi-first orders. -/
theorem exists_gammaAuxiliarySubgroup
    (K : OpenSubgroup (RationalPoint F G.X)) (hG : IsConnectedReductive G) :
    ∃ H : OpenSubgroup (RationalPoint F G.X),
      IsCompact (H : Set (RationalPoint F G.X)) ∧ H ≤ K ∧
      (∀ (m : M) (u : U) (v : V),
        (m : RationalPoint F G.X) * u * (v : RationalPoint F G.X) ∈ H ↔
          (m : RationalPoint F G.X) ∈ H ∧
            (u : RationalPoint F G.X) ∈ H ∧ (v : RationalPoint F G.X) ∈ H) ∧
      (∀ (m : M) (v : V) (u : U),
        (m : RationalPoint F G.X) * v * (u : RationalPoint F G.X) ∈ H ↔
          (m : RationalPoint F G.X) ∈ H ∧
            (v : RationalPoint F G.X) ∈ H ∧ (u : RationalPoint F G.X) ∈ H) := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsSeparated G.X.hom := hG.isSeparated
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨g, -, hbasis⟩ := exists_dynamic_oppositeIwahoriContractionBasis χ
  obtain ⟨H, hH, hHK, hUpper, hLower⟩ := hbasis K K.isOpen K.one_mem
  have hMopp : Dynamic.centralizer (oppositeCocharacter χ) = Dynamic.centralizer χ :=
    Dynamic.centralizer_inverseCocharacter χ
  have hdouble : Dynamic.inverseCocharacter (oppositeCocharacter χ) = χ :=
    Dynamic.inverseCocharacter_inverseCocharacter χ
  have hMU : M ≤ Subgroup.normalizer (U : Set (RationalPoint F G.X)) :=
    Dynamic.centralizer_le_normalizer_unipotent χ X₀
  have hMV : M ≤ Subgroup.normalizer (V : Set (RationalPoint F G.X)) := by
    rw [← hMopp]
    exact Dynamic.centralizer_le_normalizer_unipotent (oppositeCocharacter χ) X₀
  refine ⟨H, hH, hHK, ?_, ?_⟩
  · have huniq := RationalPointFamily.dynamic_opposite_factorization_unique
      (oppositeCocharacter χ)
    rw [hdouble, hMopp] at huniq
    exact mem_levi_first_iff_of_unique_factorization hMU huniq hLower.factor
  · exact mem_levi_first_iff_of_unique_factorization hMV
      (RationalPointFamily.dynamic_opposite_factorization_unique χ) hUpper.factor

/-- A genuine compact open subgroup chosen from the proved actual
opposite Iwahori basis, solely for local gamma evaluation. -/
def gammaAuxiliarySubgroup
    (K : OpenSubgroup (RationalPoint F G.X)) (hG : IsConnectedReductive G) :
    OpenSubgroup (RationalPoint F G.X) :=
  Classical.choose (exists_gammaAuxiliarySubgroup χ K hG)

theorem gammaAuxiliarySubgroup_spec
    (K : OpenSubgroup (RationalPoint F G.X)) (hG : IsConnectedReductive G) :
    IsCompact (gammaAuxiliarySubgroup χ K hG : Set (RationalPoint F G.X)) ∧
      gammaAuxiliarySubgroup χ K hG ≤ K ∧
      (∀ (m : M) (u : U) (v : V),
        (m : RationalPoint F G.X) * u * (v : RationalPoint F G.X) ∈
            gammaAuxiliarySubgroup χ K hG ↔
          (m : RationalPoint F G.X) ∈ gammaAuxiliarySubgroup χ K hG ∧
            (u : RationalPoint F G.X) ∈ gammaAuxiliarySubgroup χ K hG ∧
              (v : RationalPoint F G.X) ∈ gammaAuxiliarySubgroup χ K hG) ∧
      (∀ (m : M) (v : V) (u : U),
        (m : RationalPoint F G.X) * v * (u : RationalPoint F G.X) ∈
            gammaAuxiliarySubgroup χ K hG ↔
          (m : RationalPoint F G.X) ∈ gammaAuxiliarySubgroup χ K hG ∧
            (v : RationalPoint F G.X) ∈ gammaAuxiliarySubgroup χ K hG ∧
              (u : RationalPoint F G.X) ∈ gammaAuxiliarySubgroup χ K hG) :=
  Classical.choose_spec (exists_gammaAuxiliarySubgroup χ K hG)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom] in
/-- The actual gamma index expression is invariant under reversal of a
cocharacter: the Levi is unchanged and the two radical factors swap. -/
theorem gammaIndex_oppositeCocharacter
    (K H : OpenSubgroup (RationalPoint F G.X)) :
    gammaIndex (oppositeCocharacter χ) K H = gammaIndex χ K H := by
  have hMopp : Dynamic.centralizer (oppositeCocharacter χ) = Dynamic.centralizer χ :=
    Dynamic.centralizer_inverseCocharacter χ
  have hdouble : oppositeCocharacter (oppositeCocharacter χ) = χ :=
    Dynamic.inverseCocharacter_inverseCocharacter χ
  unfold gammaIndex
  rw [hMopp, hdouble]
  ring

variable (K : OpenSubgroup (RationalPoint F G.X))
  (hK : IsCompact (K : Set (RationalPoint F G.X)))

/-- The original gamma is computed on a proved actual small subgroup;
local H factorization is now discharged rather than postulated. -/
theorem gamma_eq_auxiliary_gammaIndex
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K) :
    gamma χ K hK = gammaIndex χ K (gammaAuxiliarySubgroup χ K hG) := by
  obtain ⟨-, hHK, hfactor, -⟩ := gammaAuxiliarySubgroup_spec χ K hG
  exact gamma_eq_gammaIndex χ K hK hG hstable _ hHK hfactor

/-- Reversing a cocharacter preserves the actual common-compact gamma.
Both compact-limit stability premises remain explicit; local small-group
factorizations are proved from the published opposite Iwahori basis. -/
theorem gamma_oppositeCocharacter
    (hG : IsConnectedReductive G)
    (hstable : ∀ p : P, (p : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom χ X₀ p : RationalPoint F G.X) ∈ K)
    (hstableOpp : ∀ q : Q, (q : RationalPoint F G.X) ∈ K →
      (Dynamic.limitHom (oppositeCocharacter χ) X₀ q : RationalPoint F G.X) ∈ K) :
    gamma (oppositeCocharacter χ) K hK = gamma χ K hK := by
  let H := gammaAuxiliarySubgroup χ K hG
  obtain ⟨-, hHK, hfactor, hfactorOpp⟩ := gammaAuxiliarySubgroup_spec χ K hG
  have hMopp : Dynamic.centralizer (oppositeCocharacter χ) = Dynamic.centralizer χ :=
    Dynamic.centralizer_inverseCocharacter χ
  have hdouble : oppositeCocharacter (oppositeCocharacter χ) = χ :=
    Dynamic.inverseCocharacter_inverseCocharacter χ
  have hlocalOpp : ∀ (m : SubgroupFunctor.carrier
      (Dynamic.centralizer (oppositeCocharacter χ)) X₀) (v : V)
      (u : unipotentPoints (oppositeCocharacter (oppositeCocharacter χ))),
      (m : RationalPoint F G.X) * v * (u : RationalPoint F G.X) ∈ H ↔
        (m : RationalPoint F G.X) ∈ H ∧
          (v : RationalPoint F G.X) ∈ H ∧ (u : RationalPoint F G.X) ∈ H := by
    rw [hMopp, hdouble]
    exact hfactorOpp
  calc
    gamma (oppositeCocharacter χ) K hK = gammaIndex (oppositeCocharacter χ) K H :=
      gamma_eq_gammaIndex (oppositeCocharacter χ) K hK hG hstableOpp H hHK hlocalOpp
    _ = gammaIndex χ K H := gammaIndex_oppositeCocharacter χ K H
    _ = gamma χ K hK := (gamma_eq_gammaIndex χ K hK hG hstable H hHK hfactor).symm

end Langlands.Plancherel.RationalDynamicSource
