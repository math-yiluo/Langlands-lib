import Langlands.GroupScheme.Rational.ParabolicRootPresentationStatement
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.GenericCocharacter
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Rational.StandardCocharacterReduction
import Langlands.GroupScheme.Rational.RelativeRootSignsProof
import Langlands.GroupScheme.Rational.RelativeRootSignInclusionsProof
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-! # Presentations from simultaneous dynamic realization of specified maps -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A cocharacter has a generic refinement whose nonnegative relative-root
support is contained in the original support. -/
theorem IsSplitTorus.exists_genericCocharacter_refining
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ξ : cocharacterLattice T) :
    ∃ ν : cocharacterLattice T, IsGenericCocharacter i ν ∧
      ∀ α ∈ relativeRoots i,
        0 ≤ latticePairing T α ν → 0 ≤ latticePairing T α ξ := by
  classical
  obtain ⟨eta, heta⟩ := hT.exists_genericCocharacter i
  let hr := hT.finite_relativeRoots i
  let q := fun α : characterLattice T => (latticePairing T α).toAddMonoidHom
  let s := hr.toFinset
  have heta' : ∀ α ∈ s, q α eta ≠ 0 := fun α hα => heta α (hr.mem_toFinset.mp hα)
  obtain ⟨hgeneric, hsupport⟩ :=
    IntegralPerturbation.regular_and_nonneg q s ξ eta heta' le_rfl
  refine ⟨IntegralPerturbation.bound q s eta • ξ + eta, ?_, ?_⟩
  · exact fun α hα => hgeneric α (hr.mem_toFinset.mpr hα)
  · exact fun α hα => hsupport α (hr.mem_toFinset.mpr hα)

/-- The given cocharacter is standard for its zero face relative to a generic
refinement; it simultaneously realizes that face's parabolic and Levi.
Negation stability is the only unproved root input here. -/
theorem exists_generic_standardFace_realizing
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)
    (ξ : cocharacterLattice T) :
    let := hG.isAffineHom
    ∃ ν : cocharacterLattice T, IsGenericCocharacter i ν ∧
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i) ∧
      IsStandardCocharacter i ν (simpleRootFace i ν ξ) ξ ∧
      standardParabolic i ν (simpleRootFace i ν ξ) =
        Dynamic.parabolic (CommGroupScheme.groupHom ξ ≫ i) ∧
      standardLevi i ν (simpleRootFace i ν ξ) =
        Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i) := by
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨ν, hν, hsupport⟩ := hi.isSplitSubtorus.1.exists_genericCocharacter_refining i ξ
  have hle := (relativeRootSignInclusions k G hG T i hi ν ξ).1.mpr hsupport
  have hξ : IsStandardCocharacter i ν (simpleRootFace i ν ξ) ξ :=
    isStandardCocharacter_simpleRootFace i ν (fun α hα =>
      hsupport α (simpleRelativeRoots_subset_positive i ν hα).1
        (simpleRelativeRoots_subset_positive i ν hα).2.le)
  have hcompare : StandardCocharacterDynamicComparison i ν (simpleRootFace i ν ξ) := by
    intro ζ hζ eta heta
    exact relativeRootSignsDetermineDynamic k G hG T i hi ζ eta
      (hζ.haveSameRelativeRootSigns i ν hν (hnegation k G hG T i hi) heta)
  have hstandard := hcompare.standard_eq_dynamic i ν (simpleRootFace i ν ξ) hξ
  exact ⟨ν, hν, hle, hξ, hstandard.1, hstandard.2.1⟩

variable {P M : GroupScheme (Spec (CommRingCat.of k))}
  {A : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Simultaneous dynamic realization of the supplied parabolic and Levi yields
a compatible presentation for every supplied split component. The generic
minimality and root-negation inputs remain explicit. -/
theorem nonempty_parabolicRootPresentation_of_dynamic_realization
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic χ)
    (hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ) :
    let := hG.isAffineHom
    Nonempty (ParabolicRootPresentation p l a) := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hl.isConnectedReductive.isAffineHom
  obtain ⟨T, i, ξ, hi, hξ⟩ := cocharacterMaximalSplitTorus k G χ
  rw [← hξ] at hP hM
  obtain ⟨ν, hν, hle, hstandard, hstdP, hstdM⟩ :=
    exists_generic_standardFace_realizing hnegation hG i hi ξ
  have hjc : IsClosedSubgroup (l ≫ p) := hl.isClosedSubgroup.comp hp.isClosedSubgroup
  let := hjc.mono
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i)).IsRepresentedBy
      (l ≫ p) := ⟨Over.mono_of_mono_left _, hM⟩
  let t := Dynamic.torusFactor i (CommGroupScheme.groupHom ξ) hrep
  have ht : t ≫ (l ≫ p) = i := Dynamic.torusFactor_comp i _ hrep
  have htmax : IsMaximalSplitTorus (t ≫ (l ≫ p)) := ht.symm ▸ hi
  obtain ⟨f, hf⟩ := ha.1.exists_factor_of_isMaximalSplitTorus hjc htmax
  have hfactor : f ≫ i = a ≫ l ≫ p := by
    rw [← ht, ← Category.assoc, hf]
  refine ⟨⟨⟨T, i, ν, simpleRootFace i ν ξ, Additive.ofMul f⟩, ?_⟩⟩
  exact
    { parabolic := hp
      levi := hl
      splitComponent := ha
      maximalSplit := hi
      generic := hν
      subset_simpleRoots := simpleRootFace_subset i ν ξ
      parabolic_eq := hP.trans hstdP.symm
      levi_eq := hM.trans hstdM.symm
      factor_comp := hfactor
      minimal := hminimal k G hG T i hi ν hν
      minimal_le := hle.trans hP.ge
      realization := ⟨ξ, hstandard, hP, hM⟩ }

/-- Choose a presentation for the supplied maps from their simultaneous dynamic
realization, retaining generic minimality and root negation as inputs. -/
def parabolicRootPresentationOfDynamicRealization
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hP : SubgroupFunctor.range p = Dynamic.parabolic χ)
    (hM : SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ) :
    let := hG.isAffineHom
    ParabolicRootPresentation p l a := by
  let := hG.isAffineHom
  exact Classical.choice (nonempty_parabolicRootPresentation_of_dynamic_realization
    hminimal hnegation hG hp hl ha χ hP hM)

/-- With generic minimality and root negation explicit, existence for the
specified maps is equivalent to their simultaneous dynamic realization. -/
theorem nonempty_parabolicRootPresentation_iff_dynamic_realization
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G)
    {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
    (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l) (ha : IsSplitComponent a) :
    let := hG.isAffineHom
    Nonempty (ParabolicRootPresentation p l a) ↔
      ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        SubgroupFunctor.range p = Dynamic.parabolic χ ∧
        SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ := by
  let := hG.isAffineHom
  constructor
  · rintro ⟨r⟩
    obtain ⟨ξ, -, hP, hM⟩ := r.isCompatible.realization
    exact ⟨_, hP, hM⟩
  · rintro ⟨χ, hP, hM⟩
    exact nonempty_parabolicRootPresentation_of_dynamic_realization
      hminimal hnegation hG hp hl ha χ hP hM

/-- The exact universal existence target reduces to simultaneous realization
of each specified parabolic and Levi, with the remaining root inputs explicit. -/
theorem parabolicRootPresentationExistenceStatement_iff_dynamic_realization
    (hminimal : GenericMinimalParabolicStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u}) :
    ParabolicRootPresentationExistenceStatement.{u} ↔
      ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
        (_hG : IsConnectedReductive G)
        (P M : GroupScheme (Spec (CommRingCat.of k)))
        (A : CommGroupScheme (Spec (CommRingCat.of k)))
        (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M),
        IsParabolicSubgroup p → IsRationalLeviSubgroup l → IsSplitComponent a →
          ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
            SubgroupFunctor.range p = Dynamic.parabolic χ ∧
            SubgroupFunctor.range (l ≫ p) = Dynamic.centralizer χ := by
  constructor
  · intro hexists k _ G hG P M A p l a hp hl ha
    exact (nonempty_parabolicRootPresentation_iff_dynamic_realization
      hminimal hnegation hG hp hl ha).mp (hexists k G hG P M A p l a hp hl ha)
  · intro hrealization k _ G hG P M A p l a hp hl ha
    exact (nonempty_parabolicRootPresentation_iff_dynamic_realization
      hminimal hnegation hG hp hl ha).mpr
      (hrealization k G hG P M A p l a hp hl ha)

end Langlands.GroupScheme
