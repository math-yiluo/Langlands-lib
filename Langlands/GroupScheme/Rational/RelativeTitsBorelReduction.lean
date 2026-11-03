import Langlands.GroupScheme.Rational.RelativeTitsCoxeterReduction
import Langlands.GroupScheme.Rational.RelativeTitsBruhatReduction
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsStatement

/-! # The Borel axioms of the relative Tits system from the Bruhat decomposition

The rational Bruhat decomposition and the minimal endpoint identity `P_∅(k) = P(ν)(k)` give the
kernel and generation axioms of the relative Tits data. The Tits axioms that involve `B = P_∅(k)`
(`HasRelativeTitsBorelAxioms`) then reduce to the multiplication and nondegeneracy axioms
(Borel–Tits 5.16), grouped here as `HasRelativeTitsCellAxioms`. At the level of the published
statements, `RelativeTitsSystemStatement` follows from `RelativeWeylCoxeterStatement`,
`StandardParabolicEndpointsStatement`, `RationalBruhatStatement` and these two axioms. None of
these inputs is proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The multiplication and nondegeneracy axioms of the relative Tits data `(G(k), B, N(k), S)`,
with `B = P_∅(k)`, `N(k) = normalizerPoints i`, `π : N(k) → N(k)/Z(k)` and
`S = simpleRelativeReflections i ν`: `s B w ⊆ B w B ∪ B s w B` for every representative, and
`n B n⁻¹ ⊈ B` for every representative `n` of `s ∈ S`. These are the fields `mul_mem_cell` and
`conj_not_le` of `Langlands.Group.IsTitsSystem` (Borel–Tits 5.16 (i) and (ii)). -/
def HasRelativeTitsCellAxioms (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (ν : cocharacterLattice T) : Prop :=
  (∀ s ∈ simpleRelativeReflections i ν, ∀ n m : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      ∀ b ∈ standardParabolicPoints i ν ∅,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b * m ∈
          Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) m) ∪
            Langlands.Group.TitsSystem.cell (standardParabolicPoints i ν ∅)
              (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)))
              (s * QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) m)) ∧
    ∀ s ∈ simpleRelativeReflections i ν, ∀ n : normalizerPoints i,
      QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i)) n = s →
      ∃ b ∈ standardParabolicPoints i ν ∅,
        (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * b *
          (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)⁻¹ ∉
            standardParabolicPoints i ν ∅

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ν : cocharacterLattice T}

/-- The Borel axioms are the kernel identity, generation and the cell axioms. -/
theorem hasRelativeTitsBorelAxioms_iff :
    HasRelativeTitsBorelAxioms i ν ↔
      (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))).ker =
          (standardParabolicPoints i ν ∅).subgroupOf (normalizerPoints i) ∧
        standardParabolicPoints i ν ∅ ⊔ normalizerPoints i = ⊤ ∧
        HasRelativeTitsCellAxioms i ν :=
  Iff.rfl

/-- The Borel axioms contain the cell axioms. -/
theorem HasRelativeTitsBorelAxioms.hasRelativeTitsCellAxioms
    (h : HasRelativeTitsBorelAxioms i ν) : HasRelativeTitsCellAxioms i ν :=
  h.2.2

/-- A relative Tits system satisfies the cell axioms. -/
theorem HasRelativeTitsSystem.hasRelativeTitsCellAxioms (h : HasRelativeTitsSystem i ν) :
    HasRelativeTitsCellAxioms i ν :=
  h.hasRelativeTitsBorelAxioms.hasRelativeTitsCellAxioms

variable (hB : standardParabolicPoints i ν ∅ =
    (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
  (hBr : HasRationalBruhatDecomposition i ν)
include hB hBr

/-- The minimal endpoint identity and the rational Bruhat decomposition, together with the
cell axioms, give the Borel axioms. -/
theorem hasRelativeTitsBorelAxioms_of_bruhat (hcell : HasRelativeTitsCellAxioms i ν) :
    HasRelativeTitsBorelAxioms i ν :=
  ⟨relativeTits_ker_eq_of_bruhat i ν hBr, relativeTits_sup_eq_of_bruhat i ν hB hBr, hcell⟩

/-- Under the minimal endpoint identity and the rational Bruhat decomposition, the Borel axioms
are equivalent to the cell axioms. -/
theorem hasRelativeTitsBorelAxioms_iff_of_bruhat :
    HasRelativeTitsBorelAxioms i ν ↔ HasRelativeTitsCellAxioms i ν :=
  ⟨HasRelativeTitsBorelAxioms.hasRelativeTitsCellAxioms,
    hasRelativeTitsBorelAxioms_of_bruhat hB hBr⟩

/-- Under `HasRelativeWeylCoxeterSystem` for a split torus, the minimal endpoint identity and
the rational Bruhat decomposition, the relative Tits system is equivalent to the cell
axioms. -/
theorem HasRelativeWeylCoxeterSystem.hasRelativeTitsSystem_iff_hasRelativeTitsCellAxioms
    (h : HasRelativeWeylCoxeterSystem i ν) (hT : IsSplitTorus T.toGrp) :
    HasRelativeTitsSystem i ν ↔ HasRelativeTitsCellAxioms i ν :=
  (h.hasRelativeTitsSystem_iff hT).trans (hasRelativeTitsBorelAxioms_iff_of_bruhat hB hBr)

omit hB hBr

/-- **Reduction of the relative Tits system to the published structural statements and the cell
axioms.** `RelativeWeylCoxeterStatement`, `StandardParabolicEndpointsStatement` and
`RationalBruhatStatement`, together with the cell axioms for every maximal split torus of a
connected reductive group and every generic cocharacter, give `RelativeTitsSystemStatement`. -/
theorem relativeTitsSystemStatement_of_statements
    (hcox : RelativeWeylCoxeterStatement.{u}) (hE : StandardParabolicEndpointsStatement.{u})
    (hBr : RationalBruhatStatement.{u})
    (hcell : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
      haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      IsGenericCocharacter i ν → HasRelativeTitsCellAxioms i ν) :
    RelativeTitsSystemStatement.{u} := by
  refine relativeTitsSystemStatement_of_relativeWeylCoxeter hcox ?_
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  have hB : standardParabolicPoints i ν ∅ =
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    rw [standardParabolicPoints, (hE k G hG T i hi ν hν).1]
  exact hasRelativeTitsBorelAxioms_of_bruhat hB (hBr k G hG T i hi ν hν)
    (hcell k G hG T i hi ν hν)

/-- Conversely, `RelativeTitsSystemStatement` gives the cell axioms in the same generality. -/
theorem RelativeTitsSystemStatement.hasRelativeTitsCellAxioms
    (h : RelativeTitsSystemStatement.{u}) (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν → HasRelativeTitsCellAxioms i ν := by
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  exact (h k G hG T i hi ν hν).hasRelativeTitsCellAxioms

end Langlands.GroupScheme
