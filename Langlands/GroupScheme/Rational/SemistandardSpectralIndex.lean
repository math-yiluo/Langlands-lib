import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Dynamic.GeometricUnipotentRadicalProof
import Langlands.GroupScheme.Rational.ParabolicFunctor

/-! # Intrinsic semistandard spectral indices on all test schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

/-- The source's actual semistandard parabolics: all-test containment of the
fixed torus, with no chosen representing scheme. -/
abbrev SemistandardParabolicFunctor :=
  {P : SubgroupFunctor G // IsParabolicFunctor P ∧ SubgroupFunctor.range i ≤ P}

/-- An intrinsic parabolic, distinguished Levi containing the fixed torus,
and geometric radical. All remaining fields are propositions. -/
structure SemistandardSpectralIndex where
  parabolic : SubgroupFunctor G
  levi : SubgroupFunctor G
  radical : SubgroupFunctor G
  torus_le_levi : SubgroupFunctor.range i ≤ levi
  isParabolicWithLeviAndRadical :
    SubgroupFunctor.IsParabolicWithLeviAndRadical parabolic levi radical

namespace SemistandardSpectralIndex

variable {i}

@[ext] theorem ext {p q : SemistandardSpectralIndex i}
    (hP : p.parabolic = q.parabolic) (hM : p.levi = q.levi)
    (hU : p.radical = q.radical) : p = q := by
  cases p
  cases q
  cases hP
  cases hM
  cases hU
  rfl

theorem levi_le_parabolic (p : SemistandardSpectralIndex i) : p.levi ≤ p.parabolic := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    p.isParabolicWithLeviAndRadical
  exact fun X => (h X).2.1

theorem radical_le_parabolic (p : SemistandardSpectralIndex i) :
    p.radical ≤ p.parabolic := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ :=
    p.isParabolicWithLeviAndRadical
  exact fun X => (h X).1

/-- Forgetting the distinguished Levi and radical lands in exactly the
source's semistandard parabolic carrier. -/
def toParabolic (p : SemistandardSpectralIndex i) : SemistandardParabolicFunctor i :=
  ⟨p.parabolic, p.isParabolicWithLeviAndRadical.isParabolicFunctor,
    p.torus_le_levi.trans p.levi_le_parabolic⟩

/-- Every actual cocharacter of the fixed torus gives an intrinsic index.
The dynamic parabolicity, reductivity and geometric-radical inputs are proved. -/
def ofCocharacter (hG : IsConnectedReductive G) (ζ : cocharacterLattice T) :
    SemistandardSpectralIndex i where
  parabolic := Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i)
  levi := Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)
  radical := Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i)
  torus_le_levi := (range_le_torusCentralizer i).trans
    (torusCentralizer_le_dynamicCentralizer i (CommGroupScheme.groupHom ζ))
  isParabolicWithLeviAndRadical := Dynamic.isParabolicWithLeviAndRadical_of_structural
    parabolicDynamic dynamicCentralizerReductive dynamicGeometricUnipotentRadical hG _

/-- Equal actual triples give the same index even when the cocharacters differ. -/
theorem ofCocharacter_eq (hG : IsConnectedReductive G) (ζ eta : cocharacterLattice T)
    (hP : Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i))
    (hM : Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i))
    (hU : Dynamic.unipotent (CommGroupScheme.groupHom ζ ≫ i) =
      Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    ofCocharacter (i := i) hG ζ = ofCocharacter hG eta :=
  ext hP hM hU

/-- Positive multiples cannot create additional spectral indices. -/
theorem ofCocharacter_zsmul (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (ζ : cocharacterLattice T) {n : ℤ} (hn : 0 < n) :
    ofCocharacter (i := i) hG (n • ζ) = ofCocharacter hG ζ := by
  let := hG.isAffineHom
  obtain ⟨hP, hM, hU⟩ := relativeRootSignsDetermineDynamic k G hG T i hi (n • ζ) ζ
    (by
      intro α _
      simp only [map_zsmul, smul_eq_mul]
      exact ⟨mul_nonneg_iff_of_pos_left hn,
        by simp only [mul_eq_zero, ne_of_gt hn, false_or],
        mul_pos_iff_of_pos_left hn⟩)
  exact ofCocharacter_eq hG _ _ hP hM hU

section Standard

variable [IsAffineHom G.X.hom] (hG : IsConnectedReductive G)
  (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
  (J : Set (characterLattice T)) (hJ : J ⊆ simpleRelativeRoots i ν)

/-- The existing choice-free standard triple, as an intrinsic semistandard
index. A standard cocharacter is used only to prove its structural property. -/
def ofStandard : SemistandardSpectralIndex i where
  parabolic := standardParabolic i ν J
  levi := standardLevi i ν J
  radical := standardUnipotent i ν J
  torus_le_levi := (range_le_torusCentralizer i).trans (torusCentralizer_le_standardLevi i ν J)
  isParabolicWithLeviAndRadical := by
    obtain ⟨ζ, hζ⟩ := (standardCocharacter k G hG T i hi ν hν J hJ).1
    obtain ⟨hP, hM, hU⟩ := (standardCocharacter k G hG T i hi ν hν J hJ).2 ζ hζ
    rw [hP, hM, hU]
    exact (ofCocharacter (i := i) hG ζ).isParabolicWithLeviAndRadical

@[simp] theorem ofStandard_parabolic : (ofStandard hG hi ν hν J hJ).parabolic =
    standardParabolic i ν J := rfl
@[simp] theorem ofStandard_levi : (ofStandard hG hi ν hν J hJ).levi =
    standardLevi i ν J := rfl
@[simp] theorem ofStandard_radical : (ofStandard hG hi ν hν J hJ).radical =
    standardUnipotent i ν J := rfl

/-- Comparison with every standard cocharacter, on all three actual subgroups. -/
theorem ofStandard_eq_ofCocharacter (ζ : cocharacterLattice T)
    (hζ : IsStandardCocharacter i ν J ζ) :
    ofStandard hG hi ν hν J hJ = ofCocharacter hG ζ := by
  obtain ⟨hP, hM, hU⟩ := (standardCocharacter k G hG T i hi ν hν J hJ).2 ζ hζ
  exact ext hP hM hU

end Standard
end SemistandardSpectralIndex

/-- Indexed semistandard Levis are actual Levi subgroup functors in the image
of the intrinsic index. Presentation witnesses live only in a proposition. -/
abbrev SemistandardSpectralLevi :=
  {M : SubgroupFunctor G // ∃ p : SemistandardSpectralIndex i, p.levi = M}

/-- The actual source fiber `P(M)`, before any Weyl-group quotient. -/
abbrev SemistandardSpectralParabolicFiber (M : SemistandardSpectralLevi i) :=
  {p : SemistandardSpectralIndex i // p.levi = M.val}

/-- Every indexed Levi has an actual parabolic in its fiber, by definition of
the image. This does not assume a finiteness theorem. -/
theorem nonempty_semistandardSpectralParabolicFiber (M : SemistandardSpectralLevi i) :
    Nonempty (SemistandardSpectralParabolicFiber i M) := by
  obtain ⟨p, hp⟩ := M.property
  exact ⟨⟨p, hp⟩⟩

namespace SemistandardSpectralIndex
variable {i}

/-- The actual Levi of an intrinsic index. -/
def toLevi (p : SemistandardSpectralIndex i) : SemistandardSpectralLevi i :=
  ⟨p.levi, p, rfl⟩

/-- The original parabolic belongs to the fiber of its actual Levi. -/
def inFiber (p : SemistandardSpectralIndex i) :
    SemistandardSpectralParabolicFiber i p.toLevi := ⟨p, rfl⟩

end SemistandardSpectralIndex

/-- I.1: every actual parabolic containing `A₀` has a distinguished reductive
Levi containing `A₀`, and a geometric radical, with all-test decomposition. -/
def SemistandardSpectralCoverageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      Function.Surjective (SemistandardSpectralIndex.toParabolic (i := i))

/-- I.1: the Levi containing `A₀` and the geometric radical are uniquely
determined by the actual parabolic. No uniqueness conclusion is a premise. -/
def SemistandardSpectralUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      Function.Injective (SemistandardSpectralIndex.toParabolic (i := i))

/-- Fixed-torus cocharacter coverage, stronger than the source comparison:
every intrinsic triple is a dynamic triple in this very torus. -/
def SemistandardSpectralDynamicCoverageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G), IsMaximalSplitTorus i →
      Function.Surjective (SemistandardSpectralIndex.ofCocharacter (i := i) hG)

/-- Geometric finiteness for the full fixed-torus semistandard index, over
arbitrary fields. This is distinct from discrete-series orbit finiteness. -/
def SemistandardSpectralFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i → Finite (SemistandardSpectralIndex i)

/-- The unquotiented source fibers are finite and nonempty; finiteness is a
conclusion, while nonemptiness also has the elementary proof above. -/
def SemistandardSpectralFiberFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i → ∀ M : SemistandardSpectralLevi i,
        Finite (SemistandardSpectralParabolicFiber i M) ∧
          Nonempty (SemistandardSpectralParabolicFiber i M)

/-- Finiteness of every actual fiber follows from that of the whole index. -/
theorem semistandardSpectralFiberFiniteness_of_finiteness
    (h : SemistandardSpectralFinitenessStatement.{u}) :
    SemistandardSpectralFiberFinitenessStatement.{u} := by
  intro k _ G hG T i hi M
  let := h k G hG T i hi
  exact ⟨inferInstance, nonempty_semistandardSpectralParabolicFiber i M⟩

end Langlands.GroupScheme
