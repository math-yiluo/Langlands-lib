import Langlands.Representation.Geometric.RepresentedGeometricLemmaRadicalLift
import Langlands.Representation.Geometric.RepresentedGeometricLemmaSourceJacquet

/-! # Actual source-radical and stabilizer coefficient quotients -/

noncomputable section

universe u v

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

private def quotientFromTwistPullback {G₀ H₀ V₀ : Type*}
    [Group G₀] [Group H₀] [AddCommGroup V₀] [Module ℂ V₀]
    (ρ : Representation ℂ G₀ V₀) (χ₀ : G₀ →* ℂˣ) (f : H₀ →* G₀)
    (N₀ : Subgroup H₀) (R₀ : Subgroup G₀)
    (himage₀ : Subgroup.map f N₀ ≤ R₀)
    (hχ₀ : ∀ g ∈ R₀, χ₀ g = 1) :
    Jacquet.Coinvariants ((Langlands.twist χ₀ ρ).comp f) N₀ →ₗ[ℂ]
      Jacquet.Localization.Coinvariants ρ R₀ 1 := by
  refine Jacquet.lift _ N₀ (Jacquet.Localization.mk ρ R₀ 1) ?_
  intro n
  apply LinearMap.ext
  intro a
  have hn : f (n : H₀) ∈ R₀ :=
    himage₀ (Subgroup.mem_map.mpr ⟨(n : H₀), n.property, rfl⟩)
  change Jacquet.Localization.mk ρ R₀ 1
    ((χ₀ (f n) : ℂ) • ρ (f n) a) = Jacquet.Localization.mk ρ R₀ 1 a
  rw [hχ₀ (f n) hn, Units.val_one, one_smul]
  have hrel := Jacquet.Localization.mk_apply_subgroup ρ R₀ 1 ⟨f n, hn⟩ a
  simp only [MonoidHom.one_apply, Units.val_one, one_smul] at hrel
  exact hrel

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance rawQuotientAmbientPointTopology : TopologicalSpace (rationalPoints G) :=
  RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  {P M N Q L U : GroupScheme (Spec (CommRingCat.of k))}
  {p : P ⟶ G} {l : M ⟶ P} {r : N ⟶ P}
  {hp : IsParabolicSubgroup p} {hr : LeviSubgroup.IsGeometricUnipotentRadical r}
  {hl : IsRationalLeviSubgroup l} {hmul : IsIso (subgroupMultiplication l r)}
  {q : Q ⟶ G} {lQ : L ⟶ Q} {rQ : U ⟶ Q}
  {hq : IsParabolicSubgroup q} {hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ}
  {hlQ : IsRationalLeviSubgroup lQ} {hmulQ : IsIso (subgroupMultiplication lQ rQ)}
  {z : rationalPoints G}

namespace GeometricLemmaIntersectionDatum

variable (D : GeometricLemmaIntersectionDatum p l r hp hr hl hmul
  q lQ rQ hq hrQ hlQ hmulQ z)

local notation "H" => Geometric.orbitStabilizer (pointImage p) (pointImage q) z⁻¹
local notation "dQ" =>
  isSemidirectDecomposition_pointImage q lQ rQ hq.isClosedSubgroup hrQ hmulQ
local notation "NQH" => Subgroup.comap (Subgroup.subtype H)
  (MonoidHom.ker (IsSemidirectDecomposition.projection dQ))
local notation "fH" => stabilizerToLeviPoints p l r hp hr hl hmul q z
local notation "R" => pointImage (D.r' ≫ D.p')
local notation "χ" => leviInducingHalfCharacter p l r hp hr hl

/-- The source-radical quotient maps onto the actual full-stabilizer
coefficient quotient, keeping the class of each original vector. -/
def sourceRadicalQuotientToStabilizerCoinvariants
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    Jacquet.Localization.Coinvariants A.representation R 1 →ₗ[ℂ]
      Jacquet.Coinvariants
        ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH := by
  letI := leviPointTopology l hl
  refine Jacquet.Localization.lift A.representation R 1 (Jacquet.mk ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH) ?_
  intro m a
  have hχ : (χ).toMonoidHom (m : rationalPoints M) = 1 :=
    D.sourceRadical_le_ker_inducingHalfCharacter m.property
  have haction : ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ (D.sourceRadicalToStabilizer m) a =
      A.representation (m : rationalPoints M) a := by
    change ((χ).toMonoidHom (fH (D.sourceRadicalToStabilizer m)) : ℂ) •
      A.representation (fH (D.sourceRadicalToStabilizer m)) a = _
    rw [D.stabilizerToLeviPoints_sourceRadicalToStabilizer, hχ]
    simp only [Units.val_one, one_smul]
  have hrel := Jacquet.mk_apply_subgroup ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH
    ⟨D.sourceRadicalToStabilizer m, D.sourceRadicalToStabilizer_mem_kernel m⟩ a
  change Jacquet.mk ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH (((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ (D.sourceRadicalToStabilizer m) a) =
    Jacquet.mk ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH a at hrel
  rw [haction] at hrel
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  exact hrel

@[simp]
theorem sourceRadicalQuotientToStabilizerCoinvariants_mk
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) (a : A) :
    letI := leviPointTopology l hl
    D.sourceRadicalQuotientToStabilizerCoinvariants A
        (Jacquet.Localization.mk A.representation R 1 a) =
      Jacquet.mk
        ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH a := rfl

/-- No reverse image inclusion is needed for surjectivity. -/
theorem sourceRadicalQuotientToStabilizerCoinvariants_surjective
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    Function.Surjective (D.sourceRadicalQuotientToStabilizerCoinvariants A) := by
  let := leviPointTopology l hl
  intro x
  obtain ⟨a, rfl⟩ := Jacquet.mk_surjective
    ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH x
  exact ⟨Jacquet.Localization.mk A.representation R 1 a, rfl⟩

/-- The canonical surjection commutes with every original coefficient map. -/
theorem sourceRadicalQuotientToStabilizerCoinvariants_natural
    {A B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (T : A ⟶ B)
    (x : letI := leviPointTopology l hl
      Jacquet.Localization.Coinvariants A.representation R 1) :
    letI := leviPointTopology l hl
    D.sourceRadicalQuotientToStabilizerCoinvariants B
        (Jacquet.Localization.mapLinear R 1 (SmoothRep.hom T) x) =
      Representation.Coinvariants.map _ _
        (Jacquet.restrictMap
          (((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).map T).hom) NQH)
        (D.sourceRadicalQuotientToStabilizerCoinvariants A x) := by
  let := leviPointTopology l hl
  obtain ⟨a, rfl⟩ := Jacquet.Localization.mk_surjective A.representation R 1 x
  rfl

/-- The reverse image inclusion gives the quotient map in the other direction.
It is an explicit intermediate geometric input. -/
def stabilizerCoinvariantsToSourceRadicalQuotient
    (himage : Subgroup.map fH NQH ≤ R)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    Jacquet.Coinvariants
        ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH →ₗ[ℂ]
      Jacquet.Localization.Coinvariants A.representation R 1 := by
  letI := leviPointTopology l hl
  exact quotientFromTwistPullback A.representation (χ).toMonoidHom fH NQH R
    himage (fun _ hg => D.sourceRadical_le_ker_inducingHalfCharacter hg)

@[simp]
theorem stabilizerCoinvariantsToSourceRadicalQuotient_mk
    (himage : Subgroup.map fH NQH ≤ R)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) (a : A) :
    letI := leviPointTopology l hl
    D.stabilizerCoinvariantsToSourceRadicalQuotient himage A
        (Jacquet.mk
          ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH a) =
      Jacquet.Localization.mk A.representation R 1 a := rfl

/-- With the reverse inclusion, the two actual coefficient quotients are
linearly equivalent by the identity on original representatives. -/
def stabilizerCoinvariantsSourceEquiv
    (himage : Subgroup.map fH NQH ≤ R)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) :
    letI := leviPointTopology l hl
    Jacquet.Coinvariants
        ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH ≃ₗ[ℂ]
      Jacquet.Localization.Coinvariants A.representation R 1 := by
  letI := leviPointTopology l hl
  exact LinearEquiv.ofLinearMap (D.stabilizerCoinvariantsToSourceRadicalQuotient himage A)
    (D.sourceRadicalQuotientToStabilizerCoinvariants A)
    (by
      apply Jacquet.Localization.hom_ext
      ext a
      rfl)
    (by
      apply Representation.Coinvariants.hom_ext
      ext a
      rfl)

@[simp]
theorem stabilizerCoinvariantsSourceEquiv_mk
    (himage : Subgroup.map fH NQH ≤ R)
    (A : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)) (a : A) :
    letI := leviPointTopology l hl
    D.stabilizerCoinvariantsSourceEquiv himage A
        (Jacquet.mk
          ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH a) =
      Jacquet.Localization.mk A.representation R 1 a := rfl

/-- The quotient equivalence is natural in all smooth coefficient objects. -/
theorem stabilizerCoinvariantsSourceEquiv_natural
    (himage : Subgroup.map fH NQH ≤ R)
    {A B : letI := leviPointTopology l hl; SmoothRep.{0, u, v} ℂ (rationalPoints M)}
    (T : A ⟶ B)
    (x : letI := leviPointTopology l hl
      Jacquet.Coinvariants
      ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH) :
    letI := leviPointTopology l hl
    D.stabilizerCoinvariantsSourceEquiv himage B
        (Representation.Coinvariants.map _ _
          (Jacquet.restrictMap
            (((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).map T).hom)
            NQH) x) =
      Jacquet.Localization.mapLinear R 1 (SmoothRep.hom T)
        (D.stabilizerCoinvariantsSourceEquiv himage A x) := by
  let := leviPointTopology l hl
  obtain ⟨a, rfl⟩ := Jacquet.mk_surjective
    ((stabilizerTwistedCoefficientFunctor p l r hp hr hl hmul q z).obj A).ρ NQH x
  rfl

end GeometricLemmaIntersectionDatum

end Langlands.Aubert.General.RepresentedParabolic
