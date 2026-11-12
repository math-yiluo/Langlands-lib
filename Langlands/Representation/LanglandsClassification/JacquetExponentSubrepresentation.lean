import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityProof
import Langlands.Representation.Exponents.JacquetEigenvectorProof
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Category.FiniteIndexRestriction
import Langlands.Representation.Category.Subquotients
import Mathlib.RingTheory.Artinian.Module

/-! # Irreducible subrepresentations carrying an actual Jacquet exponent

Admissibility turns a generalized central character into an ordinary
eigencharacter. An Artinian ambient representation then has a simple
subrepresentation inside its ordinary character space.
-/

noncomputable section

universe uA uG uV

namespace Langlands.Classification

variable {A : Type uA} [CommGroup A] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (ι : A →* G)
  (hι : ∀ t, ι t ∈ Subgroup.center G) (χ : A →* ℂˣ)

/-- The actual subrepresentation where the supplied central group acts by
the specified ordinary scalar character. -/
def scalarCharacterSubrepresentation : Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ t, ρ (ι t) v = (χ t : ℂ) • v}
      zero_mem' := by intro t; simp
      add_mem' := by
        intro v w hv hw t
        rw [map_add, hv t, hw t, smul_add]
      smul_mem' := by
        intro c v hv t
        rw [map_smul, hv t, smul_comm] }
  apply_mem_toSubmodule g v hv t := by
    rw [← Module.End.mul_apply, ← map_mul,
      (Subgroup.mem_center_iff.mp (hι t) g).symm,
      map_mul, Module.End.mul_apply, hv t, map_smul]

@[simp] theorem mem_scalarCharacterSubrepresentation (v : V) :
    v ∈ scalarCharacterSubrepresentation ρ ι hι χ ↔
      ∀ t, ρ (ι t) v = (χ t : ℂ) • v := Iff.rfl

variable [TopologicalSpace G]

/-- An admissible generalized central character has nonzero ordinary
character space. The representation carrier need not be finite dimensional. -/
theorem scalarCharacterSubrepresentation_ne_bot_of_generalized
    (hadm : IsAdmissible ρ)
    (hχ : IsGeneralizedEigencharacter (ρ.comp ι) χ) :
    scalarCharacterSubrepresentation ρ ι hι χ ≠ ⊥ := by
  obtain ⟨n, v, hv, hn⟩ := (isGeneralizedEigencharacter_iff _ _).mp hχ
  obtain ⟨K, hvK⟩ := hadm.1 v
  have : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup) := hadm.2 K
  have hstable (t : A) (w : V) (hw : w ∈ fixedVectors ρ K.toSubgroup) :
      (ρ.comp ι) t w ∈ fixedVectors ρ K.toSubgroup := by
    intro g
    have hwg : ρ (g : G) w = w := hw g
    change ρ g (ρ (ι t) w) = ρ (ι t) w
    rw [← Module.End.mul_apply, ← map_mul,
      Subgroup.mem_center_iff.mp (hι t) g,
      map_mul, Module.End.mul_apply, hwg]
  obtain ⟨w, hw, heig⟩ := exists_eigenvector_of_mem_characterSpace
    (ρ.comp ι) χ n (fixedVectors ρ K.toSubgroup) hstable hv hvK
    ((mem_characterSpace _ χ n v).mpr hn)
  intro hbot
  have hwmem : w ∈ scalarCharacterSubrepresentation ρ ι hι χ := heig
  rw [hbot] at hwmem
  exact hw hwmem

end Langlands.Classification

namespace Langlands.SmoothRep

open _root_.CategoryTheory

variable {A : Type uA} [CommGroup A] {G : Type uG} [Group G] [TopologicalSpace G]
  (B : SmoothRep.{0, uG, uV} ℂ G) (ι : A →* G)
  (hι : ∀ t, ι t ∈ Subgroup.center G) (χ : A →* ℂˣ)

include hι in
/-- An Artinian admissible representation has an irreducible smooth
subrepresentation carrying each of its supplied generalized central characters. -/
theorem exists_irreducible_scalarCharacter_subrepresentation
    (hadm : B.IsAdmissible)
    (hArt : IsArtinian (MonoidAlgebra ℂ G) B.representation.asModule)
    (hχ : IsGeneralizedEigencharacter (B.representation.comp ι) χ) :
    ∃ (τ : SmoothRep.{0, uG, uV} ℂ G), τ.IsIrreducible ∧
      ∃ j : τ ⟶ B, Function.Injective (hom j) ∧
        Classification.HasScalarCharacter τ.representation ι χ := by
  let := hArt
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.representation)
  let : IsAtomic (Subrepresentation B.representation) := e.isAtomic_iff.mpr inferInstance
  let E := Classification.scalarCharacterSubrepresentation B.representation ι hι χ
  have hE : E ≠ ⊥ :=
    Classification.scalarCharacterSubrepresentation_ne_bot_of_generalized
      B.representation ι hι χ hadm hχ
  obtain ⟨S, hS, hSE⟩ := (eq_bot_or_exists_atom_le E).resolve_left hE
  let τ := subrepresentation B S
  have hτ : τ.IsIrreducible :=
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom S hS
  refine ⟨τ, hτ, subtype B S, subtype_injective B S, ?_⟩
  intro t v
  apply Subtype.ext
  exact hSE v.property t

/-- A chosen irreducible smooth subrepresentation with its actual inclusion
and ordinary scalar-character certificate. -/
def irreducibleScalarCharacterSubrepresentation
    (hadm : B.IsAdmissible)
    (hArt : IsArtinian (MonoidAlgebra ℂ G) B.representation.asModule)
    (hχ : IsGeneralizedEigencharacter (B.representation.comp ι) χ) :
    {τ : SmoothRep.{0, uG, uV} ℂ G // τ.IsIrreducible ∧
      ∃ j : τ ⟶ B, Function.Injective (hom j) ∧
        Classification.HasScalarCharacter τ.representation ι χ} :=
  ⟨(exists_irreducible_scalarCharacter_subrepresentation B ι hι χ hadm hArt hχ).choose,
    (exists_irreducible_scalarCharacter_subrepresentation B ι hι χ hadm hArt hχ).choose_spec⟩

end Langlands.SmoothRep

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]
  {G P M U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance scalarSubrepresentationAmbientPointTopology :
    TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
  (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
  (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
  (hmul : IsIso (subgroupMultiplication l r))
  {A : CommGroupScheme (Spec (CommRingCat.of k))} {a : A.toGrp ⟶ M}
  (ha : IsSplitComponent a) (hG : IsConnectedReductive G)
  (π : SmoothRep.{0, u, v} ℂ (rationalPoints G))

include hG in
/-- A supplied actual normalized Jacquet exponent is carried by an
irreducible subrepresentation of the actual Levi Jacquet module.
Admissibility of the source and finite length of that Jacquet module are
explicit; finite-length preservation is not assumed implicitly. -/
theorem exists_irreducible_leviJacquet_subrepresentation_of_exponent
    (hadm : π.IsAdmissible)
    (hfinite : letI := leviPointTopology l hl
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).HasFiniteLength)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    letI := leviPointTopology l hl
    ∃ (τ : SmoothRep.{0, u, v} ℂ (rationalPoints M)), τ.IsIrreducible ∧
      ∃ j : τ ⟶ (leviJacquetFunctor p l r hp hr hl hmul).obj π,
        Function.Injective (SmoothRep.hom j) ∧
          Classification.HasScalarCharacter τ.representation (rationalPoints.map a) χ := by
  let := leviPointTopology l hl
  have hJ := arbitraryParabolicJacquetAdmissibility
    k G hG P M U p l r hp hl hr hmul π hadm
  have hJactual :
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).IsAdmissible :=
    isAdmissible_comp_continuousMulEquiv
      ((jacquetFunctor p l r hp hr hl hmul).obj π).representation
      (leviPointsEquiv p l hp hl) hJ
  have hgen :
      IsGeneralizedEigencharacter
        (((leviJacquetFunctor p l r hp hr hl hmul).obj π).representation.comp
          (rationalPoints.map a)) χ :=
    (isNormalizedJacquetExponent_iff p l r hp hl hr hmul ha π χ).mp hχ
  exact SmoothRep.exists_irreducible_scalarCharacter_subrepresentation
    ((leviJacquetFunctor p l r hp hr hl hmul).obj π) (rationalPoints.map a)
    (fun t => ha.isCentralSplitTorus.isCentral.map_mem_center t) χ hJactual
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfinite).2 hgen

/-- Choose the original-universe irreducible Levi subrepresentation,
retaining the injective actual Jacquet map and the supplied scalar character. -/
def irreducibleLeviJacquetExponentSubrepresentation
    (hadm : π.IsAdmissible)
    (hfinite : letI := leviPointTopology l hl
      ((leviJacquetFunctor p l r hp hr hl hmul).obj π).HasFiniteLength)
    (χ : rationalPoints A.toGrp →* ℂˣ)
    (hχ : IsNormalizedJacquetExponent p l r hp hl hr hmul ha π χ) :
    letI := leviPointTopology l hl
    {τ : SmoothRep.{0, u, v} ℂ (rationalPoints M) // τ.IsIrreducible ∧
      ∃ j : τ ⟶ (leviJacquetFunctor p l r hp hr hl hmul).obj π,
        Function.Injective (SmoothRep.hom j) ∧
          Classification.HasScalarCharacter τ.representation (rationalPoints.map a) χ} := by
  let := leviPointTopology l hl
  let H := exists_irreducible_leviJacquet_subrepresentation_of_exponent
    p l r hp hl hr hmul ha hG π hadm hfinite χ hχ
  exact ⟨H.choose, H.choose_spec⟩

end Langlands.Aubert.General.RepresentedParabolic
