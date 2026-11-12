import Langlands.Representation.Compact.CompactGroupSmoothStatements
import Langlands.Representation.Smooth.IntertwinerFiniteness
import Langlands.Representation.Hecke.CommonInvarianceProof
import Mathlib.RingTheory.SimpleModule.Rank
import Mathlib.Algebra.Module.ULift

/-! # Admissibility detected by compact-group multiplicities -/

noncomputable section
universe u v

namespace Langlands.Renard.CompactRepresentation

section Restriction

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- Admissibility restricts to an open subgroup because its open subgroups are open in the group. -/
theorem isAdmissible_restrict_openSubgroup (π : SmoothRep.{0, u, v} ℂ G)
    (hπ : π.IsAdmissible) (K : OpenSubgroup G) :
    (SmoothRep.restrictSubgroup K.toSubgroup π).IsAdmissible := by
  refine ⟨(SmoothRep.restrictSubgroup K.toSubgroup π).isSmooth, fun U => ?_⟩
  let L : OpenSubgroup G :=
    ⟨U.toSubgroup.map K.toSubgroup.subtype,
      K.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ U.isOpen⟩
  let f : fixedVectors (SmoothRep.restrictSubgroup K.toSubgroup π).representation U.toSubgroup →ₗ[ℂ]
      fixedVectors π.representation L.toSubgroup :=
    { toFun := fun x => ⟨x.val, by
        rintro ⟨g, hg⟩
        obtain ⟨k, hk, rfl⟩ := hg
        exact x.property ⟨k, hk⟩⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let := hπ.2 L
  exact Module.Finite.of_injective f (fun x y h => Subtype.ext (congrArg (fun z : fixedVectors π.representation L.toSubgroup => z.val) h))

end Restriction

section Trivial

variable {K : Type u} [Group K] [TopologicalSpace K]

private abbrev trivialSmoothRep : SmoothRep.{0, u, v} ℂ K :=
  SmoothRep.of (Representation.trivial ℂ K (ULift.{v} ℂ)) (by
    intro x
    exact ⟨⊤, fun _ => rfl⟩)

private theorem trivialSmoothRep_irreducible : (trivialSmoothRep.{u, v} (K := K)).IsIrreducible := by
  have : IsSimpleModule ℂ (ULift.{v} ℂ) := by
    apply isSimpleModule_iff_finrank_eq_one.mpr
    rw [LinearEquiv.finrank_eq (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ)]
    exact Module.finrank_self ℂ
  refine
    { exists_pair_ne := ⟨⊥, ⊤, fun h => bot_ne_top
        (congrArg _root_.Subrepresentation.toSubmodule h)⟩
      eq_bot_or_eq_top := fun S => ?_ }
  rcases eq_bot_or_eq_top S.toSubmodule with hS | hS
  · exact Or.inl (_root_.Subrepresentation.toSubmodule_injective hS)
  · exact Or.inr (_root_.Subrepresentation.toSubmodule_injective hS)

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A fixed vector supplies the equivariant linear map sending the trivial generator to it. -/
private def fixedToTrivialHom (π : SmoothRep.{0, u, v} ℂ G) (K : Subgroup G) :
    fixedVectors π.representation K →ₗ[ℂ]
      (trivialSmoothRep.{u, v} (K := K)).representation.IntertwiningMap
        (SmoothRep.restrictSubgroup K π).representation where
  toFun x :=
    { toLinearMap := (LinearMap.toSpanSingleton ℂ π x.val).comp
        (ULift.moduleEquiv : ULift.{v} ℂ ≃ₗ[ℂ] ℂ).toLinearMap
      isIntertwining' := fun k => by
        ext a
        change a.down • x.val = π.representation k.val (a.down • x.val)
        have hk : π.representation k.val x.val = x.val := x.property k
        rw [map_smul, hk] }
  map_add' x y := by ext a; exact smul_add a.down x.val y.val
  map_smul' c x := by ext a; exact smul_comm a.down c x.val

private theorem fixedToTrivialHom_injective (π : SmoothRep.{0, u, v} ℂ G) (K : Subgroup G) :
    Function.Injective (fixedToTrivialHom π K) := by
  intro x y h
  apply Subtype.ext
  have h' := congrArg (fun f => f (ULift.up (1 : ℂ))) h
  change (1 : ℂ) • x.val = (1 : ℂ) • y.val at h'
  simpa using h'

end Trivial

/-- Renard IV.1.2, Proposition, for the published all-open-subgroups admissibility convention. -/
theorem admissibleFiniteMultiplicity : AdmissibleFiniteMultiplicityStatement.{u, v} := by
  intro G _ _ _ _ _ _ π
  constructor
  · intro hπ K hK σ hσ
    let : σ.representation.IsIrreducible := hσ
    exact finite_intertwiningMap_of_finiteType σ.representation
      (SmoothRep.restrictSubgroup K.toSubgroup π).representation σ.isSmooth inferInstance
      (isAdmissible_restrict_openSubgroup π hπ K)
  · intro hmult
    refine ⟨π.isSmooth, fun L => ?_⟩
    obtain ⟨K, hKL, hK, _⟩ := Hecke.TestFunction.commonCompactOpenBiInvariance G ∅ L
    let := hmult K hK (trivialSmoothRep.{u, v} (K := K.toSubgroup))
      trivialSmoothRep_irreducible
    have hfin : FiniteDimensional ℂ (fixedVectors π.representation K.toSubgroup) :=
      FiniteDimensional.of_injective (fixedToTrivialHom π K.toSubgroup)
        (fixedToTrivialHom_injective π K.toSubgroup)
    let := hfin
    apply Submodule.finiteDimensional_of_le (S₂ := fixedVectors π.representation K.toSubgroup)
    intro x hx k
    exact hx ⟨k.val, hKL k.property⟩

end Langlands.Renard.CompactRepresentation
