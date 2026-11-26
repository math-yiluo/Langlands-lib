import Langlands.BushnellKutzko.SimpleTypes
import Langlands.BushnellKutzko.SimpleTypeTopology
import Langlands.Representation.Category.Basic

/-! # Simple types in the matrix general linear group -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uρ

variable {F : Type uF} [Field F] {n : ℕ}

local notation "G" => GeneralLinear n F
local notation "A" => Module.End F (Fin n → F)
local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : G ≃* Aut)

/-- The image of a matrix subgroup under the standard identification with `Aut_F(F^n)`. -/
def glSubgroupToAut (J : Subgroup G) : Subgroup Aut :=
  J.map (toAut).toMonoidHom

/-- The standard identification restricted to a matrix subgroup. -/
def glSubgroupToAutEquiv (J : Subgroup G) : J ≃* glSubgroupToAut J :=
  J.equivMapOfInjective (toAut).toMonoidHom (toAut).injective

variable [TopologicalSpace F]

/-- A representation in matrix coordinates, expressed on the corresponding subgroup of
`Aut_F(F^n)`. Composing with the restricted equivalence recovers the original action. -/
def glRepresentationToAut {J : Subgroup G} (ρ : SmoothRep.{0, uF, uρ} ℂ J) :
    Representation ℂ (glSubgroupToAut J) (ρ : Type uρ) :=
  ρ.representation.comp (glSubgroupToAutEquiv J).symm.toMonoidHom

@[simp] theorem glRepresentationToAut_apply {J : Subgroup G}
    (ρ : SmoothRep.{0, uF, uρ} ℂ J) (j : J) :
    glRepresentationToAut ρ (glSubgroupToAutEquiv J j) = ρ.representation j := by
  simp [glRepresentationToAut]

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- A simple type in `GL_n(F)` is a simple type after transport along `toLin`. -/
def IsGLSimpleType {J : Subgroup G} (ψF : AddChar F ℂ) (ρ : SmoothRep.{0, uF, uρ} ℂ J) : Prop :=
  IsSimpleType (V := Fin n → F) (W := (ρ : Type uρ)) ψF (glRepresentationToAut ρ)

/-- A maximal simple type in `GL_n(F)` is a maximal simple type after transport along `toLin`. -/
def IsGLMaximalSimpleType {J : Subgroup G} (ψF : AddChar F ℂ)
    (ρ : SmoothRep.{0, uF, uρ} ℂ J) : Prop :=
  IsMaximalSimpleType (V := Fin n → F) (W := (ρ : Type uρ)) ψF (glRepresentationToAut ρ)

/-- An exhibited simple type in matrix coordinates, with either of the two kinds of data
of BK93 (5.5.10). -/
inductive GLSimpleTypeData (ψF : AddChar F ℂ) {J : Subgroup G}
    (ρ : SmoothRep.{0, uF, uρ} ℂ J) : Type uF
  | positiveDepth (S : Stratum 𝒪[F] F (Fin n → F)) (q : S.DefiningSequenceChoice) (e : ℕ)
      (valid : IsSimpleTypeData (W := (ρ : Type uρ)) ψF S q e (glRepresentationToAut ρ))
  | levelZero (L : LatticeChain 𝒪[F] F (Fin n → F)) (e : ℕ)
      (valid : IsLevelZeroSimpleTypeData (W := (ρ : Type uρ)) L e (glRepresentationToAut ρ))

variable {ψF : AddChar F ℂ} {J : Subgroup (GeneralLinear n F)}
  {ρ : SmoothRep.{0, uF, uρ} ℂ J}

local notation "TypeData" => GLSimpleTypeData (n := n) (J := J) ψF ρ

namespace GLSimpleTypeData

/-- The period of the centralizer order, or the period of the original order at level zero. -/
def period : TypeData → ℕ
  | .positiveDepth _ _ e _ => e
  | .levelZero _ e _ => e

/-- The stratum element, with the level-zero convention `β = 0`. -/
def beta : TypeData → A
  | .positiveDepth S _ _ _ => S.b
  | .levelZero _ _ _ => 0

/-- The parameter field `F[β]`, realized as `F` in the level-zero case. -/
def parameterField : TypeData → Type uF
  | .positiveDepth S _ _ _ => elementAlgebra S.b
  | .levelZero _ _ _ => F

private theorem stratum_isSimple {S : Stratum 𝒪[F] F (Fin n → F)}
    {q : S.DefiningSequenceChoice} {e : ℕ}
    (h : IsSimpleTypeData (W := (ρ : Type uρ)) ψF S q e (glRepresentationToAut ρ)) : S.IsSimple := by
  obtain ⟨_, _, _, hS, _⟩ := h
  exact hS

instance (d : TypeData) : Field d.parameterField := by
  cases d with
  | positiveDepth S q e h =>
    change Field (elementAlgebra S.b)
    exact (stratum_isSimple h).1.1.fst.toField
  | levelZero =>
    change Field F
    infer_instance

instance (d : TypeData) : Algebra F d.parameterField := by
  cases d with
  | positiveDepth S q e h =>
    change Algebra F (elementAlgebra S.b)
    infer_instance
  | levelZero =>
    change Algebra F F
    exact Algebra.id F

/-- The inclusion of `F[β]` in the endomorphism algebra. At level zero it acts by scalars. -/
def fieldEmbedding (d : TypeData) : d.parameterField →ₐ[F] A := by
  cases d with
  | positiveDepth S q e h =>
    change (elementAlgebra S.b) →ₐ[F] A
    exact (elementAlgebra S.b).val
  | levelZero =>
    change F →ₐ[F] A
    exact Algebra.ofId F A

/-- The field ramification index `e(E|F)` for the exhibited data. -/
def ramificationIndex (d : TypeData) : ℕ :=
  subfieldRamificationIndex F d.parameterField

end GLSimpleTypeData

/-- A matrix pair is a simple type precisely when there are data exhibiting it. -/
theorem isGLSimpleType_iff : IsGLSimpleType (n := n) ψF ρ ↔ Nonempty TypeData := by
  constructor
  · rintro (⟨S, q, e, h⟩ | ⟨L, e, h⟩)
    · exact ⟨.positiveDepth S q e h⟩
    · exact ⟨.levelZero L e h⟩
  · rintro ⟨⟨S, q, e, h⟩ | ⟨L, e, h⟩⟩
    · exact Or.inl ⟨S, q, e, h⟩
    · exact Or.inr ⟨L, e, h⟩

/-- A matrix pair is maximal precisely when it is exhibited with period one. -/
theorem isGLMaximalSimpleType_iff :
    IsGLMaximalSimpleType (n := n) ψF ρ ↔ ∃ d : TypeData, d.period = 1 := by
  constructor
  · rintro (⟨S, q, h⟩ | ⟨L, h⟩)
    · exact ⟨.positiveDepth S q 1 h, rfl⟩
    · exact ⟨.levelZero L 1 h, rfl⟩
  · rintro ⟨(⟨S, q, e, h⟩ | ⟨L, e, h⟩), he⟩
    · change e = 1 at he
      subst e
      exact Or.inl ⟨S, q, h⟩
    · change e = 1 at he
      subst e
      exact Or.inr ⟨L, h⟩

private local instance glTypesEndTopology : TopologicalSpace A := moduleTopology F A

private theorem isCompact_isOpen_glSubgroupToAut (d : TypeData) :
    IsCompact (glSubgroupToAut J : Set Aut) ∧ IsOpen (glSubgroupToAut J : Set Aut) := by
  cases d with
  | positiveDepth S q e h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpair⟩ := h
    rw [hpair.choose]
    exact isCompact_isOpen_simpleJ S.chain S.n S.b q.tail
  | levelZero L e h =>
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpair⟩ := h
    rw [hpair.choose]
    exact ⟨isCompact_unitFiltration_zero L, isOpen_unitFiltration L 0⟩

/-- The subgroup of a simple type in matrix coordinates is compact and open. -/
theorem GLSimpleTypeData.isCompact_isOpen (d : TypeData) :
    IsCompact (J : Set G) ∧ IsOpen (J : Set G) := by
  let e := generalLinearToLinContinuous (F := F) (n := n)
  have hJ : (J : Set G) = e ⁻¹' (glSubgroupToAut J : Set Aut) := by
    ext j
    exact (Subgroup.mem_map_iff_mem (toAut).injective).symm
  obtain ⟨hc, ho⟩ := isCompact_isOpen_glSubgroupToAut d
  rw [hJ]
  exact ⟨e.toHomeomorph.isCompact_preimage.mpr hc, ho.preimage e.continuous⟩

/-- The subgroup of an exhibited matrix simple type is open. -/
theorem GLSimpleTypeData.isOpen (d : TypeData) : IsOpen (J : Set G) :=
  d.isCompact_isOpen.2

end Langlands.BushnellKutzko
