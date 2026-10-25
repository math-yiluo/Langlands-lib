import Langlands.Automorphic.CuspidalOperatorRealization
import Langlands.Global.CMConjugationGL
import Langlands.Representation.Dual.Definitions
import Langlands.Representation.FiniteVectors
import Langlands.Representation.Smooth.Transfer.SubquotientProof

/-!
# Realizations isomorphic to their conjugate contragredient

For a CM field `E` with CM involution `c`, an actual automorphic realization `π` of
`GL_n(𝔸_E)` is isomorphic to `π̌ ∘ c` when a linear bijection `T` from `π` onto the
contragredient functionals intertwines `π(g)` with `π̌(c g)`. Writing
`B y x = T x y`, this is a bilinear pairing invariant under the conjugate-twisted
finite, compact and Lie algebra operators whose partial map `x ↦ B (·) x` is a
bijection onto the contragredient functionals. Contragredient functionals are the
algebraic functionals that are smooth for the finite adelic group and finite for the
standard compact subgroup at infinity.
-/

noncomputable section

universe u

namespace Langlands.Automorphic

open NumberField Langlands.Global Langlands.Global.CMConjugation

variable {E : Type u} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

local instance conjugateContragredientRationalAddCommGroup :
    AddCommGroup (RationalInvariantFunctions E n) := Submodule.addCommGroup _
local instance conjugateContragredientContinuousAddCommGroup :
    AddCommGroup (ContinuousRationalFunctions E n) := Submodule.addCommGroup _
local instance conjugateContragredientSmoothAddCommGroup :
    AddCommGroup (FiniteSmoothRationalFunctions E n) := Submodule.addCommGroup _
local instance conjugateContragredientFormsAddCommGroup :
    AddCommGroup (AutomorphicForms E n) := Submodule.addCommGroup _
local instance conjugateContragredientStableAddCommGroup :
    AddCommGroup (StableAutomorphicFunctions E n) := Submodule.addCommGroup _

namespace OperatorRealization

variable (S T : OperatorRealization E n)

local instance conjugateContragredientSpaceAddCommGroup : AddCommGroup S.Space :=
  Submodule.addCommGroup _
local instance conjugateContragredientSpaceAddCommGroup' : AddCommGroup T.Space :=
  Submodule.addCommGroup _

/-- A real Lie algebra element acts through its complexification in the genuine
differential action. -/
def lieAction (X : ArchimedeanGL.RealLieAlgebra E n) : Module.End ℂ S.Space :=
  S.envelopingAction (ArchimedeanGL.envelopingGenerator E n (ArchimedeanGL.complexify E n X))

/-- Contragredient functionals: algebraic functionals that are smooth for the finite
adelic group and finite for the standard compact subgroup at infinity. -/
def IsContragredientFunctional (l : Module.Dual ℂ S.Space) : Prop :=
  IsSmoothVector S.finiteRepresentation.dual l ∧
    FiniteVectors.IsFiniteVector S.compactRepresentation.dual l

/-- Invariance of a pairing under the operators twisted by the CM involution in the
first variable. -/
def IsConjugateInvariantPairing (B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ) : Prop :=
  (∀ (d : FiniteAdelicGL E n) (y x : S.Space),
      B (S.finiteRepresentation (finiteConj E n d) y) (S.finiteRepresentation d x) = B y x) ∧
    (∀ (k : standardInfiniteCompact E n) (y x : S.Space),
      B (S.compactRepresentation (compactConj E n k) y) (S.compactRepresentation k x) =
        B y x) ∧
    ∀ (X : ArchimedeanGL.RealLieAlgebra E n) (y x : S.Space),
      B (S.lieAction (lieConj E n X) y) x + B y (S.lieAction X x) = 0

/-- The partial map `x ↦ B (·) x` is an isomorphism `π → π̌ ∘ c` onto the
contragredient functionals. -/
def IsConjugateContragredientPairing (B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ) : Prop :=
  S.IsConjugateInvariantPairing B ∧
    (∀ x : S.Space, S.IsContragredientFunctional (B.flip x)) ∧
    Function.Injective B.flip ∧
    ∀ l : Module.Dual ℂ S.Space, S.IsContragredientFunctional l → ∃ x, B.flip x = l

/-- The realization is isomorphic to its contragredient composed with the CM
involution. -/
def IsConjugateSelfDual : Prop :=
  ∃ B : S.Space →ₗ[ℂ] S.Space →ₗ[ℂ] ℂ, S.IsConjugateContragredientPairing B

variable {S T}

/-- The same linear map intertwines the restricted compact actions. -/
private def compactRestriction (L : S.Intertwiner T) :
    S.compactRepresentation.IntertwiningMap T.compactRepresentation where
  toLinearMap := L.toLinearMap
  isIntertwining' k := L.isIntertwining' (compactOperator E n k)

omit [IsCMField E] in
/-- Contragredient functionals pull back along full-operator intertwiners. -/
private theorem isContragredientFunctional_comp (L : S.Intertwiner T)
    {l : Module.Dual ℂ T.Space} (hl : T.IsContragredientFunctional l) :
    S.IsContragredientFunctional (l.comp L.toLinearMap) :=
  ⟨isSmoothVector_map (dualIntertwining (Intertwiner.finiteRestriction L)) hl.1,
    hl.2.map (dualIntertwining (compactRestriction L))⟩

/-- Conjugate self-duality is transported along mutually inverse intertwiners. -/
private theorem isConjugateSelfDual_of_inverse (L : S.Intertwiner T) (M : T.Intertwiner S)
    (hML : ∀ x, M (L x) = x) (hLM : ∀ y, L (M y) = y)
    (hS : S.IsConjugateSelfDual) : T.IsConjugateSelfDual := by
  obtain ⟨B, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := hS
  refine ⟨B.compl₁₂ M.toLinearMap M.toLinearMap, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    change B (M (T.finiteRepresentation (finiteConj E n d) y))
      (M (T.finiteRepresentation d x)) = B (M y) (M x)
    exact (congrArg₂ (fun a b => B a b) (Intertwiner.finite M _ y)
      (Intertwiner.finite M d x)).trans (hd d (M y) (M x))
  · intro k y x
    change B (M (T.compactRepresentation (compactConj E n k) y))
      (M (T.compactRepresentation k x)) = B (M y) (M x)
    exact (congrArg₂ (fun a b => B a b) (Intertwiner.compact M _ y)
      (Intertwiner.compact M k x)).trans (hk k (M y) (M x))
  · intro X y x
    change B (M (T.lieAction (lieConj E n X) y)) (M x) + B (M y) (M (T.lieAction X x)) = 0
    have h₁ : M (T.lieAction (lieConj E n X) y) = S.lieAction (lieConj E n X) (M y) :=
      Intertwiner.differential M _ y
    have h₂ : M (T.lieAction X x) = S.lieAction X (M x) := Intertwiner.differential M _ x
    exact (congrArg₂ (fun a b => B a (M x) + B (M y) b) h₁ h₂).trans (hX X (M y) (M x))
  · intro x
    exact isContragredientFunctional_comp M (hB (M x))
  · intro x₁ x₂ h
    have h' : B.flip (M x₁) = B.flip (M x₂) := by
      apply LinearMap.ext
      intro y
      have h₀ := LinearMap.congr_fun h (L y)
      change B (M (L y)) (M x₁) = B (M (L y)) (M x₂) at h₀
      change B y (M x₁) = B y (M x₂)
      exact (congrArg (fun z => B z (M x₁)) (hML y)).symm.trans
        (h₀.trans (congrArg (fun z => B z (M x₂)) (hML y)))
    exact (hLM x₁).symm.trans ((congrArg L (hinj h')).trans (hLM x₂))
  · intro l hl
    obtain ⟨x, hx⟩ :=
      hsurj (l.comp L.toLinearMap) (isContragredientFunctional_comp L hl)
    refine ⟨L x, ?_⟩
    apply LinearMap.ext
    intro y
    have h₀ := LinearMap.congr_fun hx (M y)
    change B (M y) x = l (L (M y)) at h₀
    change B (M y) (M (L x)) = l y
    exact (congrArg (fun z => B (M y) z) (hML x)).trans (h₀.trans (congrArg l (hLM y)))

/-- Conjugate self-duality is transported along full-operator equivalences. -/
theorem IsConjugateSelfDual.of_equivalence (e : S.Equivalence T)
    (hS : S.IsConjugateSelfDual) : T.IsConjugateSelfDual :=
  isConjugateSelfDual_of_inverse e.toIntertwiningMap e.symm.toIntertwiningMap
    (fun x => e.symm_apply_apply x) (fun y => e.apply_symm_apply y) hS

/-- Conjugate self-duality is invariant under full-operator equivalence. -/
theorem isConjugateSelfDual_iff_of_equivalence (e : S.Equivalence T) :
    S.IsConjugateSelfDual ↔ T.IsConjugateSelfDual :=
  ⟨IsConjugateSelfDual.of_equivalence e, IsConjugateSelfDual.of_equivalence e.symm⟩

/-- A full-operator class is conjugate self-dual when some representative is. -/
def IsoClass.IsConjugateSelfDual (c : IsoClass E n) : Prop :=
  ∃ S : OperatorRealization E n, S.isoClass = c ∧ S.IsConjugateSelfDual

/-- For a class, one representative is conjugate self-dual exactly when every
representative is. -/
theorem isoClass_isConjugateSelfDual_iff (S : OperatorRealization E n) :
    S.isoClass.IsConjugateSelfDual ↔ S.IsConjugateSelfDual := by
  constructor
  · rintro ⟨T, hT, hTS⟩
    obtain ⟨e⟩ := (T.isoClass_eq_iff S).mp hT
    exact hTS.of_equivalence e
  · intro h
    exact ⟨S, rfl, h⟩

end OperatorRealization

namespace CuspidalOperatorRealization

variable [CompactSpace (AdeleQuotient E)] {r : ℕ}

/-- An irreducible cuspidal class is conjugate self-dual when its full-operator class
is. -/
def IsoClass.IsConjugateSelfDual (c : IsoClass E r) : Prop :=
  c.toOperatorClass.IsConjugateSelfDual

theorem isoClass_isConjugateSelfDual_iff (S : CuspidalOperatorRealization E r) :
    S.isoClass.IsConjugateSelfDual ↔ S.realization.IsConjugateSelfDual :=
  S.realization.isoClass_isConjugateSelfDual_iff

end CuspidalOperatorRealization

end Langlands.Automorphic
