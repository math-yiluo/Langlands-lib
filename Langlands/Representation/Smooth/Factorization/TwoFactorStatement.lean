import Langlands.Representation.Smooth.Definitions
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Two-factor decomposition of admissible smooth complex representations

These proposition definitions express Flath's Theorem 1 and its fixed-vector
prerequisite. The external tensor representation is built from Mathlib's
projection homomorphisms and `Representation.tprod`; no representation or
factorization is postulated as data.
-/

namespace Langlands

universe uG₁ uG₂ uV₁ uV₂ uW₁ uW₂ uV

/-- The canonical tensor of fixed-subspace inclusions is injective and has
image exactly the fixed space for the product subgroup. -/
def ProductFixedVectorsStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    (V₁ : Type uV₁) (V₂ : Type uV₂)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂)
    (K₁ : Subgroup G₁) (K₂ : Subgroup G₂),
    let ρ := Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂))
      (ρ₂.comp (MonoidHom.snd G₁ G₂))
    let inclusion := TensorProduct.map
      (fixedVectors ρ₁ K₁).subtype (fixedVectors ρ₂ K₂).subtype
    Function.Injective inclusion ∧
      LinearMap.range inclusion = fixedVectors ρ (K₁.prod K₂)

/-- External tensor products preserve admissibility, and preserve
irreducibility when both admissible factors are irreducible. -/
def AdmissibleExternalTensorStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    (V₁ : Type uV₁) (V₂ : Type uV₂)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂),
    IsAdmissible ρ₁ → IsAdmissible ρ₂ →
    let ρ := Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂))
      (ρ₂.comp (MonoidHom.snd G₁ G₂))
    IsAdmissible ρ ∧
      (ρ₁.IsIrreducible → ρ₂.IsIrreducible → ρ.IsIrreducible)

/-- Every admissible irreducible representation of a product of two locally
profinite groups is an external tensor of admissible irreducible factors.
The existential module carriers can be taken in the universe of the original
representation space. -/
def AdmissibleProductFactorizationStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V),
    IsAdmissible ρ → ρ.IsIrreducible →
    ∃ (V₁ V₂ : ModuleCat.{uV} ℂ)
      (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂),
      IsAdmissible ρ₁ ∧ ρ₁.IsIrreducible ∧
      IsAdmissible ρ₂ ∧ ρ₂.IsIrreducible ∧
      Nonempty (ρ.Equiv (Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂))
        (ρ₂.comp (MonoidHom.snd G₁ G₂))))

/-- Equivalence of external tensors of admissible irreducible factors
determines the equivalence class of each factor separately. -/
def AdmissibleProductFactorUniquenessStatement : Prop :=
  ∀ (G₁ : Type uG₁) (G₂ : Type uG₂) [Group G₁] [Group G₂]
    [TopologicalSpace G₁] [TopologicalSpace G₂]
    [IsTopologicalGroup G₁] [IsTopologicalGroup G₂]
    [T2Space G₁] [T2Space G₂]
    [LocallyCompactSpace G₁] [LocallyCompactSpace G₂]
    [TotallyDisconnectedSpace G₁] [TotallyDisconnectedSpace G₂]
    (V₁ : Type uV₁) (V₂ : Type uV₂)
    (W₁ : Type uW₁) (W₂ : Type uW₂)
    [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂]
    (ρ₁ : Representation ℂ G₁ V₁) (ρ₂ : Representation ℂ G₂ V₂)
    (σ₁ : Representation ℂ G₁ W₁) (σ₂ : Representation ℂ G₂ W₂),
    IsAdmissible ρ₁ → ρ₁.IsIrreducible →
    IsAdmissible ρ₂ → ρ₂.IsIrreducible →
    IsAdmissible σ₁ → σ₁.IsIrreducible →
    IsAdmissible σ₂ → σ₂.IsIrreducible →
    Nonempty ((Representation.tprod (ρ₁.comp (MonoidHom.fst G₁ G₂))
      (ρ₂.comp (MonoidHom.snd G₁ G₂))).Equiv
      (Representation.tprod (σ₁.comp (MonoidHom.fst G₁ G₂))
        (σ₂.comp (MonoidHom.snd G₁ G₂)))) →
    Nonempty (ρ₁.Equiv σ₁) ∧ Nonempty (ρ₂.Equiv σ₂)

/-- Fixed vectors, tensor admissibility and irreducibility, and existence
and uniqueness of two-factor decompositions, over independent universes. -/
def FlathTwoFactorStatement : Prop :=
  ProductFixedVectorsStatement.{uG₁, uG₂, uV₁, uV₂} ∧
  AdmissibleExternalTensorStatement.{uG₁, uG₂, uV₁, uV₂} ∧
  AdmissibleProductFactorizationStatement.{uG₁, uG₂, uV} ∧
  AdmissibleProductFactorUniquenessStatement.{uG₁, uG₂, uV₁, uV₂, uW₁, uW₂}

end Langlands
