import Langlands.AlgebraicGeometry.LocallyFreeRankIso
import Langlands.Shimura.PEL.HarrisTaylorLieTensorNaturality

/-! # The positive Lie rank and scalar compatibility condition -/

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

private theorem scalarHom_id_naturality {S : AlgebraicGeometry.Scheme.{0}}
    {M N : S.Modules} (r : Γ(S, ⊤)) (f : M ⟶ N) :
    scalarHom r (𝟙 M) ≫ f = f ≫ scalarHom r (𝟙 N) := by
  change (r • (𝟙 M : M ⟶ M)) ≫ f = f ≫ (r • (𝟙 N : N ⟶ N))
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

private theorem eq_scalar_iff_of_iso {S : AlgebraicGeometry.Scheme.{0}}
    {M N : S.Modules} (e : M ≅ N) (α : End M) (β : End N)
    (h : α ≫ e.hom = e.hom ≫ β) (r : Γ(S, ⊤)) :
    α = scalarHom r (𝟙 M) ↔ β = scalarHom r (𝟙 N) := by
  have hr := scalarHom_id_naturality r e.hom
  constructor
  · intro hα
    apply (cancel_epi e.hom).mp
    rw [← h, hα, hr]
  · intro hβ
    apply (cancel_mono e.hom).mp
    rw [h, hβ, ← hr]

variable (L : Type) [Field L] [NumberField L] [IsCMField L]
  [IsQuadraticExtension ℚ L]
  {K : Type} [Field K] [NumberField K] [Algebra L K]
  (E : Type) [Field E] [Algebra E K]
  {S : AlgebraicGeometry.Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of K))
  {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]
  (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

/-- On the positive tensor factor the central `E` action equals the structural scalar action. -/
def PositiveLieScalarCondition : Prop :=
  ∀ a : E, lieTensorAction L s B i false (algebraMap K A (algebraMap E K a)) =
    scalarHom (secHom s ⊤ (algebraMap E K a)) (𝟙 (lieTensorSheaf L s B i false))

/-- The source compatibility condition, using its actual original-order positive tensor sheaf. -/
def LieCompatibility (n : ℕ) : Prop :=
  IsLocallyFreeOfRank (lieTensorSheaf L s B i false) n ∧
    PositiveLieScalarCondition L E s B i

/-- The same scalar condition on the constructed full positive Lie eigensubsheaf. -/
def PositiveLieEigenScalarCondition : Prop :=
  ∀ a : E, lieEigensheafAction L s B i false (algebraMap K A (algebraMap E K a)) =
    scalarHom (secHom s ⊤ (algebraMap E K a)) (𝟙 (lieEigensheaf L s B i false))

/-- The eigensubsheaf version of the rank and scalar compatibility condition. -/
def EigenLieCompatibility (n : ℕ) : Prop :=
  IsLocallyFreeOfRank (lieEigensheaf L s B i false) n ∧
    PositiveLieEigenScalarCondition L E s B i

/-- The constructed tensor comparison identifies the two scalar conditions. -/
theorem positiveLieScalarCondition_iff_eigensheaf :
    PositiveLieScalarCondition L E s B i ↔ PositiveLieEigenScalarCondition L E s B i := by
  unfold PositiveLieScalarCondition PositiveLieEigenScalarCondition
  exact forall_congr' fun a =>
    eq_scalar_iff_of_iso (lieTensorSheafIso L s B i false) _ _
      (lieTensorAction_comparison L s B i false (algebraMap K A (algebraMap E K a))) _

/-- The constructed comparison identifies the actual tensor and eigensubsheaf conditions. -/
theorem lieCompatibility_iff_eigensheaf (n : ℕ) :
    LieCompatibility L E s B i n ↔ EigenLieCompatibility L E s B i n :=
  and_congr (isLocallyFreeOfRank_iff_of_iso (lieTensorSheafIso L s B i false) n)
    (positiveLieScalarCondition_iff_eigensheaf L E s B i)

variable {B} {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
  (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
  (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a))

include e he in
/-- Actual equivariant rational isomorphisms preserve equality of the two central actions. -/
theorem positiveLieScalarCondition_iso :
    PositiveLieScalarCondition L E s B i ↔ PositiveLieScalarCondition L E s B' i' := by
  unfold PositiveLieScalarCondition
  apply forall_congr'
  intro a
  apply eq_scalar_iff_of_iso (lieTensorIso L s i i' false e he)
  simpa only [lieTensorIso_hom] using
    lieTensorMap_intertwines L s i i' e.hom he false (algebraMap K A (algebraMap E K a))

include e he in
/-- The full positive Lie compatibility condition is invariant under actual rational action iso. -/
theorem lieCompatibility_iso (n : ℕ) :
    LieCompatibility L E s B i n ↔ LieCompatibility L E s B' i' n :=
  and_congr (isLocallyFreeOfRank_iff_of_iso (lieTensorIso L s i i' false e he) n)
    (positiveLieScalarCondition_iso L E s i i' e he)

end Langlands.Shimura.HarrisTaylor
