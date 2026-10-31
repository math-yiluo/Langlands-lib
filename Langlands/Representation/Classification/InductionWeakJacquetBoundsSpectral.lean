import Langlands.Representation.Exponents.Jacquet
import Langlands.Representation.Filtration.GeneralizedEigencharacterProof
import Langlands.Representation.Exponents.CentralEigencharacterExtensionProof
import Langlands.Representation.Geometric.GeometricLemmaStatement

/-!
# Spectral steps for weak upper Jacquet bounds of induced representations
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uG uM uF uV

namespace Geometric

open GeneralLinear

section CentralSpectrum

variable {F : Type uF} [CommRing F] {n : ℕ} (C : BlockShape n) (R : BlockRefinement C)

/-- Constant block scalars embed as the ambient scalar matrix. -/
theorem leviEmbedding_blockScalarLevi_const {m : ℕ} (D : BlockShape m) (a : Fˣ) :
    D.leviEmbedding F (D.blockScalarLevi F fun _ => a) = GeneralLinear.scalar a := by
  apply Units.ext
  change (D.blockScalar F (fun _ => a) : Matrix (Fin m) (Fin m) F) = _
  rw [D.coe_blockScalar, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

/-- The block scalars of `C` lie in every refined Levi of `C`. -/
def refinedBlockScalar : (Fin C.length → Fˣ) →* refinedLevi F C R :=
  (C.blockScalarLevi F).codRestrict (refinedLevi F C R) fun a => by
    rw [mem_refinedLevi]
    intro i
    exact ⟨(R i).blockScalarLevi F fun _ => a i,
      leviEmbedding_blockScalarLevi_const (R i) (a i)⟩

@[simp] theorem refinedBlockScalar_val (a : Fin C.length → Fˣ) :
    (refinedBlockScalar C R a).val = C.blockScalarLevi F a := rfl

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- On refined normalized induction, the block scalars of `C` act through the
inducing representation, provided the normalizing character is trivial on them.
Evaluation at a point where a generalized eigenfunction does not vanish carries
its generalized eigencharacter to the inducing representation. -/
theorem isGeneralizedEigencharacter_of_normalizedRefinedInducedOf
    (δ : refinedLevi F C R →* ℂˣ) (hδ : ∀ a, δ (refinedBlockScalar C R a) = 1)
    (τ : Representation ℂ (refinedLevi F C R) V) (χ : (Fin C.length → Fˣ) →* ℂˣ)
    (h : IsGeneralizedEigencharacter
      ((normalizedRefinedInducedOf C R δ τ).comp (C.blockScalarLevi F)) χ) :
    IsGeneralizedEigencharacter (τ.comp (refinedBlockScalar C R)) χ := by
  obtain ⟨k, hk⟩ := h
  obtain ⟨f, hf, hf0⟩ := (Submodule.ne_bot_iff _).mp hk
  obtain ⟨x, hx⟩ : ∃ x, Induction.eval _ (refinedInducingRepresentation C R δ τ) f x ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hf0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    exact hall x
  let e : Representation.IntertwiningMap
      ((normalizedRefinedInducedOf C R δ τ).comp (C.blockScalarLevi F))
      (τ.comp (refinedBlockScalar C R)) :=
    { toFun := fun f => Induction.eval _ (refinedInducingRepresentation C R δ τ) f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      isIntertwining' := fun a => by
        refine LinearMap.ext fun f => ?_
        change Induction.eval _ _ (normalizedRefinedInducedOf C R δ τ (C.blockScalarLevi F a) f) x =
          τ (refinedBlockScalar C R a) (Induction.eval _ _ f x)
        rw [normalizedRefinedInducedOf_apply, ← C.blockScalarLevi_commute]
        have hcov := normalizedRefinedInducedOf_covariant C R δ τ f
          (refinedLeviSection F C R (refinedBlockScalar C R a)) x
        rw [refinedLeviSection_val, refinedBlockScalar_val, refinedLeviProjection_section, hδ,
          Units.val_one, one_smul] at hcov
        exact hcov }
  exact isGeneralizedEigencharacter_of_map_ne_zero e χ k hf hx

end Topology

/-- The functor form of the previous theorem. The topological instances are
implicit, so they are read off from the hypothesis rather than synthesized. -/
theorem isGeneralizedEigencharacter_of_normalizedRefinedInductionFunctorOf
    {tF : TopologicalSpace F} {hF : IsTopologicalRing F}
    (δ : refinedLevi F C R →* ℂˣ) (hδ : ∀ a, δ (refinedBlockScalar C R a) = 1)
    (Y : SmoothRep.{0, uF, uV} ℂ (refinedLevi F C R)) (χ : (Fin C.length → Fˣ) →* ℂˣ)
    (h : IsGeneralizedEigencharacter
      (((normalizedRefinedInductionFunctorOf C R δ ⋙ SmoothRep.toRep).obj Y).ρ.comp
        (C.blockScalarLevi F)) χ) :
    IsGeneralizedEigencharacter (Y.representation.comp (refinedBlockScalar C R)) χ :=
  isGeneralizedEigencharacter_of_normalizedRefinedInducedOf C R δ hδ Y.representation χ h

end CentralSpectrum

section EqualityTransport

variable {G : Type uG} [Group G] [TopologicalSpace G] {V : Type uV} [AddCommGroup V]
  [Module ℂ V] {M : Type uM} [Monoid M]

/-- Relabelling along an equality of subgroups pulls generalized
eigencharacters back along the inverse subgroup identification. -/
theorem isGeneralizedEigencharacter_subgroupEqualityFunctor (H K : Subgroup G) (h : H = K)
    (Y : SmoothRep.{0, uG, uV} ℂ H) (ι : M →* K) (χ : M →* ℂˣ) :
    IsGeneralizedEigencharacter
        (((subgroupEqualityFunctor H K h).obj Y).representation.comp ι) χ ↔
      IsGeneralizedEigencharacter
        (Y.representation.comp ((MulEquiv.subgroupCongr h).symm.toMonoidHom.comp ι)) χ := by
  subst h
  rfl

end EqualityTransport

end Geometric

namespace PadicField.TopologicalData

open Geometric GeneralLinear

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData) {n : ℕ}
  (C : BlockShape n) (R : BlockRefinement C)

/-- The inner blocks of a block scalar of `C` are constant block scalars. -/
theorem refinedLeviBlock_refinedBlockScalar (a : Fin C.length → F.Carrierˣ) (i : Fin C.length) :
    refinedLeviBlock C R i (refinedBlockScalar C R a) =
      (R i).blockScalarLevi F.Carrier fun _ => a i := by
  rw [refinedLeviBlock, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
  apply Subtype.ext
  exact (leviEmbedding_blockScalarLevi_const (R i) (a i)).symm

/-- The explicit refined modulus is trivial on the block scalars of `C`. -/
theorem refinedLeviModulus_refinedBlockScalar (a : Fin C.length → F.Carrierˣ) :
    T.refinedLeviModulus C R (refinedBlockScalar C R a) = 1 := by
  rw [refinedLeviModulus_apply]
  apply Finset.prod_eq_one
  intro i _
  rw [refinedLeviBlock_refinedBlockScalar]
  exact T.leviModulus_scalar (R i) (a i)

/-- The positive half modulus is trivial on the block scalars of `C`. -/
theorem refinedLeviHalfModulus_refinedBlockScalar (a : Fin C.length → F.Carrierˣ) :
    T.refinedLeviHalfModulus C R (refinedBlockScalar C R a) = 1 := by
  have h : refinedBlockScalar C R a ∈ (T.refinedLeviHalfModulus C R).ker := by
    rw [refinedLeviHalfModulus_ker]
    exact T.refinedLeviModulus_refinedBlockScalar C R a
  exact h

end PadicField.TopologicalData

end Langlands
