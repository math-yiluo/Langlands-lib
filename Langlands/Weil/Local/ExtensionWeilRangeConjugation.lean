import Langlands.Weil.Local.AssemblyProof
import Langlands.Weil.Local.ExtensionWeilRange

/-!
# Conjugating the image of a local Weil map

For an embedding `f : F → E` of p-adic fields, the image of `W_E` in `W_F` is the
inverse image of the fixing subgroup of the chosen image of `E` in `\bar F`. Any other
`F`-embedding `ψ : E → \bar F` differs from the chosen one by an automorphism of
`\bar F`, and since `W_F` is dense in `G_F`, an element `g` of `W_F` already moves
the chosen image onto the image of `ψ`. Conjugation by `g` therefore carries the
image of `W_E` onto the subgroup of `W_F` fixing the image of `ψ`.
-/

noncomputable section

namespace Langlands.Weil.Local

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- Every embedding `ψ : E → \bar F` over `F` is the chosen embedding followed by an
element of the absolute Galois group of `F`. -/
theorem exists_galois_comp_extensionFieldEmbedding
    (ψ : E.Carrier →+* AlgebraicClosure F.Carrier)
    (hψ : ∀ x, ψ (f x) = algebraMap F.Carrier _ x) :
    ∃ σ : Gal(AlgebraicClosure F.Carrier/F.Carrier), ∀ x : E.Carrier,
      σ (extensionFieldEmbedding F E f x) = ψ x := by
  let := extensionAlgebra F E f
  let : Algebra E.Carrier (AlgebraicClosure F.Carrier) := (extensionFieldEmbedding F E f).toAlgebra
  have : IsScalarTower F.Carrier E.Carrier (AlgebraicClosure F.Carrier) :=
    IsScalarTower.of_algebraMap_eq fun x => (extensionFieldEmbedding_comp F E f x).symm
  let χ : E.Carrier →ₐ[F.Carrier] AlgebraicClosure F.Carrier :=
    { toRingHom := ψ
      commutes' := hψ }
  let σ₀ := χ.liftNormal (AlgebraicClosure F.Carrier)
  refine ⟨AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀), fun x => ?_⟩
  exact χ.liftNormal_commutes (AlgebraicClosure F.Carrier) x

/-- If a subgroup `H` of `W_F` consists of the elements whose Galois projection fixes
the image of an embedding `ψ : E → \bar F` over `F`, then some `g ∈ W_F` conjugates the
image of `W_E` onto `H`. -/
theorem exists_conj_mem_iff_extensionWeilRange
    (ψ : E.Carrier →+* AlgebraicClosure F.Carrier)
    (hψ : ∀ x, ψ (f x) = algebraMap F.Carrier _ x)
    (H : Subgroup (localWeilGroup F))
    (hH : ∀ y : localWeilGroup F, y ∈ H ↔ ∀ x : E.Carrier,
      AlgEquiv.toAlgHom (localProjection F y) (ψ x) = ψ x) :
    ∃ g : localWeilGroup F, ∀ y : localWeilGroup F,
      y ∈ extensionWeilRange F E f ↔ g * y * g⁻¹ ∈ H := by
  obtain ⟨σ, hσ⟩ := exists_galois_comp_extensionFieldEmbedding F E f ψ hψ
  let J := extensionIntermediateField F E f
  have hJ (x : E.Carrier) : extensionFieldEmbedding F E f x ∈ J :=
    (mem_extensionIntermediateField F E f _).mpr ⟨x, rfl⟩
  -- The Galois elements agreeing with `σ` on the chosen image form an open set.
  let S : Set Gal(AlgebraicClosure F.Carrier/F.Carrier) :=
    (fun τ => σ⁻¹ * τ) ⁻¹' (J.fixingSubgroup : Set Gal(AlgebraicClosure F.Carrier/F.Carrier))
  have hSo : IsOpen S := J.fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_id)
  have hSn : σ ∈ S := by
    change σ⁻¹ * σ ∈ J.fixingSubgroup
    rw [inv_mul_cancel]
    exact J.fixingSubgroup.one_mem
  obtain ⟨g, hg⟩ := (localProjection_denseRange F).exists_mem_open hSo ⟨σ, hSn⟩
  let τ : Gal(AlgebraicClosure F.Carrier/F.Carrier) := localProjection F g
  -- The projection of `g` sends the chosen embedding to `ψ`.
  have hgx (x : E.Carrier) : τ (extensionFieldEmbedding F E f x) = ψ x := by
    have h1 : (σ⁻¹ * τ) (extensionFieldEmbedding F E f x) = extensionFieldEmbedding F E f x :=
      (IntermediateField.mem_fixingSubgroup_iff J _).mp hg _ (hJ x)
    calc τ (extensionFieldEmbedding F E f x)
        = σ (σ⁻¹ (τ (extensionFieldEmbedding F E f x))) := (σ.apply_symm_apply _).symm
      _ = σ (extensionFieldEmbedding F E f x) := congrArg σ h1
      _ = ψ x := hσ x
  refine ⟨g, fun y => ?_⟩
  have hrange : y ∈ extensionWeilRange F E f ↔ ∀ x : E.Carrier,
      AlgEquiv.toAlgHom (localProjection F y) (extensionFieldEmbedding F E f x) =
        extensionFieldEmbedding F E f x := by
    rw [extensionWeilRange, extensionWeilMap_range, extensionGaloisMap_range]
    refine (IntermediateField.mem_fixingSubgroup_iff J (localProjection F y)).trans
      ⟨fun h x => h _ (hJ x), ?_⟩
    intro h z hz
    obtain ⟨x, rfl⟩ := (mem_extensionIntermediateField F E f z).mp hz
    exact h x
  rw [hrange, hH]
  refine forall_congr' fun x => ?_
  rw [← hgx x, map_mul, map_mul, map_inv]
  change _ ↔ τ (AlgEquiv.toAlgHom (localProjection F y)
    (τ.symm (τ (extensionFieldEmbedding F E f x)))) = τ (extensionFieldEmbedding F E f x)
  rw [AlgEquiv.symm_apply_apply]
  exact τ.injective.eq_iff.symm

end Langlands.Weil.Local
