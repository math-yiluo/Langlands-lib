import Langlands.Correspondence.HenniartExtensionBijective
import Langlands.VirtualRepresentation.Weil.Dual
import Langlands.VirtualRepresentation.Supercuspidal.Contragredient

/-!
# Contragredients and the extended stable map

The dual of a class factoring through a finite quotient factors through the
same quotient, and the dual compatibility of candidates makes the stable image
of the dual the contragredient of the stable image. Since duals invert
unramified twists on both sides, the extended map commutes with duals.
-/

noncomputable section

namespace Langlands.VirtualRepresentation.Weil

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Duals invert character twists. -/
theorem dualBasisEquiv_twistBasisEquiv (χ : G →ₜ* ℂˣ) (b : IrreducibleBasis.{uG, uV} G) :
    dualBasisEquiv (twistBasisEquiv χ b) = twistBasisEquiv χ⁻¹ (dualBasisEquiv b) := by
  apply IrreducibleBasis.ext_underlyingClass
  · rfl
  · rw [underlyingClass_dualBasisEquiv, underlyingClass_twistBasisEquiv,
      underlyingClass_twistBasisEquiv, underlyingClass_dualBasisEquiv]
    obtain ⟨n, c, hc⟩ := b
    change FiniteRepresentation.dualClass (FiniteRepresentation.twistClass _
      (FiniteRepresentation.forgetPropertyClass _ c)) =
      FiniteRepresentation.twistClass _ (FiniteRepresentation.dualClass
        (FiniteRepresentation.forgetPropertyClass _ c))
    generalize FiniteRepresentation.forgetPropertyClass _ c = d
    induction d using Quotient.inductionOn with
    | h A =>
      apply Quotient.sound
      refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_⟩
      change LinearMap.id ∘ₗ (Langlands.twist χ.toMonoidHom A.representation).dual g =
        Langlands.twist (χ⁻¹).toMonoidHom A.representation.dual g ∘ₗ LinearMap.id
      rw [Langlands.dual_twist]
      rfl

/-- The dual of a class factoring through `f` factors through `f`. -/
theorem factorsThrough_dualBasisEquiv {H : Type*} [Group H] (f : G →* H)
    {b : IrreducibleBasis.{uG, uV} G} (h : FactorsThrough G f b) :
    FactorsThrough G f (dualBasisEquiv b) := by
  obtain ⟨A, hA⟩ := h
  refine ⟨FiniteRepresentation.dual A, ?_⟩
  rw [underlyingClass_dualBasisEquiv, ← hA, FiniteRepresentation.dualClass_classOf]
  apply Quotient.sound
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_⟩
  change LinearMap.id ∘ₗ A.representation.dual (f g) =
    Representation.dual (A.representation.comp f) g ∘ₗ LinearMap.id
  rw [LinearMap.id_comp, LinearMap.comp_id, Representation.dual_apply,
    Representation.dual_apply, MonoidHom.comp_apply, map_inv f]

end Langlands.VirtualRepresentation.Weil

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The dual of a unitary class factoring through a finite quotient factors
through the same quotient. -/
theorem generator_unitaryDual_mem {Q : Type*} [Group Q] [Finite Q]
    {q : Field.absoluteGaloisGroup K.Carrier →* Q} {b : LocalWeil.UnitaryBasis.{uK, uW} K}
    (h : generator b ∈ LocalWeil.unitaryFiniteFactoringSupported K q) :
    generator (LocalWeil.unitaryDualBasisEquiv K b) ∈
      LocalWeil.unitaryFiniteFactoringSupported K q := by
  have hmem : ∀ {ι : Type _} {s : Set ι} {i : ι}, generator i ∈ supported s ↔ i ∈ s := by
    intro ι s i
    constructor
    · intro hi
      exact (Finsupp.mem_supported ℤ _).mp hi (by simp [generator])
    · intro hi
      exact Finsupp.single_mem_supported ℤ 1 hi
  simp only [LocalWeil.unitaryFiniteFactoringSupported, Weil.unitaryFactoringSupported] at h ⊢
  rw [hmem] at h ⊢
  exact Weil.factorsThrough_dualBasisEquiv _ h

/-- The stable image of the dual is the contragredient of the stable image. -/
theorem IsStableImage.dual {b : LocalWeil.UnitaryBasis.{uK, uW} K}
    {π : PadicSupercuspidal.UnitaryBasis.{uK, uV} K}
    (h : IsStableImage.{uK, uW, uV, uE} K b (generator π)) :
    IsStableImage.{uK, uW, uV, uE} K (LocalWeil.unitaryDualBasisEquiv K b)
      (generator (PadicSupercuspidal.unitaryContragredientBasisEquiv K π)) := by
  obtain ⟨Q, hQ, hQf, q, hb, hex, hall⟩ := h
  refine ⟨Q, hQ, hQf, q, generator_unitaryDual_mem K hb, hex, ?_⟩
  intro W A Φ hΦ x hx
  obtain ⟨hmem, hΦd⟩ := hΦ.2.1.2.2.1 ⟨generator b, hΦ.1 hb⟩
  have hxe : x = ⟨_, hmem⟩ := by
    apply Subtype.ext
    rw [hx]
    exact (LocalWeil.unitaryDualLatticeEquiv_generator K b).symm
  rw [hxe, hΦd, hall W A Φ hΦ _ rfl]
  exact PadicSupercuspidal.unitaryContragredientLatticeEquiv_generator K π

/-- The extended stable map commutes with duals on bases. -/
theorem extensionBasis_dual (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    (b : LocalWeil.Basis.{uK, uW} K) :
    extensionBasis K hSC (Weil.dualBasisEquiv b) =
      PadicSupercuspidal.contragredientBasisEquiv K (extensionBasis K hSC b) := by
  obtain ⟨z, π₀, b₀, h, he⟩ := extensionBasis_spec K hSC b
  rw [he, PadicSupercuspidal.contragredientBasisEquiv_unramifiedTwist,
    ← PadicSupercuspidal.unitaryContragredientBasisEquiv_val]
  refine extensionBasis_eq K hSC hUTI (b₀ := LocalWeil.unitaryDualBasisEquiv K b₀)
    ⟨?_, IsStableImage.dual K h.2⟩
  rw [LocalWeil.unitaryDualBasisEquiv_val, ← h.1]
  change _ = Weil.dualBasisEquiv (Weil.twistBasisEquiv _ b₀.val)
  rw [Weil.dualBasisEquiv_twistBasisEquiv]
  have : Weil.Local.localUnramifiedCharacter K z⁻¹ =
      (Weil.Local.localUnramifiedCharacter K z)⁻¹ := by
    ext g
    change (((z⁻¹ : ℂˣ) ^ (Weil.Local.localDegree K g).toAdd : ℂˣ) : ℂ) =
      (((z ^ (Weil.Local.localDegree K g).toAdd)⁻¹ : ℂˣ) : ℂ)
    rw [inv_zpow]
  rw [this]
  rfl

/-- The extended stable map commutes with the canonical duals. -/
theorem extensionMap_dual (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE}) :
    SupercuspidalDualCompatibility K (extensionMap K hSC) := by
  rw [supercuspidalDualCompatibility_iff]
  intro n σ
  have h := extensionBasis_dual K hSC hUTI ⟨n, σ⟩
  rw [← sigma_extensionMap, ← sigma_extensionMap] at h
  exact eq_of_heq (Sigma.mk.inj h).2

end Langlands.Henniart.Extension
