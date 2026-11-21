import Langlands.Geometry.FormalGroup.GlobalIntegralFormalHom
import Langlands.Geometry.FormalGroup.IntegralFormalHomGluing
import Langlands.Geometry.FormalGroup.OrderLinearIntegralSection
import Langlands.Geometry.FormalGroup.FieldScalarIsogenyPresentation
import Langlands.Geometry.FormalGroup.LocalQuasiIsogenyGroupoid

/-! # Recover tensor quasi-isogenies from local sections over an affine base -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory Opposite TopologicalSpace

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

namespace RationalSection

/-- For a scalar-divisible source, global tensors are determined by their section on the full
spectrum. Multiplying by a uniformizer power reduces the comparison to integral coefficients. -/
theorem ofGlobalOn_top_injective (hπ : Irreducible π) (hM : M.IsPiDivisible π) :
    Function.Injective (ofGlobalOn (F := F) (M := M) (N := N) ⊤) := by
  intro z w hzw
  let t := ofGlobalOn (F := F) (M := M) (N := N) ⊤
  have hdiff : t (z - w) = 0 := by rw [map_sub, sub_eq_zero.mpr hzw]
  obtain ⟨n, f, hf⟩ := RationalHom.exists_uniformizerPower_ofHom hπ (z - w)
  have hs : ofHom (F := F) f ⊤ = 0 := by
    rw [← ofGlobalOn_ofHom, ← hf]
    change t (_ • (z - w)) = _
    rw [map_smul, hdiff, smul_zero]
  have hi : f.map (globalCoefficientEquiv O R).toAlgHom = 0 := by
    apply ofIntegral_injective_of_isPiDivisible (F := F) hπ hM
    change ofHom (F := F) f ⊤ = ofRational ⊤ (RationalHom.ofHom 0)
    rw [hs, map_zero]
    exact ((ofRational (F := F) (M := M) (N := N) ⊤).map_zero).symm
  have hfzero : f = 0 := Hom.map_globalCoefficients_injective
    (hi.trans ((Hom.mapLinear (globalCoefficientEquiv O R).toAlgHom).map_zero).symm)
  rw [hfzero, map_zero] at hf
  have hne : algebraMap O F π ≠ 0 :=
    fun h => hπ.ne_zero ((IsFractionRing.injective O F) (h.trans (map_zero _).symm))
  exact sub_eq_zero.mp ((smul_eq_zero.mp hf).resolve_left (pow_ne_zero _ hne))

end RationalSection

namespace LocalQuasiIsogeny

/-- On an affine spectrum, finitely many local denominators suffice. Their integral numerators
at a common exponent glue to a single integral formal map over the full structure sections. -/
theorem exists_integral_multiple_top (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π) :
    ∃ (n : ℕ) (f : OpenIntegralHom M N ⊤),
      (algebraMap O F π) ^ n • z.val = RationalSection.ofIntegral ⊤ f := by
  classical
  choose V hV i n f _hf he using
    fun x : PrimeSpectrum R => z.isLocal x (show x ∈ (⊤ : Opens (PrimeSpectrum R)) from trivial)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (V x : Set (PrimeSpectrum R)))
    (fun x => (V x).isOpen) (fun x _ => Set.mem_iUnion.mpr ⟨x, hV x⟩)
  let W (b : ↑s) := V b.val
  let j (b : ↑s) : W b ⟶ (⊤ : Opens (PrimeSpectrum R)) := i b.val
  have hcover : ⊤ ≤ iSup W := by
    intro x _
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨hb', hx⟩ := Set.mem_iUnion.mp hb
    exact (le_iSup W ⟨b, hb'⟩) hx
  let m := s.sup n
  let g (b : ↑s) : OpenIntegralHom M N (W b) := π ^ (m - n b.val) • f b.val
  have hg (b : ↑s) : (algebraMap O F π) ^ m • RationalSection.restrict (j b) z.val =
      RationalSection.ofIntegral (W b) (g b) := by
    dsimp only [j, W, g]
    rw [RationalSection.ofIntegral_smul, map_pow, ← he b.val, smul_smul, ← pow_add,
      Nat.sub_add_cancel (Finset.le_sup b.property)]
  have hcompat (b c : ↑s) :
      Hom.algebraMapLinear ((coefficientStructurePresheaf R).map
        (homOfLE inf_le_left : W b ⊓ W c ⟶ W b).op) (g b) =
      Hom.algebraMapLinear ((coefficientStructurePresheaf R).map
        (homOfLE inf_le_right : W b ⊓ W c ⟶ W c).op) (g c) := by
    let a : W b ⊓ W c ⟶ W b := homOfLE inf_le_left
    let d : W b ⊓ W c ⟶ W c := homOfLE inf_le_right
    have had : a ≫ j b = d ≫ j c := Subsingleton.elim _ _
    apply RationalSection.ofIntegral_injective_of_isPiDivisible (F := F) hπ z.source_divisible
    rw [← RationalSection.restrict_ofIntegral a, ← RationalSection.restrict_ofIntegral d,
      ← hg b, ← hg c, map_smul, map_smul, ← RationalSection.restrict_comp,
      ← RationalSection.restrict_comp, had]
  refine ⟨m, IntegralFormalHomGluing.glue W j hcover g hcompat, ?_⟩
  apply (rationalHomTypeSheaf F M N).eq_of_locally_eq' W ⊤ j hcover
  intro b
  change RationalSection.restrict (j b) ((algebraMap O F π) ^ m • z.val) =
    RationalSection.restrict (j b) (RationalSection.ofIntegral ⊤ _)
  rw [map_smul, RationalSection.restrict_ofIntegral,
    IntegralFormalHomGluing.restrict_glue W j hcover g hcompat b, hg]

/-- The integral multiple over the full structure sections can be recovered over the affine
ring itself and divided by its uniformizer power in the actual tensor Hom. -/
theorem exists_tensor (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π) :
    ∃ t : RationalHom F M N, RationalSection.ofGlobalOn ⊤ t = z.val := by
  obtain ⟨n, f, hf⟩ := z.exists_integral_multiple_top hπ
  refine ⟨((algebraMap O F π) ^ n)⁻¹ • RationalHom.ofHom f.ofGlobalCoefficients, ?_⟩
  rw [map_smul, RationalSection.ofGlobalOn_ofHom]
  change _ • RationalSection.ofIntegral ⊤
    (f.ofGlobalCoefficients.map (globalCoefficientEquiv O R).toAlgHom) = _
  rw [Hom.map_ofGlobalCoefficients, ← hf, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ z.scalar_ne_zero),
    one_smul]

/-- The unique tensor quasi-isogeny whose section agrees with the given local quasi-isogeny
on the full affine spectrum. Its inverse is recovered by the same construction. -/
def toTensor (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π) : QuasiIsogeny F M N := by
  let f := (z.exists_tensor hπ).choose
  let g := (z.inv.exists_tensor hπ).choose
  have hf : RationalSection.ofGlobalOn ⊤ f = z.val := (z.exists_tensor hπ).choose_spec
  have hg : RationalSection.ofGlobalOn ⊤ g = z.inv.val := (z.inv.exists_tensor hπ).choose_spec
  refine ⟨f, g, ?_, ?_⟩
  · apply RationalSection.ofGlobalOn_top_injective (F := F) hπ z.source_divisible
    rw [RationalSection.ofGlobalOn_comp, RationalSection.ofGlobalOn_id, hf, hg, inv_val,
      ← toSectionIso_hom z]
    exact z.toSectionIso.inv_hom
  · apply RationalSection.ofGlobalOn_top_injective (F := F) hπ z.target_divisible
    rw [RationalSection.ofGlobalOn_comp, RationalSection.ofGlobalOn_id, hf, hg, inv_val,
      ← toSectionIso_hom z]
    exact z.toSectionIso.hom_inv

@[simp]
theorem ofGlobalOn_toTensor_hom (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π) :
    RationalSection.ofGlobalOn ⊤ (z.toTensor hπ).hom = z.val := (z.exists_tensor hπ).choose_spec

@[simp]
theorem ofGlobalOn_toTensor_inv (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π) :
    RationalSection.ofGlobalOn ⊤ (z.toTensor hπ).inv = z.inv.val :=
  (z.inv.exists_tensor hπ).choose_spec

end LocalQuasiIsogeny

end Langlands.FormalGroup.ModuleLaw
