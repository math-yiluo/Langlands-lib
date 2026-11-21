import Langlands.Geometry.FormalGroup.NilpotentFormalHom
import Langlands.Geometry.FormalGroup.OrderRationalMorphism
import Mathlib.RingTheory.Flat.Localization

/-! # Rigidity of rational formal maps with order action -/

noncomputable section

universe u v w q

namespace Langlands.FormalGroup.ModuleLaw

open TensorProduct

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [Algebra O R] [CommRing S] [Algebra O S]
variable {F : Type q} [Field F] [Algebra O F]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ} {π : O}

namespace RationalHom

/-- Integral rigidity remains injectivity after flat scalar extension. -/
theorem map_injective_of_nilpotent [Module.Flat O F] (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiPowerTorsion π) :
    Function.Injective (map (F := F) (M := M) (N := N) φ) :=
  Module.Flat.lTensor_preserves_injective_linearMap (Hom.mapLinear φ)
    (Hom.map_injective_of_nilpotent φ hφ hI hM hN)

/-- The scalar powers needed to lift integral homomorphisms are invertible
in rational Hom, so the actual tensor map is surjective. -/
theorem map_surjective_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hN : N.IsPiPowerTorsion π) (hπ : algebraMap O F π ≠ 0) :
    Function.Surjective (map (F := F) (M := M) (N := N) φ) := by
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a f =>
    obtain ⟨k, g, hg⟩ := Hom.exists_lift_smul_of_nilpotent φ hφ hI hN f
    let c := algebraMap O F π ^ k
    have hc : c ≠ 0 := pow_ne_zero k hπ
    refine ⟨(a / c) ⊗ₜ[O] g, ?_⟩
    change (a / c) ⊗ₜ[O] g.map φ = a ⊗ₜ[O] f
    rw [hg, ← TensorProduct.smul_tmul, Algebra.smul_def, map_pow]
    change (c * (a / c)) ⊗ₜ[O] f = a ⊗ₜ[O] f
    rw [mul_comm c, div_mul_cancel₀ _ hc]
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨g₁, rfl⟩ := h₁
    obtain ⟨g₂, rfl⟩ := h₂
    exact ⟨g₁ + g₂, map_add _ _ _⟩

end RationalHom

namespace OrderAction

variable {A : Type w} [Ring A] [Algebra O A]
variable {E : OrderAction A M} {E' : OrderAction A N}

namespace RationalHom

/-- Order commutation is reflected by the injective ambient rational Hom map. -/
theorem map_bijective_of_nilpotent [Module.Flat O F] (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiPowerTorsion π) (hπ : algebraMap O F π ≠ 0) :
    Function.Bijective (map (F := F) (E := E) (E' := E') φ) := by
  have hinj := ModuleLaw.RationalHom.map_injective_of_nilpotent (F := F) φ hφ hI hM hN
  refine ⟨fun f g he => ext (hinj (congrArg Subtype.val he)), ?_⟩
  intro f₀
  obtain ⟨f, hf⟩ := ModuleLaw.RationalHom.map_surjective_of_nilpotent
    (M := M) φ hφ hI hN hπ f₀.val
  have hcomm : ∀ a : A,
      ModuleLaw.RationalHom.comp f (ModuleLaw.RationalHom.ofHom (E.action a)) =
        ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (E'.action a)) f := by
    intro a
    apply hinj
    rw [ModuleLaw.RationalHom.map_comp, ModuleLaw.RationalHom.map_comp,
      ModuleLaw.RationalHom.map_ofHom, ModuleLaw.RationalHom.map_ofHom, hf,
      ← OrderAction.map_action, ← OrderAction.map_action]
    exact f₀.commutes a
  exact ⟨⟨f, hcomm⟩, ext hf⟩

/-- The canonical rational Hom comparison with all order commutation equations. -/
def nilpotentMapEquiv [Module.Flat O F] (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiPowerTorsion π) (hπ : algebraMap O F π ≠ 0) :
    RationalHom F E E' ≃ₗ[F] RationalHom F (E.map φ) (E'.map φ) :=
  LinearEquiv.ofBijective (map φ) (map_bijective_of_nilpotent φ hφ hI hM hN hπ)

end RationalHom

namespace QuasiIsogeny

variable [IsDomain O] [IsFractionRing O F]

/-- Coefficient reduction recovers the actual invertible full-order map,
since injectivity also reflects its two inverse equations. -/
theorem map_bijective_of_nilpotent (φ : R →ₐ[O] S)
    (hφ : Function.Surjective φ) (hI : IsNilpotent (RingHom.ker φ.toRingHom))
    (hM : M.IsPiDivisible π) (hN : N.IsPiDivisible π) (hπ : π ≠ 0) :
    Function.Bijective (map (F := F) (E := E) (E' := E') φ) := by
  let _ := IsLocalization.flat F (nonZeroDivisors O)
  have hc : algebraMap O F π ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective O F).ne hπ
  have hf := RationalHom.map_bijective_of_nilpotent (E := E) (E' := E') φ hφ hI hM hN.torsion hc
  have hg := RationalHom.map_bijective_of_nilpotent (E := E') (E' := E) φ hφ hI hN hM.torsion hc
  refine ⟨fun f g he => ext (hf.injective (congrArg QuasiIsogeny.hom he)), ?_⟩
  intro f₀
  obtain ⟨f, hfred⟩ := hf.surjective f₀.hom
  obtain ⟨g, hgred⟩ := hg.surjective f₀.inv
  refine ⟨⟨f, g, ?_, ?_⟩, ?_⟩
  · apply (RationalHom.map_bijective_of_nilpotent (E := E) (E' := E) φ hφ hI hM hM.torsion hc).injective
    rw [RationalHom.map_comp, hgred, hfred, RationalHom.map_id, f₀.inv_hom]
  · apply (RationalHom.map_bijective_of_nilpotent (E := E') (E' := E') φ hφ hI hN hN.torsion hc).injective
    rw [RationalHom.map_comp, hfred, hgred, RationalHom.map_id, f₀.hom_inv]
  · exact ext hfred

end QuasiIsogeny

end OrderAction
end Langlands.FormalGroup.ModuleLaw
