import Langlands.Geometry.FormalGroup.GlobalTensorQuasiIsogeny
import Langlands.Geometry.FormalGroup.OrderRationalMorphism

/-! # Order linearity and coherence of affine tensor recovery -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.LocalQuasiIsogeny

open TopologicalSpace

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {F : Type v} [Field F] [Algebra O F] [IsFractionRing O F]
variable {σ τ σ' τ' υ : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ'] [Finite υ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'} {P : ModuleLaw O R υ}
variable {π : O}

/-- Tensor recovery commutes with actual affine coefficient pullback. -/
theorem toTensor_baseChange (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π)
    (φ : R →ₐ[O] S) :
    (z.baseChange φ).toTensor hπ = (z.toTensor hπ).map φ := by
  apply QuasiIsogeny.ext
  apply RationalSection.ofGlobalOn_top_injective (F := F) hπ (z.source_divisible.map φ)
  change RationalSection.ofGlobalOn ⊤ ((z.baseChange φ).toTensor hπ).hom =
    RationalSection.ofGlobalOn ⊤ (RationalHom.map φ (z.toTensor hπ).hom)
  let t : LocalQuasiIsogeny F π (M.map φ) (N.map φ) ⊤ := z.baseChange φ
  have ht : t.val = RationalSection.baseChange φ ⊤ z.val := rfl
  exact (ofGlobalOn_toTensor_hom t hπ).trans (ht.trans
    ((congrArg (RationalSection.baseChange φ ⊤) (ofGlobalOn_toTensor_hom z hπ).symm).trans
      (RationalSection.baseChange_ofGlobalOn φ ⊤ (z.toTensor hπ).hom)))

/-- Changing chart coordinates by actual integral isomorphisms conjugates the recovered tensor. -/
theorem toTensor_transportIso (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π)
    (a : Iso M M') (b : Iso N N') :
    (z.transportIso a b).toTensor hπ =
      ((QuasiIsogeny.ofIso a.symm).trans (z.toTensor hπ)).trans (QuasiIsogeny.ofIso b) := by
  apply QuasiIsogeny.ext
  apply RationalSection.ofGlobalOn_top_injective (F := F) hπ (a.isPiDivisible π z.source_divisible)
  change RationalSection.ofGlobalOn ⊤ ((z.transportIso a b).toTensor hπ).hom =
    RationalSection.ofGlobalOn ⊤ (RationalHom.comp (RationalHom.ofHom b.hom)
      (RationalHom.comp (z.toTensor hπ).hom (RationalHom.ofHom a.inv)))
  rw [ofGlobalOn_toTensor_hom, RationalSection.ofGlobalOn_comp, RationalSection.ofGlobalOn_comp,
    RationalSection.ofGlobalOn_ofHom, RationalSection.ofGlobalOn_ofHom, ofGlobalOn_toTensor_hom]
  rfl

/-- Recovering the tensor respects composition of the actual local quasi-isogenies. -/
theorem toTensor_comp (g : LocalQuasiIsogeny F π N P ⊤) (z : LocalQuasiIsogeny F π M N ⊤)
    (hπ : Irreducible π) : (g.comp z).toTensor hπ = (z.toTensor hπ).trans (g.toTensor hπ) := by
  apply QuasiIsogeny.ext
  apply RationalSection.ofGlobalOn_top_injective (F := F) hπ z.source_divisible
  change RationalSection.ofGlobalOn ⊤ ((g.comp z).toTensor hπ).hom =
    RationalSection.ofGlobalOn ⊤ (RationalHom.comp (g.toTensor hπ).hom (z.toTensor hπ).hom)
  rw [ofGlobalOn_toTensor_hom, RationalSection.ofGlobalOn_comp, ofGlobalOn_toTensor_hom,
    ofGlobalOn_toTensor_hom, comp_val]

variable {D : Type w} [Ring D] [Algebra O D]
variable {E : OrderAction D M} {G : OrderAction D N}

/-- Order commutation of the actual rational section implies order commutation of the tensor. -/
def toOrderTensor (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π)
    (hz : RationalSection.IsOrderLinear E G z.val) : OrderAction.QuasiIsogeny F E G :=
  OrderAction.QuasiIsogeny.ofModuleQuasiIsogeny (z.toTensor hπ) (by
    intro b
    apply RationalSection.ofGlobalOn_top_injective (F := F) hπ z.source_divisible
    rw [RationalSection.ofGlobalOn_comp, RationalSection.ofGlobalOn_comp,
      RationalSection.ofGlobalOn_ofHom, RationalSection.ofGlobalOn_ofHom, ofGlobalOn_toTensor_hom]
    exact hz b)

@[simp]
theorem toOrderTensor_toModuleQuasiIsogeny (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π)
    (hz : RationalSection.IsOrderLinear E G z.val) :
    (z.toOrderTensor hπ hz).toModuleQuasiIsogeny = z.toTensor hπ :=
  OrderAction.QuasiIsogeny.toModule_ofModuleQuasiIsogeny _ _

@[simp]
theorem ofGlobalOn_toOrderTensor_hom (z : LocalQuasiIsogeny F π M N ⊤) (hπ : Irreducible π)
    (hz : RationalSection.IsOrderLinear E G z.val) :
    RationalSection.ofGlobalOn ⊤ (z.toOrderTensor hπ hz).hom.val = z.val :=
  ofGlobalOn_toTensor_hom z hπ

end Langlands.FormalGroup.ModuleLaw.LocalQuasiIsogeny
