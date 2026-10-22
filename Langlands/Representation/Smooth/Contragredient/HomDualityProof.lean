import Langlands.Representation.Smooth.Contragredient.HomDualityStatement
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof

/-! # Recovering intertwiners from smooth contragredients -/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

theorem contragredientMap_add (f g : ρ.IntertwiningMap σ) :
    contragredientMap (f + g) = contragredientMap f + contragredientMap g := by
  ext ℓ v
  exact map_add ℓ.val (f v) (g v)

theorem contragredientMap_smul (c : R) (f : ρ.IntertwiningMap σ) :
    contragredientMap (c • f) = c • contragredientMap f := by
  ext ℓ v
  exact map_smul ℓ.val c (f v)

/-- Bijective target bidual evaluation suffices for recovering every
intertwiner from its contragredient, over an arbitrary commutative ring. -/
theorem contragredientMap_bijective_of_bidual (hρ : IsSmooth ρ)
    (hσ : IsSmooth σ) (hb : Function.Bijective (smoothBidual hσ)) :
    Function.Bijective (fun f : ρ.IntertwiningMap σ => contragredientMap f) := by
  constructor
  · intro f g h
    ext v
    apply hb.1
    apply Subtype.ext
    apply LinearMap.ext
    intro ℓ
    exact congrArg (fun a : (smoothContragredient σ).IntertwiningMap
      (smoothContragredient ρ) => (a ℓ).val v) h
  · intro a
    let e : σ.Equiv
        (smoothContragredient (V := SmoothDual σ) (smoothContragredient σ)) :=
      (smoothBidual hσ).ofBijective hb
    let f : ρ.IntertwiningMap σ :=
      e.symm.toIntertwiningMap.comp ((contragredientMap a).comp (smoothBidual hρ))
    refine ⟨f, ?_⟩
    ext ℓ v
    change ℓ.val (e.symm (contragredientMap a (smoothBidual hρ v))) = (a ℓ).val v
    have he := e.apply_symm_apply (contragredientMap a (smoothBidual hρ v))
    change smoothBidual hσ (e.symm (contragredientMap a (smoothBidual hρ v))) =
      contragredientMap a (smoothBidual hρ v) at he
    exact congrArg
      (fun ψ : SmoothDual (V := SmoothDual σ) (smoothContragredient σ) => ψ.val ℓ) he

/-- The recovered map is the inverse of the canonical linear Hom-space map. -/
theorem contragredientHomEquiv_exists_of_bidual (hρ : IsSmooth ρ)
    (hσ : IsSmooth σ) (hb : Function.Bijective (smoothBidual hσ)) :
    ∃ e : ρ.IntertwiningMap σ ≃ₗ[R]
      (smoothContragredient σ).IntertwiningMap (smoothContragredient ρ),
      ∀ f, e f = contragredientMap f := by
  let t : ρ.IntertwiningMap σ →ₗ[R]
      (smoothContragredient σ).IntertwiningMap (smoothContragredient ρ) :=
    { toFun := contragredientMap
      map_add' := contragredientMap_add
      map_smul' := contragredientMap_smul }
  exact ⟨LinearEquiv.ofBijective t
    (contragredientMap_bijective_of_bidual hρ hσ hb), fun _ => rfl⟩

section Complex

variable [Module ℂ V] [Module ℂ W]

theorem smoothContragredientHomDuality
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W] :
    SmoothContragredientHomDualityStatement (G := G) (V := V) (W := W) := by
  intro _ hcof ρc σc hρ hσ
  exact contragredientHomEquiv_exists_of_bidual hρ hσ.1
    ⟨smoothBidual_injective_of_compact_cofinal hcof σc hσ.1,
      smoothBidual_surjective_of_compact_cofinal hcof σc hσ⟩

end Complex

end Langlands
