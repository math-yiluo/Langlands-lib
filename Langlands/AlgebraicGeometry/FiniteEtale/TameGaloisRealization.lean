import Langlands.AlgebraicGeometry.FiniteEtale.GeometricContinuousActionEquivalenceProof
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-! # A Galois cover realizing a finite continuous quotient of the fundamental group -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FiniteEtale.TameGaloisRealization

/-- The total space of a Galois cover, as a finite étale cover. -/
def toCover {S : Scheme.{u}} {G : Type (u + 1)} [Group G] [Finite G]
    (W : Scheme.GaloisCover G S) : Cover S :=
  @cover _ _ W.π W.isFinite W.etale

open scoped FintypeCatDiscrete

/-- **Galois cover of a finite quotient.** For a connected locally Noetherian scheme `S`, a
geometric point `s` and a continuous homomorphism `ρ` from the fundamental group to a finite
discrete group `H`, there is a Galois cover of `S` with finite group `G`, `|G|` dividing `|H|`,
such that an element of the fundamental group fixing some geometric point of the cover lies in
the kernel of `ρ`. -/
theorem exists_galoisCover
    {S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (hfin : ∀ Y : Cover S, Finite (Fiber s Y))
    {H : Type v} [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    (ρ : FundamentalGroup s hfin →* H) (hρ : Continuous ρ) :
    ∃ (G : Type (u + 1)) (_ : Group G) (_ : Finite G) (W : Scheme.GaloisCover G S),
      Nat.card G ∣ Nat.card H ∧
      ∀ (γ : FundamentalGroup s hfin) (p : Fiber s (toCover W)), γ • p = p → ρ γ = 1 := by
  classical
  let N : Subgroup (FundamentalGroup s hfin) := ρ.ker
  have hNopen : IsOpen (N : Set (FundamentalGroup s hfin)) :=
    hρ.isOpen_preimage {1} (isOpen_discrete _)
  let Q := FundamentalGroup s hfin ⧸ N
  have : Finite Q := Finite.of_injective _ (QuotientGroup.kerLift_injective ρ)
  have hcard : Nat.card Q ∣ Nat.card H :=
    Subgroup.card_dvd_of_injective _ (QuotientGroup.kerLift_injective ρ)
  let V := Shrink.{u} Q
  let eV : Q ≃ V := equivShrink.{u} Q
  let _ : MulAction (FundamentalGroup s hfin) V :=
    { smul γ w := eV ((γ : Q) * eV.symm w)
      one_smul w := by simp [HSMul.hSMul]
      mul_smul γ δ w := by simp [HSMul.hSMul, mul_assoc] }
  have hsmulV (γ : FundamentalGroup s hfin) (w : V) : γ • w = eV ((γ : Q) * eV.symm w) := rfl
  have hopen (w w' : V) : IsOpen ((fun γ : FundamentalGroup s hfin ↦ (eV ((γ : Q) * eV.symm w) : V)) ⁻¹'
      {w'}) := by
    obtain ⟨γ₀, hγ₀⟩ := QuotientGroup.mk_surjective (eV.symm w' * (eV.symm w)⁻¹)
    have hset : ((fun γ : FundamentalGroup s hfin ↦ (eV ((γ : Q) * eV.symm w) : V)) ⁻¹'
        {w'}) = (fun γ ↦ γ₀⁻¹ * γ) ⁻¹' (N : Set (FundamentalGroup s hfin)) := by
      ext γ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [← Equiv.eq_symm_apply, ← eq_mul_inv_iff_mul_eq, ← QuotientGroup.eq,
        hγ₀, eq_comm]
    exact hset ▸ hNopen.preimage (continuous_const.mul continuous_id)
  let X : ContAction FintypeCat.{u} (FundamentalGroup s hfin) :=
    ⟨Action.FintypeCat.ofMulAction _ (FintypeCat.of V), by
      constructor
      have : DiscreteTopology ((forget₂ (Action FintypeCat (FundamentalGroup s hfin)) TopCat).obj
        (Action.FintypeCat.ofMulAction _ (FintypeCat.of V))) := ⟨rfl⟩
      have : DiscreteTopology ((forget₂ FintypeCat TopCat).obj
        (Action.FintypeCat.ofMulAction (FundamentalGroup s hfin) (FintypeCat.of V)).V) := ⟨rfl⟩
      exact continuous_prod_of_discrete_right.mpr fun w ↦
        continuous_discrete_rng.mpr fun w' ↦ hopen w w'⟩
  -- right multiplication by `g⁻¹` on `Q`, an automorphism of the `π₁`-set `X`
  let τ (g : Q) : X ⟶ X := ObjectProperty.homMk
    { hom := FintypeCat.homMk fun w ↦ eV (eV.symm w * g⁻¹)
      comm γ := FintypeCat.hom_ext _ _ fun w ↦ by
        change eV (eV.symm (eV ((γ : Q) * eV.symm w)) * g⁻¹) =
          eV ((γ : Q) * eV.symm (eV (eV.symm w * g⁻¹)))
        simp only [Equiv.symm_apply_apply, mul_assoc] }
  let E := continuousActionFunctor s hfin
  have : E.IsEquivalence := geometricContinuousActionEquivalence s hfin
  let A := E.objPreimage X
  let c : E.obj A ≅ X := E.objObjPreimageIso X
  let T (g : Q) : A ⟶ A := E.preimage (c.hom ≫ τ g ≫ c.inv)
  have hT (g : Q) : E.map (T g) = c.hom ≫ τ g ≫ c.inv := E.map_preimage _
  have hT1 : T 1 = 𝟙 A := E.map_injective <| by
    rw [hT, E.map_id]
    have : τ 1 = 𝟙 X := ObjectProperty.hom_ext _ (Action.Hom.ext (FintypeCat.hom_ext _ _
      fun w ↦ by
        have h1 (w : V) : eV (eV.symm w * 1⁻¹) = w := by simp
        exact h1 w))
    simp [this]
  have hTmul (g h : Q) : T (g * h) = T h ≫ T g := E.map_injective <| by
    rw [hT, E.map_comp, hT, hT]
    have : τ (g * h) = τ h ≫ τ g := ObjectProperty.hom_ext _ (Action.Hom.ext
      (FintypeCat.hom_ext _ _ fun w ↦ by
        change eV (eV.symm w * (g * h)⁻¹) = eV (eV.symm (eV (eV.symm w * h⁻¹)) * g⁻¹)
        simp [mul_assoc]))
    simp [this]
  let cV := (ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso c
  let β : Fiber s A → V := fun p ↦ cV.hom p
  have hβ : Function.Injective β := (FintypeCat.equivEquivIso.symm cV).injective
  have hβT (g : Q) (p : Fiber s A) : β (p ≫ (T g).hom) = eV (eV.symm (β p) * g⁻¹) := by
    have h₁ : p ≫ (T g).hom = (E.map (T g)).hom.hom p := rfl
    rw [h₁, hT]
    change ((c.hom ≫ τ g ≫ c.inv) ≫ c.hom).hom.hom p = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hβsmul (γ : FundamentalGroup s hfin) (p : Fiber s A) : β (γ • p) = γ • β p := by
    have := congrArg (fun f ↦ f.hom p) (c.hom.hom.comm γ)
    exact this
  have hAfin : IsFinite A.obj.hom := A.property.1
  have hAet : Etale A.obj.hom := A.property.2
  let P : S.FiniteEtale := ⟨MorphismProperty.Over.mk ⊤ A.obj.hom hAet, hAfin⟩
  let v (g : Q) : P ⟶ P :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk (T g).hom.left (Over.w (T g).hom))
  let toL (x : (Scheme.FiniteEtale.fiber s).obj P) : Fiber s A :=
    Over.homMk (U := Over.mk s) (V := A.obj) x.left (Scheme.FiniteEtale.fiber_left_comp s x)
  have htoL_inj : Function.Injective toL := fun x y h ↦
    Scheme.FiniteEtale.fiber_ext s (congrArg (fun f ↦ f.left) h)
  have htoL_map (g : Q) (x : (Scheme.FiniteEtale.fiber s).obj P) :
      toL ((Scheme.FiniteEtale.fiber s).map (v g) x) = toL x ≫ (T g).hom := by
    ext1
    rfl
  have hv (x y : (Scheme.FiniteEtale.fiber s).obj P) :
      ∃! m : Q, (Scheme.FiniteEtale.fiber s).map (v m) x = y := by
    refine ⟨(eV.symm (β (toL y)))⁻¹ * eV.symm (β (toL x)), htoL_inj (hβ ?_), fun m hm ↦ ?_⟩
    · rw [htoL_map, hβT, mul_inv_rev, inv_inv, mul_inv_cancel_left, Equiv.apply_symm_apply]
    · have := congrArg (fun z ↦ β (toL z)) hm
      simp only [htoL_map, hβT] at this
      rw [← this, Equiv.symm_apply_apply]
      group
  have hne : Nonempty ((Scheme.FiniteEtale.fiber s).obj P) := by
    let a : Fiber s A := (cV.inv (eV 1) : Fiber s A)
    exact ⟨Over.homMk (V := (Scheme.Etale.forget S).obj P.obj) a.left (Over.w a)⟩
  let W : Scheme.GaloisCover Q S :=
    { P := A.obj.left
      π := A.obj.hom
      isFinite := hAfin
      etale := hAet
      surjective := Scheme.FiniteEtale.surjective_of_nonempty_fiber s P hne
      smul g := (T g).hom.left
      smul_π g := Over.w (T g).hom
      one_smul := by rw [hT1]; rfl
      mul_smul g h := by rw [hTmul]; rfl
      isIso_sigmaDesc := Scheme.FiniteEtale.isIso_sigmaDesc_of_existsUnique s P v hv }
  have key (γ : FundamentalGroup s hfin) (p : Fiber s A) (hp : γ • p = p) : ρ γ = 1 := by
    have hp' : γ • β p = β p := by
      rw [← hβsmul]
      exact congrArg β hp
    rw [hsmulV] at hp'
    have hq : (γ : Q) * eV.symm (β p) = eV.symm (β p) :=
      eV.injective (hp'.trans (eV.apply_symm_apply _).symm)
    exact (QuotientGroup.eq_one_iff γ).mp (mul_eq_right.mp hq)
  exact ⟨Q, inferInstance, inferInstance, W, hcard, fun γ p hp ↦ key γ p hp⟩

end Langlands.AlgebraicGeometry.FiniteEtale.TameGaloisRealization
