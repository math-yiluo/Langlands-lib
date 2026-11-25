/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Frobenius
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorCoefficients
public import WeilConjectures.Mathlib.NumberTheory.Padics.RingHoms

/-!
# Continuous `ℤ_ℓ`-characters of the fundamental group and `lim_n H¹(Y, ℤ/ℓⁿ)`

Let `Y` be a connected scheme with a geometric point `s`, `G = π₁(Y, s)` and `ℓ` a prime. The
identifications `H¹(Y_ét, ℤ/ℓⁿ) ≃ Hom_cont(G, ℤ/ℓⁿ)` of blueprint
`lemma-invariant-additive-characters` are compatible with the reductions `ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom_map`), so they identify
`Hom_cont(G, ℤ_ℓ)` with the inverse limit of the groups `H¹(Y_ét, ℤ/ℓⁿ)` under the maps induced
by reduction (`AlgebraicGeometry.Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv`). The
identification is equivariant for an automorphism `e` of `Y`: precomposition with the induced
map `σ` of `G` corresponds to the transport of torsors along `e`
(`AlgebraicGeometry.Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv_comp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

variable (Y : Scheme.{u}) (l : ℕ) [Fact l.Prime]

/-- The constant sheaf `ℤ/ℓⁿ` on the small étale site of `Y`. -/
noncomputable abbrev constantZModPow (n : ℕ) : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod (l ^ n))))

/-- The reduction `ℤ/ℓⁿ⁺¹ ⟶ ℤ/ℓⁿ` of constant sheaves. -/
noncomputable abbrev constantZModPowReduction (n : ℕ) :
    constantZModPow Y l (n + 1) ⟶ constantZModPow Y l n :=
  (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map (AddCommGrpCat.ofHom
    (ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))).toAddMonoidHom.uliftMap)

/-- The inverse limit `lim_n H¹(Y_ét, ℤ/ℓⁿ)` under the maps induced by the reductions
`ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ`: the compatible families of classes. -/
abbrev sheafHOneLimit : Type (u + 1) :=
  {x : ∀ n : ℕ, Sheaf.H (constantZModPow Y l n) 1 //
    ∀ n, Sheaf.H.map (constantZModPowReduction Y l n) 1 (x (n + 1)) = x n}

/-- The compatible families of classes form a subgroup of the product of the groups
`H¹(Y_ét, ℤ/ℓⁿ)`, as the transition maps are additive. -/
def sheafHOneLimitAddSubgroup : AddSubgroup (∀ n : ℕ, Sheaf.H (constantZModPow Y l n) 1) where
  carrier := {x | ∀ n, Sheaf.H.map (constantZModPowReduction Y l n) 1 (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by
    rw [Pi.add_apply, map_add, hx n, hy n, Pi.add_apply]
  zero_mem' n := map_zero _
  neg_mem' {x} hx n := by
    rw [Pi.neg_apply, map_neg, hx n, Pi.neg_apply]

/-- The group structure on `lim_n H¹(Y_ét, ℤ/ℓⁿ)`, as a subgroup of the product. -/
noncomputable instance : AddCommGroup (sheafHOneLimit Y l) :=
  inferInstanceAs (AddCommGroup (sheafHOneLimitAddSubgroup Y l))

omit [Fact l.Prime] in
@[simp]
lemma sheafHOneLimit.coe_add (x y : sheafHOneLimit Y l) (n : ℕ) : (x + y).1 n = x.1 n + y.1 n :=
  rfl

omit [Fact l.Prime] in
@[simp]
lemma sheafHOneLimit.coe_zero (n : ℕ) : (0 : sheafHOneLimit Y l).1 n = 0 :=
  rfl

/-- `x ↦ x n`, the projection `lim_n H¹(Y_ét, ℤ/ℓⁿ) → H¹(Y_ét, ℤ/ℓⁿ)` as a group homomorphism. -/
def sheafHOneLimit.proj (n : ℕ) : sheafHOneLimit Y l →+ Sheaf.H (constantZModPow Y l n) 1 where
  toFun x := x.1 n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Continuous homomorphisms to `ZMod k` and to `ULift (ZMod k)`. -/
noncomputable def continuousMonoidHomULiftEquiv (G : Type u) [Group G] [TopologicalSpace G]
    (k : ℕ) :
    (G →ₜ* Multiplicative (ZMod k)) ≃ (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod k))) where
  toFun f := (⟨AddEquiv.ulift.symm.toAddMonoidHom.toMultiplicative,
    continuous_of_discreteTopology⟩ :
      Multiplicative (ZMod k) →ₜ* Multiplicative (ULift.{u + 1} (ZMod k))).comp f
  invFun f := (⟨AddEquiv.ulift.toAddMonoidHom.toMultiplicative,
    continuous_of_discreteTopology⟩ :
      Multiplicative (ULift.{u + 1} (ZMod k)) →ₜ* Multiplicative (ZMod k)).comp f
  left_inv _ := rfl
  right_inv _ := rfl

variable {Y} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

/-- The class in `H¹(Y_ét, ℤ/ℓⁿ⁺¹)` reduces to the class in `H¹(Y_ét, ℤ/ℓⁿ)` if and only if the
corresponding characters of `π₁(Y, s)` do. -/
lemma map_constantZModPowReduction_eq_iff (n : ℕ) (y : Sheaf.H (constantZModPow Y l (n + 1)) 1)
    (z : Sheaf.H (constantZModPow Y l n) 1) :
    Sheaf.H.map (constantZModPowReduction Y l n) 1 y = z ↔
      ∀ g, ZMod.castHom (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))
        (sheafHEquivContinuousMonoidHom _ s G y g).toAdd.down =
          (sheafHEquivContinuousMonoidHom _ s G z g).toAdd.down := by
  rw [← (sheafHEquivContinuousMonoidHom _ s G).injective.eq_iff]
  refine ⟨fun h g ↦ ?_, fun h ↦ ContinuousMonoidHom.ext fun g ↦ ?_⟩
  · rw [← h]
    exact (congrArg ULift.down (sheafHEquivContinuousMonoidHom_map s G (ZMod.castHom
      (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))).toAddMonoidHom.uliftMap y g)).symm
  · apply Multiplicative.toAdd.injective
    apply ULift.ext
    exact (congrArg ULift.down (sheafHEquivContinuousMonoidHom_map s G (ZMod.castHom
      (pow_dvd_pow l (Nat.le_add_right n 1)) (ZMod (l ^ n))).toAddMonoidHom.uliftMap y g)).trans
        (h g)

/-- Blueprint `lemma-invariant-additive-characters`: Continuous `ℤ_ℓ`-characters are compatible
finite-level classes.

For a connected scheme `Y` with geometric point `s`, `G = π₁(Y, s)` and a prime `ℓ`, the
bijection `Hom_cont(π₁(Y, s), ℤ_ℓ) ≃ lim_n H¹(Y_ét, ℤ/ℓⁿ)`: a continuous homomorphism is sent to
the family of classes of its reductions modulo `ℓⁿ` under
`H¹(Y_ét, ℤ/ℓⁿ) ≃ Hom_cont(π₁(Y, s), ℤ/ℓⁿ)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`), and the transition maps
of the inverse limit are induced by the reductions `ℤ/ℓⁿ⁺¹ → ℤ/ℓⁿ`. It is equivariant for the
Frobenius (`AlgebraicGeometry.Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv_comp`). -/
noncomputable def continuousMonoidHomPadicEquiv :
    (G →ₜ* Multiplicative ℤ_[l]) ≃ sheafHOneLimit Y l :=
  (PadicInt.continuousMonoidHomEquiv l G).trans (Equiv.subtypeEquiv
    (Equiv.piCongrRight fun n ↦ (continuousMonoidHomULiftEquiv G (l ^ n)).trans
      (sheafHEquivContinuousMonoidHom _ s G).symm) fun f ↦ by
    refine forall_congr' fun n ↦ ?_
    rw [Equiv.piCongrRight_apply, Equiv.piCongrRight_apply,
      map_constantZModPowReduction_eq_iff l s G]
    simp only [Pi.map_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
    rfl)

/-- The class at level `n` attached to a continuous homomorphism `b : π₁(Y, s) → ℤ_ℓ` is the
class of its reduction modulo `ℓⁿ`. -/
@[simp]
lemma sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv
    (b : G →ₜ* Multiplicative ℤ_[l]) (n : ℕ) (g : G) :
    (sheafHEquivContinuousMonoidHom _ s G ((continuousMonoidHomPadicEquiv l s G b).1 n)
      g).toAdd.down = PadicInt.toZModPow n (b g).toAdd := by
  change (sheafHEquivContinuousMonoidHom _ s G ((sheafHEquivContinuousMonoidHom _ s G).symm
    (continuousMonoidHomULiftEquiv G (l ^ n) ((PadicInt.continuousMonoidHomEquiv l G b).1 n)))
      g).toAdd.down = _
  rw [Equiv.apply_symm_apply]
  exact PadicInt.continuousMonoidHomEquiv_apply_coe b n g

/-- The bijection `Hom_cont(π₁(Y, s), ℤ_ℓ) ≃ lim_n H¹(Y_ét, ℤ/ℓⁿ)` sends products of characters
to sums of classes: at each level this is the additivity of
`H¹(Y_ét, ℤ/ℓⁿ) ≃ Hom_cont(π₁(Y, s), ℤ/ℓⁿ)`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom_add`). -/
lemma continuousMonoidHomPadicEquiv_mul (b b' : G →ₜ* Multiplicative ℤ_[l]) :
    continuousMonoidHomPadicEquiv l s G (b * b') =
      continuousMonoidHomPadicEquiv l s G b + continuousMonoidHomPadicEquiv l s G b' := by
  refine Subtype.ext (funext fun n ↦ (sheafHEquivContinuousMonoidHom _ s G).injective ?_)
  refine ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective (ULift.ext ?_)
  have h₁ := sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv l s G b n g
  have h₂ := sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv l s G b' n g
  have hadd := congrArg (fun χ ↦ (χ g).toAdd.down) (sheafHEquivContinuousMonoidHom_add _ s G
    ((continuousMonoidHomPadicEquiv l s G b).1 n) ((continuousMonoidHomPadicEquiv l s G b').1 n))
  simp only [ContinuousMonoidHom.mul_apply, toAdd_mul, ULift.add_down, h₁, h₂] at hadd
  refine (sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv l s G (b * b') n g).trans ?_
  rw [ContinuousMonoidHom.mul_apply, toAdd_mul, map_add]
  exact hadd.symm

/-- Blueprint `lemma-invariant-additive-characters`: Continuous `ℤ_ℓ`-characters are compatible
finite-level classes.

The group isomorphism `Hom_cont(π₁(Y, s), ℤ_ℓ) ≃+ lim_n H¹(Y_ét, ℤ/ℓⁿ)` underlying the
bijection `AlgebraicGeometry.Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv`; it is
equivariant for the Frobenius
(`AlgebraicGeometry.Scheme.EtaleTorsor.continuousMonoidHomPadicEquiv_comp`). -/
noncomputable def continuousMonoidHomPadicAddEquiv :
    Additive (G →ₜ* Multiplicative ℤ_[l]) ≃+ sheafHOneLimit Y l where
  toEquiv := Additive.toMul.trans (continuousMonoidHomPadicEquiv l s G)
  map_add' b b' := continuousMonoidHomPadicEquiv_mul l s G b.toMul b'.toMul

@[simp]
lemma continuousMonoidHomPadicAddEquiv_apply (b : Additive (G →ₜ* Multiplicative ℤ_[l])) :
    continuousMonoidHomPadicAddEquiv l s G b = continuousMonoidHomPadicEquiv l s G b.toMul :=
  rfl

variable {l}

variable (Y) in
/-- The action of an automorphism `e` of `Y` on `H¹(Y_ét, M)` in the torsor model: the class of a
torsor `P` is sent to the class of its transport `P ⟶ Y ⟶ Y` along `e`. -/
noncomputable def mapIsoH1 (M : Type (u + 1)) [AddCommGroup M] [Finite M] (e : Y ≅ Y) :
    Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1 →
    Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1 := fun x ↦
  classH1Equiv M Y (Quotient.map
    (fun t ↦ t.mapIso e) (fun _ _ h ↦ IsIsomorphic.mapIso h e) ((classH1Equiv M Y).symm x))

omit [ConnectedSpace Y] in
lemma mapIsoH1_classH1 {M : Type (u + 1)} [AddCommGroup M] [Finite M] (e : Y ≅ Y)
    (t : EtaleTorsor M Y) : mapIsoH1 Y M e (classH1 M Y ⟦t⟧) = classH1 M Y ⟦t.mapIso e⟧ := by
  rw [mapIsoH1, ← classH1Equiv_apply, Equiv.symm_apply_apply]
  rfl

/-- Blueprint `lemma-invariant-additive-characters`: Continuous `ℤ_ℓ`-characters are compatible
finite-level classes, the Frobenius equivariance.

Let `e` be an automorphism of `Y`, `τ : F_s ∘ e_* ≅ F_s` a transport of the fibre functor and
`σ : π₁(Y, s) → π₁(Y, s)` the induced continuous homomorphism, `τ (g • x) = σ g • τ x`. Then the
bijection `Hom_cont(π₁(Y, s), ℤ_ℓ) ≃ lim_n H¹(Y_ét, ℤ/ℓⁿ)` sends `b ∘ σ` to the transport along
`e` of the family attached to `b`. For the Frobenius of a curve over a finite field and a lift
`s` of Frobenius to the Weil group, `σ` is conjugation `g ↦ s⁻¹ g s` (up to the convention for
`s`), which is the Frobenius action `f ↦ [g ↦ f (s⁻¹ g s)]` of the blueprint. -/
theorem continuousMonoidHomPadicEquiv_comp (e : Y ≅ Y)
    (τ : FiniteEtale.mapIso e ⋙ fiber s ≅ fiber s) (σ : G →ₜ* G)
    (hσ : ∀ P (g : G) (x : (fiber s).obj ((FiniteEtale.mapIso e).obj P)),
      τ.hom.app P (g • x) = σ g • τ.hom.app P x)
    (b : G →ₜ* Multiplicative ℤ_[l]) (n : ℕ) :
    (continuousMonoidHomPadicEquiv l s G (b.comp σ)).1 n =
      mapIsoH1 Y _ e ((continuousMonoidHomPadicEquiv l s G b).1 n) := by
  obtain ⟨T, hT⟩ := (bijective_classH1 (M := ULift.{u + 1} (ZMod (l ^ n))) (Y := Y)).2
    ((continuousMonoidHomPadicEquiv l s G b).1 n)
  induction T using Quotient.inductionOn with | h t => ?_
  rw [← hT, mapIsoH1_classH1]
  apply (sheafHEquivContinuousMonoidHom _ s G).injective
  refine ContinuousMonoidHom.ext fun g ↦ Multiplicative.toAdd.injective (ULift.ext ?_)
  rw [sheafHEquivContinuousMonoidHom_classH1, monodromy_mapIso s G e τ σ hσ t g,
    ← sheafHEquivContinuousMonoidHom_classH1 s G t, hT,
    sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv,
    sheafHEquivContinuousMonoidHom_continuousMonoidHomPadicEquiv]
  rfl

end AlgebraicGeometry.Scheme.EtaleTorsor
