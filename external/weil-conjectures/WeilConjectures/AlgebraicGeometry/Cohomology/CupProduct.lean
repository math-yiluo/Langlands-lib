/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DualityPairing
public import WeilConjectures.AlgebraicGeometry.Modules.Ext
public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection

/-!
# Cup product with a class of degree zero

Let `X` be a scheme over a field `k` and `F`, `G` two `𝒪_X`-modules. A class `b ∈ H⁰(X, G)` is a
global section of `G`, i.e. a morphism `𝒪_X ⟶ G`, and the cup product with `b` is `H^q` of the
morphism `F ⟶ F ⊗ G`, `s ↦ s ⊗ b`. This gives the cup product
`H^q(X, F) × H⁰(X, G) → H^q(X, F ⊗ G)` (`AlgebraicGeometry.Scheme.Modules.cupH0`).

For the trace pairing of Serre duality, we take `G = Fᵛ ⊗ ω` and compose with the evaluation
`ev : F ⊗ (Fᵛ ⊗ ω) ⟶ ω`, `s ⊗ (φ ⊗ w) ↦ φ(s) w`
(`AlgebraicGeometry.Scheme.Modules.evalTensor`). The pairing
`H^q(F) × H⁰(Fᵛ ⊗ ω) → H^q(ω)`, `(a, b) ↦ H^q(ev)(a ∪ b)` is `H^q` of the morphism
`F ⟶ ω` corresponding to `b` under `H⁰(Fᵛ ⊗ ω) ≅ H⁰(Hom(F, ω)) = Hom(F, ω)`
(`AlgebraicGeometry.Scheme.Modules.H_map_evalTensor_cupH0`). Hence for `q = 1` and a linear
form `t : H¹(ω) → k`, the cup-product pairing `t ∘ H¹(ev) ∘ ∪` is the duality pairing
`AlgebraicGeometry.Scheme.Modules.dualPairingH` (`AlgebraicGeometry.Scheme.Modules.cupPairing_eq`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The morphism `F ⟶ F ⊗ G`, `s ↦ s ⊗ b`, attached to a global section `b : 𝒪_X ⟶ G`. -/
def tensorSectionHom (F : X.Modules) {G : X.Modules} (b : 𝟙_ X.Modules ⟶ G) : F ⟶ F ⊗ G :=
  (ρ_ F).inv ≫ F ◁ b

/-- `tensorSectionHom F b` sends a section `s` to `s ⊗ b`. -/
lemma tensorSectionHom_app (F : X.Modules) {G : X.Modules} (b : 𝟙_ X.Modules ⟶ G)
    (U : X.Opens) (s : Γ(F, U)) :
    (tensorSectionHom F b).app U s = tmulSection s (b.app U (unitSectionsEquiv U 1)) := by
  rw [tensorSectionHom, Hom.comp_app, ConcreteCategory.comp_apply, rightUnitor_inv_app,
    whiskerLeft_app_tmulSection]

lemma tensorSectionHom_add (F : X.Modules) {G : X.Modules} (b b' : 𝟙_ X.Modules ⟶ G) :
    tensorSectionHom F (b + b') = tensorSectionHom F b + tensorSectionHom F b' := by
  refine hom_ext _ _ fun U ↦ ?_
  ext s
  rw [Hom.add_app]
  change _ = (tensorSectionHom F b).app U s + (tensorSectionHom F b').app U s
  rw [tensorSectionHom_app, tensorSectionHom_app, tensorSectionHom_app, Hom.add_app]
  exact tmulSection_add _ _ _

lemma tensorSectionHom_comp_smulHom (F : X.Modules) {G : X.Modules} (b : 𝟙_ X.Modules ⟶ G)
    (r : Γ(X, ⊤)) :
    tensorSectionHom F (b ≫ G.smulHom r) = F.smulHom r ≫ tensorSectionHom F b := by
  refine hom_ext _ _ fun U ↦ ?_
  ext s
  rw [Hom.comp_app, ConcreteCategory.comp_apply, tensorSectionHom_app, tensorSectionHom_app,
    Hom.comp_app, ConcreteCategory.comp_apply, smulHom_app_apply, smulHom_app_apply,
    tmulSection_smul, smul_tmulSection]

/-- **Naturality of `s ↦ s ⊗ b`.** -/
lemma tensorSectionHom_naturality {F F' G G' : X.Modules} (f : F ⟶ F') (g : G ⟶ G')
    (b : 𝟙_ X.Modules ⟶ G) :
    f ≫ tensorSectionHom F' (b ≫ g) = tensorSectionHom F b ≫ (f ⊗ₘ g) := by
  simp only [tensorSectionHom, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    rightUnitor_inv_naturality_assoc, tensorHom_def']
  rw [← whisker_exchange_assoc, ← whisker_exchange]

/-- The morphism `𝒪_X ⟶ G` attached to a class of `H⁰(X, G)`. -/
def homOfHZero {G : X.Modules} (b : G.H 0) : 𝟙_ X.Modules ⟶ G :=
  (unitHomAddEquiv G).symm (H.zeroLinearEquiv G b)

lemma homOfHZero_add {G : X.Modules} (b b' : G.H 0) :
    homOfHZero (b + b') = homOfHZero b + homOfHZero b' := by
  rw [homOfHZero, homOfHZero, homOfHZero, map_add, map_add]

lemma homOfHZero_smul {G : X.Modules} (r : Γ(X, ⊤)) (b : G.H 0) :
    homOfHZero (r • b) = homOfHZero b ≫ G.smulHom r := by
  rw [homOfHZero, AddEquiv.symm_apply_eq, unitHomAddEquiv_comp, homOfHZero,
    AddEquiv.apply_symm_apply, smulHom_app_top_apply, LinearEquiv.map_smul]

lemma homOfHZero_map {G G' : X.Modules} (g : G ⟶ G') (b : G.H 0) :
    homOfHZero (H.map g 0 b) = homOfHZero b ≫ g := by
  rw [homOfHZero, AddEquiv.symm_apply_eq, unitHomAddEquiv_comp, homOfHZero,
    AddEquiv.apply_symm_apply, H.zeroLinearEquiv_map_homObj]

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **The cup product with a class of degree `0`**: for `a ∈ H^q(X, F)` and `b ∈ H⁰(X, G)`,
`a ∪ b ∈ H^q(X, F ⊗ G)` is the image of `a` under `H^q` of the morphism `F ⟶ F ⊗ G`,
`s ↦ s ⊗ b`. It is `k`-bilinear and natural in `F` and `G` (`cupH0_naturality`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
def cupH0 (F G : X.Modules) (q : ℕ) : F.H q →ₗ[k] G.H 0 →ₗ[k] (F ⊗ G).H q :=
  LinearMap.mk₂ k (fun a b ↦ H.map (tensorSectionHom F (homOfHZero b)) q a)
    (fun a a' b ↦ map_add _ a a')
    (fun c a b ↦ H.map_smul _ q (globalSectionsRingHom k c) a)
    (fun a b b' ↦ by rw [homOfHZero_add, tensorSectionHom_add, H.map_add_apply])
    (fun c a b ↦ by
      change H.map _ q a = globalSectionsRingHom k (X := X) c • _
      rw [smul_H_eq_globalSectionsRingHom_smul, homOfHZero_smul, tensorSectionHom_comp_smulHom,
        H.map_comp_apply, ← smul_H_eq_map, H.map_smul])

variable {k}

lemma cupH0_apply {F G : X.Modules} {q : ℕ} (a : F.H q) (b : G.H 0) :
    cupH0 k F G q a b = H.map (tensorSectionHom F (homOfHZero b)) q a :=
  rfl

/-- **Naturality of the cup product**: `H^q(f)(a) ∪ H⁰(g)(b) = H^q(f ⊗ g)(a ∪ b)`. -/
lemma cupH0_naturality {F F' G G' : X.Modules} (f : F ⟶ F') (g : G ⟶ G') {q : ℕ} (a : F.H q)
    (b : G.H 0) :
    cupH0 k F' G' q (H.map f q a) (H.map g 0 b) = H.map (f ⊗ₘ g) q (cupH0 k F G q a b) := by
  rw [cupH0_apply, cupH0_apply, homOfHZero_map, ← H.map_comp_apply, ← H.map_comp_apply,
    tensorSectionHom_naturality]

variable (F ω : X.Modules)

/-- **The evaluation** `ev : F ⊗ (Fᵛ ⊗ ω) ⟶ ω`, `s ⊗ (φ ⊗ w) ↦ φ(s) w`: the morphism
`Fᵛ ⊗ ω ⟶ Hom(F, ω)` (`dualTensorHom`) followed by the evaluation of the internal hom.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
def evalTensor : F ⊗ (Fᵛ ⊗ ω) ⟶ ω :=
  F ◁ dualTensorHom F ω ≫ (ihom.ev F).app ω

variable {F ω}

/-- The curried morphism `𝒪_X ⟶ Hom(F, N)` of `ψ : F ⟶ N` corresponds to the global section
`ψ` of `Hom(F, N)`. -/
lemma unitHomAddEquiv_curry (ψ : F ⟶ ω) :
    unitHomAddEquiv _ (MonoidalClosed.curry ((ρ_ F).hom ≫ ψ)) = homToΓHomObj F ω ψ := by
  have hc : MonoidalClosed.curry ((ρ_ F).hom ≫ ψ) =
      SheafOfModules.tensorHomEquiv F (𝟙_ X.Modules) ω ((ρ_ F).hom ≫ ψ) := by
    apply MonoidalClosed.uncurry_injective
    rw [MonoidalClosed.uncurry_curry]
    exact ((SheafOfModules.uncurry_eq_tensorHomEquiv_symm (A := F) (T := 𝟙_ X.Modules)
      (N := ω) _).trans
      (Equiv.symm_apply_apply _ _)).symm
  rw [hc]
  refine PresheafOfModules.hom_ext fun W ↦ ?_
  ext m
  change ((ρ_ F).hom ≫ ψ).val.app (op W.unop.left)
      ((SheafOfModules.tensorObjIsoSheafification F (𝟙_ X.Modules)).inv.val.app
        (op W.unop.left) ((toSheafifyTensor F (𝟙_ X.Modules)).app (op W.unop.left)
          (m ⊗ₜ (𝟙_ X.Modules).val.map W.unop.hom.op (1 : Γ(X, ⊤))))) =
    ψ.val.app (op W.unop.left) m
  have h1 : (𝟙_ X.Modules).val.map W.unop.hom.op (1 : Γ(X, ⊤)) =
      unitSectionsEquiv W.unop.left 1 :=
    map_one (X.presheaf.map W.unop.hom.op).hom
  rw [h1]
  change ψ.app W.unop.left ((ρ_ F).hom.app W.unop.left (tmulSection m _)) = _
  rw [rightUnitor_hom_app_tmulSection, one_smul]
  rfl

/-- **Evaluation after cup product with a global section of `Hom(F, N)`**: for a global section
`x` of `Hom(F, N)`, the composite `F ⟶ F ⊗ Hom(F, N) ⟶ N`, `s ↦ ev(s ⊗ x)`, is the morphism
`F ⟶ N` corresponding to `x`. -/
lemma tensorSectionHom_comp_ihom_ev (x : Γ(SheafOfModules.homObj (R := X.sheaf) F ω, ⊤)) :
    tensorSectionHom F ((unitHomAddEquiv _).symm x) ≫ (ihom.ev F).app ω =
      ΓHomObjAddEquiv F ω x := by
  obtain ⟨ψ, rfl⟩ := (ΓHomObjAddEquiv F ω).symm.surjective x
  have hψ : (ΓHomObjAddEquiv F ω).symm ψ = homToΓHomObj F ω ψ :=
    (ΓHomObjAddEquiv F ω).symm_apply_eq.2 (by
      apply homToΓHomObj_injective
      rw [homToΓHomObj_ΓHomObjAddEquiv])
  have hc : (unitHomAddEquiv (SheafOfModules.homObj (R := X.sheaf) F ω)).symm
      (homToΓHomObj F ω ψ) = MonoidalClosed.curry ((ρ_ F).hom ≫ ψ) :=
    (AddEquiv.symm_apply_eq _).2 (unitHomAddEquiv_curry ψ).symm
  rw [AddEquiv.apply_symm_apply, hψ, hc, tensorSectionHom, Category.assoc,
    ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry, Iso.inv_hom_id_assoc]

variable (t : Module.Dual k (ω.H 1))

/-- **The cup-product pairing** `H⁰(X, Fᵛ ⊗ ω) × H¹(X, F) → k`,
`(b, a) ↦ t(H¹(ev)(a ∪ b))`: cup product `H¹(F) ⊗ H⁰(Fᵛ ⊗ ω) → H¹(F ⊗ Fᵛ ⊗ ω)`, evaluation
`H¹(F ⊗ Fᵛ ⊗ ω) → H¹(ω)` and the linear form `t : H¹(ω) → k`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
def cupPairing (F : X.Modules) : (Fᵛ ⊗ ω).H 0 →ₗ[k] Module.Dual k (F.H 1) :=
  (cupH0 k F (Fᵛ ⊗ ω) 1).flip.compr₂ (t ∘ₗ H.mapLinearMap k (evalTensor F ω) 1)

lemma cupPairing_apply (b : (Fᵛ ⊗ ω).H 0) (a : F.H 1) :
    cupPairing t F b a = t (H.map (evalTensor F ω) 1 (cupH0 k F (Fᵛ ⊗ ω) 1 a b)) :=
  rfl

/-- **The cup-product pairing and the duality morphism.** For `a ∈ H^q(X, F)` and
`b ∈ H⁰(X, Fᵛ ⊗ ω)`, the class `H^q(ev)(a ∪ b) ∈ H^q(X, ω)` is the image of `a` under `H^q` of the
morphism `F ⟶ ω` corresponding to `b` under `H⁰(Fᵛ ⊗ ω) ⟶ H⁰(Hom(F, ω)) = Hom(F, ω)`
(`dualTensorHom`, an isomorphism `dualTensorHomIso` for invertible `ω`; `homObjHZeroAddEquiv`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
lemma H_map_evalTensor_cupH0 {q : ℕ} (a : F.H q) (b : (Fᵛ ⊗ ω).H 0) :
    H.map (evalTensor F ω) q (cupH0 k F (Fᵛ ⊗ ω) q a b) =
      H.map (homObjHZeroAddEquiv F ω (H.map (dualTensorHom F ω) 0 b)) q a := by
  rw [cupH0_apply, ← H.map_comp_apply]
  refine congrArg (fun φ ↦ H.map φ q a) ?_
  have h2 := tensorSectionHom_comp_ihom_ev (F := F) (ω := ω)
    (H.zeroLinearEquiv _ (H.map (dualTensorHom F ω) 0 b))
  have h : (unitHomAddEquiv _).symm (H.zeroLinearEquiv _ (H.map (dualTensorHom F ω) 0 b)) =
      homOfHZero b ≫ dualTensorHom F ω :=
    homOfHZero_map _ b
  rw [h, tensorSectionHom, Category.assoc, MonoidalCategory.whiskerLeft_comp,
    Category.assoc] at h2
  rw [evalTensor, tensorSectionHom, Category.assoc]
  exact h2

/-- **The cup-product pairing is the duality pairing**: under `Fᵛ ⊗ ω ⟶ Hom(F, ω)`
(`dualTensorHom`, an isomorphism `dualTensorHomIso` for invertible `ω`), the pairing
`t ∘ H¹(ev) ∘ ∪` is `dualPairingH t F`, i.e. `(b, a) ↦ t(H¹(φ_b)(a))` for the morphism
`φ_b : F ⟶ ω` corresponding to `b`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
lemma cupPairing_eq (F : X.Modules) :
    cupPairing t F = dualPairingH t F ∘ₗ H.mapLinearMap k (dualTensorHom F ω) 0 := by
  refine LinearMap.ext fun b ↦ LinearMap.ext fun a ↦ ?_
  rw [cupPairing_apply, H_map_evalTensor_cupH0]
  rfl

end AlgebraicGeometry.Scheme.Modules
