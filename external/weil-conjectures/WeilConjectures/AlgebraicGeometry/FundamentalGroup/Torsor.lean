/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Data.Fintype.Shrink
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent

/-!
# Torsors under a finite abelian group and the étale fundamental group

Let `Y` be a connected scheme with geometric point `s` and let `M` be a finite abelian group.
An `M`-torsor `P` over `Y` (`AlgebraicGeometry.Scheme.EtaleTorsor`) is a finite étale
`Y`-scheme, and `M` acts simply transitively on its geometric fibre `P_s`, commuting with
the action of the étale fundamental group `π₁(Y, s)`. Choosing `p ∈ P_s`, the element `g` of
`π₁(Y, s)` moves `p` to `f_P(g) +ᵥ p`; this defines a continuous homomorphism
`f_P : π₁(Y, s) → M`, independent of `p` because `M` is abelian, and depending only on the
isomorphism class of `P` (`AlgebraicGeometry.Scheme.EtaleTorsor.monodromy`). Through the
Galois correspondence `AlgebraicGeometry.Scheme.FiniteEtale.equivalenceContAction` the
construction `P ↦ f_P` is a bijection between isomorphism classes of `M`-torsors and
continuous homomorphisms `π₁(Y, s) → M`, and together with the torsor description of `H¹`
(`AlgebraicGeometry.Scheme.EtaleTorsor.classH1`) this identifies
`H¹(Y_ét, M)` with `Hom_cont(π₁(Y, s), M)`.

## Main definitions

- `AlgebraicGeometry.Scheme.EtaleTorsor.toFiniteEtale`: a torsor as a finite étale scheme.
- `AlgebraicGeometry.Scheme.EtaleTorsor.monodromy`: the continuous homomorphism
  `f_P : π₁(Y, s) → M` attached to a torsor.

## Main statements

- `AlgebraicGeometry.Scheme.EtaleTorsor.existsUnique_fiber_map_vaddHom`: `M` acts simply
  transitively on the geometric fibre of a torsor.
- `AlgebraicGeometry.Scheme.EtaleTorsor.bijective_monodromy`: the bijection between
  isomorphism classes of torsors and continuous homomorphisms.
- `AlgebraicGeometry.Scheme.EtaleTorsor.monodromy_eq_of_classH1_eq`: the canonical class in
  `H¹(Y_ét, M)` determines the monodromy character.
- `AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom` and
  `AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom_classH1`: the canonical
  identification `H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)`, sending the class of a torsor to its
  monodromy character.
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_equiv_sheafH_continuousMonoidHom`: the same, with
  the maps forgotten.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry.Scheme.EtaleTorsor

variable {M : Type (u + 1)} [AddCommGroup M] [Finite M] {Y : Scheme.{u}}

/-- The total space of an `M`-torsor over `Y`, as a finite étale `Y`-scheme. -/
def toFiniteEtale (t : EtaleTorsor M Y) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ t.π t.etale, t.isFinite⟩

@[simp]
lemma toFiniteEtale_obj_left (t : EtaleTorsor M Y) : t.toFiniteEtale.obj.left = t.P := rfl

@[simp]
lemma toFiniteEtale_obj_hom (t : EtaleTorsor M Y) : t.toFiniteEtale.obj.hom = t.π := rfl

/-- The action of `m : M` on the total space of a torsor, as an endomorphism of finite étale
`Y`-schemes. -/
def vaddHom (t : EtaleTorsor M Y) (m : M) : t.toFiniteEtale ⟶ t.toFiniteEtale :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (t.vadd m) (t.vadd_π m))

@[simp]
lemma vaddHom_hom_left (t : EtaleTorsor M Y) (m : M) : (t.vaddHom m).hom.left = t.vadd m := rfl

lemma vaddHom_zero (t : EtaleTorsor M Y) : t.vaddHom 0 = 𝟙 _ :=
  FiniteEtale.hom_ext t.zero_vadd

lemma vaddHom_add (t : EtaleTorsor M Y) (m n : M) :
    t.vaddHom (m + n) = t.vaddHom m ≫ t.vaddHom n :=
  FiniteEtale.hom_ext (t.add_vadd m n)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y)

section Fiber

open FiniteEtale

variable (t : EtaleTorsor M Y)

/-- Applying `m` and then `n` to a point of the geometric fibre is applying `m + n`. -/
lemma fiber_map_vaddHom_vaddHom (m n : M) (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom n) ((fiber s).map (t.vaddHom m) x) =
      (fiber s).map (t.vaddHom (m + n)) x := by
  rw [vaddHom_add, Functor.map_comp, FintypeCat.comp_apply]

lemma fiber_map_vaddHom_zero (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom 0) x = x := by
  rw [vaddHom_zero, CategoryTheory.Functor.map_id, FintypeCat.id_apply]

/-- `M` acts transitively on the geometric fibre of an `M`-torsor: the point `(y, x)` of
`P ×_Y P` comes from a unique summand of `∐_{m ∈ M} P ≅ P ×_Y P`, and a morphism from the
spectrum of a field into a coproduct factors through one summand. -/
lemma exists_fiber_map_vaddHom (x y : (fiber s).obj t.toFiniteEtale) :
    ∃ m, (fiber s).map (t.vaddHom m) x = y := by
  have := t.isIso_sigmaDesc
  let D := Sigma.desc fun m : M ↦
    pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by rw [t.vadd_π, Category.id_comp])
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Spec (.of Ω) ⟶ pullback t.π t.π,
      z ≫ pullback.fst _ _ = y.left ∧ z ≫ pullback.snd _ _ = x.left :=
    ⟨pullback.lift y.left x.left ((fiber_left_comp s y).trans (fiber_left_comp s x).symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  let w := z ≫ inv D
  obtain ⟨m, p, hp⟩ : ∃ (m : M) (p : t.P), Sigma.ι (fun _ : M ↦ t.P) m p = w default :=
    (sigmaOpenCover fun _ : M ↦ t.P).exists_eq (w default)
  have hrange : Set.range w.base ⊆ Set.range (Sigma.ι (fun _ : M ↦ t.P) m).base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact ⟨p, hp⟩
  have : IsOpenImmersion (Sigma.ι (fun _ : M ↦ t.P) m) :=
    (sigmaOpenCover fun _ : M ↦ t.P).map_prop (m : (sigmaOpenCover fun _ : M ↦ t.P).I₀)
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Sigma.ι (fun _ : M ↦ t.P) m = w :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have h1 : l ≫ pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by rw [t.vadd_π, Category.id_comp]) = z := by
    rw [← Sigma.ι_comp_desc (fun m : M ↦ pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by rw [t.vadd_π, Category.id_comp])) m, ← Category.assoc, hl]
    simp [w, D]
  have hfst := congrArg (· ≫ pullback.fst t.π t.π) h1
  have hsnd := congrArg (· ≫ pullback.snd t.π t.π) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id, hz1, hz2]
    at hfst hsnd
  refine ⟨m, fiber_ext s ?_⟩
  change x.left ≫ t.vadd m = y.left
  exact hsnd ▸ hfst

/-- `M` acts freely on the geometric fibre of an `M`-torsor: the summands of
`∐_{m ∈ M} P ≅ P ×_Y P` are disjoint. -/
lemma eq_of_fiber_map_vaddHom_eq (x : (fiber s).obj t.toFiniteEtale) {m n : M}
    (h : (fiber s).map (t.vaddHom m) x = (fiber s).map (t.vaddHom n) x) : m = n := by
  have := t.isIso_sigmaDesc
  let x' : Spec (.of Ω) ⟶ t.P := x.left
  have h' : x' ≫ t.vadd m = x' ≫ t.vadd n := congrArg CommaMorphism.left h
  have h2 : x' ≫ Sigma.ι (fun _ : M ↦ t.P) m = x' ≫ Sigma.ι (fun _ : M ↦ t.P) n := by
    rw [← cancel_mono (Sigma.desc fun m : M ↦
      pullback.lift (f := t.π) (g := t.π) (t.vadd m) (𝟙 t.P)
      (by rw [t.vadd_π, Category.id_comp]))]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, Sigma.ι_comp_desc_assoc, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id, h']
  have h3 := congrArg (fun f ↦ f (default : Spec (.of Ω))) h2
  simp only [Scheme.Hom.comp_apply] at h3
  have := (sigmaι_eq_iff (fun _ : M ↦ t.P) m n _ _).mp h3
  exact congrArg Sigma.fst this

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

`M` acts simply transitively on the geometric fibre `P_s` of an `M`-torsor `P`. -/
lemma existsUnique_fiber_map_vaddHom (x y : (fiber s).obj t.toFiniteEtale) :
    ∃! m, (fiber s).map (t.vaddHom m) x = y := by
  obtain ⟨m, hm⟩ := t.exists_fiber_map_vaddHom s x y
  exact ⟨m, hm, fun n hn ↦ t.eq_of_fiber_map_vaddHom_eq s x (hn.trans hm.symm)⟩

/-- The geometric fibre of an `M`-torsor is nonempty, as its structure morphism is
surjective. -/
lemma nonempty_fiber : Nonempty ((fiber s).obj t.toFiniteEtale) := by
  have := t.etale
  have := t.surjective
  obtain ⟨x, hx⟩ := t.π.surjective (s default)
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed t.π s x hx
  exact ⟨Over.homMk l hl⟩

end Fiber

section Monodromy

open FiniteEtale

open scoped FintypeCatDiscrete

variable [ConnectedSpace Y] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  (t : EtaleTorsor M Y)

/-- The action of the fundamental group on the geometric fibre of a torsor commutes with the
action of `M`. -/
lemma fiber_map_vaddHom_smul (m : M) (g : G) (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom m) (g • x) = g • (fiber s).map (t.vaddHom m) x :=
  IsNaturalSMul.naturality g _ x

/-- The function underlying the monodromy character `f_P` of a torsor `P`: `f_P(g)` is the
element of `M` moving a chosen point `p` of the geometric fibre to `g • p`. -/
noncomputable def monodromyFun (g : G) : M :=
  (t.exists_fiber_map_vaddHom s (t.nonempty_fiber s).some (g • (t.nonempty_fiber s).some)).choose

/-- `f_P(g)` moves every point `x` of the geometric fibre to `g • x`; it does not depend on the
chosen point because `M` is abelian. -/
lemma fiber_map_vaddHom_monodromyFun (g : G) (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom (t.monodromyFun s G g)) x = g • x := by
  have h₀ := (t.exists_fiber_map_vaddHom s (t.nonempty_fiber s).some
    (g • (t.nonempty_fiber s).some)).choose_spec
  obtain ⟨n, rfl⟩ := t.exists_fiber_map_vaddHom s (t.nonempty_fiber s).some x
  rw [← fiber_map_vaddHom_smul, ← monodromyFun] at *
  rw [← h₀, fiber_map_vaddHom_vaddHom, fiber_map_vaddHom_vaddHom, add_comm]

lemma monodromyFun_eq_iff (g : G) (x : (fiber s).obj t.toFiniteEtale) (m : M) :
    t.monodromyFun s G g = m ↔ (fiber s).map (t.vaddHom m) x = g • x := by
  refine ⟨fun h ↦ h ▸ t.fiber_map_vaddHom_monodromyFun s G g x, fun h ↦ ?_⟩
  exact t.eq_of_fiber_map_vaddHom_eq s x ((t.fiber_map_vaddHom_monodromyFun s G g x).trans h.symm)

variable [TopologicalSpace M] [DiscreteTopology M]

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

The monodromy character `f_P : π₁(Y, s) → M` of an `M`-torsor `P`, characterised by
`g • p = f_P(g) +ᵥ p` for `p` in the geometric fibre `P_s`
(`AlgebraicGeometry.Scheme.EtaleTorsor.fiber_map_vaddHom_monodromy`): a continuous
homomorphism, as the stabilisers of the points of `P_s` are open. -/
noncomputable def monodromy : G →ₜ* Multiplicative M where
  toFun g := Multiplicative.ofAdd (t.monodromyFun s G g)
  map_one' := by
    rw [ofAdd_eq_one, t.monodromyFun_eq_iff s G 1 (t.nonempty_fiber s).some, one_smul]
    exact t.fiber_map_vaddHom_zero s _
  map_mul' g h := by
    let p := (t.nonempty_fiber s).some
    rw [← ofAdd_add]
    congr 1
    rw [t.monodromyFun_eq_iff s G _ p, mul_smul, ← t.fiber_map_vaddHom_monodromyFun s G h p,
      ← fiber_map_vaddHom_smul, ← t.fiber_map_vaddHom_monodromyFun s G g p,
      fiber_map_vaddHom_vaddHom, add_comm]
  continuous_toFun := by
    refine continuous_discrete_rng.mpr fun m ↦ ?_
    let p := (t.nonempty_fiber s).some
    have : (fun g ↦ Multiplicative.ofAdd (t.monodromyFun s G g)) ⁻¹' {m} =
        (fun g : G ↦ g • p) ⁻¹' {(fiber s).map (t.vaddHom m.toAdd) p} := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      rw [eq_comm (b := (fiber s).map _ p), ← t.monodromyFun_eq_iff s G g p,
        ← Multiplicative.toAdd.injective.eq_iff, toAdd_ofAdd]
    rw [this]
    exact (continuous_id.smul continuous_const).isOpen_preimage _ (isOpen_discrete _)

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

The defining property of the monodromy character: `g • p = f_P(g) +ᵥ p`. -/
lemma fiber_map_vaddHom_monodromy (g : G) (x : (fiber s).obj t.toFiniteEtale) :
    (fiber s).map (t.vaddHom (t.monodromy s G g).toAdd) x = g • x :=
  t.fiber_map_vaddHom_monodromyFun s G g x

lemma monodromy_eq_iff (g : G) (x : (fiber s).obj t.toFiniteEtale) (m : M) :
    t.monodromy s G g = Multiplicative.ofAdd m ↔ (fiber s).map (t.vaddHom m) x = g • x := by
  rw [← t.monodromyFun_eq_iff s G g x]
  exact ⟨fun h ↦ congrArg Multiplicative.toAdd h, fun h ↦ congrArg Multiplicative.ofAdd h⟩

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

Isomorphic torsors have the same monodromy character. -/
lemma monodromy_eq_of_isIsomorphic {t₁ t₂ : EtaleTorsor M Y} (h : t₁.IsIsomorphic t₂) :
    t₁.monodromy s G = t₂.monodromy s G := by
  obtain ⟨φ, hπ, hv⟩ := h
  let Φ : t₁.toFiniteEtale ⟶ t₂.toFiniteEtale :=
    ObjectProperty.homMk (MorphismProperty.Over.homMk φ.hom hπ)
  have hΦ (m : M) : t₁.vaddHom m ≫ Φ = Φ ≫ t₂.vaddHom m := FiniteEtale.hom_ext (hv m)
  ext g
  let p := (t₁.nonempty_fiber s).some
  refine congrArg Multiplicative.toAdd ((t₂.monodromy_eq_iff s G g ((fiber s).map Φ p)
    (t₁.monodromy s G g).toAdd).mpr ?_).symm
  rw [← FintypeCat.comp_apply, ← Functor.map_comp, ← hΦ, Functor.map_comp,
    FintypeCat.comp_apply, t₁.fiber_map_vaddHom_monodromy s G g p]
  exact IsNaturalSMul.naturality g Φ p

end Monodromy

section Bijection

open FiniteEtale

open scoped FintypeCatDiscrete

variable [ConnectedSpace Y] (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]
  [TopologicalSpace M] [DiscreteTopology M]

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

Torsors with the same monodromy character are isomorphic: matching the points `m +ᵥ p₁` and
`m +ᵥ p₂` of the geometric fibres is an isomorphism of `π₁(Y, s)`-sets commuting with `M`, so
it comes from an isomorphism of finite étale `Y`-schemes by the Galois correspondence. -/
lemma isIsomorphic_of_monodromy_eq {t₁ t₂ : EtaleTorsor M Y}
    (h : t₁.monodromy s G = t₂.monodromy s G) : t₁.IsIsomorphic t₂ := by
  let p₁ := (t₁.nonempty_fiber s).some
  let p₂ := (t₂.nonempty_fiber s).some
  choose d₁ hd₁ using t₁.exists_fiber_map_vaddHom s p₁
  choose d₂ hd₂ using t₂.exists_fiber_map_vaddHom s p₂
  have hd₁' (m : M) : d₁ ((fiber s).map (t₁.vaddHom m) p₁) = m :=
    t₁.eq_of_fiber_map_vaddHom_eq s p₁ (hd₁ _)
  have hd₂' (m : M) : d₂ ((fiber s).map (t₂.vaddHom m) p₂) = m :=
    t₂.eq_of_fiber_map_vaddHom_eq s p₂ (hd₂ _)
  let ψ : (fiber s).obj t₁.toFiniteEtale → (fiber s).obj t₂.toFiniteEtale :=
    fun x ↦ (fiber s).map (t₂.vaddHom (d₁ x)) p₂
  let e : (fiber s).obj t₁.toFiniteEtale ≃ (fiber s).obj t₂.toFiniteEtale :=
    { toFun := ψ
      invFun y := (fiber s).map (t₁.vaddHom (d₂ y)) p₁
      left_inv x := by simp only [ψ, hd₂', hd₁]
      right_inv y := by simp only [ψ, hd₁', hd₂] }
  have hvadd (m : M) (x : (fiber s).obj t₁.toFiniteEtale) :
      ψ ((fiber s).map (t₁.vaddHom m) x) = (fiber s).map (t₂.vaddHom m) (ψ x) := by
    have : (fiber s).map (t₁.vaddHom m) x = (fiber s).map (t₁.vaddHom (d₁ x + m)) p₁ := by
      rw [← fiber_map_vaddHom_vaddHom, hd₁]
    simp only [ψ]
    rw [this, hd₁', fiber_map_vaddHom_vaddHom]
  have hsmul (g : G) (x : (fiber s).obj t₁.toFiniteEtale) : ψ (g • x) = g • ψ x := by
    rw [← t₁.fiber_map_vaddHom_monodromy s G g x, hvadd, h,
      t₂.fiber_map_vaddHom_monodromy s G g (ψ x)]
  let E := equivalenceContAction s G
  let I : E.functor.obj t₁.toFiniteEtale ≅ E.functor.obj t₂.toFiniteEtale :=
    ObjectProperty.isoMk _ (Action.mkIso (FintypeCat.equivEquivIso e) fun g ↦
      FintypeCat.hom_ext _ _ fun x ↦ hsmul g x)
  let Φ := E.fullyFaithfulFunctor.preimageIso I
  have hΦ (x : (fiber s).obj t₁.toFiniteEtale) : (fiber s).map Φ.hom x = ψ x := by
    have := congrArg (fun f ↦ f.hom.hom x) (E.fullyFaithfulFunctor.map_preimage I.hom)
    exact this
  refine ⟨⟨Φ.hom.hom.left, Φ.inv.hom.left, congrArg (fun f ↦ f.hom.left) Φ.hom_inv_id,
    congrArg (fun f ↦ f.hom.left) Φ.inv_hom_id⟩, hom_left_comp Φ.hom, fun m ↦ ?_⟩
  have : t₁.vaddHom m ≫ Φ.hom = Φ.hom ≫ t₂.vaddHom m := by
    refine (fiber s).map_injective (FintypeCat.hom_ext _ _ fun x ↦ ?_)
    rw [Functor.map_comp, Functor.map_comp, FintypeCat.comp_apply, FintypeCat.comp_apply, hΦ,
      hΦ, hvadd]
  exact congrArg (fun f ↦ f.hom.left) this

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

Every continuous homomorphism `f : π₁(Y, s) → M` is the monodromy character of a torsor:
`M` with `π₁(Y, s)` acting by `g • a = f(g) + a` is a finite continuous `π₁(Y, s)`-set on which
the translations act by automorphisms, and the corresponding finite étale `Y`-scheme with the
induced action of `M` is a torsor. -/
lemma exists_monodromy_eq (φ : G →ₜ* Multiplicative M) :
    ∃ t : EtaleTorsor M Y, t.monodromy s G = φ := by
  let V := Shrink.{u} M
  let eM : M ≃ V := equivShrink.{u, u + 1} M
  let _ : MulAction G V :=
    { smul g v := eM ((φ g).toAdd + eM.symm v)
      one_smul v := by simp [HSMul.hSMul]
      mul_smul g h v := by simp [HSMul.hSMul, add_assoc] }
  have hsmul (g : G) (v : V) : g • v = eM ((φ g).toAdd + eM.symm v) := rfl
  let X : ContAction FintypeCat.{u} G :=
    ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of V), by
      constructor
      have : DiscreteTopology ((forget₂ (Action FintypeCat G) TopCat).obj
        (Action.FintypeCat.ofMulAction G (FintypeCat.of V))) := ⟨rfl⟩
      have : DiscreteTopology ((forget₂ FintypeCat TopCat).obj
        (Action.FintypeCat.ofMulAction G (FintypeCat.of V)).V) := ⟨rfl⟩
      refine continuous_prod_of_discrete_right.mpr fun v ↦
        continuous_discrete_rng.mpr fun w ↦ ?_
      exact (isOpen_discrete ((fun a : Multiplicative M ↦ (eM (a.toAdd + eM.symm v) : V)) ⁻¹'
        {(w : V)})).preimage φ.continuous⟩
  let τ (n : M) : X ⟶ X := ObjectProperty.homMk
    { hom := FintypeCat.homMk fun v ↦ eM (n + eM.symm v)
      comm g := FintypeCat.hom_ext _ _ fun v ↦ by
        change eM (n + eM.symm (eM ((φ g).toAdd + eM.symm v))) =
          eM ((φ g).toAdd + eM.symm (eM (n + eM.symm v)))
        simp only [Equiv.symm_apply_apply, add_left_comm] }
  have hτ (n : M) (v : V) : (τ n).hom.hom v = eM (n + eM.symm v) := rfl
  let E := equivalenceContAction s G
  let P := E.inverse.obj X
  let c := E.counitIso.app X
  let T (n : M) : P ⟶ P := E.functor.preimage (c.hom ≫ τ n ≫ c.inv)
  have hT (n : M) : E.functor.map (T n) = c.hom ≫ τ n ≫ c.inv := E.functor.map_preimage _
  have hT0 : T 0 = 𝟙 P := E.functor.map_injective <| by
    rw [hT, E.functor.map_id]
    have : τ 0 = 𝟙 X := ObjectProperty.hom_ext _ (Action.Hom.ext (FintypeCat.hom_ext _ _
      fun v ↦ by
        change eM (0 + eM.symm v) = v
        rw [zero_add]
        exact eM.apply_symm_apply v))
    simp [this]
    rfl
  have hTadd (m n : M) : T (m + n) = T m ≫ T n := E.functor.map_injective <| by
    rw [hT, E.functor.map_comp, hT, hT]
    have : τ (m + n) = τ m ≫ τ n := ObjectProperty.hom_ext _ (Action.Hom.ext
      (FintypeCat.hom_ext _ _ fun v ↦ by
        change eM ((m + n) + eM.symm v) = eM (n + eM.symm (eM (m + eM.symm v)))
        simp [add_left_comm, add_assoc]))
    simp [this]
  let cV := (ObjectProperty.ι _ ⋙ Action.forget _ _).mapIso c
  let β : (fiber s).obj P → V := fun x ↦ cV.hom x
  have hβ : Function.Injective β := (FintypeCat.equivEquivIso.symm cV).injective
  have hβT (n : M) (x : (fiber s).obj P) :
      β ((fiber s).map (T n) x) = eM (n + eM.symm (β x)) := by
    have h₁ : (fiber s).map (T n) x = (E.functor.map (T n)).hom.hom x := rfl
    rw [h₁, hT]
    change ((c.hom ≫ τ n ≫ c.inv) ≫ c.hom).hom.hom x = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hβsmul (g : G) (x : (fiber s).obj P) : β (g • x) = g • β x := by
    have := congrArg (fun f ↦ f.hom x) (c.hom.hom.comm g)
    exact this
  have hne : Nonempty ((fiber s).obj P) := ⟨c.inv.hom.hom (eM 0)⟩
  have huniq (x y : (fiber s).obj P) : ∃! n, (fiber s).map (T n) x = y := by
    refine ⟨eM.symm (β y) - eM.symm (β x), hβ ?_, fun n hn ↦ ?_⟩
    · rw [hβT, sub_add_cancel, Equiv.apply_symm_apply]
    · have := congrArg β hn
      rw [hβT] at this
      rw [← this, Equiv.symm_apply_apply, add_sub_cancel_right]
  let t : EtaleTorsor M Y :=
    { P := P.obj.left
      π := P.obj.hom
      isFinite := P.property
      etale := P.obj.prop
      surjective := surjective_of_nonempty_fiber s P hne
      vadd n := (T n).hom.left
      vadd_π n := hom_left_comp (T n)
      zero_vadd := by rw [hT0]; rfl
      add_vadd m n := by rw [hTadd]; rfl
      isIso_sigmaDesc := isIso_sigmaDesc_of_existsUnique s P T huniq }
  refine ⟨t, ContinuousMonoidHom.ext fun g ↦ ?_⟩
  obtain ⟨x⟩ := hne
  refine (t.monodromy_eq_iff s G g x (φ g).toAdd).mpr (hβ ?_)
  change β ((fiber s).map (T (φ g).toAdd) x) = β (g • x)
  rw [hβT, hβsmul, hsmul]

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

The monodromy character `P ↦ f_P` is a bijection between isomorphism classes of `M`-torsors
over `Y` and continuous homomorphisms `π₁(Y, s) → M`. -/
theorem bijective_monodromy :
    Function.Bijective (Quotient.lift (s := EtaleTorsor.setoid M Y) (fun t ↦ t.monodromy s G)
      fun _ _ h ↦ monodromy_eq_of_isIsomorphic s G h) := by
  refine ⟨fun a b h ↦ ?_, fun φ ↦ ?_⟩
  · induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound (isIsomorphic_of_monodromy_eq s G h)
  · obtain ⟨t, rfl⟩ := exists_monodromy_eq s G φ
    exact ⟨⟦t⟧, rfl⟩

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

Torsors with the same class in `H¹(Y_ét, M)` under the canonical class map
`AlgebraicGeometry.Scheme.EtaleTorsor.classH1` have the same monodromy character. -/
theorem monodromy_eq_of_classH1_eq {t₁ t₂ : EtaleTorsor M Y}
    (h : classH1 M Y ⟦t₁⟧ = classH1 M Y ⟦t₂⟧) : t₁.monodromy s G = t₂.monodromy s G :=
  monodromy_eq_of_isIsomorphic s G (Quotient.exact (injective_classH1 h))

variable (M) in
/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

**`H¹(Y_ét, M) = Hom_cont(π₁(Y, s), M)`.** For a connected scheme `Y` with geometric point `s`,
`G = π₁(Y, s)` the étale fundamental group and `M` a finite abelian group, the canonical bijection
`H¹(Y_ét, M) ≃ Hom_cont(π₁(Y, s), M)`: the inverse of the class bijection
`AlgebraicGeometry.Scheme.EtaleTorsor.classH1Equiv` followed by the monodromy character
`P ↦ f_P` (`AlgebraicGeometry.Scheme.EtaleTorsor.bijective_monodromy`), where
`g • p = f_P(g) +ᵥ p` for `p` in the geometric fibre `P_s`. -/
noncomputable def sheafHEquivContinuousMonoidHom :
    Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of M)) 1 ≃ (G →ₜ* Multiplicative M) :=
  (classH1Equiv M Y).symm.trans (Equiv.ofBijective _ (bijective_monodromy (M := M) s G))

/-- The class of a torsor `P` in `H¹(Y_ét, M)` corresponds to its monodromy character `f_P`. -/
theorem sheafHEquivContinuousMonoidHom_classH1 (t : EtaleTorsor M Y) :
    sheafHEquivContinuousMonoidHom M s G (classH1 M Y ⟦t⟧) = t.monodromy s G := by
  rw [sheafHEquivContinuousMonoidHom, Equiv.trans_apply, ← classH1Equiv_apply,
    Equiv.symm_apply_apply]
  rfl

/-- Blueprint `lemma-invariant-additive-characters`: Abelian case: torsors, characters and H^1.

Let `Y` be a connected scheme with geometric point `s`, let `G = π₁(Y, s)` be the étale
fundamental group (a fundamental group of the fibre functor on finite étale `Y`-schemes) and
let `M` be a finite abelian group. Then the canonical bijections `c = classH1Equiv` from torsor
classes to `H¹(Y_ét, M)` and `e = sheafHEquivContinuousMonoidHom` from `H¹(Y_ét, M)` to
`Hom_cont(π₁(Y, s), M)` satisfy: the class of a torsor vanishes exactly when the torsor has a
section, and the character `e(c(P))` describes the action of `π₁(Y, s)` on the geometric fibre:
`g • p = e(c(P))(g) +ᵥ p`. This statement forgets the two maps. -/
theorem exists_equiv_sheafH_continuousMonoidHom :
    ∃ (c : Quotient (EtaleTorsor.setoid M Y) ≃ Sheaf.H
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)) 1)
      (e : Sheaf.H ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of M)) 1 ≃ (G →ₜ* Multiplicative M)),
      (∀ t : EtaleTorsor M Y, c ⟦t⟧ = 0 ↔ ∃ σ : Y ⟶ t.P, σ ≫ t.π = 𝟙 Y) ∧
      ∀ (t : EtaleTorsor M Y) (g : G) (p : (fiber s).obj t.toFiniteEtale),
        (fiber s).map (t.vaddHom (e (c ⟦t⟧) g).toAdd) p = g • p :=
  ⟨classH1Equiv M Y, sheafHEquivContinuousMonoidHom M s G, classH1_eq_zero_iff, fun t g p ↦ by
    rw [classH1Equiv_apply, sheafHEquivContinuousMonoidHom_classH1]
    exact t.fiber_map_vaddHom_monodromy s G g p⟩

end Bijection

end AlgebraicGeometry.Scheme.EtaleTorsor
