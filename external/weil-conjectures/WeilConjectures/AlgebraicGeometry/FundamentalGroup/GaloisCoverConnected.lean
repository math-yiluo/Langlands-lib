/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.OpenSubgroups
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorMonodromyHom
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

/-!
# Connected subcovers of Galois covers

Let `Y` be a connected scheme and `c : P ⟶ Y` a finite étale Galois cover with group `G`
(`AlgebraicGeometry.Scheme.GaloisCover`); the total space `P` need not be connected. A connected
component `P₀` of `P` is again a Galois cover of `Y`, with group the stabilizer `H ≤ G` of `P₀`.
In terms of the Galois correspondence: the geometric fibre `P_s` is a `G`-torsor with a commuting
action of `π₁(Y, s)`; a `π₁`-orbit `O ⊆ P_s` corresponds to a connected finite étale `Y`-scheme
`P₀` with a morphism to `P`, and the subgroup `H = {g ∈ G | g • O = O}` acts simply transitively
on `O` (blueprint `lemma-cohomology-near-two-transverse-divisors--1`, dévissage step).

## Main statements

- `AlgebraicGeometry.Scheme.GaloisCover.exists_connected_subcover`: a Galois cover of a connected
  scheme with group `G` admits a connected Galois subcover with group a subgroup of `G`.
- `AlgebraicGeometry.Scheme.GaloisCover.existsUnique_fiber_map_smulHom`: `G` acts simply
  transitively on the geometric fibres of a Galois cover with group `G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.GaloisCover

open FiniteEtale PreGaloisCategory

variable {Y : Scheme.{u}} {G : Type (u + 1)} [Group G] [Finite G]

/-- The total space of a Galois cover, as a finite étale `Y`-scheme. -/
def toFiniteEtale (c : Y.GaloisCover G) : Y.FiniteEtale :=
  ⟨MorphismProperty.Over.mk ⊤ c.π c.etale, c.isFinite⟩

/-- The action of `g : G` on the total space of a Galois cover, as an endomorphism of finite
étale `Y`-schemes. -/
def smulHom (c : Y.GaloisCover G) (g : G) : c.toFiniteEtale ⟶ c.toFiniteEtale :=
  ObjectProperty.homMk (MorphismProperty.Over.homMk (c.smul g) (c.smul_π g))

/-- The unit of `G` acts as the identity endomorphism. -/
lemma smulHom_one (c : Y.GaloisCover G) : c.smulHom 1 = 𝟙 _ :=
  FiniteEtale.hom_ext c.one_smul

/-- The action of `G` on the total space is a left action. -/
lemma smulHom_mul (c : Y.GaloisCover G) (g h : G) :
    c.smulHom (g * h) = c.smulHom h ≫ c.smulHom g :=
  FiniteEtale.hom_ext (c.mul_smul g h)

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) (c : Y.GaloisCover G)

/-- The unit of `G` acts trivially on the geometric fibre. -/
lemma fiber_map_smulHom_one (x : (fiber s).obj c.toFiniteEtale) :
    (fiber s).map (c.smulHom 1) x = x := by
  rw [smulHom_one, CategoryTheory.Functor.map_id, FintypeCat.id_apply]

/-- The action of `G` on the geometric fibre is a left action. -/
lemma fiber_map_smulHom_mul (g h : G) (x : (fiber s).obj c.toFiniteEtale) :
    (fiber s).map (c.smulHom (g * h)) x =
      (fiber s).map (c.smulHom g) ((fiber s).map (c.smulHom h) x) := by
  rw [smulHom_mul, Functor.map_comp, FintypeCat.comp_apply]

/-- `G` acts transitively on the geometric fibre of a Galois cover: the point `(y, x)` of
`P ×_Y P` comes from a summand of `∐_{g ∈ G} P ≅ P ×_Y P`, and a morphism from the spectrum of a
field into a coproduct factors through one summand. -/
lemma exists_fiber_map_smulHom (x y : (fiber s).obj c.toFiniteEtale) :
    ∃ g, (fiber s).map (c.smulHom g) x = y := by
  have := c.isIso_sigmaDesc
  let D := Sigma.desc fun g : G ↦
    pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P)
      (by rw [c.smul_π, Category.id_comp])
  obtain ⟨z, hz1, hz2⟩ : ∃ z : Spec (.of Ω) ⟶ pullback c.π c.π,
      z ≫ pullback.fst _ _ = y.left ∧ z ≫ pullback.snd _ _ = x.left :=
    ⟨pullback.lift y.left x.left ((fiber_left_comp s y).trans (fiber_left_comp s x).symm),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  let w := z ≫ inv D
  obtain ⟨g, p, hp⟩ : ∃ (g : G) (p : c.P), Sigma.ι (fun _ : G ↦ c.P) g p = w default :=
    (sigmaOpenCover fun _ : G ↦ c.P).exists_eq (w default)
  have hrange : Set.range w.base ⊆ Set.range (Sigma.ι (fun _ : G ↦ c.P) g).base := by
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a default]
    exact ⟨p, hp⟩
  have : IsOpenImmersion (Sigma.ι (fun _ : G ↦ c.P) g) :=
    (sigmaOpenCover fun _ : G ↦ c.P).map_prop (g : (sigmaOpenCover fun _ : G ↦ c.P).I₀)
  obtain ⟨l, hl⟩ : ∃ l, l ≫ Sigma.ι (fun _ : G ↦ c.P) g = w :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have h1 : l ≫ pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P)
      (by rw [c.smul_π, Category.id_comp]) = z := by
    rw [← Sigma.ι_comp_desc (fun g : G ↦ pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P)
      (by rw [c.smul_π, Category.id_comp])) g, ← Category.assoc, hl]
    simp [w, D]
  have hfst := congrArg (· ≫ pullback.fst c.π c.π) h1
  have hsnd := congrArg (· ≫ pullback.snd c.π c.π) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id, hz1, hz2]
    at hfst hsnd
  refine ⟨g, fiber_ext s ?_⟩
  rw [fiber_map_left]
  exact hsnd ▸ hfst

/-- `G` acts freely on the geometric fibre of a Galois cover: the summands of
`∐_{g ∈ G} P ≅ P ×_Y P` are disjoint. -/
lemma eq_of_fiber_map_smulHom_eq (x : (fiber s).obj c.toFiniteEtale) {g h : G}
    (hgh : (fiber s).map (c.smulHom g) x = (fiber s).map (c.smulHom h) x) : g = h := by
  have := c.isIso_sigmaDesc
  let x' : Spec (.of Ω) ⟶ c.P := x.left
  have h' : x' ≫ c.smul g = x' ≫ c.smul h := congrArg CommaMorphism.left hgh
  have h2 : x' ≫ Sigma.ι (fun _ : G ↦ c.P) g = x' ≫ Sigma.ι (fun _ : G ↦ c.P) h := by
    rw [← cancel_mono (Sigma.desc fun g : G ↦
      pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P)
      (by rw [c.smul_π, Category.id_comp]))]
    apply pullback.hom_ext <;>
      simp only [Category.assoc, Sigma.ι_comp_desc_assoc, pullback.lift_fst, pullback.lift_snd,
        Category.comp_id, h']
  have h3 := congrArg (fun f ↦ f (default : Spec (.of Ω))) h2
  simp only [Scheme.Hom.comp_apply] at h3
  have := (sigmaι_eq_iff (fun _ : G ↦ c.P) g h _ _).mp h3
  exact congrArg Sigma.fst this

/-- `G` acts simply transitively on the geometric fibre of a Galois cover with group `G`. -/
lemma existsUnique_fiber_map_smulHom (x y : (fiber s).obj c.toFiniteEtale) :
    ∃! g, (fiber s).map (c.smulHom g) x = y := by
  obtain ⟨g, hg⟩ := c.exists_fiber_map_smulHom s x y
  exact ⟨g, hg, fun h hh ↦ c.eq_of_fiber_map_smulHom_eq s x (hh.trans hg.symm)⟩

/-- An injective equivariant map preserves stabilizers. -/
lemma _root_.MulAction.stabilizer_eq_of_injective {M X Z : Type*} [Group M] [MulAction M X]
    [MulAction M Z] {f : X → Z} (hf : Function.Injective f)
    (h : ∀ (g : M) (x : X), f (g • x) = g • f x) (x : X) :
    MulAction.stabilizer M (f x) = MulAction.stabilizer M x := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, ← h, hf.eq_iff]

/-- A finite étale Galois cover `c` of a connected scheme `Y` with group `G` has a connected
Galois subcover: there are a subgroup `H ≤ G`, a Galois cover `c'` of `Y` with group `H` and
connected total space, and a morphism of `Y`-schemes `c'.P ⟶ c.P` (blueprint
`lemma-cohomology-near-two-transverse-divisors--1`). -/
theorem exists_connected_subcover {Y : Scheme.{u}} [ConnectedSpace Y] {G : Type (u + 1)}
    [Group G] [Finite G] (c : Y.GaloisCover G) :
    ∃ (H : Subgroup G) (c' : Y.GaloisCover H) (_ : ConnectedSpace c'.P) (i : c'.P ⟶ c.P),
      i ≫ c.π = c'.π := by
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  let s : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y
  obtain ⟨π, _, _⟩ := exists_isFundamentalGroup s
  set P := c.toFiniteEtale
  have := c.surjective
  obtain ⟨x₀⟩ : Nonempty ((fiber s).obj P) :=
    nonempty_fiber_of_nonempty s P ⟨(c.π.surjective y).choose⟩
  -- a connected cover `A` with a point `a` whose stabilizer is that of `x₀`
  obtain ⟨A, a, hA, hstab⟩ :=
    exists_isConnected_stabilizer_eq s π (stabilizerOpenSubgroup s π P x₀)
  let o : MulAction.orbit π x₀ := ⟨x₀, MulAction.mem_orbit_self x₀⟩
  obtain ⟨e, hea, he⟩ := exists_equiv_of_stabilizer_eq π a o (by
    rw [hstab]
    ext γ
    simp [o, stabilizerOpenSubgroup, Subtype.ext_iff])
  have := hA
  -- the fibre of `A` embeds equivariantly onto the `π`-orbit of `x₀`
  let ψ : (fiber s).obj A → (fiber s).obj P := fun x ↦ (e x : (fiber s).obj P)
  have hψ (γ : π) (x : (fiber s).obj A) : ψ (γ • x) = γ • ψ x :=
    congrArg Subtype.val (he γ x)
  have hψinj : Function.Injective ψ := Subtype.val_injective.comp e.injective
  have hψa : ψ a = x₀ := congrArg Subtype.val hea
  obtain ⟨i, hi⟩ := exists_hom_fiber_map_eq s π ψ hψ
  -- the action of `G` on the fibre commutes with that of `π`
  have hnat (g : G) (γ : π) (x : (fiber s).obj P) :
      (fiber s).map (c.smulHom g) (γ • x) = γ • (fiber s).map (c.smulHom g) x :=
    IsNaturalSMul.naturality γ (c.smulHom g) x
  have hinj (g : G) : Function.Injective ((fiber s).map (c.smulHom g)) := fun x x' hxx' ↦ by
    have := congrArg ((fiber s).map (c.smulHom g⁻¹)) hxx'
    rwa [← fiber_map_smulHom_mul, ← fiber_map_smulHom_mul, inv_mul_cancel,
      fiber_map_smulHom_one, fiber_map_smulHom_one] at this
  -- the subgroup of `G` preserving the orbit of `x₀`
  let H : Subgroup G :=
    { carrier := {g | ∃ γ : π, (fiber s).map (c.smulHom g) x₀ = γ • x₀}
      mul_mem' := by
        rintro g h ⟨γ, hγ⟩ ⟨δ, hδ⟩
        refine ⟨δ * γ, ?_⟩
        rw [fiber_map_smulHom_mul, hδ, hnat, hγ, smul_smul]
      one_mem' := ⟨1, by rw [fiber_map_smulHom_one, _root_.one_smul]⟩
      inv_mem' := by
        rintro g ⟨γ, hγ⟩
        refine ⟨γ⁻¹, eq_inv_smul_iff.mpr ?_⟩
        rw [← hnat, ← hγ, ← fiber_map_smulHom_mul, inv_mul_cancel, fiber_map_smulHom_one] }
  have hmem (h : H) : ∃ γ : π, (fiber s).map (c.smulHom h) x₀ = γ • x₀ := h.2
  choose γ hγ using hmem
  -- each `h ∈ H` lifts to an endomorphism of `A`
  have hlift (h : H) : ∃ φ : A ⟶ A, (fiber s).map φ a = γ h • a := by
    obtain ⟨f, hf⟩ := (exists_iso_fiber_map_eq_iff s π A A a (γ h • a)).2 (by
      rw [← MulAction.stabilizer_eq_of_injective hψinj hψ a,
        ← MulAction.stabilizer_eq_of_injective hψinj hψ (γ h • a), hψ, hψa, ← hγ]
      exact (MulAction.stabilizer_eq_of_injective (hinj h) (hnat h) x₀).symm)
    exact ⟨f.hom, hf⟩
  choose φ hφ using hlift
  have hφi (h : H) : φ h ≫ i = i ≫ c.smulHom h :=
    evaluation_injective_of_isConnected (fiber s) A P a (by
      simp only [Functor.map_comp, ConcreteCategory.comp_apply, hφ, hi, hψ, hψa]
      exact (hγ h).symm)
  have hcancel (f₁ f₂ : A ⟶ A) (hf : f₁ ≫ i = f₂ ≫ i) : f₁ = f₂ := by
    refine evaluation_injective_of_isConnected (fiber s) A A a (hψinj ?_)
    have := congrArg (fun f ↦ (fiber s).map f a) hf
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply, hi] using this
  have hfib (h : H) (x : (fiber s).obj A) :
      ψ ((fiber s).map (φ h) x) = (fiber s).map (c.smulHom h) (ψ x) := by
    have := congrArg (fun f ↦ (fiber s).map f x) (hφi h)
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply, hi] using this
  -- `H` acts simply transitively on the fibre of `A`
  have hv (x y : (fiber s).obj A) : ∃! h : H, (fiber s).map (φ h) x = y := by
    obtain ⟨g, hg, hu⟩ := c.existsUnique_fiber_map_smulHom s (ψ x) (ψ y)
    obtain ⟨δ, rfl⟩ := MulAction.exists_smul_eq π a x
    obtain ⟨ε, rfl⟩ := MulAction.exists_smul_eq π a y
    have hg' := hg
    rw [hψ, hψ, hψa, hnat] at hg'
    have hgH : g ∈ H := ⟨δ⁻¹ * ε, by rw [← smul_smul, ← hg', inv_smul_smul]⟩
    refine ⟨⟨g, hgH⟩, hψinj (by rw [hfib]; exact hg), fun h hh ↦ Subtype.ext (hu h ?_)⟩
    beta_reduce
    rw [← hfib, hh]
  have hone : φ 1 = 𝟙 A := hcancel _ _ (by
    rw [hφi, Subgroup.coe_one, smulHom_one, Category.comp_id, Category.id_comp])
  have hmul (g h : H) : φ (g * h) = φ h ≫ φ g := hcancel _ _ (by
    rw [hφi, Category.assoc, hφi, ← Category.assoc, hφi, Category.assoc, Subgroup.coe_mul,
      smulHom_mul])
  refine ⟨H,
    { P := A.obj.left
      π := A.obj.hom
      isFinite := A.property
      etale := A.obj.prop
      surjective := surjective_of_nonempty_fiber s A ⟨a⟩
      smul h := (φ h).hom.left
      smul_π h := hom_left_comp (φ h)
      one_smul := by rw [hone]; rfl
      mul_smul g h := by rw [hmul]; rfl
      isIso_sigmaDesc := isIso_sigmaDesc_of_existsUnique s A φ hv },
    connectedSpace_of_isConnected A, i.hom.left, hom_left_comp i⟩

end AlgebraicGeometry.Scheme.GaloisCover
