/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.FieldTheory.BrauerScalarDefect
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.Abel

@[expose] public section
universe u
namespace Field

set_option backward.isDefEq.respectTransparency false in
/-- A jointly locally constant scalar two-cocycle has a homogeneous realization.
Proof: set f(g₀,g₁,g₂) = g₀(c(g₀⁻¹g₁,g₁⁻¹g₂)) and write its values
additively using Additive.ofMul. The action on each fixed unit is locally
constant, since the unit is algebraic and its stabilizer is Krull-open.
Together with joint local constancy of c and continuous group operations,
this makes f jointly continuous into the discrete coefficient module.
The absolute Galois group is compact Hausdorff, so the compact-open exponential
law curries f into the iterated continuous-map object in degree two.
Left translation of all three coordinates applies that same translation to
f, placing it in the invariant homogeneous cochains. At four coordinates,
put g = g₀⁻¹g₁, h = g₁⁻¹g₂ and k = g₂⁻¹g₃. The given identity, acted on
by g₀, is exactly the vanishing alternating homogeneous differential.
Lift this closed cochain along the kernel inclusion to obtain z. Evaluation
at (1,g,gh) is c(g,h), proving the requested equality. Normalization is unused.
Source: Stacks Project, Section 0DVG, homogeneous and inhomogeneous cochains.
(blueprint: lem-sc-brauer-scalar-defect-cocycle-realization). -/
theorem exists_galoisUnits_cocycle_of_scalar_cocycle (K : Type u) [Field K]
    (c : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      (SeparableClosure K ≃ₐ[K] SeparableClosure K) → (SeparableClosure K)ˣ)
    (hlc : IsLocallyConstant (Function.uncurry c))
    (hc : ∀ g h k, c g h * c (g * h) k =
      g (c h k) * c g (h * k)) :
    ∃ z : ContinuousCohomology.cocycles (galoisUnitsTopRep K) 2,
      ∀ g h, galoisUnitsCocycleValue K z g h = c g h := by
  classical
  -- Keep the coefficient ring abstract while constructing homogeneous cochains.
  have realize : ∀ {R : Type} [CommRing R] [TopologicalSpace R] {G : Type u}
      [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] (A : TopRep R G)
      (ha : Continuous (fun p : G × A ↦ A.ρ p.1 p.2)) (ca : C(G × G, A)),
      (∀ g h k, A.ρ g (ca (h, k)) - ca (g * h, k) + ca (g, h * k) - ca (g, h) = 0) →
      ∃ z : ContinuousCohomology.cocycles A 2,
        ∀ g h, (((TopRep.homogeneousCochains A).iCycles 2).hom z).val 1 g (g * h) =
          ca (g, h) := by
    intro R _ _ G _ _ _ _ A ha ca hδ
    have hr : ∀ (g h : G) (m : A),
        A.ρ g (A.ρ h m) = A.ρ (g * h) m := by
      intro g h m
      exact (congrArg (fun t ↦ t m) (A.ρ.toMonoidHom.map_mul g h)).symm
    let F : C((G × G) ×
        G, A) :=
      ⟨fun p ↦ A.ρ p.1.1 (ca (p.1.1⁻¹ * p.1.2, p.1.2⁻¹ * p.2)),
        ha.comp (continuous_fst.fst.prodMk (ca.continuous.comp
          ((continuous_fst.fst.inv.mul continuous_fst.snd).prodMk
            (continuous_fst.snd.inv.mul continuous_snd))))⟩
    let f : ((TopRep.resolution' A).X 2).invariants := ⟨F.curry.curry, by
      apply (ContRepresentation.mem_invariants _).mpr
      intro g
      ext a b d
      change A.ρ g (A.ρ (g⁻¹ * a)
          (ca ((g⁻¹ * a)⁻¹ * (g⁻¹ * b), (g⁻¹ * b)⁻¹ * (g⁻¹ * d)))) =
        A.ρ a (ca (a⁻¹ * b, b⁻¹ * d))
      simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left]
      rw [hr, mul_inv_cancel_left]⟩
    have hf : ((TopRep.homogeneousCochains A).d 2 3).hom f = 0 := by
      apply Subtype.ext
      ext a b d e
      rw [TopRep.homogeneousCochains.d_apply]
      change A.ρ b (ca (b⁻¹ * d, d⁻¹ * e)) -
        (A.ρ a (ca (a⁻¹ * d, d⁻¹ * e)) -
          (A.ρ a (ca (a⁻¹ * b, b⁻¹ * e)) - A.ρ a (ca (a⁻¹ * b, b⁻¹ * d)))) = 0
      have hh := congrArg (A.ρ a) (hδ (a⁻¹ * b) (b⁻¹ * d) (d⁻¹ * e))
      simp only [map_sub, map_add, map_zero, hr, mul_assoc, mul_inv_cancel_left] at hh
      abel_nf at hh ⊢
      exact hh
    -- The concrete kernel is isomorphic to the categorical cycle object.
    let e : CategoryTheory.Iso (ContinuousCohomology.cocycles A 2)
        (TopModuleCat.of R ((TopRep.homogeneousCochains A).d 2 3).hom.ker) :=
      CategoryTheory.Limits.KernelFork.mapIsoOfIsLimit
        ((TopRep.homogeneousCochains A).cyclesIsKernel 2 3 (by simp))
        (TopModuleCat.isLimitKer _) (CategoryTheory.Iso.refl _)
    let z : ContinuousCohomology.cocycles A 2 := e.inv.hom ⟨f, hf⟩
    have hz : ((TopRep.homogeneousCochains A).iCycles 2).hom z = f := by
      have he := CategoryTheory.Limits.KernelFork.mapOfIsLimit_ι
        (CategoryTheory.Limits.KernelFork.ofι
          (TopModuleCat.kerι ((TopRep.homogeneousCochains A).d 2 3))
          (TopModuleCat.kerι_comp _))
        ((TopRep.homogeneousCochains A).cyclesIsKernel 2 3 (by simp))
        (CategoryTheory.Iso.refl (CategoryTheory.Arrow.mk
          ((TopRep.homogeneousCochains A).d 2 3))).inv
      exact congrArg (fun t ↦ t.hom ⟨f, hf⟩) he
    refine ⟨z, ?_⟩
    intro g h
    rw [hz]
    change A.ρ 1 (ca (1⁻¹ * g, g⁻¹ * (g * h))) = ca (g, h)
    simp
  -- Specialize the explicit construction to the discrete Galois units.
  let A := galoisUnitsTopRep K
  have : DiscreteTopology A := ⟨rfl⟩
  have ha : Continuous (fun p : Gal(SeparableClosure K/K) × A ↦ A.ρ p.1 p.2) := by
    rw [continuous_prod_of_discrete_right]
    intro x
    rw [continuous_discrete_rng]
    intro y
    change Additive ((SeparableClosure K)ˣ) at x y
    let : TopologicalSpace (SeparableClosure K) := ⊥
    have : DiscreteTopology (SeparableClosure K) := ⟨rfl⟩
    have : ContinuousSMul Gal(SeparableClosure K/K) (SeparableClosure K) :=
      continuousSMul_iff_stabilizer_isOpen.mpr stabilizer_isOpen_of_isIntegral
    have h : Continuous (fun g : Gal(SeparableClosure K/K) ↦
        g • ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)) :=
      continuous_id.smul continuous_const
    convert h.isOpen_preimage {((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)}
      (isOpen_discrete _) using 1
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change Additive.ofMul (g • x.toMul) = y ↔
      g ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K) =
        ((y.toMul : (SeparableClosure K)ˣ) : SeparableClosure K)
    exact ⟨fun h ↦ congrArg (fun z : Additive ((SeparableClosure K)ˣ) ↦
        (z.toMul : SeparableClosure K)) h,
      fun h ↦ congrArg Additive.ofMul (Units.ext h)⟩
  let ca : C(Gal(SeparableClosure K/K) × Gal(SeparableClosure K/K), A) :=
    ⟨fun p ↦ Additive.ofMul (c p.1 p.2), by
      let : TopologicalSpace ((SeparableClosure K)ˣ) := ⊥
      let : TopologicalSpace (Additive ((SeparableClosure K)ˣ)) := ⊥
      have : DiscreteTopology (Additive ((SeparableClosure K)ˣ)) := ⟨rfl⟩
      exact continuous_ofMul.comp hlc.continuous⟩
  have hδ : ∀ g h k, A.ρ g (ca (h, k)) - ca (g * h, k) +
      ca (g, h * k) - ca (g, h) = 0 := by
    intro g h k
    have he : ca (g, h) + ca (g * h, k) = A.ρ g (ca (h, k)) + ca (g, h * k) := by
      change Additive.ofMul (c g h * c (g * h) k) =
        Additive.ofMul ((g • c h k) * c g (h * k))
      exact congrArg Additive.ofMul (Units.ext (hc g h k))
    apply sub_eq_zero.mpr
    calc
      A.ρ g (ca (h, k)) - ca (g * h, k) + ca (g, h * k) =
          (A.ρ g (ca (h, k)) + ca (g, h * k)) - ca (g * h, k) := by abel
      _ = ca (g, h) := by rw [← he]; abel
  obtain ⟨z, hz⟩ := realize A ha ca hδ
  refine ⟨z, ?_⟩
  intro g h
  exact congrArg Additive.toMul (hz g h)
end Field
