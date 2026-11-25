/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule

/-!
# Surjectivity of diagonal evaluation of torsor sections

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 0A3R, 04TR and 04TS.
(blueprint: lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- Every module value occurs as the value of an equivariant section at a
specified point on the diagonal of the torsor's double overlap.
Source: Stacks Project, etale-cohomology.tex Tag 0DV5 (3), Tags 0DV6 and 0A3R.
(blueprint: lem-weil-pbc-torsor-equivariant-module-diagonal-evaluation)

Proof: Compose the torsor isomorphism with interchange of the two factors.
This identifies c.P times_V c.P with the disjoint union, indexed by the group,
of copies of c.P, whose g-th component is (identity, g times identity). Given a
value n, prescribe on this component the constant value rho(g)n. These
functions are locally constant on the disjoint union; transport them across the
isomorphism to the double overlap. The second factor action by h carries
component g to component hg. The representation identity rho(hg)n =
rho(h)(rho(g)n) proves equivariance. On the identity component, which is the
diagonal, the value is rho(1)n = n. Thus the section has the requested value at
the diagonal point. No connectedness or nonzero module hypothesis is needed,
and the construction works for the trivial group. -/
theorem equivariantSections_diagonalEvaluation_surjective
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V)
    (N : Rep.{u + 1} (ZMod ℓ) P) (x : c.P) :
    letI := c.etale
    Function.Surjective (fun s : c.equivariantSections ℓ N (Etale.mk c.π) ↦
      s.val ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x)) := by
  set_option backward.isDefEq.respectTransparency false in
    classical
    have := c.etale
    let D₀ : (∐ fun _ : ULift.{u + 1} P ↦ c.P) ⟶ pullback c.π c.π :=
      Sigma.desc fun g : ULift.{u + 1} P ↦
        pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P) (by simp [c.smul_π])
    let : IsIso D₀ := c.isIso_sigmaDesc
    let D : (∐ fun _ : ULift.{u + 1} P ↦ c.P) ⟶ pullback c.π c.π :=
      D₀ ≫ (pullbackSymmetry c.π c.π).hom
    let : IsIso D := by dsimp [D]; infer_instance
    let j (g : ULift.{u + 1} P) : c.P ⟶ pullback c.π c.π :=
      pullback.lift (𝟙 c.P) (c.smul g) (by simp [c.smul_π])
    have hj (g : ULift.{u + 1} P) : Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) g ≫ D = j g := by
      apply pullback.hom_ext <;> simp [D, D₀, j]
    have hcover (z : (pullback c.π c.π : Scheme)) : ∃ g y, j g y = z := by
      obtain ⟨g, y, hy⟩ := (sigmaOpenCover fun _ : ULift.{u + 1} P ↦ c.P).exists_eq (inv D z)
      refine ⟨g, y, ?_⟩
      have h := congrArg (fun t ↦ D t) hy
      change D (Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) g y) = D (inv D z) at h
      simpa only [← Scheme.Hom.comp_apply, hj, IsIso.inv_hom_id,
        Scheme.Hom.id_base, TopCat.id_app] using h
    let q (z : (pullback c.π c.π : Scheme)) : ULift.{u + 1} P := (hcover z).choose
    have hq (g : ULift.{u + 1} P) (y : c.P) : q (j g y) = g := by
      obtain ⟨y', hy'⟩ := (hcover (j g y)).choose_spec
      have h := congrArg (fun t ↦ inv D t) hy'
      have hi (a : ULift.{u + 1} P) : j a ≫ inv D = Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) a := by
        rw [← hj, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      simp only [← Scheme.Hom.comp_apply, hi] at h
      exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 h)
    have hfib (g : ULift.{u + 1} P) :
        q ⁻¹' {g} = (inv D) ⁻¹' Set.range (Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) g) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_range]
      have hi (a : ULift.{u + 1} P) : j a ≫ inv D = Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) a := by
        rw [← hj, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      refine ⟨fun hz ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩
      · obtain ⟨y, hy⟩ := (hcover z).choose_spec
        refine ⟨y, ?_⟩
        have h := congrArg (fun t ↦ inv D t) hy
        change (j (q z) ≫ inv D) y = inv D z at h
        simpa only [hi, hz] using h
      · have h := congrArg (fun t ↦ D t) hy
        have hz : j g y = z := by
          simpa only [← Scheme.Hom.comp_apply, sigmaOpenCover_f, hj, IsIso.inv_hom_id,
            Scheme.Hom.id_base, TopCat.id_app] using h
        rw [← hz]
        exact hq g y
    let Q : LocallyConstant (pullback c.π c.π : Scheme) (ULift.{u + 1} P) :=
      ⟨q, IsLocallyConstant.iff_isOpen_fiber.2 fun g ↦ by
        rw [hfib]
        have hopen :=
          (Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) g).isOpenEmbedding.isOpenMap.isOpen_range
        exact hopen.preimage (inv D).continuous⟩
    dsimp only
    intro n
    let s : LocallyConstant (pullback c.π c.π : Scheme) N.V := Q.map fun g ↦ N.ρ g.down n
    have hs (g : ULift.{u + 1} P) (y : c.P) : s (j g y) = N.ρ g.down n := by
      change N.ρ (q (j g y)).down n = _
      rw [hq]
    have ha (h : P) (g : ULift.{u + 1} P) :
        j g ≫ c.sectionAction (Etale.mk c.π) h = j (⟨h⟩ * g) := by
      change j g ≫ pullback.map c.π c.π c.π c.π (𝟙 _) (c.smul ⟨h⟩) (𝟙 _)
        (by simp) (by simp [c.smul_π]) = _
      apply pullback.hom_ext <;> simp [j, c.mul_smul]
    refine ⟨⟨s, ?_⟩, ?_⟩
    · intro h z
      obtain ⟨g, y, rfl⟩ := hcover z
      change s ((j g ≫ c.sectionAction (Etale.mk c.π) h) y) = N.ρ h (s (j g y))
      rw [ha]
      change s (j (⟨h⟩ * g) y) = N.ρ h (s (j g y))
      rw [hs, hs]
      exact congrArg (fun f : N.V →ₗ[ZMod ℓ] N.V ↦ f n) (N.ρ_mul h g.down)
    · have hdiag : pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl = j 1 := by
        simp [j, c.one_smul]
      change s _ = n
      rw [hdiag, hs]
      simp

end AlgebraicGeometry.Scheme.GaloisCover
