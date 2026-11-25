/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule
import WeilConjectures.ConstructibleSheaf.TorsorEquivariantModuleDiagonalEvaluation


@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

/-- Recover a unique linear map from the diagonal values of the component of eta
at the torsor object. No formula on arbitrary etale objects is asserted here.
Source: Stacks Project, etale-cohomology.tex Tags 0DV5 (3) and 0DV6 (context).
(blueprint: lem-weil-pbc-torsor-equivariant-module-recover-linear-diagonal)

Proof: The torsor isomorphism, with its factors interchanged, identifies
c.P times_V c.P with copies of c.P indexed by g in P. On the g-th copy a section
has the value rho(g) applied to its value on the diagonal. Thus restriction to
the diagonal determines an equivariant section. Conversely any locally constant
function t on c.P extends on the g-th copy with value rho(g)t. This extension
is locally constant because the copies are open, and equivariance follows from
rho(hg)=rho(h)rho(g). The restriction and extension operations are linear and
inverse. Every locally constant function on the connected nonempty space c.P
is constant, so diagonal evaluation gives a linear isomorphism from these sections
to N, and likewise to N'. Conjugate the linear component eta at Etale.mk c.pi
by these two isomorphisms to obtain f. At each point x the diagonal evaluations
are the same constants, so the asserted formula holds for every s and x.
For uniqueness fix one x, which exists by connectedness. For every n, extend
the constant diagonal function with value n; evaluating the formulas for two
candidate maps on this section at x shows equality at n. Linear extensionality
then gives equality of the maps. The zero module and trivial group work with
the same construction; ell need not be prime or positive. -/
theorem equivariantModulePresheaf_recoverLinear_diagonal
    {V : Scheme.{u}} (ℓ : ℕ) {P : Type u} [Group P] [Finite P]
    (c : Scheme.GaloisCover (ULift.{u + 1} P) V) [ConnectedSpace c.P]
    (N N' : Rep.{u + 1} (ZMod ℓ) P)
    (η : c.equivariantModulePresheaf ℓ N ⟶ c.equivariantModulePresheaf ℓ N') :
    letI := c.etale
    ∃! f : N.V →ₗ[ZMod ℓ] N'.V,
      ∀ (s : c.equivariantSections ℓ N (Etale.mk c.π)) (x : c.P),
        (η.app (op (Etale.mk c.π)) s).val
            ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x) =
          f (s.val ((pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl) x)) := by
  classical
  let _ := c.etale
  let δ : c.P ⟶ pullback c.π c.π :=
    pullback.lift (f := c.π) (g := c.π) (𝟙 c.P) (𝟙 c.P) rfl
  let x₀ : c.P := Classical.arbitrary c.P
  let E (M : Rep.{u + 1} (ZMod ℓ) P) :
      c.equivariantSections ℓ M (Etale.mk c.π) →ₗ[ZMod ℓ] M.V :=
    { toFun := fun s ↦ s.val (δ x₀)
      map_add' := by intro a b; rfl
      map_smul' := by intro r a; rfl }
  have hconst (M : Rep.{u + 1} (ZMod ℓ) P)
      (s : c.equivariantSections ℓ M (Etale.mk c.π)) (x y : c.P) :
      s.val (δ x) = s.val (δ y) := by
    exact (s.val.comap ⟨δ, δ.continuous⟩).apply_eq_of_preconnectedSpace x y
  have hinj (M : Rep.{u + 1} (ZMod ℓ) P) : Function.Injective (E M) := by
    set_option backward.isDefEq.respectTransparency false in
      let D₀ : (∐ fun _ : ULift.{u + 1} P ↦ c.P) ⟶ pullback c.π c.π :=
        Sigma.desc fun g : ULift.{u + 1} P ↦
          pullback.lift (f := c.π) (g := c.π) (c.smul g) (𝟙 c.P)
            (by simp [c.smul_π])
      let _ : IsIso D₀ := c.isIso_sigmaDesc
      let D : (∐ fun _ : ULift.{u + 1} P ↦ c.P) ⟶ pullback c.π c.π :=
        D₀ ≫ (pullbackSymmetry c.π c.π).hom
      let _ : IsIso D := by dsimp [D]; infer_instance
      let j (g : ULift.{u + 1} P) : c.P ⟶ pullback c.π c.π :=
        pullback.lift (𝟙 c.P) (c.smul g) (by simp [c.smul_π])
      have hj (g : ULift.{u + 1} P) :
          Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) g ≫ D = j g := by
        apply pullback.hom_ext <;> simp [D, D₀, j]
      have hcover (z : (pullback c.π c.π : Scheme)) : ∃ g y, j g y = z := by
        obtain ⟨g, y, hy⟩ :=
          (sigmaOpenCover fun _ : ULift.{u + 1} P ↦ c.P).exists_eq (inv D z)
        refine ⟨g, y, ?_⟩
        have h := congrArg (fun t ↦ D t) hy
        change D (Sigma.ι (fun _ : ULift.{u + 1} P ↦ c.P) g y) = D (inv D z) at h
        simpa only [← Scheme.Hom.comp_apply, hj, IsIso.inv_hom_id,
          Scheme.Hom.id_base, TopCat.id_app] using h
      have haction (g : ULift.{u + 1} P) :
          δ ≫ c.sectionAction (Etale.mk c.π) g.down = j g := by
        change δ ≫ pullback.map c.π c.π c.π c.π (𝟙 _) (c.smul g) (𝟙 _)
          (by simp) (by simp [c.smul_π]) = j g
        apply pullback.hom_ext
        · simp [δ, j]
        · simp only [δ, j, Category.assoc, pullback.lift_snd_assoc,
            pullback.lift_snd, pullback.map, Category.id_comp]
      intro s t h
      apply Subtype.ext
      apply LocallyConstant.ext
      intro z
      obtain ⟨g, y, rfl⟩ := hcover z
      have hs := s.property g.down (δ y)
      have ht := t.property g.down (δ y)
      change s.val ((δ ≫ c.sectionAction (Etale.mk c.π) g.down) y) = _ at hs
      change t.val ((δ ≫ c.sectionAction (Etale.mk c.π) g.down) y) = _ at ht
      rw [haction] at hs ht
      have hdiag : s.val (δ y) = t.val (δ y) :=
        (hconst M s y x₀).trans (h.trans (hconst M t y x₀).symm)
      exact hs.trans ((congrArg (M.ρ g.down) hdiag).trans ht.symm)
  let e : c.equivariantSections ℓ N (Etale.mk c.π) ≃ₗ[ZMod ℓ] N.V :=
    LinearEquiv.ofBijective (E N)
      ⟨hinj N, c.equivariantSections_diagonalEvaluation_surjective ℓ N x₀⟩
  let f : N.V →ₗ[ZMod ℓ] N'.V :=
    (E N').comp ((η.app (op (Etale.mk c.π))).hom.comp e.symm.toLinearMap)
  have hf (s : c.equivariantSections ℓ N (Etale.mk c.π)) (x : c.P) :
      (η.app (op (Etale.mk c.π)) s).val (δ x) = f (s.val (δ x)) := by
    rw [hconst N' _ x x₀, hconst N s x x₀]
    change E N' (η.app (op (Etale.mk c.π)) s) =
      E N' (η.app (op (Etale.mk c.π)) (e.symm (e s)))
    rw [e.symm_apply_apply]
  refine ⟨f, hf, ?_⟩
  intro g hg
  apply LinearMap.ext
  intro n
  obtain ⟨s, hs⟩ := c.equivariantSections_diagonalEvaluation_surjective ℓ N x₀ n
  exact (congrArg g hs).symm.trans ((hg s x₀).symm.trans ((hf s x₀).trans
    (congrArg f hs)))

end AlgebraicGeometry.Scheme.GaloisCover
