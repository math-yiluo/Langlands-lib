import Langlands.Representation.CuspidalSupport.RationalUniversalSmallProgeneratorStatement
import Langlands.Representation.Induction.OpenAdjunction

/-! Renard VI.4.2: the convolution algebra H(G,ρ) of the common norm kernel and
its identification with the endomorphisms of the compact induction of ρ. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Hecke

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instTopologicalSpaceRationalPoints_rationalNormKernelHeckeStatement :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Renard's H(G,ρ) (VI.4.2.1): the functions φ : G(F) → End W with
φ(h g h') = ρ(h) φ(g) ρ(h') for h, h' in the common norm kernel H⁰, whose support
meets only finitely many cosets g H⁰. -/
def rationalNormKernelHecke (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G)) :
    Submodule ℂ (GroupScheme.rationalPoints G → Module.End ℂ ρ) where
  carrier := {φ |
    (∀ (h h' : rationalCommonNormKernel G) (g : GroupScheme.rationalPoints G),
      φ ((h : GroupScheme.rationalPoints G) * g * h') =
        ρ.representation h * φ g * ρ.representation h') ∧
    (QuotientGroup.mk '' Function.support φ :
      Set (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G)).Finite}
  zero_mem' := by
    refine ⟨fun h h' g => ?_, ?_⟩
    · simp
    · simp
  add_mem' := by
    rintro φ ψ ⟨hφ, sφ⟩ ⟨hψ, sψ⟩
    refine ⟨fun h h' g => ?_, ?_⟩
    · simp only [Pi.add_apply, hφ, hψ, mul_add, add_mul]
    · refine (sφ.union sψ).subset ?_
      rintro _ ⟨x, hx, rfl⟩
      by_cases h0 : φ x = 0
      · refine Or.inr ⟨x, fun h1 => hx ?_, rfl⟩
        simp [h0, h1]
      · exact Or.inl ⟨x, h0, rfl⟩
  smul_mem' := by
    rintro c φ ⟨hφ, sφ⟩
    refine ⟨fun h h' g => ?_, ?_⟩
    · simp only [Pi.smul_apply, hφ, mul_smul_comm, smul_mul_assoc]
    · refine sφ.subset ?_
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, fun h0 => hx ?_, rfl⟩
      simp [h0]

/-- Renard's convolution product on H(G,ρ):
(φ ∗ ψ)(x) = ∑_{g ∈ G/H⁰} φ(g) ψ(g⁻¹ x), summed over the chosen representatives
of the cosets g H⁰ (the value does not depend on the choice for φ in H(G,ρ)). -/
def rationalNormKernelConvolution (ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G))
    (φ ψ : GroupScheme.rationalPoints G → Module.End ℂ ρ) :
    GroupScheme.rationalPoints G → Module.End ℂ ρ :=
  fun x => ∑ᶠ q : GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G,
    φ q.out * ψ (q.out⁻¹ * x)

end Hecke

open GroupScheme Induction

/-- VI.4.2, Proposition: for an irreducible smooth ρ of the common norm kernel H⁰
and Π = ind_{H⁰}^G ρ, the map α ↦ φ_α, φ_α(g)(w) = α(f_w)(g), is a linear
isomorphism from End Π onto H(G,ρ) carrying composition to convolution, with
inverse φ ↦ α_φ, α_φ(f)(x) = ∑_{H⁰ g ∈ H⁰\G} φ(g)(f(g⁻¹ x)). Here f_w is the
function supported on H⁰ with f_w(h) = ρ(h) w. -/
def RationalNormKernelHeckeStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    haveI : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
      rationalPoint_isTopologicalGroup F G
    ∀ ρ : SmoothRep.{0, uF, uV} ℂ (rationalCommonNormKernel G),
      ρ.IsIrreducible →
      let I := (compactInductionFunctor (rationalCommonNormKernel G)).obj (SmoothRep.toRep.obj ρ)
      let f : ρ → I := fun w => unitFunction (rationalCommonNormKernel G)
        (isOpen_rationalCommonNormKernel G) ρ.representation ρ.isSmooth w
      ∃ e : End I ≃ₗ[ℂ] rationalNormKernelHecke G ρ,
        (∀ (α : End I) (g : GroupScheme.rationalPoints G) (w : ρ),
          (e α : GroupScheme.rationalPoints G → Module.End ℂ ρ) g w =
            eval (rationalCommonNormKernel G) ρ.representation (SmoothRep.hom α (f w)).1 g) ∧
        (∀ (φ : rationalNormKernelHecke G ρ) (v : I) (x : GroupScheme.rationalPoints G),
          eval (rationalCommonNormKernel G) ρ.representation (SmoothRep.hom (e.symm φ) v).1 x =
            ∑ᶠ q : LeftQuotient (rationalCommonNormKernel G),
              (φ : GroupScheme.rationalPoints G → Module.End ℂ ρ) q.out
                (eval (rationalCommonNormKernel G) ρ.representation v.1 (q.out⁻¹ * x))) ∧
        (∀ α β : End I,
          (e (α * β) : GroupScheme.rationalPoints G → Module.End ℂ ρ) =
            rationalNormKernelConvolution G ρ (e α) (e β))

end Langlands.CuspidalSupport
