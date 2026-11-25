/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.CechH1MapNatural
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.AlgebraicGeometry.Boundary.BoundaryDerivationAlgebraicData

/-!
# Boundary maps for square-zero extensions

Source: Stacks Project, Cohomology, Lemma 0B8S
(blueprint: lem-sc-boundary-derivation-square-zero).

The algebra sheaves are `Scheme.CommAlgebraSheaf`s and their underlying `𝒪_X`-modules are
`commAlgebraSheafModule`, with the module map of `p` given by `commAlgebraSheafModuleFunctor`.
The kernel `I` is tied by the short exactness of `0 → I → O' → O → 0`.
The connecting map is the snake boundary of any compatible injective resolutions,
transported to the recorded module cohomology (independent of the choice by
lem-weil-pbc-horseshoe-delta-functor). No boundary is an arbitrary function.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- The boundary of a square-zero extension is a derivation for the induced action.
`σ` is the local quotient action on the kernel, commuting with restriction.
`μ` is its action by global sections on the kernel sheaf. `ρ` is the induced
ring action on H¹, identified with H¹ applied to `μ`. `δ` is the connecting map,
computed by the snake boundary of a horseshoe and the canonical resolution isomorphisms.
The compatible resolutions are a presentation of the boundary, not extra geometric
conditions on the extension.

Source: Stacks Project, Cohomology, Lemma 0B8S
(blueprint: lem-sc-boundary-derivation-square-zero).

Proof:
1. I² = 0 makes the product of a local lift with a kernel section independent of
its lift. Thus multiplication factors through O, giving μ. Applying H¹ to these
endomorphisms gives ρ. The long exact sequence of pqf-def-cohomology gives δ;
injective resolutions compute it by the displayed snake-boundary formula.
2. The boundary is additive, so it remains to check the Leibniz identity.
3. Choose an open cover with lifts fᵢ and gᵢ. By lem-sc-boundary-cech-local-lifts,
the differences αᵢⱼ = fᵢ - fⱼ and βᵢⱼ = gᵢ - gⱼ represent δ(f) and δ(g), while
the differences γᵢⱼ = fᵢgᵢ - fⱼgⱼ represent δ(fg).
4. On overlaps γᵢⱼ = (fᵢ - fⱼ)gᵢ + fⱼ(gᵢ - gⱼ) = gαᵢⱼ + fβᵢⱼ since I² = 0.
Naturality of the Cech-to-H¹ map (lem-sc-cech-h1-map-natural) gives the asserted
identity after passing to cohomology. -/
theorem boundary_derivation_square_zero (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (_hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (_hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0) :
    ∃ (IA : InjectiveResolution I) (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf B))
      (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf C))
      (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
      (hαβ : α ≫ β = 0)
      (_hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map i ≫ IB.ι)
      (_hιB : IB.ι ≫ β =
        (CochainComplex.single₀ _).map ((commAlgebraSheafModuleFunctor X.sheaf).map p) ≫ IC.ι)
      (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
        (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
      (hΓ : ((ShortComplex.mk α β hαβ).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ))).ShortExact),
      ∃ (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U)))
      (μ : C.right.obj.obj (op ⊤) →+* End I)
      (ρ : C.right.obj.obj (op ⊤) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I))
      (δ : C.right.obj.obj (op ⊤) →+
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I)),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) ∧
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) ∧
      (∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens) (x : I.val.obj (op U)),
        (μ f).asHom.val.app (op U) x = σ U (C.right.obj.map (homOfLE le_top).op f) x) ∧
      (∀ f : C.right.obj.obj (op ⊤), ρ f =
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ f).asHom).hom) ∧
      (∀ f : C.right.obj.obj (op ⊤), δ f =
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
            (commAlgebraSheafModule X.sheaf C) ≫
          (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
          hΓ.δ 0 1 rfl ≫
          (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom
            f)) ∧
      ∀ f g : C.right.obj.obj (op ⊤), δ (f * g) = ρ f (δ g) + ρ g (δ f) := by
  obtain ⟨IA, IB, IC, α, β, hιA, hιB, hrows⟩ :=
    CategoryTheory.InjectiveResolution.exists_horseshoe_resolutions
      (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw) _hS
  obtain ⟨hαβ, hrows⟩ := hrows
  let hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact :=
    fun k => (hrows k).1
  -- Each row splits because its first term is injective, so global sections preserve it.
  have hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro k
    have hr := hH k
    change (ShortComplex.mk (α.f k) (β.f k) _).ShortExact at hr
    exact (hr.splittingOfInjective.map
      (RingedSpace.globalSectionsFunctor X.toRingedSpace)).shortExact
  refine ⟨IA, IB, IC, α, β, hαβ, hιA, hιB, hH, hΓ, ?_⟩
  exact boundary_derivation_algebraic_data X B C p I i hw _hS _hsq IA IB IC α β hαβ
    hιA hιB hH hΓ

end AlgebraicGeometry
