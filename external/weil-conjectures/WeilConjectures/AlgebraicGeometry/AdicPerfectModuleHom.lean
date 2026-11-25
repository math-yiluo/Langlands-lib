/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModuleFunctors
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModels
import WeilConjectures.AlgebraicGeometry.AdicPerfectUnitHom
import Mathlib.RingTheory.Finiteness.Projective

/-! # The ordinary quotient comparison for a single pair of modules

Source: Stacks Project, Tags 093T and 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w z uD vD
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change

private abbrev moduleHom {A : Type w} [CommRing A] (M N : ModuleCat.{w} A) :=
  ModuleCat.of A (M →ₗ[A] N)

private def precomp {A : Type w} [CommRing A] {M M' : ModuleCat.{w} A}
    (a : M' ⟶ M) (N : ModuleCat.{w} A) : moduleHom M N ⟶ moduleHom M' N :=
  ModuleCat.ofHom (LinearMap.lcomp A N a.hom)

private theorem finiteProjective_decomposition {A : Type w} [CommRing A]
    (M : ModuleCat.{w} A) [Module.Finite A M] [Module.Projective A M] :
    ∃ (r : ℕ) (i : Fin r → (ModuleCat.of A A ⟶ M))
      (p : Fin r → (M ⟶ ModuleCat.of A A)), ∑ j, p j ≫ i j = 𝟙 M := by
  classical
  obtain ⟨r, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let i (j : Fin r) : ModuleCat.of A A ⟶ M :=
    ModuleCat.ofHom (f.comp (LinearMap.single A (fun _ : Fin r ↦ A) j))
  let p (j : Fin r) : M ⟶ ModuleCat.of A A :=
    ModuleCat.ofHom ((LinearMap.proj j).comp g)
  refine ⟨r, i, p, ?_⟩
  ext m
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change ∑ j, f (Pi.single j (g m j)) = m
  rw [← map_sum, LinearMap.sum_single_apply]
  exact congrArg (fun h ↦ h m) hfg

private theorem precomp_decomposition {A : Type w} [CommRing A]
    (M N : ModuleCat.{w} A) {r : ℕ}
    (i : Fin r → (ModuleCat.of A A ⟶ M)) (p : Fin r → (M ⟶ ModuleCat.of A A))
    (hs : ∑ j, p j ≫ i j = 𝟙 M) :
    ∑ j, precomp (i j) N ≫ precomp (p j) N = 𝟙 (moduleHom M N) := by
  ext f m
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply]
  change ∑ j, f (i j (p j m)) = f m
  rw [← map_sum]
  congr 1
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using
      congrArg (fun h ↦ h.hom m) hs

private theorem group_sum_apply {B C : AddCommGrpCat.{z}} {ι : Type*}
    (s : Finset ι) (f : ι → (B ⟶ C)) (x : B) :
    (∑ j ∈ s, f j) x = ∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

private theorem finiteProjective_hom_bijective
    {A : Type w} [CommRing A] {D : Type uD} [Category.{vD} D] [Preadditive D]
    (H : ModuleCat.{w} A ⥤ AddCommGrpCat.{z}) [H.Additive]
    (F : ModuleCat.{w} A ⥤ D) [F.Additive]
    (t : ∀ M N : ModuleCat.{w} A, H.obj (moduleHom M N) →+ (F.obj M ⟶ F.obj N))
    (ht : ∀ (M M' N : ModuleCat.{w} A) (a : M' ⟶ M)
      (x : H.obj (moduleHom M N)),
      t M' N (H.map (precomp a N) x) = F.map a ≫ t M N x)
    (hu : ∀ N : ModuleCat.{w} A, Function.Bijective (t (ModuleCat.of A A) N))
    (M N : ModuleCat.{w} A) [Module.Finite A M] [Module.Projective A M] :
    Function.Bijective (t M N) := by
  classical
  obtain ⟨r, i, p, hs⟩ := finiteProjective_decomposition M
  have hx (x : H.obj (moduleHom M N)) :
      ∑ j, H.map (precomp (p j) N) (H.map (precomp (i j) N) x) = x := by
    have h := congrArg (fun f ↦ H.map f)
      (precomp_decomposition M N i p hs)
    rw [H.map_sum, H.map_id] at h
    have he := congrArg (fun f ↦ f x) h
    simpa only [group_sum_apply, Functor.map_comp, AddCommGrpCat.comp_apply,
      AddCommGrpCat.id_apply] using he
  have hy (y : F.obj M ⟶ F.obj N) : ∑ j, F.map (p j) ≫ F.map (i j) ≫ y = y := by
    simp only [← Category.assoc]
    rw [← Preadditive.sum_comp]
    simp only [← F.map_comp, ← F.map_sum, hs, F.map_id, Category.id_comp]
  constructor
  · intro x y hxy
    have hcoord (j : Fin r) : H.map (precomp (i j) N) x =
        H.map (precomp (i j) N) y := by
      apply (hu N).1
      rw [ht, ht, hxy]
    rw [← hx x, ← hx y]
    exact Finset.sum_congr rfl fun j _ ↦ congrArg (H.map (precomp (p j) N)) (hcoord j)
  · intro y
    choose z hz using fun j : Fin r ↦ (hu N).2 (F.map (i j) ≫ y)
    refine ⟨∑ j, H.map (precomp (p j) N) (z j), ?_⟩
    rw [map_sum]
    simpa only [ht, hz] using hy y

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The quotient Hom comparison for modules is additive, natural in both variables,
is invertible for a finite projective source, and respects actual scalar balancing.
No complexes, differentials, degree bounds or cohomology occur in this assertion.

Source: Stacks Project, Modules on Sites, Tag 093T; proetale.tex, Tag 09C6,
the quotient total-Hom calculation; More on Algebra, Tag 0A8H.
(auxiliary; not a blueprint node).

Proof: first balance scalar extension from the constant ring through its completion
and then to its quotient. The completion cone equation identifies the composite
ring map with the constant quotient map. Constant module sheafification and
restriction to the slice commute with this extension, so the quotient realization
of M is the constant sheaf of M/J^(n+1)M over the constant quotient ring.
A linear map M to N induces a map of those quotients. It factors through the
quotient of Hom_A(M,N), since J^(n+1) acts trivially on the target. Constant
sheafification gives the comparison on locally constant Hom sections; evaluation
at the terminal object turns these into global module-sheaf morphisms. This
constructs the comparison for arbitrary M,N, and additivity and two-variable
naturality follow on constant sections and hence by sheaf separatedness.
For M finite free, evaluate on a finite basis: Hom commutes with the quotient
and with constant sheafification's finite products. A finite projective module is
a retract of a finite free module, and these natural comparisons preserve the
retraction; hence the comparison is bijective for a finite projective source.
For the successor identity, both sides on a constant linear map and a local pure
tensor have value given by the same linear map followed by the quotient. The
balancing map multiplies the two scalar factors. Local generators and separatedness
extend the equation to all sections. The zero module, zero ring, unit ideal and
empty slice are included; the corresponding maps are the unique zero maps. -/
theorem adicPerfectModuleHom (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    let G := AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U)) ⋙
        forget₂ (ModuleCat A) AddCommGrpCat
    let H := fun n : ℕ ↦ AdicCohomology.quotient J (n + 1) ⋙ G
    let F := fun n : ℕ ↦ adicPerfectQuotientFunctor X J U n
    ∃ t : ∀ (n : ℕ) (M N : ModuleCat.{max v (u + 1)} A),
        (H n).obj (ModuleCat.of A (M →ₗ[A] N)) →+ ((F n).obj M ⟶ (F n).obj N),
      (∀ (n : ℕ) (M N : ModuleCat.{max v (u + 1)} A)
        (_ : Module.Finite A M) (_ : Module.Projective A M), Function.Bijective (t n M N)) ∧
      (∀ (n : ℕ) (M M' N N' : ModuleCat.{max v (u + 1)} A)
        (a : M' ⟶ M) (b : N ⟶ N') (x : (H n).obj (ModuleCat.of A (M →ₗ[A] N))),
        t n M' N' ((H n).map (ModuleCat.ofHom
          ((LinearMap.llcomp A M' N N' b.hom).comp (LinearMap.lcomp A N a.hom))) x) =
          (F n).map a ≫ t n M N x ≫ (F n).map b) ∧
      (∀ (n : ℕ) (M N : ModuleCat.{max v (u + 1)} A)
        (x : (H (n + 1)).obj (ModuleCat.of A (M →ₗ[A] N))),
        t n M N (G.map ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app
            (ModuleCat.of A (M →ₗ[A] N))) x) =
          ((adicPerfectQuotientModuleStep X J U n).app M).inv ≫
            (change (adicPerfectQuotientScalarStep X J U n)).map (t (n + 1) M N x) ≫
              ((adicPerfectQuotientModuleStep X J U n).app N).hom) := by
  dsimp only
  obtain ⟨t, hu, hn, hs⟩ := adicPerfectUnitHom.{u, v} X J U
  refine ⟨t, ?_, hn, hs⟩
  intro n M N hM hP
  let := hM
  let := hP
  apply finiteProjective_hom_bijective
    (AdicCohomology.quotient J (n + 1) ⋙
      AdicCohomology.sections
        ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U)) ⋙
      forget₂ (ModuleCat A) AddCommGrpCat)
    (adicPerfectQuotientFunctor X J U n) (t n) ?_ (hu n) M N
  intro M M' N a x
  have h := hn n M M' N N a (𝟙 N) x
  have he : ModuleCat.ofHom
      ((LinearMap.llcomp A M' N N (ModuleCat.Hom.hom (𝟙 N))).comp (LinearMap.lcomp A N a.hom)) =
        precomp a N := by
    ext f m
    rfl
  rw [he] at h
  change _ = (adicPerfectQuotientFunctor X J U n).map a ≫
    t n M N x ≫ (adicPerfectQuotientFunctor X J U n).map (𝟙 N) at h
  rw [(adicPerfectQuotientFunctor X J U n).map_id, Category.comp_id] at h
  exact h

end AlgebraicGeometry.Scheme
