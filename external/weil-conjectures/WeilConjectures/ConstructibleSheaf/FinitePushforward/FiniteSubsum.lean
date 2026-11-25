/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.Generators

/-!
# Constructible sheaves are quotients of finite subsums (Stacks 095M)

If a constructible sheaf `F` of `Λ`-modules on a quasi-compact quasi-separated scheme, `Λ`
Noetherian, is a quotient of a sum `∐ᵢ Gᵢ` of constructible sheaves, it is already a quotient of
a finite subsum (`AlgebraicGeometry.Etale.exists_epi_sigmaDesc_fin`). The stalks of `F` are
finitely generated, so at each point finitely many `Gᵢ` suffice; the locus where a given finite
subsum surjects is the vanishing locus of a constructible cokernel, open in the constructible
topology (`AlgebraicGeometry.Etale.isOpen_constructibleTopology_stalkZeroLocus`), and the
constructible topology is quasi-compact.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

/-- A coproduct of finitely many constructible sheaves is constructible. -/
lemma isConstructibleSheaf_sigma_fin {n : ℕ} (G : Fin n → Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) [∀ k, IsConstructibleSheaf (G k)] : IsConstructibleSheaf (∐ G) :=
  have := IsConstructibleSheaf.biproduct G
  IsConstructibleSheaf.of_iso (biproduct.isoCoproduct G)

/-- A morphism of sheaves is an epimorphism at a geometric point exactly when the stalk of its
cokernel vanishes there. -/
lemma isZero_sheafFiber_cokernel_iff {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) {G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (d : G ⟶ F) :
    IsZero ((pointSmallEtale s).sheafFiber.obj (cokernel d)) ↔
      Function.Surjective ((pointSmallEtale s).sheafFiber.map d) := by
  rw [← ModuleCat.epi_iff_surjective, Preadditive.epi_iff_isZero_cokernel,
    (PreservesCokernel.iso (pointSmallEtale s).sheafFiber d).isZero_iff]


variable {ι : Type (u + 1)} (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (φ : ∀ i, G i ⟶ F)

/-- The subsum of `∐ᵢ Gᵢ ⟶ F` indexed by a finite set `S`. -/
noncomputable abbrev finsetSigmaDesc (S : Finset ι) : (∐ fun i : S ↦ G i.1) ⟶ F :=
  Sigma.desc fun i : S ↦ φ i.1

lemma isConstructibleSheaf_finsetSigma (S : Finset ι) [∀ i, IsConstructibleSheaf (G i)] :
    IsConstructibleSheaf (∐ fun i : S ↦ G i.1) :=
  have := isConstructibleSheaf_sigma_fin fun k : Fin S.card ↦ G (S.equivFin.symm k).1
  IsConstructibleSheaf.of_iso (Sigma.whiskerEquiv S.equivFin.symm fun _ ↦ Iso.refl _)

/-- Larger subsums have larger images on stalks. -/
lemma range_sheafFiber_map_finsetSigmaDesc_mono {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (.of Ω) ⟶ X) {S S' : Finset ι} (h : S ⊆ S') :
    Set.range ((pointSmallEtale s).sheafFiber.map (finsetSigmaDesc G φ S)) ⊆
      Set.range ((pointSmallEtale s).sheafFiber.map (finsetSigmaDesc G φ S')) := by
  let incl : (∐ fun i : S ↦ G i.1) ⟶ ∐ fun i : S' ↦ G i.1 :=
    Sigma.desc fun i : S ↦ Sigma.ι (fun i : S' ↦ G i.1) ⟨i.1, h i.2⟩
  have hfac : incl ≫ finsetSigmaDesc G φ S' = finsetSigmaDesc G φ S := by
    ext i
    simp [incl]
  rintro _ ⟨y, rfl⟩
  refine ⟨(pointSmallEtale s).sheafFiber.map incl y, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, hfac]


/-- **Finitely many summands suffice at a point.** If `∐ᵢ Gᵢ ⟶ F` is an epimorphism and the stalk
of `F` at a geometric point is finitely generated, a finite subsum surjects onto it. -/
lemma exists_finset_surjective_sheafFiber_map [Epi (Sigma.desc φ)] {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (hfin : Module.Finite Λ (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F)) :
    ∃ S : Finset ι, Function.Surjective
      ((pointSmallEtale s).sheafFiber.map (finsetSigmaDesc G φ S)) := by
  classical
  let Φ := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have hsurj : Function.Surjective (Φ.map (Sigma.desc φ)) :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨g, hg⟩ := hfin.fg_top
  let c := sigmaComparison Φ G
  have hc : c ≫ Φ.map (Sigma.desc φ) = Sigma.desc fun i ↦ Φ.map (φ i) := by
    ext i
    rw [ι_comp_sigmaComparison_assoc, ← Φ.map_comp, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  have key (m : Φ.obj F) : ∃ S : Finset ι,
      m ∈ ⨆ i ∈ S, LinearMap.range (Φ.map (φ i)).hom := by
    obtain ⟨y, rfl⟩ := hsurj m
    obtain ⟨S, hS⟩ := ModuleCat.exists_finset_mem_iSup_range.{u + 1, u + 1, u + 1}
      (fun i ↦ Φ.obj (G i))
      (Sigma.desc fun i ↦ Φ.map (φ i)) (inv c y)
    refine ⟨S, ?_⟩
    simp only [Sigma.ι_comp_desc] at hS
    have hy : (Sigma.desc fun i ↦ Φ.map (φ i)) (inv c y) = Φ.map (Sigma.desc φ) y := by
      rw [← hc, ConcreteCategory.comp_apply, IsIso.inv_hom_id_apply]
    rw [← hy]
    exact hS
  choose S hS using key
  refine ⟨g.biUnion S, ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  intro m hm
  refine (iSup₂_le fun i hi ↦ ?_ : _ ≤ LinearMap.range (Φ.map (finsetSigmaDesc G φ _)).hom)
    (hS m)
  rintro _ ⟨z, rfl⟩
  have hi' : i ∈ g.biUnion S := Finset.mem_biUnion.mpr ⟨m, hm, hi⟩
  refine ⟨(Φ.map (Sigma.ι (fun j : g.biUnion S ↦ G j.1) (⟨i, hi'⟩ : g.biUnion S)) :
    Φ.obj (G i) ⟶ _) z, ?_⟩
  rw [← ConcreteCategory.comp_apply, ← Φ.map_comp, Sigma.ι_comp_desc]


/-- **Stacks 095M.** If a constructible sheaf `F` on a quasi-compact quasi-separated scheme is a
quotient of a sum `∐ᵢ Gᵢ` of constructible sheaves, it is a quotient of a finite subsum. -/
@[stacks 095M]
theorem exists_epi_finsetSigmaDesc [CompactSpace X] [QuasiSeparatedSpace X]
    [IsConstructibleSheaf F] [∀ i, IsConstructibleSheaf (G i)] [Epi (Sigma.desc φ)] :
    ∃ S : Finset ι, Epi (finsetSigmaDesc G φ S) := by
  classical
  have hQ (S : Finset ι) : IsConstructibleSheaf (cokernel (finsetSigmaDesc G φ S)) :=
    have := isConstructibleSheaf_finsetSigma G S
    IsConstructibleSheaf.cokernel _
  have hFfin := (inferInstance : IsConstructibleSheaf F).isFiniteSheaf
  -- the pointwise statement at the algebraic closure points
  have hpt (x : X) : ∃ S : Finset ι, Function.Surjective
      ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.map (finsetSigmaDesc G φ S)) :=
    exists_finset_surjective_sheafFiber_map G φ (X.algClosurePoint x)
      ((ModuleCat.isFinitelyGenerated_iff _).1 (hFfin.isFinitelyGenerated_sheafFiber _ _))
  have hcov : (Set.univ : Set X) ⊆
      ⋃ S : Finset ι, stalkZeroLocus (cokernel (finsetSigmaDesc G φ S)) := by
    intro x _
    obtain ⟨S, hS⟩ := hpt x
    have := hQ S
    have h := mem_stalkZeroLocus_of_isZero_sheafFiber _ (X.algClosurePoint x)
      ((isZero_sheafFiber_cokernel_iff _ _).2 hS)
    rw [X.algClosurePoint_base] at h
    exact Set.mem_iUnion.mpr ⟨S, h⟩
  obtain ⟨T, hT₀⟩ := (isCompact_univ (X := WithConstructibleTopology X)).elim_finite_subcover
    (fun S : Finset ι ↦ WithTopology.ofTopology ⁻¹'
      stalkZeroLocus (cokernel (finsetSigmaDesc G φ S)))
    (fun S ↦ by
      have := hQ S
      rw [WithConstructibleTopology.isOpen_iff]
      exact isOpen_constructibleTopology_stalkZeroLocus _)
    (fun w _ ↦ by simpa using hcov (Set.mem_univ (WithTopology.ofTopology w)))
  have hT (x : X) : x ∈ ⋃ S ∈ T, stalkZeroLocus (cokernel (finsetSigmaDesc G φ S)) := by
    simpa using hT₀ (Set.mem_univ (WithTopology.toTopology _ x))
  refine ⟨T.sup id, Preadditive.epi_of_isZero_cokernel _ ?_⟩
  have hall (x : X) : IsZero ((pointSmallEtale (X.algClosurePoint x)).sheafFiber.obj
      (cokernel (finsetSigmaDesc G φ (T.sup id)))) := by
    obtain ⟨S, hST, hx⟩ := Set.mem_iUnion₂.mp (hT x)
    have h0 := hx _ (X.algClosurePoint x) (X.algClosurePoint_base x _)
    rw [isZero_sheafFiber_cokernel_iff] at h0 ⊢
    intro m
    obtain ⟨y, hy⟩ := h0 m
    exact range_sheafFiber_map_finsetSigmaDesc_mono G φ _ (Finset.le_sup (f := id) hST) ⟨y, hy⟩
  have : IsIso (0 : cokernel (finsetSigmaDesc G φ (T.sup id)) ⟶ _) :=
    isIso_of_isIso_sheafFiber_map _ fun x ↦ by
      have hx : IsZero ((X.uliftPointSmallEtale x).sheafFiber.obj
          (cokernel (finsetSigmaDesc G φ (T.sup id)))) :=
        (hall x).of_iso (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso _).app _)
      exact ⟨0, hx.eq_of_src _ _, hx.eq_of_src _ _⟩
  rw [IsZero.iff_id_eq_zero, ← IsIso.hom_inv_id (0 : cokernel (finsetSigmaDesc G φ (T.sup id)) ⟶
    cokernel (finsetSigmaDesc G φ (T.sup id))), zero_comp]

end Etale

end AlgebraicGeometry
