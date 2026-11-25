/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.H1ClosedPointIdealQuotient
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-! # Affine basic neighbourhoods of closed points

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
first paragraph of the proof (blueprint: lem-pqf-h1-closed-point-affine-basic-open).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem surjective_globalSections_of_h1_zero (X : Scheme.{u})
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h : Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj S.X₁)) :
    Function.Surjective (S.g.app ⊤) := by
  let F := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)))
  obtain ⟨δ, _, hδ⟩ := hS.exists_rightDerived_full_long_exact F
  obtain ⟨_, _, _, hex, _⟩ := hδ 0
  have hd : δ 0 = 0 := by
    ext a
    exact h.elim _ _
  have he : Epi ((F.rightDerived 0).map S.g) := hex.epi_f hd
  let e := F.rightDerivedZeroIsoSelf
  have he' : Epi (F.map S.g) := by
    have hn := e.hom.naturality S.g
    have hc : Epi ((F.rightDerived 0).map S.g ≫ e.hom.app S.X₃) := inferInstance
    rw [hn] at hc
    exact epi_of_epi (e.hom.app S.X₂) (F.map S.g)
  exact (ModuleCat.epi_iff_surjective (F.map S.g)).mp he'

/-- Ideal H¹ vanishing gives an affine basic neighbourhood of each closed point.

Source: Stacks Project, Tag 01XF, label lemma-quasi-compact-h1-zero-covering,
first paragraph of the proof (blueprint: lem-pqf-h1-closed-point-affine-basic-open).

Proof: Choose an affine neighbourhood U = Spec A of x and let m be its maximal
ideal. Put Z = X \ U and Z' = Z ∪ {x}. The reduced induced closed subschemes give
quasi-coherent ideals I and I' with I' ≤ I. On U these are A and m; on X \ {x}
they agree. Thus I/I' is supported at x and its sections are A/m (glue using
the cover U, X \ {x}; the quotient is zero on the second open and the overlap).
The long exact sequence and H¹(X,I') = 0 lift 1 in A/m to a section f of I.
Viewed in the structure sheaf, f vanishes on Z and is nonzero at x, so
x ∈ X_f ⊆ U. Restriction identifies X_f with D(f|_U), which is affine.
No quasi-compactness or separation hypothesis is used in this step. -/
theorem exists_affineBasicOpen_of_isClosed_singleton_of_h1_ideal_zero (X : Scheme.{u})
    (hI : ∀ (I : X.IdealSheafData), I.toModules.IsQuasicoherent →
      Subsingleton ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules))
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  classical
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := x) (U := ⊤) (by trivial)
  let Z : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  let Z' : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ ∪ {x},
    U.isOpen.isClosed_compl.union hx⟩
  let I := Scheme.IdealSheafData.vanishingIdeal Z
  let J := Scheme.IdealSheafData.vanishingIdeal Z'
  let i := Scheme.IdealSheafData.toModulesOfLE
    (Scheme.IdealSheafData.vanishingIdeal_antimono
      (show Z ≤ Z' from Set.subset_union_left))
  have : Mono i := by
    have hi : i ≫ I.toModulesι = J.toModulesι :=
      Scheme.IdealSheafData.toModulesOfLE_toModulesι _
    have : Mono (i ≫ I.toModulesι) := hi ▸ inferInstance
    exact mono_of_mono i I.toModulesι
  have hS : (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
    { exact := ShortComplex.exact_cokernel i }
  obtain ⟨q, hq⟩ := exists_closedPoint_ideal_quotient_section X U x hxU hx
  have hJqc : J.toModules.IsQuasicoherent := by
    have := SheafOfModules.isQuasicoherent_unit (R := J.subscheme.ringCatSheaf)
    have := SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf)
    have : SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
        ((SheafOfModules.pushforward J.subschemeι.toRingCatSheafHom).obj
          (SheafOfModules.unit J.subscheme.ringCatSheaf)) :=
      Scheme.Modules.isQuasicoherent_pushforward_of_isClosedImmersion J.subschemeι _
    exact Scheme.Modules.isQuasicoherent_kernel J.toPushforwardSubscheme
  obtain ⟨s, hs⟩ := surjective_globalSections_of_h1_zero X
    (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)) hS
      (hI J hJqc) q
  let f : Γ(X, ⊤) := I.toModulesι.app ⊤ s
  have hxone : X.evaluation ⊤ x (by trivial) f = 1 := hq s hs
  have hxf : x ∈ X.basicOpen f := by
    apply (X.evaluation_ne_zero_iff_mem_basicOpen x (by trivial) f).mp
    rw [hxone]
    exact one_ne_zero
  have hfI : f ∈ I.idealOfOpens ⊤ := by
    change f ∈ (I.idealOfOpens ⊤ : Set Γ(X, ⊤))
    rw [← I.range_toModulesι_app_eq_idealOfOpens]
    exact ⟨s, rfl⟩
  have hfZ := (Scheme.IdealSheafData.reduced_induced_closed_subscheme X Z).1 ⊤ f |>.mp hfI
  have hle : X.basicOpen f ≤ U := by
    intro y hy
    by_contra hyU
    have hyzero := hfZ y (by trivial) hyU
    exact ((X.evaluation_eq_zero_iff_notMem_basicOpen y (by trivial) f).mp hyzero) hy
  refine ⟨f, hxf, ?_⟩
  have ha := hU.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op f)
  rwa [Scheme.basicOpen_res, inf_eq_right.mpr hle] at ha

end AlgebraicGeometry
