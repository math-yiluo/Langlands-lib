/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PrincipalOpenCechTotal
import WeilConjectures.AlgebraicGeometry.PrincipalOpenSectionsResolutionQuasiIso
import WeilConjectures.AlgebraicGeometry.PrincipalCechFiniteColumnModel
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Principal Čech totalization of a quasi-coherent resolution

Source: Stacks, Tags 08D2 and 08C2
(blueprint: lem-sc-principal-cech-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- On a finite principal-open cover, totalization takes a K-injective resolution
of a termwise quasi-coherent complex to a quasi-isomorphism. The resolution's
terms need not be quasi-coherent.
Source: Stacks, Tags 08D2 and 08C2
(blueprint: lem-sc-principal-cech-resolution-quasi-iso).

Proof:
1. Restrict F and its resolution i to each nonempty principal intersection D(g_J).
Restriction preserves quasi-isomorphisms and K-injectivity. The terms, cokernels
of differentials, and cohomology sheaves of F restricted to this affine open are
quasi-coherent, so their higher cohomology vanishes. The unbounded affine acyclic
section comparison therefore says that Γ(D(g_J), i) is a quasi-isomorphism.
This is the intersectionwise comparison used in the proof of
lem-sc-qcoh-complex-alternating-cech-derived-sections (Tags 08D2 and 08C2).
2. Filter the two principal Čech totals by subset cardinality, equivalently by
Čech degree. The map induced by i respects the filtration; its graded map in
row p is the finite product over |J|=p+1 of those section quasi-isomorphisms,
shifted by p. Finite products and shifts preserve quasi-isomorphisms.
3. There are only rows 0 through r-1. Induction on this finite filtration, using
the long exact cohomology sequences, proves that the total map is a
quasi-isomorphism. This argument makes no boundedness assumption in the vertical
direction. For r=0 both totals are zero. For r=1 it is the affine section
comparison alone. The zero complex case is included by the same argument. -/
theorem principalCech_resolution_quasiIso
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    (F J : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso ((principalCechFunctor r f).map i) := by
  have hsections (S : {S : Finset (Fin r) // S.Nonempty}) :
      QuasiIso (((affineOpenSections A
        (principalCechIntersection r f S.val)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map i) := by
    exact principalOpenSections_resolution_quasiIso A (∏ j ∈ S.val, f j) F J hF i
  obtain ⟨K, L, φ, hKge, hKle, hLge, hLle, hcolumns, ⟨e⟩⟩ :=
    principalCech_finiteColumn_model A r f F J i
  have := hKge
  have := hKle
  have := hLge
  have := hLle
  have htotal : QuasiIso (HomologicalComplex₂.total.map φ (ComplexShape.up ℤ)) :=
    HomologicalComplex₂.total.quasiIso_map_of_finitely_many_columns φ 0 ((r : ℤ) - 1)
      (fun p hp hp' ↦ hcolumns p hp hp' hsections)
  exact (quasiIso_iff_of_arrow_mk_iso _ _ e).mpr htotal

end AlgebraicGeometry
