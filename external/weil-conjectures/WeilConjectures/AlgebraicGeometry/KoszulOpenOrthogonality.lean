/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import WeilConjectures.AlgebraicGeometry.KoszulAffineDetection
import WeilConjectures.AlgebraicGeometry.DerivedOpenUnitCone
import WeilConjectures.AlgebraicGeometry.KoszulPowersOrthogonality
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZero

/-! # Koszul orthogonality detects extension from an open

Source: Stacks Project, Lemma 36.15.2, Tag 09IR
(blueprint: lem-pc-perfect-generation-koszul-orthogonal).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- For an affine open `V = Spec A`, orthogonality to all shifts of its Koszul complex is
exactly invertibility of the canonical derived open-restriction unit.
Source: Stacks Project, Tag 09IR
(blueprint: lem-pc-perfect-generation-koszul-orthogonal).

Proof:
1. Form the cone `C` of the canonical map. The Koszul complex restricts to zero on the
   complement of its zero locus: each `f i` acts null-homotopically and is a unit on `D(f i)`
   (Tag 0663). Derived adjunction (lem-pc-ringed-spaces-derived-adjoint-general) therefore
   makes all Hom groups from its shifts to the derived pushforward zero. The triangle
   identifies vanishing against `E` with vanishing against `C`. The unit is invertible
   exactly when `C` is zero.
2. The cone restricts to zero on the open. Koszul multiplication triangles (Tag 062C)
   imply vanishing against every positive-power tuple by induction on the exponents.
   Apply lem-pc-koszul-affine-detection to this supported cone to obtain `C = 0`.
3. Conversely, an invertible unit identifies `E` with its derived pushforward; restriction
   of the Koszul complex is zero, so derived adjunction gives the required Hom vanishing.

`a` identifies `Spec A` with the affine open `V`. Open immersion `j` is represented by
`U.ι`. The overlap is `a ⁻¹ᵁ U`. A right adjoint to exact derived open restriction is the
unbounded derived direct image; `adj.unit` is the canonical map of the statement.
The Koszul complex `K` is `ExteriorAlgebra.koszulComplex A r f` placed in cohomological
degrees `-q` by `ComplexShape.embeddingDownNat`, sheafified termwise by `tilde.functor`
and localized, in the form of lem-pc-koszul-affine-detection. -/
theorem koszul_open_orthogonality
    (X : Scheme.{u₁}) (U : X.Opens) (A : Type u₁) [CommRing A]
    (a : Spec (.of A) ⟶ X) [IsOpenImmersion a]
    (hcover : U ⊔ a ''ᵁ ⊤ = ⊤) (hqc : IsCompact (a ⁻¹ᵁ U : Set (Spec (.of A))))
    (r : ℕ) (f : Fin r → A)
    (hZ : ∀ x : PrimeSpectrum A, x ∉ a ⁻¹ᵁ U ↔ ∀ i : Fin r, f i ∈ x.asIdeal)
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} ((moduleRings (Spec (.of A)).toRingedSpace).over (a ⁻¹ᵁ U)))]
    (R : DerivedCategory
        (SheafOfModules.{u₁} ((moduleRings (Spec (.of A)).toRingedSpace).over (a ⁻¹ᵁ U))) ⥤
      schemeDerivedCategory (Spec (.of A)))
    (adj : (SheafOfModules.overFunctor.{u₁}
      (moduleRings (Spec (.of A)).toRingedSpace) (a ⁻¹ᵁ U)).mapDerivedCategory ⊣ R)
    (E : schemeDerivedCategory (Spec (.of A)))
    (hE : schemeDerivedQCohProperty (Spec (.of A)) E) :
    IsIso (adj.unit.app E) ↔
      ∀ n : ℤ, Subsingleton
        (((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u₁} A)
            (SheafOfModules.{u₁} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r f).extend
              ComplexShape.embeddingDownNat)))⟦n⟧) ⟶ E) := by
  classical
  have _cover := hcover
  let K : schemeDerivedCategory (Spec (.of A)) := DerivedCategory.Q.obj
    ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u₁} A)
      (SheafOfModules.{u₁} (moduleRings (Spec (.of A)).toRingedSpace))
      _ _ _ _ (tilde.functor (.of A))
      ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat))
  let F := (SheafOfModules.overFunctor.{u₁}
    (moduleRings (Spec (.of A)).toRingedSpace) (a ⁻¹ᵁ U)).mapDerivedCategory
  change IsIso (adj.unit.app E) ↔ ∀ n : ℤ, Subsingleton (K⟦n⟧ ⟶ E)
  have hU : a ⁻¹ᵁ U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i) := by
    ext x
    change x ∈ a ⁻¹ᵁ U ↔ x ∈ ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i)
    rw [Opens.mem_iSup]
    change x ∈ a ⁻¹ᵁ U ↔ ∃ i, f i ∉ x.asIdeal
    simpa only [not_forall, not_not] using not_congr (hZ x)
  have hFK (n : ℤ) : Limits.IsZero (F.obj (K⟦n⟧)) :=
    isZero_restrict_shift_koszul A r f (a ⁻¹ᵁ U) hU n
  have hB (n : ℤ) : Subsingleton (K⟦n⟧ ⟶ R.obj (F.obj E)) := by
    have : Subsingleton (F.obj (K⟦n⟧) ⟶ F.obj E) := ⟨(hFK n).eq_of_src⟩
    exact (adj.homEquiv (K⟦n⟧) (F.obj E)).symm.subsingleton
  constructor
  · intro hi n
    let := hi
    exact ⟨fun x y ↦ (cancel_mono (adj.unit.app E)).mp
      (@Subsingleton.elim _ (hB n) _ _)⟩
  · intro horth
    obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle (adj.unit.app E)
    let T := Pretriangulated.Triangle.mk (adj.unit.app E) g h
    obtain ⟨hC, hres⟩ := derived_open_unit_cone_properties A (a ⁻¹ᵁ U) hqc R adj E hE
      C g h hT
    have hshift (n : ℤ) : Subsingleton (K⟦n⟧ ⟶ E⟦(1 : ℤ)⟧) := by
      have hs := horth (n + -1)
      have : Subsingleton (K⟦n⟧⟦(-1 : ℤ)⟧ ⟶ E) := by
        refine ⟨fun x y ↦ ?_⟩
        apply (cancel_epi ((shiftFunctorAdd _ n (-1)).hom.app K)).mp
        exact Subsingleton.elim _ _
      exact @Equiv.subsingleton _ _
        ((shiftEquiv _ (1 : ℤ)).symm.toAdjunction.homEquiv (K⟦n⟧) E).symm this
    have horthC (n : ℤ) : Subsingleton (K⟦n⟧ ⟶ C) := by
      have hz (v : K⟦n⟧ ⟶ C) : v = 0 := by
        obtain ⟨b, hb⟩ := T.coyoneda_exact₃ hT v
          (@Subsingleton.elim _ (hshift n) _ 0)
        have hb0 : b = 0 := @Subsingleton.elim _ (hB n) _ 0
        simpa [hb0] using hb
      exact ⟨fun v w ↦ (hz v).trans (hz w).symm⟩
    have hzero : Limits.IsZero C := isZero_of_koszul_powers_orthogonal A r f (a ⁻¹ᵁ U) hU
      ⟨C, hC⟩ hres (koszul_powers_orthogonal_of_orthogonal A r f C horthC)
    exact (T.isZero₃_iff_isIso₁ hT).mp hzero

end AlgebraicGeometry
