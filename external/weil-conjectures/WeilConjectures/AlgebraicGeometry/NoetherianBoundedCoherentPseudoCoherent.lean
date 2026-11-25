/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.AlgebraicGeometry.CoherentPseudoCoherent
import WeilConjectures.AlgebraicGeometry.PseudoCoherentDistinguishedTriangle

/-! # Bounded coherent complexes on Noetherian schemes are pseudo-coherent

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.10.3 (Tag 08E8;
label lemma-identify-pseudo-coherent-noetherian)
(blueprint: lem-pc-noetherian-bounded-coherent-pseudo-coherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private theorem pseudoCoherent_of_iso (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    {E F : schemeDerivedCategory S}
    (e : E ≅ F) (hE : IsPseudoCoherent S E) : IsPseudoCoherent S F := by
  intro x
  obtain ⟨U, hx, P, hb, hf, ⟨eP⟩⟩ := hE x
  exact ⟨U, hx, P, hb, hf,
    ⟨((SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory.mapIso
      e.symm) ≪≫ eP⟩⟩

private theorem pseudoCoherent_shift (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    {E : schemeDerivedCategory S}
    (hE : IsPseudoCoherent S E) (n : ℤ) : IsPseudoCoherent S (E⟦n⟧) := by
  intro x
  obtain ⟨U, hx, P, ⟨b, hb⟩, hf, ⟨eP⟩⟩ := hE x
  refine ⟨U, hx, P⟦n⟧, ⟨b - n, fun i hi ↦ ?_⟩, ?_, ?_⟩
  · exact hb (i + n) (by omega)
  · exact fun i ↦ hf (i + n)
  · let F := (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory
    exact ⟨(F.commShiftIso n).app E ≪≫ (shiftFunctor _ n).mapIso eP ≪≫
      ((DerivedCategory.Q.commShiftIso n).app P).symm⟩

private theorem pseudoCoherent_of_isZero (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    {E : schemeDerivedCategory S}
    (hE : IsZero E) : IsPseudoCoherent S E := by
  intro x
  let U : S.Opens := ⊤
  let R := (moduleRings S.toRingedSpace).over U
  have hfree : IsZero (SheafOfModules.free (R := R) (ULift.{u} (Fin 0))) := by
    apply (IsZero.iff_id_eq_zero _).2
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact Fin.elim0 i.down
  let P : CochainComplex (SheafOfModules.{u} R) ℤ := HomologicalComplex.zero
  have hP : IsZero P := HomologicalComplex.isZero_zero
  refine ⟨U, by trivial, P, ⟨0, fun i _ ↦ ?_⟩, fun i ↦ ?_, ?_⟩
  · exact (HomologicalComplex.eval _ _ i).map_isZero hP
  · exact ⟨0, ⟨((HomologicalComplex.eval _ _ i).map_isZero hP).iso hfree⟩⟩
  · let F := (SheafOfModules.overFunctor.{u} (moduleRings S.toRingedSpace) U).mapDerivedCategory
    exact ⟨(F.map_isZero hE).iso (DerivedCategory.Q.map_isZero hP)⟩

/-- On a Noetherian scheme `S`, an object `E` of `D(𝒪_S)` whose cohomology sheaves vanish
outside a bounded range `[a, b]` and are all coherent is pseudo-coherent. Source: Stacks
Project, Tag 08E8 (blueprint: lem-pc-noetherian-bounded-coherent-pseudo-coherent).

Proof: Choose `a ≤ b` with `H^i(E) = 0` for `i < a` and `i > b`. For each `i ∈ [a, b]` the
sheaf `H^i(E)` is coherent on the Noetherian scheme `S`, so it is pseudo-coherent as a complex
in degree zero (lem-sc-coherent-pseudo-coherent), and so is its shift `H^i(E)[-i]`. For
`m = b, b - 1, …, a` the lower-truncation triangle
`H^m(E)[-m] → τ_{≥ m}E → τ_{≥ m+1}E → H^m(E)[-m+1]`
(lem-pc-derived-lower-truncation-step-triangle) and the two-out-of-three property of
pseudo-coherence for distinguished triangles (lem-pc-pseudo-coherent-distinguished-triangle)
show by descending induction that `τ_{≥ m}E` is pseudo-coherent, starting from
`τ_{≥ b+1}E = 0`. At `m = a` the vanishing below `a` identifies `τ_{≥ a}E` with `E`. -/
theorem isPseudoCoherent_of_bounded_coherent
    (S : Scheme.{u}) [IsNoetherian S]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S)
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ,
      i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent S.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) i).obj E)) :
    IsPseudoCoherent S E := by
  let C := SheafOfModules.{u} (moduleRings S.toRingedSpace)
  let t := DerivedCategory.TStructure.t (C := C)
  obtain ⟨a, b, hab⟩ := hbounded
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2
    (fun i hi ↦ hab i (Or.inl hi))
  have hLE : E.IsLE b := (DerivedCategory.isLE_iff E b).2
    (fun i hi ↦ hab i (Or.inr hi))
  have htrunc (k : ℕ) : IsPseudoCoherent S ((t.truncGE (b + 1 - k)).obj E) := by
    induction k with
    | zero =>
      apply pseudoCoherent_of_isZero S
      simpa using t.isZero_truncGE_obj_of_isLE b (b + 1) rfl E
    | succ k ih =>
      let m : ℤ := b + 1 - (k + 1)
      obtain ⟨f, h, hT⟩ := DerivedCategory.exists_lowerTruncationStepTriangle E (-m)
      have hpc : IsPseudoCoherent S
          ((DerivedCategory.Q.obj ((CochainComplex.singleFunctor C 0).obj
            ((DerivedCategory.homologyFunctor C (- -m)).obj E)))⟦-m⟧) := by
        exact pseudoCoherent_shift S
          (isPseudoCoherent_singleFunctor_obj_of_isCoherent S _ (hcoherent (- -m))) (-m)
      have hright : IsPseudoCoherent S ((t.truncGE (- -m + 1)).obj E) := by
        convert ih using 1
        dsimp [m]
        congr 2
        omega
      have hmiddle := isPseudoCoherent_of_distinguished_triangle S
        (CategoryTheory.Pretriangulated.Triangle.mk f _ h) hT hpc hright
      convert hmiddle using 1
      dsimp [m]
      congr 2
      omega
  let k : ℕ := (b + 1 - a).toNat
  have hk : b + 1 - (k : ℤ) ≤ a := by dsimp [k]; omega
  have hGE' : t.IsGE E (b + 1 - k) := t.isGE_of_ge E _ a hk
  have : IsIso ((t.truncGEπ (b + 1 - k)).app E) :=
    (t.isGE_iff_isIso_truncGEπ_app _ E).1 hGE'
  exact pseudoCoherent_of_iso S (asIso ((t.truncGEπ (b + 1 - k)).app E)).symm (htrunc k)

end AlgebraicGeometry.Scheme
