/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import WeilConjectures.AlgebraicGeometry.AffineBasisLowerTailSectionsReconstruction
import WeilConjectures.AlgebraicGeometry.AffineBasisLowerTailSectionsStep
import WeilConjectures.CategoryTheory.Triangulated.MilnorSequence
import WeilConjectures.CategoryTheory.DerivedLimitEventuallyIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Derived sections vanish above a lower tail with basis-acyclic homology

Source: Stacks Project, Tag 0BKT (cohomology-over-U-trivial), applied to the
strictly lower tail; Tags 071B and 0D64 for its tower reconstruction.
(blueprint: lem-sc-affine-basis-derived-sections-lower-tail-vanishing).
-/

@[expose] public section

universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Derived sections of the part strictly below `a` vanish in degrees at least `a`.
This is a statement about the lower tail only, without K-injectivity or a raw
cycle-class map.

Source: Stacks Project, Tag 0BKT, lemma-cohomology-over-U-trivial, applied to
the strictly lower tail; its proof uses Tag 0D64 and the bounded-below
hypercohomology spectral sequence. Tag 071B gives the compatible resolution model.
(blueprint: lem-sc-affine-basis-derived-sections-lower-tail-vanishing).

Proof: Restrict the derived lower tail to V. Affine opens W contained in V form
an open basis, including V itself. Its homology in degrees r < a is the restriction
of H^r(F); in degrees r >= a it is zero. Thus all its homology sheaves have
vanishing positive cohomology on this basis. Apply the compatible bounded-below
injective resolution tower of Tag 071B, after a shift of the cutoff if necessary.
Tag 0D64 identifies its limit with the lower tail. Its transitions are split
surjections degreewise, with injective kernels; applying sections preserves these
surjections and commutes with the inverse limit. For each bounded-below truncation,
the convergent hypercohomology spectral sequence has only its sections row:
positive cohomology of the actual homology sheaves vanishes also on V. Hence its
cohomology in degree i >= a is zero, and in degree i-1 the groups and transition
maps stabilize once the lower cutoff is below i-1. Apply the Milnor exact sequence.
The first derived limit in degree i-1 vanishes since its transitions are eventually
isomorphisms; the degree-i inverse limit is zero. Thus limit cohomology in degree i
is zero. This proves the claim for the canonical derived sections functor, not
for a chosen unrelated cohomology object. The exact module-to-abelian cohomology
comparison converts the stated source H vanishings to module sections vanishings;
forgetting modules reflects zero objects. Empty V yields the zero module category;
zero complexes and arbitrary integer a and i obey the same argument. No termwise
acyclicity, differential-cokernel acyclicity, or boundedness of F is assumed. -/
theorem affineBasisDerivedSections_lowerTail_isZero
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V)))]
    (F : CochainComplex X.Modules ℤ)
    (hhomology : ∀ (W : X.Opens), IsAffineOpen W → W ≤ V → ∀ (n : ℤ) (q : ℕ),
      Subsingleton (((F.homology n).restrict W.ι).H (q + 1)))
    (a i : ℤ) (hai : a ≤ i) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (S.rightDerivedFunctor.obj
        ((DerivedCategory.TStructure.t.truncLT a).obj (DerivedCategory.Q.obj F)))) := by
  dsimp only
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  let Vforget := forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
  let : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  let G := S ⋙ Vforget
  let t := DerivedCategory.TStructure.t (C := C)
  let E := (t.truncLT a).obj (DerivedCategory.Q.obj F)
  let H := G.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  have hbase : IsZero (H.obj ((t.truncGE (-(-a))).obj E)) := by
    have hz : IsZero ((t.truncGE a).obj E) :=
      t.isZero_truncGE_obj_of_isLE (a - 1) a (by omega) E
    have hz' := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map_isZero
      (G.isZero_rightDerivedFunctor_obj hz)
    simpa only [H, Functor.comp_obj, neg_neg] using hz'
  have hzero : ∀ n : ℤ, -a ≤ n → IsZero (H.obj ((t.truncGE (-n)).obj E)) := by
    refine Int.leInduction (motive := fun n _ ↦
      IsZero (H.obj ((t.truncGE (-n)).obj E))) hbase ?_
    intro n hn ih
    have hstep := affineBasisLowerTail_sections_step_isIso
      X V hV F hhomology a i (n + 1) (by omega)
    have htarget : IsZero (H.obj ((t.truncGE (-(n + 1) + 1)).obj E)) := by
      simpa only [show -(n + 1) + 1 = -n by omega] using ih
    have : IsIso (H.map ((t.natTransTruncGEOfLE (-(n + 1)) (-(n + 1) + 1)
      (Int.le_add_one (le_refl (-(n + 1))))).app E)) := hstep
    exact htarget.of_iso (asIso (H.map
      ((t.natTransTruncGEOfLE (-(n + 1)) (-(n + 1) + 1)
        (Int.le_add_one (le_refl (-(n + 1))))).app E)))
  let T : ℕ → DerivedCategory AddCommGrpCat.{u} := fun n ↦
    G.rightDerivedFunctor.obj ((t.truncGE (-(n : ℤ))).obj E)
  let f : ∀ n : ℕ, T (n + 1) ⟶ T n := fun n ↦
    G.rightDerivedFunctor.map ((t.natTransTruncGEOfLE
      (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)
  let K := Functor.ofOpSequence f
  obtain ⟨δ, hδ⟩ := affineBasisLowerTail_sections_reconstruction X V hV F hhomology a
  let p : G.rightDerivedFunctor.obj E ⟶ ∏ᶜ T := Pi.lift (fun n ↦
    G.rightDerivedFunctor.map ((t.truncGEπ (-(n : ℤ))).app E))
  obtain ⟨l, r, hmilnor, _⟩ := milnor_shortExact i
  have hδ' : IsDerivedLimitTriangle
      (fun n ↦ K.map (homOfLE (Nat.le_succ n)).op)
      (G.rightDerivedFunctor.obj E) p δ := by
    simpa only [K, Functor.ofOpSequence_map_homOfLE_succ] using hδ
  obtain ⟨⟨hw, hexact⟩, _⟩ := hmilnor K (G.rightDerivedFunctor.obj E) p δ hδ'
  let A := K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} (i - 1)
  have hA : ∃ m : ℕ, ∀ n : ℕ, m ≤ n →
      IsIso (A.map (homOfLE (Nat.le_succ n)).op) := by
    refine ⟨(1 - i).toNat, ?_⟩
    intro n hn
    have hstep := affineBasisLowerTail_sections_step_isIso
      X V hV F hhomology a (i - 1) ((n + 1 : ℕ) : ℤ) (by omega)
    rw! [show -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) by omega] at hstep
    simpa only [A, K, Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ,
      f, t] using hstep
  have hleft := isZero_firstDerivedLimit_of_eventually_isIso A hA
  let B := K ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  have hright : IsZero (limit B) := by
    rw [IsZero.iff_id_eq_zero]
    apply limit.hom_ext
    intro j
    let n := max j.unop (-a).toNat
    have hn : -a ≤ (n : ℤ) := by dsimp [n]; omega
    have hBn : IsZero (B.obj (Opposite.op n)) := hzero n hn
    have hπ : limit.π B (Opposite.op n) = 0 := hBn.eq_of_tgt _ _
    have hw := limit.w B (homOfLE (show j.unop ≤ n by exact le_max_left _ _)).op
    simpa only [hπ, zero_comp, Category.id_comp] using hw.symm
  have hz := hexact.exact.isZero_X₂ (hleft.eq_of_src _ _) (hright.eq_of_tgt _ _)
  let e := Functor.isoWhiskerRight
    (S.rightDerivedFunctorCompMapDerivedCategoryIso Vforget)
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} i) ≪≫
    Functor.isoWhiskerLeft S.rightDerivedFunctor
      (Vforget.mapDerivedCategoryHomologyFunctorIso i).symm
  have hzforget := hz.of_iso (e.app E).symm
  change IsZero ((DerivedCategory.homologyFunctor _ i).obj
    (S.rightDerivedFunctor.obj E))
  rw [IsZero.iff_id_eq_zero]
  apply Vforget.map_injective
  rw [Vforget.map_id, Vforget.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hzforget


end AlgebraicGeometry
