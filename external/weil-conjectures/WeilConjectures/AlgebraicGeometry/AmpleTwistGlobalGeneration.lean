/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.AmpleFinitePowerCover
import WeilConjectures.AlgebraicGeometry.AffineSectionCoverTwistGeneration
import WeilConjectures.AlgebraicGeometry.AmpleSeparated
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Global generation after a sufficiently positive ample twist

Source: EGA II, Proposition 4.5.5, implication ample ⇒ d); Stacks Project,
Properties, Proposition 01Q3, (1) ⇒ (7)
(blueprint: lem-weil-pbc-coherent-twist-global-generation).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Refine a finite generating cover by trivializing opens and transport the generators. -/
private theorem finiteType_tensor_invertible {X : Scheme.{u}} (F L : X.Modules)
    [F.IsFiniteType] [L.IsInvertible] : (tensorObj F L).IsFiniteType := by
  classical
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := L) x
  let W : q.I × X → X.Opens := fun i ↦ q.X i.1 ⊓ U i.2
  have hW : (_root_.Opens.grothendieckTopology X).CoversTop W := by
    rw [_root_.Opens.coversTop_iff]
    have hqcover : TopologicalSpace.IsOpenCover q.X :=
      (_root_.Opens.coversTop_iff _ q.X).mp q.coversTop
    refine TopologicalSpace.IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ ?_)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hqcover.iSup_eq_top.ge (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, x), hi, hU x⟩
  let d : (tensorObj F L).LocalGeneratorsData :=
    { I := q.I × X
      X := W
      coversTop := hW
      generators i := by
        let f : W i ⟶ q.X i.1 := CategoryTheory.homOfLE inf_le_left
        let P := SheafOfModules.overMap X.ringCatSheaf f
        let g := (q.generators i.1).map P (SheafOfModules.overMapUnitIso f).symm
        let t : (P.obj (F.over (q.X i.1))) ≅ F.over (W i) :=
          (SheafOfModules.overFunctorMap X.ringCatSheaf f).app F
        let j := X.homOfLE (inf_le_right : W i ≤ U i.2)
        let b : (pullback (W i).ι).obj L ≅ SheafOfModules.unit _ :=
          (pullbackCongr (X.homOfLE_ι (inf_le_right : W i ≤ U i.2)).symm).app L ≪≫
            ((pullbackComp j (U i.2).ι).app L).symm ≪≫
            (pullback j).mapIso (e i.2).some ≪≫ pullbackObjUnitIso j
        let a := (nonempty_over_tensorObj_iso F L b).some
        exact g.ofEpi (CategoryTheory.CategoryStruct.comp t.hom a.inv) }
  have hd : d.IsFiniteType :=
    { isFiniteType := fun i ↦ by
        have := hq.isFiniteType i.1
        dsimp only [d]
        infer_instance }
  exact SheafOfModules.IsFiniteType.mk (M := tensorObj F L) ⟨d, hd⟩

/-- A finite type quasi-coherent module twisted by sufficiently large powers of an
absolutely ample invertible module has a finite family of generating global sections.
Here `σ.IsFiniteType` says that the index type of the generating sections is finite;
the evaluation map from the free module on that family is an epimorphism by `σ.epi`.
The exponent is a natural number, since the node uses nonnegative tensor powers.

Source: EGA II, Proposition 4.5.5, last paragraph of the proof; Stacks Project,
Properties, Proposition 01Q3, (1) ⇒ (7)
(blueprint: lem-weil-pbc-coherent-twist-global-generation).

Proof following the six steps of the node:
1. Absolute ampleness gives quasi-compactness. The lemma
   `lem-weil-pbc-ample-scheme-separated` gives separatedness, so
   `lem-pc-section-clearing-denominators` applies.
2. Choose a finite affine cover by nonvanishing loci of sections of positive powers of L.
   Replace the sections by powers to put them all in one degree m > 0; their nonvanishing
   loci do not change, since the maximal ideals in the stalks are prime.
3. For any finite type quasi-coherent G, choose finite generators on each affine of this
   cover by `lem-weil-pbc-affine-finite-type-generating-sections`.
4. Extend each local generator after twisting by a suitable power of L^m, using
   `lem-pc-section-clearing-denominators`. Multiplication by further powers of the
   covering section extends these generators for every sufficiently large multiple of m.
5. By `lem-weil-pbc-nonvanishing-section-trivializes`, the covering section trivializes
   the twisting module on its nonvanishing locus. The extended generators therefore
   generate on every affine in the cover. Their finite union gives a sheaf epimorphism
   from the free module, as in `def-weil-pbc-generating-sections`.
6. Apply steps 3–5 to G = F tensor L^p for each 0 ≤ p < m. These modules remain
   quasi-coherent of finite type, since L is locally trivial. Take the maximum K of the
   finitely many bounds. For d ≥ mK, write d = mk + p with 0 ≤ p < m and k ≥ K;
   the resulting finite generating family gives the assertion. -/
theorem exists_finite_generatingSections_tensorPow_of_isAmple
    (X : Scheme.{u}) (L F : X.Modules) [L.IsInvertible]
    (hL : IsAmple X L) [F.IsQuasicoherent] [F.IsFiniteType] :
    ∃ d₀ : ℤ, ∀ d : ℕ, d₀ ≤ (d : ℤ) →
      ∃ σ : (tensorObj F (L.tensorPow d)).GeneratingSections, σ.IsFiniteType := by
  classical
  have : CompactSpace X := hL.1
  have : X.IsSeparated :=
    AlgebraicGeometry.isSeparated_of_isAmple X L hL
  obtain ⟨m, hm, r, s, haff, hcover⟩ := hL.exists_finite_common_power_cover X L
  have hres (p : Fin m) : ∃ K : ℕ, ∀ k : ℕ, K ≤ k →
      ∃ σ : (tensorObj (tensorObj F (L.tensorPow p))
        ((L.tensorPow m).tensorPow k)).GeneratingSections, σ.IsFiniteType := by
    have : (tensorObj F (L.tensorPow p)).IsQuasicoherent :=
      isQuasicoherent_tensorObj F (L.tensorPow p)
    have : (tensorObj F (L.tensorPow p)).IsFiniteType :=
      finiteType_tensor_invertible F (L.tensorPow p)
    exact exists_finite_generatingSections_tensorPow_of_affine_section_cover X
      (L.tensorPow m) (tensorObj F (L.tensorPow p)) s haff hcover
  choose K hK using hres
  let B := Finset.univ.sup K
  refine ⟨(m * B : ℕ), ?_⟩
  intro d hd
  have hd' : m * B ≤ d := by exact_mod_cast hd
  let p : Fin m := ⟨d % m, Nat.mod_lt d hm⟩
  have hk : B ≤ d / m := (Nat.le_div_iff_mul_le hm).2 (by simpa [mul_comm] using hd')
  obtain ⟨σ, hσ⟩ := hK p (d / m)
    ((Finset.le_sup (Finset.mem_univ p)).trans hk)
  have : σ.IsFiniteType := hσ
  have hexp : (p : ℕ) + m * (d / m) = d := Nat.mod_add_div d m
  let e : tensorObj (tensorObj F (L.tensorPow p)) ((L.tensorPow m).tensorPow (d / m)) ≅
      tensorObj F (L.tensorPow d) :=
    CategoryTheory.MonoidalCategory.associator _ _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl F)
        (CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl (L.tensorPow p))
          (L.tensorPowMulIso m (d / m)).symm) ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl F)
        (L.tensorPowAddIso p (m * (d / m))).symm ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl F)
        (CategoryTheory.eqToIso (congrArg L.tensorPow hexp))
  exact ⟨σ.ofEpi e.hom, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
