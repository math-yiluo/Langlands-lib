/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.Sites.CohomologyFilteredColimit
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Pro-étale cohomology of a qcqs scheme commutes with filtered colimits

Let `S` be a quasi-compact quasi-separated scheme and `c` a colimit cocone of a filtered diagram
`D : K ⥤ Sh(S_proét, Ab)` of abelian pro-étale sheaves, indexed by a `u + 1`-small category.
Then `colim_k Hᵠ(S_proét, D_k) ⟶ Hᵠ(S_proét, c.pt)` is bijective for every `q`.

## Main statements

- `AlgebraicGeometry.Scheme.ProEt.exists_finite_affine_of_mem_topology`: every covering sieve
  of a quasi-compact quasi-separated object of `S.ProEt` contains a finite covering family of
  objects with affine underlying scheme.
- `AlgebraicGeometry.Scheme.ProEt.H_map_isColimit_of_isFiltered_small`: pro-étale cohomology of
  a qcqs scheme commutes with filtered colimits.
- `AlgebraicGeometry.Scheme.ProEt.subsingleton_H_of_isColimit_of_isFiltered`: a filtered colimit
  of pro-étale sheaves with vanishing `Hᵠ` has vanishing `Hᵠ`.

## Implementation notes

We apply the site-generic `CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small` to the
class of objects of `S.ProEt` with quasi-compact quasi-separated underlying scheme. Pro-étale
coverings are quasi-compact, so a covering sieve of such an object contains a finite family of
affine opens of members of a covering family, and finite products in `Over V` of objects with
qcqs underlying scheme again have qcqs underlying scheme.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- On an object `W` of the small pro-étale site with quasi-compact quasi-separated underlying
scheme, every covering sieve contains a finite covering family of objects with affine
underlying schemes: affine opens of the members of a quasi-compact covering family. -/
lemma exists_finite_affine_of_mem_topology {W : S.ProEt} [CompactSpace W.left]
    [QuasiSeparatedSpace W.left] {R : Sieve W} (hR : R ∈ topology S W) :
    ∃ (n : ℕ) (U : Fin n → S.ProEt) (g : ∀ a, U a ⟶ W), (∀ a, R (g a)) ∧
      (∀ a, IsAffine (U a).left) ∧ Sieve.ofArrows U g ∈ topology S W := by
  obtain ⟨P, hP, hle⟩ := mem_topology_iff.1 hR
  obtain ⟨ι, Z, f, rfl⟩ := P.exists_eq_ofArrows
  rw [mem_precoverage_iff, Presieve.map_ofArrows] at hP
  let E : PreZeroHypercover W.left := ⟨ι, fun i ↦ (Z i).left, fun i ↦ (f i).left⟩
  have hE : QuasiCompactCover E := Scheme.presieve₀_mem_qcPrecoverage_iff.1 hP.1
  have hEf (i : ι) : WeaklyEtale (f i).left :=
    ((Scheme.presieve₀_mem_precoverage_iff E).1 hP.2).2 i
  obtain ⟨n, j, V, hV, hcov⟩ :=
    QuasiCompactCover.exists_isAffineOpen_of_isCompact E (U := ⊤) isCompact_univ
  refine ⟨n, fun a ↦ ofOpenImmersion (Z (j a)) (V a).ι,
    fun a ↦ ofOpenImmersionHom _ _ ≫ f (j a),
    fun a ↦ R.downward_closed (hle _ _ (Presieve.ofArrows.mk (j a))) _, fun a ↦ hV a, ?_⟩
  rw [mem_topology_iff]
  refine ⟨_, ?_, Sieve.le_generate _⟩
  rw [mem_precoverage_iff, Presieve.map_ofArrows]
  let E' : PreZeroHypercover W.left := ⟨Fin n, fun a ↦ V a, fun a ↦ (V a).ι ≫ (f (j a)).left⟩
  have hE' : E'.presieve₀ ∈ Scheme.precoverage @WeaklyEtale W.left := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun a ↦ ?_⟩
    · have hx : x ∈ ⋃ a, E.f (j a) '' (V a) := by
        rw [hcov]
        trivial
      obtain ⟨a, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
      exact ⟨a, ⟨y, hy⟩, rfl⟩
    · exact inferInstanceAs (WeaklyEtale ((V a).ι ≫ (f (j a)).left))
  let 𝒱 : W.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'⟩
  have (a : Fin n) : QuasiCompact (𝒱.f a) :=
    have : IsAffine (V a) := hV a
    quasiCompact_of_compactSpace _
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.2 (QuasiCompactCover.of_finite (𝒰 := 𝒱)), hE'⟩

/-- Quasi-compactness and quasi-separatedness of the underlying scheme are invariant under
isomorphisms of objects of the small pro-étale site. -/
lemma compactSpace_and_quasiSeparatedSpace_of_iso {A B : S.ProEt} (e : A ≅ B)
    (h : CompactSpace A.left ∧ QuasiSeparatedSpace A.left) :
    CompactSpace B.left ∧ QuasiSeparatedSpace B.left := by
  let φ := TopCat.homeoOfIso
    (Scheme.forgetToTop.mapIso ((ProEt.forget S ⋙ Over.forget S).mapIso e))
  exact ⟨@Homeomorph.compactSpace _ _ _ _ h.1 φ, (quasiSeparatedSpace_congr φ).1 h.2⟩

/-- A fibre product of objects of the small pro-étale site with quasi-compact quasi-separated
underlying schemes over one with quasi-separated underlying scheme has quasi-compact
quasi-separated underlying scheme. -/
lemma compactSpace_and_quasiSeparatedSpace_pullback {V A B : S.ProEt} (f : A ⟶ V) (g : B ⟶ V)
    [QuasiSeparatedSpace V.left] [CompactSpace A.left] [QuasiSeparatedSpace A.left]
    [CompactSpace B.left] [QuasiSeparatedSpace B.left] :
    CompactSpace (pullback f g).left ∧ QuasiSeparatedSpace (pullback f g).left := by
  let iso := PreservesPullback.iso (ProEt.forget S ⋙ Over.forget S) f g
  have : QuasiCompact f.left := quasiCompact_of_compactSpace _
  have : CompactSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) := inferInstance
  have : QuasiSeparatedSpace ↥(Limits.pullback (C := Scheme.{u}) f.left g.left) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f.left g.left)
  let φ := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso iso).symm
  exact ⟨@Homeomorph.compactSpace _ _ _ _ ‹_› φ, (quasiSeparatedSpace_congr φ).1 ‹_›⟩

/-- A finite product in `Over V` of objects of the small pro-étale site with quasi-compact
quasi-separated underlying schemes has quasi-compact quasi-separated underlying scheme, if `V`
has. -/
lemma compactSpace_and_quasiSeparatedSpace_piObj {V : S.ProEt} [CompactSpace V.left]
    [QuasiSeparatedSpace V.left] {J : Type*} [Finite J] (U : J → Over V)
    (hU : ∀ j, CompactSpace (U j).left.left ∧ QuasiSeparatedSpace (U j).left.left) :
    CompactSpace (∏ᶜ U).left.left ∧ QuasiSeparatedSpace (∏ᶜ U).left.left := by
  let P : ObjectProperty (Over V) := fun A ↦
    CompactSpace A.left.left ∧ QuasiSeparatedSpace A.left.left
  have hiso {A B : Over V} (e : A ≅ B) (h : P A) : P B :=
    compactSpace_and_quasiSeparatedSpace_of_iso ((Over.forget V).mapIso e) h
  have : P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty) := ⟨by
    rintro A ⟨h⟩
    have hA : IsTerminal A := (isLimitEquivIsTerminalOfIsEmpty _ _) h.isLimit
    exact hiso (Over.mkIdTerminal.uniqueUpToIso hA) ⟨‹_›, ‹_›⟩⟩
  have : P.IsClosedUnderBinaryProducts := ⟨by
    rintro A ⟨h⟩
    let e : A ≅ h.diag.obj ⟨.left⟩ ⨯ h.diag.obj ⟨.right⟩ :=
      h.isLimit.conePointUniqueUpToIso (limit.isLimit _) ≪≫ HasLimit.isoOfNatIso (diagramIsoPair _)
    refine hiso e.symm ?_
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.left⟩
    obtain ⟨_, _⟩ := h.prop_diag_obj ⟨.right⟩
    exact compactSpace_and_quasiSeparatedSpace_of_iso (Over.prodLeftIsoPullback _ _).symm
      (compactSpace_and_quasiSeparatedSpace_pullback _ _)⟩
  have : P.IsClosedUnderFiniteProducts := .mk'
  exact P.prop_product hU

/-- The objects of the small pro-étale site with quasi-compact quasi-separated underlying
scheme satisfy the hypothesis of the Čech criterion: every covering sieve of such an object
contains a finite covering family whose Čech nerve again consists of such objects. -/
lemma exists_finite_cechNerve_of_mem_topology {V : S.ProEt}
    (hV : CompactSpace V.left ∧ QuasiSeparatedSpace V.left) {R : Sieve V}
    (hR : R ∈ topology S V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), CompactSpace (Presheaf.cechNerveObj U y).left.left ∧
        QuasiSeparatedSpace (Presheaf.cechNerveObj U y).left.left) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ topology S V := by
  obtain ⟨_, _⟩ := hV
  obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_topology hR
  refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg, hg⟩
  refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
  have := hU (y l)
  exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
    inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩

variable (S) in
/-- **Pro-étale cohomology commutes with `u + 1`-small filtered colimits on a qcqs scheme.**
Let `S` be quasi-compact and quasi-separated and let `c` be a colimit cocone of a filtered
diagram `D : K ⥤ Sh(S_proét, Ab)` indexed by a `u + 1`-small category. Then for every `q` the
canonical map `colim_k Hᵠ(S_proét, D_k) ⟶ Hᵠ(S_proét, c.pt)` is bijective, spelled out
elementwise. This is `CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small` for the class
of objects with quasi-compact quasi-separated underlying scheme. -/
theorem H_map_isColimit_of_isFiltered_small [CompactSpace S] [QuasiSeparatedSpace S]
    {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1}} {c : Cocone D} (hc : IsColimit c)
    (q : ℕ) :
    (∀ x : Sheaf.H c.pt q, ∃ (k : K) (y : Sheaf.H (D.obj k) q),
      Sheaf.H.map (c.ι.app k) q y = x) ∧
    ∀ (k : K) (y : Sheaf.H (D.obj k) q), Sheaf.H.map (c.ι.app k) q y = 0 →
      ∃ (k' : K) (a : k ⟶ k'), Sheaf.H.map (D.map a) q y = 0 :=
  Sheaf.H_map_isColimit_of_isFiltered_small
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale S)
    (fun V : S.ProEt ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left)
    ⟨‹CompactSpace S›, ‹QuasiSeparatedSpace S›⟩
    (fun _ hV _ hR ↦ exists_finite_cechNerve_of_mem_topology hV hR) hc q

variable (S) in
/-- **Vanishing of pro-étale cohomology passes to filtered colimits.** On a quasi-compact
quasi-separated scheme `S`, if the pro-étale sheaves `D k` of a `u + 1`-small filtered diagram
have vanishing `Hᵠ`, then so does their colimit. -/
theorem subsingleton_H_of_isColimit_of_isFiltered [CompactSpace S] [QuasiSeparatedSpace S]
    {K : Type (u + 1)} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Sheaf (topology S) AddCommGrpCat.{u + 1}} {c : Cocone D} (hc : IsColimit c)
    (q : ℕ) (hD : ∀ k, Subsingleton (Sheaf.H (D.obj k) q)) :
    Subsingleton (Sheaf.H c.pt q) :=
  Sheaf.subsingleton_H_of_isColimit_of_isFiltered
    (MorphismProperty.Over.mkIdTerminal @WeaklyEtale S)
    (fun V : S.ProEt ↦ CompactSpace V.left ∧ QuasiSeparatedSpace V.left)
    ⟨‹CompactSpace S›, ‹QuasiSeparatedSpace S›⟩
    (fun _ hV _ hR ↦ exists_finite_cechNerve_of_mem_topology hV hR) hc q hD

end AlgebraicGeometry.Scheme.ProEt
