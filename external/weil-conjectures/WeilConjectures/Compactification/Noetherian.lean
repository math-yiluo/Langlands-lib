/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Compactification.TwoOpen
public import WeilConjectures.Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.Mathlib.Topology.Maps.Basic

/-!

# Nagata compactification over a Noetherian base

This file proves **Nagata's compactification theorem over a Noetherian base**
(`AlgebraicGeometry.nagataCompactification_of_isNoetherian`; blueprint `thm:nagata-noetherian`,
proof order item 52): a separated, quasi-compact morphism locally of finite type to a
Noetherian scheme factors as an open immersion followed by a proper morphism.

The proof is an induction over a finite affine open cover of the source with dense total
intersection. Such a cover exists because the source is Noetherian, hence has finitely many
irreducible components
(`AlgebraicGeometry.exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter`); a
choice of one is packaged as `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter`.
Writing `U 0, …, U (n - 1)` for the cover and `X_r = U 0 ∪ ⋯ ∪ U (r - 1)` for its partial
unions (`AlgebraicGeometry.Scheme.partialAffineOpenUnions`), the induction runs as follows:

- `X_0` is empty, so `X_0 ⟶ S` is proper and in particular compactifiable;
- `X_1 = U 0` is affine, so the affine case
  `AlgebraicGeometry.HasCompactification.of_isQuasiAffine` applies;
- `X_{r+1} = X_r ∪ U r` is covered by the two opens `X_r` and `U r`, whose intersection
  contains the (dense) total intersection of the cover and is therefore dense in `X_{r+1}`
  (`Dense.preimage_val_inter`); the two-open theorem
  `AlgebraicGeometry.HasCompactification.of_two_open_cover` then compactifies `X_{r+1} ⟶ S`.

Separatedness, finite type and quasi-compactness of `X_r ⟶ S` — the hypotheses of the
two-open theorem — hold at every stage because they are inherited from `X ⟶ S` by the open
subscheme `X_r`. Since `X_n = X`, the last stage compactifies `X ⟶ S`.

## Main definitions

- `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter`: a chosen finite affine open
  cover of a quasi-compact scheme with finitely many irreducible components, with dense
  total intersection (blueprint: `def:nagata-dense-affine-cover`);
- `AlgebraicGeometry.Scheme.partialAffineOpenUnions`: the partial unions
  `X_r = U 0 ∪ ⋯ ∪ U (r - 1)` of a finite family of opens (blueprint:
  `def:nagata-partial-affine-unions`);
- `AlgebraicGeometry.noetherianCompactificationConstruction`: the dependent recursion
  producing a compactification of `X_r ⟶ S` for every `r` (blueprint:
  `def:nagata-noetherian-compactification`).

## Main results

- `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter_spec`: the selected cover
  consists of affine opens, covers the scheme, and has dense total intersection (blueprint:
  `lemma:nagata-dense-affine-cover`);
- `AlgebraicGeometry.HasCompactification.of_sup_of_dense_subset`: the gluing step, an
  application of the two-open theorem to two opens sharing a dense subset;
- `AlgebraicGeometry.nagataCompactification_of_isNoetherian`: Nagata's compactification
  theorem over a Noetherian base (blueprint: `thm:nagata-noetherian`).

-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### The selected dense affine cover -/

/-- **The selected dense affine cover**: a chosen finite affine open cover of a quasi-compact
scheme `X` with finitely many irreducible components whose total intersection is dense, given
as the pair of its length and the family itself. Its defining properties are
`AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter_spec`.
(blueprint: `def:nagata-dense-affine-cover`) -/
noncomputable def Scheme.finiteAffineOpenCoverDenseIInter (X : Scheme.{u}) [CompactSpace X]
    (hX : (irreducibleComponents X).Finite) : (n : ℕ) × (Fin n → X.Opens) :=
  ⟨_, (exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter X hX).choose_spec.choose⟩

/-- **Properties of the selected dense affine cover**: the selected family consists of affine
opens, covers `X`, and its total intersection is dense in `X`.
(blueprint: `lemma:nagata-dense-affine-cover`) -/
theorem Scheme.finiteAffineOpenCoverDenseIInter_spec (X : Scheme.{u}) [CompactSpace X]
    (hX : (irreducibleComponents X).Finite) :
    (∀ i, IsAffineOpen ((X.finiteAffineOpenCoverDenseIInter hX).2 i)) ∧
      iSup (X.finiteAffineOpenCoverDenseIInter hX).2 = ⊤ ∧
      Dense (⋂ i, ((X.finiteAffineOpenCoverDenseIInter hX).2 i : Set X)) := by
  obtain ⟨h₁, h₂, -, h₄⟩ :=
    (exists_isAffineOpen_iSup_eq_top_and_genericPoints_subset_iInter X hX).choose_spec.choose_spec
  exact ⟨h₁, h₂, h₄⟩

/-- **The selected affine neighbourhood of a point and finitely many generic points**: for a
quasi-separated scheme `X`, a finite set `s` of generic points of irreducible components of `X`
and a point `x`, a chosen affine open `A(x; s)` containing `x` and every point of `s`, selected
from `AlgebraicGeometry.exists_isAffineOpen_mem_of_subset_genericPoints`. Its defining
properties are `AlgebraicGeometry.Scheme.affineOpenGenericPoints_spec`.
(blueprint: `lemma-affine-covers-dense-intersection--1`) -/
noncomputable def Scheme.affineOpenGenericPoints (X : Scheme.{u}) [QuasiSeparatedSpace X]
    {s : Set X} (hsf : s.Finite) (hs : s ⊆ genericPoints X) (x : X) : X.Opens :=
  (exists_isAffineOpen_mem_of_subset_genericPoints hsf hs x).choose

/-- **Properties of the selected affine neighbourhood**: `A(x; s)` is affine and contains `x`
and every point of `s`.
(blueprint: `lemma-affine-covers-dense-intersection--1`; the existence statement
`lemma-affine-covers-dense-intersection--1` is
`AlgebraicGeometry.exists_isAffineOpen_mem_of_subset_genericPoints`) -/
theorem Scheme.affineOpenGenericPoints_spec (X : Scheme.{u}) [QuasiSeparatedSpace X]
    {s : Set X} (hsf : s.Finite) (hs : s ⊆ genericPoints X) (x : X) :
    IsAffineOpen (X.affineOpenGenericPoints hsf hs x) ∧ x ∈ X.affineOpenGenericPoints hsf hs x ∧
      s ⊆ (X.affineOpenGenericPoints hsf hs x : Set X) :=
  (exists_isAffineOpen_mem_of_subset_genericPoints hsf hs x).choose_spec

/-! ### Partial unions -/

/-- **The partial unions of a finite family of opens**: `X_r = U 0 ∪ ⋯ ∪ U (r - 1)`, so that
`X_0 = ∅` and `X_n` is the union of the whole family.
(blueprint: `def:nagata-partial-affine-unions`) -/
def Scheme.partialAffineOpenUnions {n : ℕ} (U : Fin n → X.Opens) (r : ℕ) : X.Opens :=
  ⨆ i : Fin n, ⨆ _ : (i : ℕ) < r, U i

namespace Scheme

variable {n : ℕ} (U : Fin n → X.Opens)

@[simp]
theorem partialAffineOpenUnions_zero : partialAffineOpenUnions U 0 = ⊥ := by
  simp [partialAffineOpenUnions]

theorem partialAffineOpenUnions_succ (r : ℕ) :
    partialAffineOpenUnions U (r + 1) =
      partialAffineOpenUnions U r ⊔ ⨆ h : r < n, U ⟨r, h⟩ :=
  SetLike.ext fun x => by
    simp only [partialAffineOpenUnions, Opens.mem_iSup, Opens.mem_sup,
      Nat.lt_succ_iff_lt_or_eq]
    constructor
    · rintro ⟨⟨i, hin⟩, hi | rfl, hx⟩
      · exact .inl ⟨⟨i, hin⟩, hi, hx⟩
      · exact .inr ⟨hin, hx⟩
    · rintro (⟨i, hi, hx⟩ | ⟨hrn, hx⟩)
      · exact ⟨i, .inl hi, hx⟩
      · exact ⟨⟨r, hrn⟩, .inr rfl, hx⟩

theorem partialAffineOpenUnions_self : partialAffineOpenUnions U n = iSup U :=
  SetLike.ext fun x => by
    simp only [partialAffineOpenUnions, Opens.mem_iSup]
    exact ⟨fun ⟨i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i, i.2, hx⟩⟩

theorem le_partialAffineOpenUnions {i : Fin n} {r : ℕ} (h : (i : ℕ) < r) :
    U i ≤ partialAffineOpenUnions U r :=
  le_iSup₂ (f := fun (i : Fin n) (_ : (i : ℕ) < r) => U i) i h

end Scheme

/-! ### The gluing step -/

/-- **The gluing step of the induction over a dense affine cover** (blueprint: the
induction step of `def:nagata-noetherian-compactification`, using
`lemma:nagata-partial-union-overlap-dense`).

This is the two-open theorem `AlgebraicGeometry.HasCompactification.of_two_open_cover` applied
to the two opens `V` and `W` of `V ∪ W`: their intersection contains `D`, which is dense in
`V ∪ W` because `V ∪ W` is open in `X` (`Dense.preimage_val_inter`). -/
theorem HasCompactification.of_sup_of_dense_subset [IsNoetherian S] (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {D : Set X} (hD : Dense D)
    {V W : X.Opens} (hDV : D ⊆ (V : Set X)) (hDW : D ⊆ (W : Set X))
    [HasCompactification (V.ι ≫ f)] [HasCompactification (W.ι ≫ f)] :
    HasCompactification ((V ⊔ W).ι ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have : NoetherianSpace (V ⊔ W).toScheme :=
    inferInstanceAs (NoetherianSpace (((V ⊔ W : X.Opens) : Set X) : Type u))
  have h₁ : HasCompactification (((V ⊔ W).ι ⁻¹ᵁ V).ι ≫ (V ⊔ W).ι ≫ f) := by
    have := HasCompactification.comp_of_isOpenImmersion (f := V.ι ≫ f)
      (Scheme.Opens.isoOfLE (le_sup_left : V ≤ V ⊔ W)).hom
    rwa [← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc] at this
  have h₂ : HasCompactification (((V ⊔ W).ι ⁻¹ᵁ W).ι ≫ (V ⊔ W).ι ≫ f) := by
    have := HasCompactification.comp_of_isOpenImmersion (f := W.ι ≫ f)
      (Scheme.Opens.isoOfLE (le_sup_right : W ≤ V ⊔ W)).hom
    rwa [← Category.assoc, Scheme.Opens.isoOfLE_hom_ι, Category.assoc] at this
  have hcov : ((V ⊔ W).ι ⁻¹ᵁ V) ⊔ ((V ⊔ W).ι ⁻¹ᵁ W) = ⊤ :=
    Opens.ext (Set.eq_univ_of_forall fun x => x.2)
  have hdense : Dense ((((V ⊔ W).ι ⁻¹ᵁ V) ⊓ ((V ⊔ W).ι ⁻¹ᵁ W) : (V ⊔ W).toScheme.Opens) :
      Set (V ⊔ W).toScheme) :=
    hD.preimage_val_inter (V ⊔ W).isOpen hDV hDW
  exact HasCompactification.of_two_open_cover ((V ⊔ W).ι ≫ f) _ _ hcov hdense

/-! ### The recursion -/

/-- **The recursive Noetherian compactification construction**: given a finite family of
affine opens `U` of `X` with dense total intersection, a compactification of every partial
union `X_r = U 0 ∪ ⋯ ∪ U (r - 1)` over `S`, constructed by recursion on `r`.

`X_0` is empty, hence proper over `S`; `X_1 = U 0` is affine, so the affine case applies;
and `X_{r+1} = X_r ∪ U r` is obtained from `X_r` and `U r` by the two-open theorem, whose
density hypothesis holds because the total intersection of the cover is contained in both
`X_r` and `U r`.
(blueprint: `def:nagata-noetherian-compactification`) -/
noncomputable def noetherianCompactificationConstruction [IsNoetherian S] (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] {n : ℕ} (U : Fin n → X.Opens)
    (hUaff : ∀ i, IsAffineOpen (U i)) (hUdense : Dense (⋂ i, (U i : Set X))) (r : ℕ) :
    Compactification ((Scheme.partialAffineOpenUnions U r).ι ≫ f) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  induction r with
  | zero =>
    rw [Scheme.partialAffineOpenUnions_zero]
    have : IsEmpty ((⊥ : X.Opens).toScheme) := Set.isEmpty_coe_sort.mpr rfl
    exact HasCompactification.compactification _
  | succ r ih =>
    have hprev : HasCompactification ((Scheme.partialAffineOpenUnions U r).ι ≫ f) :=
      ih.hasCompactification
    rw [Scheme.partialAffineOpenUnions_succ]
    by_cases hrn : r < n
    · rw [iSup_pos hrn]
      have : IsAffine (U ⟨r, hrn⟩).toScheme := hUaff _
      have hWc : HasCompactification ((U ⟨r, hrn⟩).ι ≫ f) :=
        HasCompactification.of_isQuasiAffine _
      by_cases hr : 0 < r
      · have h0 : (0 : ℕ) < n := lt_of_le_of_lt (Nat.zero_le r) hrn
        have hDV : (⋂ i, (U i : Set X)) ⊆
            ((Scheme.partialAffineOpenUnions U r : X.Opens) : Set X) :=
          (Set.iInter_subset _ ⟨0, h0⟩).trans
            (SetLike.coe_subset_coe.mpr
              (Scheme.le_partialAffineOpenUnions U (i := ⟨0, h0⟩) hr))
        have hDW : (⋂ i, (U i : Set X)) ⊆ ((U ⟨r, hrn⟩ : X.Opens) : Set X) :=
          Set.iInter_subset _ _
        have := HasCompactification.of_sup_of_dense_subset f hUdense hDV hDW
        exact HasCompactification.compactification _
      · obtain rfl : r = 0 := Nat.le_zero.mp (Nat.not_lt.mp hr)
        rw [Scheme.partialAffineOpenUnions_zero, bot_sup_eq]
        exact HasCompactification.compactification _
    · rw [iSup_neg hrn, sup_bot_eq]
      exact HasCompactification.compactification _

/-- **Nagata compactification over a Noetherian base** (blueprint: `thm:nagata-noetherian`).

The last stage `X_n = X` of the recursion
`AlgebraicGeometry.noetherianCompactificationConstruction` over the selected dense affine
cover of `X` is a compactification of `f`. -/
theorem nagataCompactification_of_isNoetherian [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : HasCompactification f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  obtain ⟨haff, hcov, hdense⟩ := X.finiteAffineOpenCoverDenseIInter_spec hfin
  have key : HasCompactification ((⊤ : X.Opens).ι ≫ f) := by
    have := (noetherianCompactificationConstruction f _ haff hdense
      (X.finiteAffineOpenCoverDenseIInter hfin).1).hasCompactification
    rwa [Scheme.partialAffineOpenUnions_self, hcov] at this
  have := HasCompactification.comp_of_isOpenImmersion (f := (⊤ : X.Opens).ι ≫ f) X.topIso.inv
  rwa [← Category.assoc, X.toIso_inv_ι, Category.id_comp] at this

/-- **The constructed Noetherian compactification** `C_Noeth(X/S)`: the last stage `X_n = X`
of the recursion `AlgebraicGeometry.noetherianCompactificationConstruction` over the selected
dense affine cover `AlgebraicGeometry.Scheme.finiteAffineOpenCoverDenseIInter` of `X`,
transported along the identification `X ≅ X_n`.
(blueprint: `theorem-nagata-s-compactification-theorem--1`) -/
noncomputable def noetherianCompactification [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] : Compactification f :=
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := ⟨⟩
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hspec := X.finiteAffineOpenCoverDenseIInter_spec hfin
  have hle : (⊤ : X.Opens) ≤ Scheme.partialAffineOpenUnions
      (X.finiteAffineOpenCoverDenseIInter hfin).2 (X.finiteAffineOpenCoverDenseIInter hfin).1 := by
    rw [Scheme.partialAffineOpenUnions_self, hspec.2.1]
  ((noetherianCompactificationConstruction f _ hspec.1 hspec.2.2
      (X.finiteAffineOpenCoverDenseIInter hfin).1).precomp
      (X.topIso.inv ≫ X.homOfLE hle)).copy (by
    rw [Category.assoc, X.homOfLE_ι_assoc, X.toIso_inv_ι_assoc])

end AlgebraicGeometry
