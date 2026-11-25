/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Cubes of mates

Consider two "layers" of adjunctions `Lf ⊣ Rf`, `Lf' ⊣ Rf'` (the *first layer*, e.g. derived
pullback and pushforward with coefficients `R`) and `Mf ⊣ Sf`, `Mf' ⊣ Sf'` (the *second layer*,
e.g. with coefficients `S`), functors `Gr`, `Hr`, `Gs`, `Hs` relating the two adjunctions of each
layer (e.g. pullbacks along the horizontal maps of a commutative square of schemes), functors
`PY`, `PX`, `PY'`, `PX'` from the first to the second layer (e.g. a change of coefficients) and
2-cells
```
σr : Gr ⋙ Lf' ⟶ Lf ⋙ Hr,       σs : Gs ⋙ Mf' ⟶ Mf ⋙ Hs,
αf : PY ⋙ Mf ⟶ Lf ⋙ PX,         αf' : PY' ⋙ Mf' ⟶ Lf' ⋙ PX',
αg : PY ⋙ Gs ⟶ Gr ⋙ PY',        αg' : PX ⋙ Hs ⟶ Hr ⋙ PX'.
```
If the cube formed by these 2-cells on the left adjoints commutes, then so does the cube formed
by the mates of `σr`, `σs`, `αf` and `αf'` (base change maps of the right adjoints) together with
`αg` and `αg'`: this is `CategoryTheory.mateEquiv_app_cube`.

This is used to show that the change of coefficients of pro-étale sheaves commutes with the
derived base change maps (blueprint `theorem-grothendieck-lefschetz-trace-formula--7`).
-/

@[expose] public section

namespace CategoryTheory

variable {DY DX DY' DX' EY EX EY' EX' : Type*} [Category* DY] [Category* DX] [Category* DY']
  [Category* DX'] [Category* EY] [Category* EX] [Category* EY'] [Category* EX']
  {Lf : DY ⥤ DX} {Rf : DX ⥤ DY} {Lf' : DY' ⥤ DX'} {Rf' : DX' ⥤ DY'}
  {Mf : EY ⥤ EX} {Sf : EX ⥤ EY} {Mf' : EY' ⥤ EX'} {Sf' : EX' ⥤ EY'}
  (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (bf : Mf ⊣ Sf) (bf' : Mf' ⊣ Sf')
  {Gr : DY ⥤ DY'} {Hr : DX ⥤ DX'} {Gs : EY ⥤ EY'} {Hs : EX ⥤ EX'}
  {PY : DY ⥤ EY} {PX : DX ⥤ EX} {PY' : DY' ⥤ EY'} {PX' : DX' ⥤ EX'}
  (σr : Gr ⋙ Lf' ⟶ Lf ⋙ Hr) (σs : Gs ⋙ Mf' ⟶ Mf ⋙ Hs)
  (αf : PY ⋙ Mf ⟶ Lf ⋙ PX) (αf' : PY' ⋙ Mf' ⟶ Lf' ⋙ PX')
  (αg : PY ⋙ Gs ⟶ Gr ⋙ PY') (αg' : PX ⋙ Hs ⟶ Hr ⋙ PX')

/-- **Cubes of mates.** If the cube of 2-cells on the left adjoints commutes, i.e. for every `M`
the two composites `Mf' (Gs (PY M)) ⟶ PX' (Hr (Lf M))`
```
Mf' (αg M) ≫ αf' (Gr M) ≫ PX' (σr M) = σs (PY M) ≫ Hs (αf M) ≫ αg' (Lf M)
```
agree, then the cube of the mates commutes: for every `K` the two composites
`Gs (PY (Rf K)) ⟶ Sf' (PX' (Hr K))` built from `αg`, `αg'`, the base change maps
`Rf ⋙ Gr ⟶ Hr ⋙ Rf'` and `Rf ⋙ PY ⟶ PX ⋙ Sf` (mates of `σr` and `αf`) and their second
layer analogues agree. -/
lemma mateEquiv_app_cube
    (h : ∀ M, Mf'.map (αg.app M) ≫ αf'.app (Gr.obj M) ≫ PX'.map (σr.app M) =
      σs.app (PY.obj M) ≫ Hs.map (αf.app M) ≫ αg'.app (Lf.obj M)) (K : DX) :
    αg.app (Rf.obj K) ≫ PY'.map ((mateEquiv af af' σr).app K) ≫
        (mateEquiv af' bf' αf').app (Hr.obj K) =
      Gs.map ((mateEquiv af bf αf).app K) ≫ (mateEquiv bf bf' σs).app (PX.obj K) ≫
        Sf'.map (αg'.app K) := by
  apply (bf'.homEquiv _ _).symm.injective
  have h₁ := mateEquiv_counit af' bf' αf' (Hr.obj K)
  have h₂ := αf'.naturality ((mateEquiv af af' σr).app K)
  have h₃ := mateEquiv_counit af af' σr K
  have h₄ := αg'.naturality (af.counit.app K)
  have h₅ := mateEquiv_counit bf bf' σs (PX.obj K)
  have h₆ := σs.naturality ((mateEquiv af bf αf).app K)
  have h₇ := mateEquiv_counit af bf αf K
  dsimp at h₁ h₂ h₃ h₄ h₅ h₆ h₇
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Adjunction.counit_naturality]
  rw [h₁, reassoc_of% h₂, ← PX'.map_comp, h₃, PX'.map_comp, reassoc_of% (h (Rf.obj K)),
    reassoc_of% h₅, reassoc_of% h₆, ← Hs.map_comp_assoc, h₇, Hs.map_comp, Category.assoc, h₄]

/-- **Cubes of mates, converse.** If the cube of the mates commutes (the conclusion of
`CategoryTheory.mateEquiv_app_cube`) at every object, then the cube of 2-cells on the left
adjoints commutes. -/
lemma mateEquiv_app_cube_converse
    (h : ∀ K, αg.app (Rf.obj K) ≫ PY'.map ((mateEquiv af af' σr).app K) ≫
        (mateEquiv af' bf' αf').app (Hr.obj K) =
      Gs.map ((mateEquiv af bf αf).app K) ≫ (mateEquiv bf bf' σs).app (PX.obj K) ≫
        Sf'.map (αg'.app K)) (M : DY) :
    Mf'.map (αg.app M) ≫ αf'.app (Gr.obj M) ≫ PX'.map (σr.app M) =
      σs.app (PY.obj M) ≫ Hs.map (αf.app M) ≫ αg'.app (Lf.obj M) := by
  apply (bf'.homEquiv _ _).injective
  have h₁ := unit_mateEquiv af' bf' αf' (Gr.obj M)
  have h₂ := (mateEquiv af' bf' αf').naturality (σr.app M)
  have h₃ := unit_mateEquiv af af' σr M
  have h₄ := αg.naturality (af.unit.app M)
  have h₅ := unit_mateEquiv bf bf' σs (PY.obj M)
  have h₆ := (mateEquiv bf bf' σs).naturality (αf.app M)
  have h₇ := unit_mateEquiv af bf αf M
  have h₈ := bf'.unit.naturality (αg.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  dsimp only [Functor.comp_obj]
  rw [← reassoc_of% h₈, ← reassoc_of% h₁, ← h₂, ← PY'.map_comp_assoc, ← h₃,
    PY'.map_comp_assoc, ← reassoc_of% h₄, h (Lf.obj M), ← reassoc_of% h₅, ← reassoc_of% h₆,
    ← Gs.map_comp_assoc (bf.unit.app (PY.obj M)), ← h₇, Gs.map_comp_assoc]

end CategoryTheory
