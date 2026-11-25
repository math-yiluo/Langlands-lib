/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.Triangle

/-!
# The staircase of triangles of compactifications of three composable morphisms

Let `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` be composable morphisms of `Over S`, with
compactifications `cf = (i_f, p_f)`, `cg = (i_g, p_g)`, `ch = (i_h, p_h)`. Let `dfg = (a, b)` be a
compactification of `p_f ≫ i_g`, `dgh = (c, d)` one of `p_g ≫ i_h`, and `dV = (e, u)` one of
`b ≫ c`, all with cartesian squares. They form the staircase
```
Z_f --a--> W_fg --e--> V
|p_f       |b          |u
X --i_g--> P_g --c---> W_gh
           |p_g        |d
           Y ---i_h--> P_h
```
which carries the compactification `W ⟶[i_f ≫ a ≫ e] V ⟶[u ≫ d ≫ p_h] Z` of `f ≫ g ≫ h`
(`Compactification.assocCompactification`), and two triangles of compactifications with this
composite: `Compactification.Triangle.assocLeft` of `(f ≫ g, h)` and
`Compactification.Triangle.assocRight` of `(f, g ≫ h)`. These are the triangles in the proof of
the associativity of the composition isomorphisms of the lower shriek.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S : Scheme.{u}} {W X Y Z : Over S} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
  (cf : Compactification f.left) (cg : Compactification g.left) (ch : Compactification h.left)
  (dfg : Compactification (cf.overG ≫ cg.overI).left)
  (dgh : Compactification (cg.overG ≫ ch.overI).left)
  (dV : Compactification (dfg.overG ≫ dgh.overI).left)

/-- The compactification `W ⟶[i_f ≫ a ≫ e] V ⟶[u ≫ d ≫ p_h] Z` of `(f ≫ g ≫ h).left` attached to
compactifications `cf = (i_f, p_f)`, `cg`, `ch = (i_h, p_h)` of `f`, `g`, `h`, a compactification
`dfg = (a, b)` of `p_f ≫ i_g`, a compactification `dgh = (c, d)` of `p_g ≫ i_h` and a
compactification `dV = (e, u)` of `b ≫ c`. -/
noncomputable def assocCompactification : Compactification (f ≫ g ≫ h).left where
  Z := dV.Z
  g := dV.g ≫ dgh.g ≫ ch.g
  i := cf.i ≫ dfg.i ≫ dV.i
  comm := by
    have h₁ : cf.g ≫ cg.i = dfg.i ≫ dfg.g := dfg.comm
    have h₂ : cg.g ≫ ch.i = dgh.i ≫ dgh.g := dgh.comm
    have h₃ : dfg.g ≫ dgh.i = dV.i ≫ dV.g := dV.comm
    have e : f.left ≫ g.left ≫ h.left = (cf.i ≫ cf.g) ≫ (cg.i ≫ cg.g) ≫ ch.i ≫ ch.g := by
      rw [← cf.comm, ← cg.comm, ← ch.comm]
    refine e.trans ?_
    simp only [Category.assoc]
    rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃]
  isProper := inferInstance
  isOpenImmersion := inferInstance

namespace Triangle

variable {cf cg ch dfg dgh dV}

/-- The triangle of compactifications of `(f ≫ g, h)` of a staircase: the composite
compactification `cf.overComp cg dfg` of `f ≫ g`, the compactification `ch` of `h` and
`assocCompactification`, with the maps `q = e` and `p = u ≫ d`. -/
noncomputable abbrev assocLeft (hgh : IsPullback cg.overG dgh.overI ch.overI dgh.overG)
    (hV : IsPullback dfg.overG dV.overI dgh.overI dV.overG) :
    Triangle (f ≫ g).left h.left where
  cf := cf.overComp cg dfg
  cg := ch
  cfg := assocCompactification cf cg ch dfg dgh dV
  q := dV.i
  p := dV.g ≫ dgh.g
  i_q := rfl
  p_g := rfl
  isPullback := (hV.paste_horiz hgh).map (Over.forget S)

/-- The triangle of compactifications of `(f, g ≫ h)` of a staircase: the compactification `cf`
of `f`, the composite compactification `cg.overComp ch dgh` of `g ≫ h` and
`assocCompactification`, with the maps `q = a ≫ e` and `p = u`. -/
noncomputable abbrev assocRight (hfg : IsPullback cf.overG dfg.overI cg.overI dfg.overG)
    (hV : IsPullback dfg.overG dV.overI dgh.overI dV.overG) :
    Triangle f.left (g ≫ h).left where
  cf := cf
  cg := cg.overComp ch dgh
  cfg := assocCompactification cf cg ch dfg dgh dV
  q := dfg.i ≫ dV.i
  p := dV.g
  i_q := rfl
  p_g := rfl
  isPullback := (hfg.paste_vert hV).map (Over.forget S)

end Triangle

end AlgebraicGeometry.Compactification
