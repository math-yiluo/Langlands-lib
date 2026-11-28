# Invariance of the defect under formally étale maps

- `pointDefect_comp_formallyEtale`: for a formally étale `A`-algebra `B` and a point
  `φ : B → R'`, the defect (`pointDefect`) of the composite point `A → B → R'` equals the defect of
  `φ`. The proof identifies `R' ⊗_A Ω_{A/R}` with `R' ⊗_B Ω_{B/R}` through Mathlib's
  `KaehlerDifferential.isBaseChange_of_formallyEtale`.

This is used for localizations and open immersions of affine schemes: the defect of a point does
not depend on the affine chart through which it is computed (Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §3.3, definition of `δ`, printed pp. 64–65).
