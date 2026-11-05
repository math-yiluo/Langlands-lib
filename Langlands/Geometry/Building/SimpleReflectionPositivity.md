# Signs on the chamber across a simple wall

This module proves the geometric positivity step used in the chamber-simple
factorization of KP (7.5.1). It works for arbitrary real affine torsors, in
independent universes for points and vectors, and the existing geometric
definition of a chamber-simple affine root. It uses the given coroot; no
additional building axiom or chosen normalizer representative is needed.

`exists_wall_point_of_mem_simpleAffineRoots` chooses a point of the face
whose affine span is the wall. The face lies in the sign closure of the
chamber. Any root vanishing at this point vanishes on the face, hence on its
affine span, and is a scalar multiple of the wall root by the published
`eq_smul_of_hyperplane_le`.

`sign_reflection_eq_of_mem_simpleAffineRoots` uses this point for a root
not proportional to the wall root. That root is nonzero there. Its
reflection is another root by the coroot law, and reflection fixes the wall
point. The closure relation therefore identifies the signs of the original
root at a chamber point and at its reflected point.
`mem_positiveRoots_reflected_chamber` expresses the positive-sign consequence
on the image chamber.

The proof is derived from the published definitions and affine hyperplane
lemmas. Its source motivation is the positivity assertion citing
Proposition 1.3.25 in the proof of Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Theorem 7.5.1, printed p.259 / PDF p.290, as corrected on
PDF p.35 of the authors' 1 November 2024 corrections. The registered source
IDs are `kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`)
and `kaletha-prasad-2024-corrections` (SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`).
`SimpleReflectionPositivityStatement` is the Prop-valued universal statement on
the given affine torsor, and `simpleReflectionPositivity` proves it from the
positive-root corollary. These lemmas prove the geometric step, not the group factorization or the
full chamber Iwahori decomposition. Author: Worker 1647.
