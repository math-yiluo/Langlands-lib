# Additive cocycles on affine faithfully flat covers

Worker 1515's internal prerequisite for the Ga step of the split-unipotent
torsor theorem (task 21d6e245-dcea-4c7a-af4a-c532ea0dd295). It shows that a
natural additive cocycle on an affine fpqc cover of an affine base is a
coboundary. This is the standard vanishing of degree-one Čech cohomology of
the structure sheaf for an affine faithfully flat cover, as in faithfully
flat descent. The proof here is derived from the tensor formulas and Mathlib's
faithfully flat API; it does not follow a particular cited text.

## Algebra

Take a commutative ring A and an A-algebra B in the same universe. The face
maps `face12`, `face13` and `face23` from B ⊗ B to B ⊗ (B ⊗ B) send b ⊗ c to
b ⊗ c ⊗ 1, b ⊗ 1 ⊗ c and 1 ⊗ b ⊗ c. The differential `e0` sends b to
1 ⊗ b − b ⊗ 1. The differential `e1` is face23 − face13 + face12.
`e1_e0` proves that e1 composed with e0 is zero.

`contracting_identity` uses the Library's contraction
`AmitsurDegreeOne.contraction` (b ⊗ x ↦ b·x) as a contracting homotopy of
the complex after tensoring on the left with B. Tensor induction proves the
identity. `baseChange_exact` deduces exactness of the base-changed complex with
no flatness assumption. When B is faithfully flat over A, `exact` uses
Mathlib's `Module.FaithfullyFlat.lTensor_reflects_exact` to get
`Function.Exact (e0 A B) (e1 A B)`. `exists_primitive` restates this for an
element x of B ⊗ B: if face13 x = face12 x + face23 x, then some b satisfies
b ⊗ 1 − 1 ⊗ b = x.

## Schemes

Fix a scheme T₀. An `AddCocycle U`, for U an object of `Over T₀`, is a family
`toFun a b : Γ(Z.left, ⊤)` defined for every Z in `Over T₀` and every pair of
morphisms a, b : Z ⟶ U. It satisfies two axioms:

- naturality: `toFun (t ≫ a) (t ≫ b) = t.left.appTop (toFun a b)`;
- additivity: `toFun a c = toFun a b + toFun b c`.

The rest assumes T₀ and U.left are affine. `specOver φC` is Spec C over T₀
for a ring map φC from Γ(T₀). `specPoint` is the point of U over it given by
a compatible ring map ψ out of Γ(U.left). `specMap` is the morphism of spectra
induced by a ring map χ under Γ(T₀). `specMap_comp_specPoint` says that
precomposing a `specPoint` with `specMap` gives the `specPoint` of the
composite ring maps.

`AddCocycle.ringFun` reads the cocycle on two such points as an element of C,
through `Scheme.ΓSpecIso`. `ringFun_map` states its naturality in the ring and
`ringFun_cocycle` its additivity.

`AddCocycle.exists_ringFun_eq` assumes U.hom is flat and surjective. Then
B = Γ(U.left) is faithfully flat over A = Γ(T₀), by Mathlib's
`Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`. Evaluate the
cocycle on the two inclusions of B into B ⊗ B; this gives an element x.
Naturality applied to the three algebra maps from B ⊗ B to B ⊗ (B ⊗ B) turns
the cocycle identity into the hypothesis of `exists_primitive`, which yields a
primitive β. For any compatible pair ψ₁, ψ₂ out of B, the induced map
B ⊗ B → C sends x to ψ₁ β − ψ₂ β, and naturality identifies the image of x
with `ringFun` of ψ₁, ψ₂.

`AddCocycle.exists_coboundary` is the scheme-level statement. Under the same
assumptions there is β : Γ(U.left, ⊤) with

  `α.toFun a b = a.left.appTop β - b.left.appTop β`

for every Z : Over T₀ and a, b : Z ⟶ U. To prove it, factor an arbitrary Z
through Spec Γ(Z) via `Scheme.toSpecΓ`. Each point of U over Z factors as a
`specPoint`, and the result follows from `exists_ringFun_eq`, naturality, and
`Scheme.toSpecΓ_appTop`.

The module only proves this vanishing. It does not mention group schemes or
torsors; those appear in the separate module `Langlands.GroupScheme.TorsorCocycle`.
