# Proof of continuity of algebraic coefficient orbit maps

Author: Worker 255.

The target is `Langlands.Shimura.Coefficients.AlgebraicOrbitContinuityStatement`.
The theorem `Langlands.Shimura.Coefficients.algebraicOrbitContinuity` proves it
for the declared universe `u`, keeping every quantifier of the statement: any
field `K`, finite-dimensional `K`-algebra `A` with anti-involution `σ`,
finite-dimensional `K`-vector space `W`, published representation
`ρ : σ.AlgebraicRepresentation W`, and commutative `K`-algebra `S` with a
topology making it a topological ring. No hypothesis is added: the proof uses
only the naturality field of `ρ` and the published topology on `σ.Points S`
(module topology on `S ⊗[K] A`, units, similitude subtype).

The proof reuses the published coordinate ring of
`Langlands.Shimura.Unitary.SimilitudeCoordinates`: for a finite basis `b` of
`A`, `σ.similitudeCoordinateRing b` is a quotient of a polynomial ring in the
variables `unit i`, `unitInv i`, `multiplier`, `multiplierInv`; it carries the
universal similitude `σ.universalSimilitude b`, and each point `g` over `S` has
a classifying algebra map `σ.similitudeHom b g`, with
`σ.similitudePoint_similitudeHom` saying that it sends the universal similitude
to `g`.

The proof has four steps, stated in the namespace
`Langlands.Shimura.AlgebraInvolution` over an arbitrary commutative ring `K`.

1. `continuous_similitudeHom_apply`: for every element `c` of the coordinate
   ring, `g ↦ σ.similitudeHom b g c` is continuous. Write `c` as the class of a
   polynomial `p` (surjectivity of the quotient map). By
   `similitudeHom_quotient`, the value is `aeval (σ.similitudeValues b g) p`,
   which equals evaluation of the coefficient-mapped polynomial
   `MvPolynomial.map (algebraMap K S) p` at `σ.similitudeValues b g`. Mathlib's
   `MvPolynomial.continuous_eval` makes this evaluation continuous in the
   variable values. The variable values depend continuously on `g`: the unit,
   its inverse, the multiplier and its inverse are continuous by the unit-group
   and subtype topologies (`Units.continuous_val`, `Units.continuous_coe_inv`),
   and each basis coordinate on `S ⊗[K] A` is an `S`-linear map, hence
   continuous for the module topology (`IsModuleTopology.continuous_of_linearMap`).
   No topology on `K` is used; `K` only enters through the polynomial
   coefficients, already mapped into `S`.

2. `AlgebraicRepresentation.act_one_tmul`: applying the naturality of `ρ` to
   the classifying map `σ.similitudeHom b g`, the universal similitude, and
   `1 ⊗ w` gives
   `ρ.act S g (1 ⊗ w) = rTensor (σ.similitudeHom b g) (ρ.act C u (1 ⊗ w))`,
   where `C` is the coordinate ring and `u` the universal similitude.

3. `AlgebraicRepresentation.continuous_rTensor_similitudeHom`: for any fixed
   `y ∈ C ⊗[K] W`, the map `g ↦ rTensor (σ.similitudeHom b g) y` is continuous
   for the module topology on `S ⊗[K] W`. By induction on `y`
   (`TensorProduct.inductionOn`), a pure tensor `c ⊗ w` maps to
   `σ.similitudeHom b g c • (1 ⊗ w)`, continuous by step 1 and continuity of
   scalar multiplication for the module topology (`ModuleTopology.continuousSMul`);
   sums are handled by continuity of addition (`ModuleTopology.continuousAdd`).
   This induction principle has only pure-tensor and sum cases.

4. `AlgebraicRepresentation.continuous_act`: for `A` free and finite over `K`
   and any `x ∈ S ⊗[K] W`, the orbit map `g ↦ ρ.act S g x` is continuous. Use
   the basis `Module.Free.chooseBasis K A`, whose index type lies in the
   universe of `A`, so the coordinate ring lies in the universe on which `ρ` is
   defined. By induction on `x`: for a pure tensor `s ⊗ w = s • (1 ⊗ w)`,
   `S`-linearity of `ρ.act S g` and step 2 give
   `ρ.act S g (s ⊗ w) = s • rTensor (σ.similitudeHom b g) (ρ.act C u (1 ⊗ w))`,
   continuous by step 3 and continuity of scalar multiplication; sums again
   use continuity of addition.

Finally `algebraicOrbitContinuity` introduces the quantified data of the
statement and applies step 4; over a field `K`, `A` is a free `K`-module, and
its finiteness is the statement's hypothesis `Module.Finite K A`. The
hypothesis `Module.Finite K W` is not needed by this proof.

The proof route follows the suggestion recorded in the statement's Markdown and
in the task context; it does not follow a literature proof.
