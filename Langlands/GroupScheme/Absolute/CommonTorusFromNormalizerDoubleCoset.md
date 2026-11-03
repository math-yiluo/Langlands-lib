# A common maximal torus from a normalizer double coset

This is an internal, derived construction on the Library's actual group schemes.
It supplies the categorical assembly needed for the common-torus theorem once
the independent geometric hypotheses have been established. It does not prove
the absolute Bruhat covering or the existence or conjugacy of Borel subgroups.

Let `i : B ⟶ G` and `i' : B' ⟶ G` be homomorphisms over any field, and let
`j : T.toGrp ⟶ G` be an ambient maximal torus factoring as `f ≫ i`. Suppose an
actual base point `g` and an isomorphism `φ : B ≅ B'` satisfy
`i ≫ Int(g) = φ.hom ≫ i'`. Suppose also that
`g = i(b₁) * n * i(b₂)`, where the actual point `n` belongs to
`normalizerPoints j`. No Borel, closedness of the overgroups, reductivity,
algebraic closedness, or characteristic assumption is needed for the assembly.
The universe is arbitrary.

`commonTorusOfNormalizerDoubleCoset` returns a dependent triple consisting of
an actual homomorphism `t : T.toGrp ⟶ G`, a homomorphism into `B`, and a
homomorphism into `B'`, together with ambient maximality and the two
factorization equalities. Write `σ` for `normalizingAut j n`, so that
`j ≫ Int(n) = groupHom(σ.hom) ≫ j`. The returned maps are

* `t = j ≫ Int(i(b₁))`,
* `f₁ = f ≫ Int_B(b₁)`,
* `f₂ = groupHom(σ.inv) ≫ f ≫ Int_B(b₂⁻¹) ≫ φ.hom`.

The proof uses `innerIso_hom_comp` from `ConjugacyBaseChange` to commute
inner conjugation with a group-scheme homomorphism on every test scheme.
This gives `f₁ ≫ i = t`. For the other map,
replace `φ.hom ≫ i'` by `i ≫ Int(g)`, move `Int_B(b₂⁻¹)` across `i`, and combine
the inner automorphisms. The point product becomes
`g * i(b₂⁻¹) = i(b₁) * n`. Normalization then cancels `σ.inv` against `σ.hom`.
Finally, `IsMaximalTorus.comp_iso` gives the maximality of `t`.

The construction is derived from the definitions of `innerIso`,
`normalizerPoints` and `IsMaximalTorus` and their elementary transport laws.
Its import closure contains none of the rational Bruhat decomposition,
Borel–Tits 4.18, or the two parabolic-intersection statements. It makes no
unconditional common-torus existence claim.
