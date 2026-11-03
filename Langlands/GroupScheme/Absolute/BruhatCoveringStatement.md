# Absolute Bruhat covering for a Borel pair

Workers 1440 and 1458.

`BorelTorusBruhatCovering i j` expresses the covering
\(G(k)=B(k)N_G(T)(k)B(k)\) for given actual homomorphisms
`i : B ⟶ G` and `j : T.toGrp ⟶ G`. Each base point `g` is a product
`i(b₁) * n * i(b₂)`. The middle point belongs to the published subgroup
`normalizerPoints j`. By its definition, this provides a group-scheme
automorphism `σ : T ≅ T` and the equation
`j ≫ (G.innerIso n).hom = CommGroupScheme.groupHom σ.hom ≫ j`.
Thus its normalizer condition holds as an equality of morphisms of
group schemes, on every test scheme.
There is no assertion that arbitrary test-scheme points admit such a
product without a cover.

`AbsoluteBruhatCoveringStatement` states this property for every actual
Borel pair of a connected reductive group over an algebraically closed
field `k : Type u`. The universe and characteristic are unrestricted.
This is a proposition definition, not a proof of the covering.

The source is Borel and Tits, *Groupes réductifs* (1965), §2.3–§2.4,
printed pp.64–65 (one-based PDF pp.11–12), especially §2.4's disjoint
covering by the double cosets `B n_w B`. Forgetting disjointness and the
chosen Weyl representatives gives precisely the displayed covering.
The normalizer of a closed embedded torus acts on it by an algebraic-group
automorphism; here that restriction is recorded by `normalizerPoints`.
The source's §0.3–§0.4, printed pp.57–58 (PDF pp.4–5), allows the
intrinsic interpretation by affine geometrically reduced group schemes.
The present smooth groups over an algebraically closed field have that
property. The 1972 *Compléments*, §5, printed pp.274–275 (PDF pp.23–24),
lists no correction to §2.4 or this covering.

This prerequisite is independent of the rational Bruhat statement,
Borel–Tits Proposition 4.18 and the parabolic-intersection geometry and
torus statements. None of those is used here. A proof must supply the
covering from independent absolute geometry; defining it supplies none
of that structural argument.
