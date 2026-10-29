# Descent of compatible global units

`Langlands.Scheme.CompatibleUnitsDescentStatement` states that, for a
quasi-compact, flat, surjective morphism of schemes `p : X ⟶ Y`, a global unit
`s` of `X` descends to a unique global unit `t` of `Y` if the pullbacks of `s`
along every pair `a b : U ⟶ X` with `a ≫ p = b ≫ p` agree. The conclusion is
literal equality `Units.map p.appTop.hom.toMonoidHom t = s`. Test schemes `U`
are arbitrary in the same universe as `X` and `Y`.

The statement is an internal consequence of two existing formal results.
Mathlib `AlgebraicGeometry/Sites/Fpqc.lean` proves that a quasi-compact flat
surjection is an effective epimorphism of schemes. The Library's
`Langlands.GroupScheme.Gm.unitsHomEquiv`, with naturality lemma
`unitsHomEquiv_comp`, represents global units by the spectrum of the integral
Laurent polynomial ring. The compatibility assumption therefore gives the
coequalizing condition for effective-epimorphism descent to that representing
scheme, and epimorphism cancellation gives uniqueness. No external literature
claim is added by this internal interface.

An affine morphism is quasi-compact, so the statement applies in particular
to affine flat surjections. It supplies the scalar descent step in descent
of locally trivial line bundles; it does not assert descent or gluing of
module sheaves or prove the kernel-character classification.
