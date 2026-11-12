# Left Hecke actions and the functors F and I along a continuous homomorphism

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, III.2.1, printed p.70 / PDF p.76, and I.2.3,
printed pp.17–18 / PDF pp.23–24. Registered source:
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

For a continuous group homomorphism `φ : H →* G` between Hausdorff locally
compact nonarchimedean groups with left Haar measures, `leftModule` is the
published integrated Hecke action on the published left regular test-function
representation, pulled back along `φ`. The carrier is the existing
`HeckeAlgebra μG`; there is no replacement algebra or supplied action certificate.
Under the Haar identification of functions with distributions this is precisely
the left action of III.2.1. Its scalarized formula is

`(a • f)(x) = ∫ h, a(h) f(φ(h)⁻¹x) dμH(h)`.

The implementation derives smoothness of the regular representations from the
published common compact-open bi-invariance theorem, and idempotentedness of
the Hecke algebras from the published finite-family local units. Right
convolution intertwines the restricted left regular action, by left-Haar
substitution in the convolution integral. The published integrated-intertwiner
identity therefore proves that the left `H(H)` action commutes with right
multiplication by `H(G)`. Its nondegeneracy is the published nondegeneracy of
the integrated action; right regular nondegeneracy follows from local units.

`F` and `I` specialize `NondegenerateTensorFunctor.F` and
`RenardHomFunctors.I`, with precisely these actions and laws. They are
functors on nondegenerate additive modules, with the same convention as their
published Chapter I inputs. The two group universes and the input carrier
universe are independent. The output carrier universe is `max uG v`, as in
the Chapter I constructions.

This unit covers the left `H(H)`–right `H(G)` bimodule and the Hecke-side
functors `F` and `I`. It does not claim the right `H(H)` action, the functors
`P` and pseudo-`F`, the smooth-representation comparison, or any induction
comparison theorem. Those are subsequent units of Task 5296.
