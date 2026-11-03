# Residue fibres, reduction and connectedness for actual integral models

This is an internal construction on the supplied models of
`Langlands.GroupScheme.IntegralModel`, rather than a model-existence assertion.
It supplies the residue-fibre and point-map vocabulary used in Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), §8.3, particularly
Proposition 8.3.12(3), Theorem 8.3.13 and Propositions 8.3.15–8.3.16
(printed pp. 299–301 / PDF pp. 330–332). The registered original is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, registered as
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 37–39, correct the proof of Theorem 8.3.13 using connected fibres
and retain the perfect-residue-field assumption for §8.3. This module does
not implement that theorem or impose its setting on the elementary maps.

The constructions require only that the integral domain base `R` is a local
ring with specified fraction field `K`. In particular, they apply to DVRs
without any Henselian, perfection or reductivity assumption.
`residueBaseMap R` is `Spec.map` of the actual quotient homomorphism
`IsLocalRing.residue R : R → R / maximalIdeal R`.
`specialFibre M` is the group-scheme pullback along this map, retaining
its group law and structure over `IsLocalRing.ResidueField R`. It is the full
special fibre; no reductive quotient is constructed.

`reduction M` is the general `baseChangeSectionHom` homomorphism along this
residue map. The underlying scheme morphism is the pullback lift of the
restricted integral section and the identity on the residue spectrum.
`reduction_left` is the previously proved lift formula specialized to this
map. For a compatible-model morphism, `Hom.specialFibreMap` is its actual
base change. Reduction naturality is exactly the general section naturality,
and preservation of the congruence kernel follows by evaluating at the
identity.

`congruenceKernel M` is the kernel of reduction inside
`M.integralSections = G_R(R)`. Its membership law says precisely that the
reduction is the identity; its normality is the general kernel theorem.
`congruenceSubgroup M` is its image in `G(K)` under the supplied model's
integral-point map. Its membership law records both the identity reduction
and the chosen integral lift. It lies in `M.integralPoints`.
`congruenceInIntegralPoints M` takes the same image under the surjective
range restriction of the integral-point map. The image of a normal subgroup
under a surjective homomorphism is normal. An explicit equality identifies
this subgroup with
`M.congruenceSubgroup.subgroupOf M.integralPoints`, proving normality with
the integral-point image as the ambient group. This argument requires no
injectivity theorem for the integral-point map and asserts no normality in
the entire generic rational-point group.

The connectedness predicates refer to actual scheme spaces and morphisms.
`HasConnectedSpecialFibre` means connectedness, including nonemptiness, of
the Zariski space of the full special fibre.
`HasConnectedFibres` quantifies over all points `x` of `Spec R` and asks for
connectedness of the scheme-theoretic pullback to the actual residue field
at `x`. `HasGeometricallyConnectedFibres` is Mathlib's
`GeometricallyConnected` property of the model's structural morphism: every
pullback along a field-valued point of the base is connected. The supplied
equivalence with geometric connectedness of each residue-field fibre is
Mathlib's `GeometricallyConnected.iff_geometricallyConnected_fiber`.
`HasGeometricallyConnectedSpecialFibre` applies the same geometric property
to the special fibre over its residue field. The proved implications are:
geometric connectedness of all fibres implies their ordinary connectedness
and geometric connectedness of the special fibre, and geometric
connectedness of the special fibre implies its ordinary connectedness.
The first uses the residue-field fibre instances, the second stability under
base change, and the third the fact that a field spectrum is a singleton.
No converse or identification of these predicates is asserted here.

Model existence, relative identity components, equality with parahoric or
fixer subgroups, reduction surjectivity, maximal reductive quotients,
pro-p assertions, topologies and the corrected Theorem 9.2.7 certificate
remain separate obligations.
