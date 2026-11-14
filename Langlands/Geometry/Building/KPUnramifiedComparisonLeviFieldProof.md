# The Levi field of concrete unramified apartment lifts

Authors: Worker 257 and Worker 617.

`Langlands.Geometry.Building.unramifiedComparisonLeviField` proves exactly
`UnramifiedComparisonLeviFieldStatement.{u}` for an arbitrary universe `u`.
It preserves all published hypotheses and works for every supplied concrete
unramified apartment lift, over every nonarchimedean local field in the target.
The apartment-axiom hypothesis is available but is not needed by this proof.

The proof chooses an integral downstairs cocharacter `ξ` generic for the
relative roots of `P.i`, using `IsSplitTorus.exists_genericCocharacter` inside
`L.exists_generic_levi_geometry`. With `K = UnramifiedClosure F`, the chosen
upstairs vector is
`descentCocharacterMap F K t.f hS ((1 : ℝ) ⊗ₜ[ℤ] ξ)`.
For an upstairs root, zero pairing with this vector is equivalent to trivial
restriction to the base change of the downstairs split torus. The geometry
helper proves this by `weightSpace_le_comp`, split character-lattice
base-change bijectivity, `mem_roots_baseChange_iff`, and the evaluation
identities for descent and pure tensors.

`L.centralizer_mem_pairingLeviSpan_descent_tmul` proves containment for every
integral downstairs cocharacter, hence for this choice. Naturality of scalar
extension and `CentralizerDatum.isRepresentedBy_baseChange` put every extended
downstairs centralizer point in the centralizer of the chosen upstairs
cocharacter. The internal lemma
`dynamicCentralizer_rationalPoints_le_of_zeroRootGroups` shows that this
centralizer lies in the pairing Levi. It uses `dynamicCentralizerReductive`
and `relativeRootGeneratedSubgroup_sup_centralizerPoints` on the canonical
represented cocharacter centralizer, together with root-group functoriality
and the zero pairing of its roots. The paired containment and root-generation
modules explain these transports.

For valuation constancy, `L.val_eq_of_restriction_zero` applies
`unramified_exists_descent_vadd_of_galoisFixed` to two points of the lift.
Their difference is a descended vector from `V(P.S)`. Each zero-pairing root
restricts trivially to `P.S`, so its evaluation on the difference vanishes.
`RootFunctionFamily.vadd_apply` then gives equality of the entire valuation
functions at the two points. The final theorem combines this constancy with
the centralizer containment for the same vector. No other comparison field
is assumed.

The source motivation is Kaletha and Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), the opening of §9.6 (printed p. 364, PDF p. 395), and §9.8.2
(printed pp. 375–376, PDF pp. 406–407). The registered 2024 corrections,
PDF p. 41, correct the projection domain in the proof of Lemma 9.8.1 to
`B(G)_M`. This proof works directly on the supplied fixed apartment and uses
no projection outside that domain. The formal proof is a derived combination
of the named Library results; it does not claim construction of the supplied
lift or a full unramified Moy–Prasad comparison.
