# Actual affine root systems under central-isogeny pullback

This is a derived comparison for the actual `KPApartmentData.centralIsogenyPullback`
constructed in `CentralIsogenyApartment`. It supplies the AS2–AS4 components
for the source apartment whenever the corresponding components hold for the
target apartment. The proof uses the actual affine-root equivalences in
`CentralIsogenyAffineRoots` and all seven generic root-system transport laws
in `AffineRootSystemTransport`; it introduces no separate literature assertion.

The field `k : Type u` has arbitrary universe `u`. The source and target groups
are affine and locally of finite type. The data retained throughout are split
tori `S` and `T`, monomorphic acting embeddings `i` and `j`, a central isogeny
`q`, a torus isogeny `t`, and the commuting square
`i ≫ q = groupHom t ≫ j`. These data are supplied, with no assertion that they
exist for every group. The scalar function `ω : kˣ → ℝ` is arbitrary.

The existing affine apartment equivalence sends actual target valuation points
to their normalized source pullbacks. Inverse precomposition by this equivalence
is the existing linear equivalence of affine functional spaces. The new theorem
`transportedExtendedRoots_centralIsogenyPullback` identifies the image of the
target extended root set with the source extended root set. Its proof uses
surjectivity of functional transport and the exact extended-root membership
comparison. The corresponding ordinary-root image equality is imported from
`CentralIsogenyAffineRoots`.

The theorem `derivativeTransport_range_rootForm_centralIsogenyPullback`
identifies the image of the target root-form range under the dual equivalence
with the actual source root-form range. On each relative root this is exactly
the root-form identity for `centralIsogenyTranslationEquiv`. Surjectivity of the
actual relative-root pullback equivalence proves the reverse set inclusion.
Thus the derivative identification retains the original reduced translation
spaces and root forms.

The definitions `centralIsogenyExtendedAffineRootSystem` and
`centralIsogenyAffineRootSystem` construct elements of the subtype of actual
source root sets satisfying `IsAffineRootSystemWithRankZero`. Their underlying
sets are, respectively, the source apartment's existing extended and ordinary
affine roots. The input for each definition is the corresponding target
root-system proof. The property is proved by generic seven-field transport
and the exact image equality, so these objects provide the root-system clauses
of AS2 and AS3.

The two `derivativeRoots_*_centralIsogenyPullback` theorems transfer the
remaining derivative equalities of AS2 and AS3. They rewrite derivative roots
as the dual image of the target derivative set, substitute the target equality,
and apply the root-form-range comparison above.

Finally, `mem_or_two_smul_mem_centralIsogenyPullback` transfers AS4. Pull an
arbitrary source extended root back to a target functional, use the target
extended-root comparison, and apply the target disjunction. Ordinary-root
membership transports in either case; real linearity identifies the transported
doubled functional with twice the transported functional.

The candidate supplies precisely these root-system and root-set components.
It neither assumes nor constructs source AS5, full-centralizer V6, V7, derived
cover tori, or the final simply connected normalizer-image theorem.
