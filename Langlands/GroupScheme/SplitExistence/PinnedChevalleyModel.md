# A Chevalley model of the actual based root datum of a split pinning

For a supplied pinning `p : SplitPinning G` over a field, the split torus gives
a finite free character lattice and the pinning gives a finite reduced root
datum on its actual character and cocharacter lattices.
`SplitPinning.chevalleyLieData` and `SplitPinning.chevalleyGroup` choose integral
Chevalley Lie data and a represented Chevalley group over the field from
`nonempty_chevalleyLieData` and `ChevalleyData.nonempty_chevGroup`. The construction
uses the supplied base.

`SplitPinning.chevalleyPinning` equips any fixed model on those data with its
standard torus and the base pushed forward by `chevDatumEquiv`. The root pairs
remain reduced because the character identification preserves linear
independence. The simple-root trivializations compose `LocalSplitCell.gaLieEquiv`
with `RelativeRoot.representedRootLieEquiv` for the raw Chevalley root maps.
The first equivalence sends one to `VectorGroup.standardEpsilon`. The second
identifies the differential with the actual root weight space using the absence
of higher roots. Evaluating the trivialization at one thus gives the
differential at the standard epsilon vector.

`SplitPinning.chevalleyIso` applies `pinnedIsomorphism` to the inverse of
`chevDatumEquiv`. Inverse character pullback and forward cocharacter pushforward
carry the model lattices to the supplied lattices. The comparison uses the
identity on root indices. Its commuting torus square carries the actual
coroot into the model group to the actual coroot into the supplied group,
hence commutes with coroot evaluation on every test scheme.

## Sources

- Brian Conrad, *Reductive group schemes* (2014), Definition 6.1.1, p. 186,
  and Theorems 6.1.16(2) and 6.1.17, pp. 196–197.
  `conrad-2014-reductive-group-schemes`, SHA-256
  `1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
  The field construction uses the pinning by simple Lie vectors and the lifting
  of the based root datum isomorphism.
- Robert Steinberg, *Lectures on Chevalley Groups* (2016), Chapter 3, p. 19
  and Lemma 19(c), p. 22 (PDF pp. 32 and 35),
  `steinberg-2016-lectures-chevalley-groups`, SHA-256
  `e3f9ab93111dd88ff3d944a951f4d39b7e08539f6a9b57f22fba0d9bbc19eb89`.
  The additive coordinate is the divided-power root parameter of Chapter 3.
  Its first-order coefficient gives the Lie vector. The weight evaluation of
  Lemma 19(c) explains the coroot coordinate used with root parameter identities.
