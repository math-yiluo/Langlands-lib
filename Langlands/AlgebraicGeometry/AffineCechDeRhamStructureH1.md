# From Čech–de Rham classes to Čech classes of functions

`structureH1` uses the function presheaf on the supplied affine cover and
forms the quotient of its degree-one Čech cocycles `structureCocycles` by
its Čech boundaries `structureBoundaries`, the range of the degree-zero
Čech differential. The projection `toStructureH1` forgets the one-form
component of a degree-one Čech–de Rham class. The first component of the
total differential is the Čech differential of the function component, so
`forgetFormsCocycle` lands in function cocycles. The function component of
a total boundary is the ordinary Čech boundary of the same degree-zero
cochain, so the map descends to `H1`; `toStructureH1_class` records its
value on the class of a cocycle.

`ker_toStructureH1` proves exactness at the middle of the degree-one Hodge
sequence: the kernel of `toStructureH1` is `hodgeF1`. If the function
component of a cocycle is a Čech boundary \(\partial h\), subtract the total
boundary \((\partial h,dh)\). The resulting representative has zero function
component, so its total cocycle conditions say that its one-forms agree on
overlaps and are closed; it is the image of that compatible closed form.
Conversely, the class of a compatible closed one-form has zero function
component.

## Source correspondence

Kai-Wen Lan, *Arithmetic compactifications of PEL-type Shimura varieties*,
revised 14 March 2021, §2.1.6, printed p. 135 (PDF p. 163), says that the
construction of \(H^1_{\mathrm{dR}}\) by the Čech total complex gives a
morphism \(H^1_{\mathrm{dR}}(X/S)\to H^1(X,\mathcal O_X)\) corresponding to
the summand \(C^{1,0}\) of \(C^1\); this is `toStructureH1`. Lan also obtains
it from the quotient \(\Omega^\bullet_{X/S}\to\mathcal O_X\) with kernel the
truncation \(\Omega^{\bullet\ge1}_{X/S}\), as the last map of the exact
sequence (2.1.6.5). The first hypercohomology of the truncation consists of
the closed global one-forms. Lan writes this term as
\(H^0(X,\Omega^1_{X/S})\) in (2.1.6.5); the two agree when every global
one-form is closed, as on an abelian scheme. In the Čech coordinates of the
supplied cover the closed global one-forms are `closedForms`. Thus `ker_toStructureH1` is the exactness of (2.1.6.5) at
\(H^1_{\mathrm{dR}}\) in those coordinates.
The retained source is `lan-2008-pel-thesis-revision-2021`, SHA-256
`a7a454f5d0735f4bf11f00a8afc14c361c5fc2cefd691d7466f7620ab4c3a079`.
