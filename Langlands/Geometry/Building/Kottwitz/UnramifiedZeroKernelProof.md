# The unramified Kottwitz zero-kernel equality

`unramifiedZeroKernel` proves the existing
`Langlands.Geometry.Building.Kottwitz.UnramifiedZeroKernelStatement`
unconditionally, at arbitrary universe `u`. This is the unramified step in
Kaletha–Prasad, *Bruhat–Tits theory: a new approach* (2023), Proposition 11.5.4,
printed page 431 / PDF page 462 (registered source
`kaletha-prasad-2023-bruhat-tits-new-approach`).

For every nonarchimedean local field `F`, compatible field of definition `k`,
connected reductive `k`-group `G`, and existing unramified zero datum `E` for
the base change of `G` to `K = UnramifiedClosure F`, the theorem identifies
`E.zeroPoints` with the kernel of `reductiveKottwitz F k G hG`, pulled back
along the actual coefficient-point equivalence `baseChangeCoeffEquiv`.
It retains all the tower, separable-closure and normality hypotheses of the
published statement. It quantifies over every supplied datum and uses the
constructed Kottwitz map and the existing zero subgroup.

The proof applies the published
`unramifiedZeroKernel_of_torus_zExtension` from `ZeroKernelAssembly` to four
proved inputs:

- `torusKottwitzKernel` from `TorusKernelProof`, identifying the torus norm
  subgroup with the kernel of the constructed torus Kottwitz map;
- `simplyConnectedDerivedKottwitz_proof` from
  `SimplyConnectedDerivedKottwitzProof`, giving the cocenter specification
  of the map when the derived subgroup is simply connected;
- `reductiveKottwitzExistence_assembled` from `ZExtensionKernelProof`,
  providing z-extension existence and the selected reductive map's
  specification, including its simply connected derived compatibility;
- `zExtensionKottwitzKernelSurjectivity` from `ZExtensionKernelProof`,
  whose unramified conjunct maps the upstairs Kottwitz kernel onto the
  downstairs kernel.

The applied assembly chooses an actual z-extension with simply connected
derived source. Its cocenter reduction identifies the source zero subgroup
with its Kottwitz kernel. The central torus-kernel image theorem identifies
the image of that zero subgroup with the supplied target zero subgroup,
and the z-extension theorem identifies the image of its kernel with the
target Kottwitz kernel. Naturality of the coefficient-point equivalence
places both image equalities on the same point map. The present proof
supplies all four assumptions of that assembly from proved theorems.

The accompanying `zeroKernel_of_unramifiedZeroDescent` applies the published
`zeroKernel_of_unramified` with the proved
`reductiveKottwitzDescent_assembled` and `unramifiedZeroKernel`. Its sole
remaining premise is `UnramifiedZeroDescentStatement`, the assertion
including descent of the actual zero subgroups. Consequently this
corollary is conditional: it does not establish the unconditional rational
`ZeroKernelStatement`.

The implementation uses the published full z-extension kernel theorem, so
the assembly of `ZeroKernelAssembly` applies directly.
