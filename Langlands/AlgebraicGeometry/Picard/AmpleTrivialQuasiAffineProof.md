# Quasi-affineness from an ample trivial line bundle

This module proves the Library proposition
`Langlands.AlgebraicGeometry.Picard.AmpleTrivialQuasiAffineStatement`: a scheme
`X` with a line bundle `L` such that `L.IsAmple` and
`L.obj ≅ SheafOfModules.unit X.ringCatSheaf` is quasi-affine in Mathlib's sense
`AlgebraicGeometry.Scheme.IsQuasiAffine X`. The theorem is
`Langlands.AlgebraicGeometry.Picard.ampleTrivialQuasiAffine`, at an arbitrary
universe `u` and with no further hypotheses.

The statement and all definitions come from the Library unchanged. The proof
uses only the published definitions and Mathlib; it does not formalize the
Proj argument of the literature source. The transport of trivialization opens
along isomorphisms comes from the shared module
`Langlands.AlgebraicGeometry.Picard.AmpleIsoProof`
(`Langlands.SchemeModule.trivializationOpen_mapIso`), which this module
imports rather than reproves.

## The trivialization open of a global function is its basic open

Here `structureModule X` is the structure sheaf as a module over itself, and a
global function `r : Γ(X, ⊤)` is a global section of it.

- `Langlands.SchemeModule.trivializesOn_structureModule_iff`: for every open
  `U`, `TrivializesOn (structureModule X) r U ↔ U ≤ X.basicOpen r`.

  Forward direction. If the restriction of `sectionHom (structureModule X) r`
  to `U` is an isomorphism, then its component on the image of the top open
  of `U` is bijective (`Scheme.Modules.Hom.isIso_iff_isIso_app`). Take a
  preimage `a` of `1`. By the published `structureMulHom_app` the component
  multiplies by the restriction of `r`, so `a` times that restriction is `1`
  and the restriction of `r` to `U` is a unit. Mathlib's
  `Scheme.basicOpen_of_isUnit`, `Scheme.basicOpen_res` and
  `Scheme.Opens.ι_image_top` then give `U ⊓ X.basicOpen r = U`, that is,
  `U ≤ X.basicOpen r`.

  Reverse direction. The published `unitEnd_restrict_isIso` (from
  `Langlands.AlgebraicGeometry.Modules.LineBundleFrameOpen`) reduces the
  claim to the coefficient `unitEndCoefficient` of the endomorphism on `U`
  being a unit. By `structureMulHom_app` this coefficient is the restriction
  of `r` to `U`. That restriction factors through `X.basicOpen r`, where `r`
  restricts to a unit (Mathlib's `isUnit_res_basicOpen`), and ring maps send
  units to units.

- `Langlands.SchemeModule.trivializationOpen_structureModule`:
  `trivializationOpen (structureModule X) r = X.basicOpen r`.

  Proof. The trivialization open is the supremum of the opens on which `r`
  trivializes. By the previous lemma each such open lies in `X.basicOpen r`,
  and `X.basicOpen r` itself is one of them. So the whole maximal open, not
  merely a neighborhood, equals the basic open.

## Tensor powers of the structure sheaf

- `Langlands.AlgebraicGeometry.Picard.tensorPowStructureSheafIso X n`:
  `tensorPow (structureSheaf X) n ≅ structureSheaf X`, by recursion on `n`.
  At `0` it is the identity. At `n + 1` it applies the tensor functor to the
  identity and the isomorphism for `n`, and then the published left unitor
  `tensorLeftUnitor (structureSheaf X)`.

## The main theorem

Given `X`, `L`, `hL : L.IsAmple` and `e : L.obj ≅ SheafOfModules.unit _`:

1. `hL.compactSpace` gives `CompactSpace X`.
2. For a point `x`, `hL.exists_section x` gives an exponent `n` and a section
   `s` of `tensorPow L.obj n` such that `x ∈ L.sectionOpen s` and
   `L.sectionOpen s` is affine.
3. Let `φ` be the published `Langlands.Scheme.Modules.tensorPowIso e n`
   followed by `tensorPowStructureSheafIso X n`. It is an actual isomorphism
   from `tensorPow L.obj n` to the structure module, so `φ.hom.app ⊤ s` is a
   global function on `X`.
4. `L.sectionOpen s` is by definition the trivialization open of `s`. By
   `trivializationOpen_mapIso` it equals the trivialization open of
   `φ.hom.app ⊤ s` in the structure module. By
   `trivializationOpen_structureModule` that is `X.basicOpen (φ.hom.app ⊤ s)`.
5. So `X.basicOpen (φ.hom.app ⊤ s)` is affine and contains `x`. Mathlib's
   `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`
   then gives `Scheme.IsQuasiAffine X`.
