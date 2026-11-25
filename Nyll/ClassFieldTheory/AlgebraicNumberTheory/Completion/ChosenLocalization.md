# Local-field structure on the chosen completion at a finite place

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.ChosenLocalization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite Galois extension, with K a number field, and let w₀ be a finite place of K. The library fixes one extension `chosenFinitePlaceExtension w₀` of the w₀-adic absolute value to L, and a localized completion of L at it, `ChosenFinitePlaceLocalizedCompletion w₀`, defined in imported files. This file makes the localized completion and the completion of K at w₀ nonarchimedean local fields through global instances. It also defines what it means for the completed extension to be unramified.

## Definitions

- `ChosenFinitePlaceBaseCompletion w₀`: the completion of K at the absolute value `adicAbv K w₀`. This is the absolute-value model, not Mathlib's `adicCompletion`.
- `ChosenFinitePlaceIsUnramified w₀`: the proposition that the localized completion is unramified over the base completion, in the sense of the library's `IsNonarchimedeanLocalField.IsUnramifiedValuedExtension`.

## Instances

- On the base completion: an `ℝ≥0`-valued valuation and a valuative relation, a nontrivially normed field structure, local compactness, the ultrametric property, a nontrivial compatible valuation, the valuative topology, and finally `IsNonarchimedeanLocalField`.
- On the completion of L at the chosen extension: an algebra over K and over the base completion, finite dimension over the base completion, continuity of scalar multiplication, and local compactness.
- On the localized completion: a valuation extending that of the base, finite dimension over the base, the Galois property over the base, local compactness, the ultrametric property, nontriviality, and `IsNonarchimedeanLocalField`.
- On the valuation rings: the ring of the localized completion is the integral closure of that of the base, and it is a finite module over it.

## Proofs

Finite dimension comes from `completionModuleFinite` and `localizedCompletionModuleFinite`. Local compactness of the completion of L follows from finite dimension over a complete locally compact field. The localized completion is isometric to the completion of L, so it is locally compact as well. The Galois property is `HilbertRamification.algebraicLocalization_isGalois`, and finiteness of the integers uses the separability that follows from it.

## Points to watch

- The instances that involve L depend on the chosen extension of w₀ to L, that is, on a choice of place of L above w₀. Those on the base completion alone depend only on K and w₀.
- `ChosenFinitePlaceIsUnramified` is only a definition. The file does not prove it for any place. The module comment says that users of these instances supply unramifiedness as a hypothesis.
- The notion of unramified used is the library's own, stated for valued local fields. It is not Mathlib's `Algebra.IsUnramified`.
- L is only assumed to be a field, finite and Galois over K. It is not required to be a number field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Completion/ChosenLocalization.lean`: the Lean file is the source byte for byte (SHA-256 `395796725be619f43b5a88449f9c9fade5a28d2d5ca80b96ed859dc771a041d0`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
