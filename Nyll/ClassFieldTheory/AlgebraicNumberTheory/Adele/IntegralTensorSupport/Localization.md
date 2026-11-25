# Localizing the relative integral lattice

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite extension of number fields. Take the lattice in 𝓞 L spanned over 𝓞 K by the integrally scaled basis of L/K, constructed in the lattice file. This file localizes it at a finite place w of K. If w lies outside the finite bad set `integralTensorBadPlaces`, the scaled basis vectors span the localization of 𝓞 L over the local ring of K at w.

## Definitions

- `RelativeBaseIntegerLocalization w`: the local ring (𝓞 K)_w, the localization at the prime w.
- `RelativeExtensionIntegerLocalization w`: the localization of 𝓞 L at the image of the complement of w.
- `relativeIntegerLocalizationLinearMap w`: the localization map from 𝓞 L, as an 𝓞 K-linear map.
- `localizedScaledRelativeIntegerLattice w`: the (𝓞 K)_w-span of the images of the scaled basis vectors.

## Results

- `exists_notMem_smul_mem_scaledRelativeIntegerLattice`: for w outside the bad set and x ∈ 𝓞 L, some d ∈ 𝓞 K with d ∉ w has d·x in the global lattice. The chosen annihilator of the lattice quotient serves as d.
- `relativeIntegerLocalizationLinearMap_mem_localizedLattice`: the global lattice maps into the localized span, for every w.
- `algebraMap_mem_localizedScaledRelativeIntegerLattice_of_notMem`: outside the bad set, the image of every element of 𝓞 L lies in the localized span.
- `localizedScaledRelativeIntegerLattice_eq_top_of_notMem`: outside the bad set, the localized span is the whole localization of 𝓞 L.

## Proofs

The annihilator a kills 𝓞 L modulo the lattice. It does not lie in w, so it becomes a unit in (𝓞 K)_w, and dividing by it puts each element of 𝓞 L in the localized span. Since 𝓞 L generates its localization over (𝓞 K)_w, the span is everything.

## Points to watch

- The module comment speaks of a comparison with the integral closure and of coordinatewise integrality. The file itself proves only the spanning statements above.
- Only spanning is shown. The file does not state that the scaled vectors form a basis of the localization.
- The bad set depends on the choices made in the lattice file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Adele/IntegralTensorSupport/Localization.lean`: the Lean file is the source byte for byte (SHA-256 `caac5063a32ccede03a37dbba753eb104bc3b550de72fc1f65c18df2c05219b9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
