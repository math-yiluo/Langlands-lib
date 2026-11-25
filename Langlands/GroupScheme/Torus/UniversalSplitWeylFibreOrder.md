# Universal local-base orders for split Weyl quotients

This internal supporting construction composes the actual point-quotient transport, fibre-order comparison, fibrewise maximality transport and arbitrary-base reductivity results. All schemes, ring types, field types and coordinate types lie in the same arbitrary universe. No new structural theorem from the literature is assumed.

For a coordinate torus map `i : splitTorus S I ⟶ G`, an arbitrary base morphism `b : S' ⟶ S` and any test scheme over `S'`, `splitTorus.pointWeylGroupBaseChangedEquiv` compares the actual point Weyl quotient of the canonical coordinate pullback map with the original point quotient on the composed test scheme. The canonical coordinate map is the inverse split-torus base-change isomorphism followed by the pullback of `i`. The equivalence first removes this source isomorphism and then uses the point-quotient base-change equivalence. It needs no closedness, smoothness, reductivity, maximality or field hypothesis.

Now suppose that `G` is reductive, the coordinate torus map is closed and fibrewise maximal, and `n : N ⟶ G` represents its actual all-test normalizer. Let `q : N ⟶ W` be scheme-surjective, with both `N` and `W` locally of finite type over `S`, and suppose its kernel on every test scheme is the inverse image of the actual torus centralizer under `n`.

For every commutative local ring `R` and every morphism `b : Spec R ⟶ S`, `natCard_quotientFibre_eq_localSplitWeylOrder_of_baseChange` counts the actual lifts of each composite `Spec k ⟶ Spec R ⟶ S` into the original total scheme of `W`. Here `k` is any algebraically closed field equipped with its given `R`-algebra structure. This natural cardinality is the common Weyl order of the coordinate pullback over `R`.

The proof uses `weylQuotientFibrePointEquiv` on the composite field-valued base map. It then applies the inverse of the first equivalence to pass to the point quotient of the coordinate local pullback. Arbitrary-base reductivity and fibrewise maximality transport supply the hypotheses of `natCard_pointWeylGroup_eq_localSplitWeylOrder`; closedness follows by base change and composition with the canonical source isomorphism. The imported local theorem gives the common order, defined using the closed residue-field fibre of this local pullback. Thus the proof counts lifts into the original quotient directly.

`exists_natCard_quotientFibre_constant_on_local_base` packages this formula with quantifier order `∀ R, ∀ b, ∃ d, ∀ k`. The number depends on the local ring and its base map, and is independent of the field and its supplied algebra structure. This is the universal local-base condition required for a subsequent separated étale finiteness argument.

The quotient, its normalizer and kernel properties, local finite type, and surjectivity remain inputs. This module constructs no quotient and asserts no finiteness, separatedness, quasi-compactness or étaleness.
