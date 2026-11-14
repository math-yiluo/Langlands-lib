# Geometric fibre cohomology dimensions of proper flat families

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.GeometricFibreSectionsDim` (namespace
`Langlands.AlgebraicGeometry.Modules.GeometricFibreSectionsDim`) is an internal helper for the proof
of `ProjectiveRelativeDivisorFibreHilbertStatement`. It proves two theorems.

Common setting: `B` is a noetherian ring, `g : Y ⟶ Spec B` is proper and flat, `F` is an
invertible module on `Y` (FLT `Scheme.Modules.IsInvertible`), and `sk : B →+* k` is a ring map
to a field `k`. The point `t` is the image in `Spec B` of the closed point of `Spec k`. The
geometric fibre `Y_k` is Mathlib's chosen pullback of `g` along `Spec k ⟶ Spec B`.

- `finrank_relativeCohomology_geomFibre g F hF k sk p`: for every `p`,
  `dim_k Hᵖ(Y_k, F_k) = fibreCohomologyDim g t F p`. That is, it equals
  `dim_{κ(t)} Hᵖ(Y_t, F_t)` on the fibre over `t` (as an integer equality). Here `Hᵖ(Y_k, F_k)`
  is the `k`-module `relativeCohomology` of `pullback.snd g (Spec.map sk)`, applied to the pullback
  of `F` along `pullback.fst`.
- `geomFibreH0Finrank_eq g F hF k sk`: the case `p = 0`, in the form of the FLT dimension
  `Scheme.Modules.geomFibreH0Finrank g F k sk`.

## Proof

The argument is the one in the proof of `ProperFibreCohomologyDimBaseChangeStatement`, based on
D. Mumford, *Abelian Varieties*, Chapter II, §5, Corollary 5, pp.53–54 (literature id
`mumford-abelian-varieties-chapter-ii-scan`).

1. `FibreSemicontinuity.exists_perfectModel`, from the proof module of
   `ProperFlatFibreCohomologySemicontinuityStatement`, is applied to the fibre
   `Y_t ⟶ Spec κ(t)`, which is proper and flat over the noetherian field `κ(t)`. It gives a
   strictly perfect complex `K` of `κ(t)`-modules. For every ring map `φ : κ(t) ⟶ S`, the
   complex `K ⊗_φ S` represents the derived sections of the pullback of `F_t` to the chosen
   pullback along `Spec φ`.
2. With `φ = 𝟙`, as in the proof of `ProperFibreCohomologyDimBaseChangeStatement`,
   `dim_{κ(t)} Hᵖ(Y_t, F_t) = homologyDim K p (ker 𝟙)`.
3. Let `φ = descResidueField (stalkClosedPointTo (Spec.map sk)) : κ(t) ⟶ k`. Mathlib's
   `Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField` gives
   `Spec φ ≫ (Spec κ(t) ⟶ Spec B) = Spec.map sk`. Pasting the chosen pullback along `Spec φ`
   with the fibre square gives a cartesian square of `g` along `Spec.map sk`. The Library's
   `nonempty_relativeCohomology_iso_chosenPullback`, with `Scheme.Modules.pullbackComp` and
   `DerivedPlus.homologyIsoOfIsoDerivedComplex`, then identifies `Hᵖ(Y_k, F_k)` with
   `Hᵖ(K ⊗_φ k)`. By `finrank_homology_baseChange_eq` its dimension is
   `homologyDim K p (ker φ)`.
4. Ring maps out of a field are injective, so both kernels are zero and the dimensions agree.
5. For `geomFibreH0Finrank_eq`, `relativeCohomologyZeroIso` identifies `H⁰` with
   `relativeGlobalSections`. The `k`-module structure of `geomFibreH0Finrank` is given by
   `(ΓSpecIso k).inv ≫ (pullback.snd …).appLE ⊤ ⊤ le_top`, and this equals
   `structureRingHom (pullback.snd …)` (`Scheme.Hom.app_eq_appLE`). The two finranks therefore
   coincide.

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
