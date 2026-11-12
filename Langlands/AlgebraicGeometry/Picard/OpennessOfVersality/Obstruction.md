# The obstruction cochains of a family of transition functions

Module `Langlands.AlgebraicGeometry.Picard.OpennessOfVersality.Obstruction`, namespace
`Langlands.AlgebraicGeometry.Picard.OpennessOfVersality`. Author: Worker 5103 (task
`14dfbe95-4d4a-46fd-933a-182df994126c`, openness of versality for actual Picard
families). Everything is proved in the file, with no hypotheses beyond those in the
signatures.

The notation is that of `OpennessOfVersality.CechData`: `f : X ⟶ Spec R`, an `R`-algebra
`P`, an ordered affine cover `K` of `relSpace f P`, a `P`-algebra `A₀`, the base-changed
Čech complex `cplx f K A₀` with differential `dif`, the pulled-back covers `testCover f K A`,
the section maps `secMap`, and the comparison maps `compMap`. `Thick A F` is the
commutative trivial square-zero extension of `Langlands.Algebra.ThickSquareZero`.

The module builds the data `(θ, z, δ)` of the Library's
`Langlands.Cohomology.ModuleComplex.ObstructionCone.OpenStatement` for this complex and
proves its two hypotheses `d θ = δ_* z` and `d z = 0` (`dif_thetaObs`, `dif_zObs`).

## Setting of the main results

- `π = algebraMap P A₀` is surjective (`hπ`). `Q` is an `A₀`-module with a compatible
  `P`-module structure. `jQ : Q →ₗ[P] P` has image exactly `ker π`
  (`hjQ : ∀ a, a ∈ ker π ↔ ∃ q, jQ q = a`) and square-zero products
  (`hsq : jQ q * jQ q' = 0`). For `dif_zObs` it is also injective. In the application
  `P = P'/J²`, `A₀ = P'/J` and `Q` is the ideal `J/J²`.
- `F` is an `A₀`-module with compatible `P`- and `R`-module structures, and
  `D : Derivation R P F`.
- `g : ∀ i j : K.ι, Γ(relSpace f P, K.U i ⊓ K.U j)ˣ` is a family of units on all pairwise
  intersections. Hypothesis `hg`: for every `s : K.Idx 2`, `defect f K g s` lies in the
  extension `Ideal.map (structureHom f P (K.inter s)) (ker π)`. In the application `g`
  lifts the transition functions of a line bundle on `relSpace f A₀`, so the cocycle
  identity holds modulo `ker π`.

## Section maps along algebra maps (`Along`)

- `surjective_relMap`: for a surjective `t : A →ₐ[R] A'` whose kernel lies in the
  nilradical, `relMap f t` is surjective on points. Proof: Mathlib's
  `range_comap_of_surjective` and `zeroLocus_eq_univ_iff` give surjectivity of
  `Spec.map t`. Surjectivity is stable under base change, and `relMap f t` is a base
  change of `Spec.map t` (`isPullback_relMap`).
- `secMapAlong f K s hs σ`: for an `R`-algebra map `s : P →ₐ[R] A` with the same preimages of
  opens as the structure map (`hs`), the ring map
  `Γ(relSpace f P, K.inter σ) ⟶ Γ(relSpace f A, (testCover f K A).inter σ)` given by
  `(relMap f s).appLE`. For the structure map it is `secMap` (`secMapAlong_toAlgHom`).
  Lemmas: `secMapAlong_congr`, `structureHom_comp_secMapAlong`, `secMapAlong_res` (it
  commutes with restrictions).
- `testMapAlong f K h hpre σ`: the analogous map
  `Γ(relSpace f A, (testCover f K A).inter σ) ⟶ Γ(relSpace f A', (testCover f K A').inter σ)`
  for an `R`-algebra map `h : A →ₐ[R] A'` of `P`-algebras such that
  `h ∘ (P → A)` and `P → A'` have the same preimages of opens (`hpre`;
  `testCover_inter_eq_of_comp`). Lemmas: `secMapAlong_comp_testMapAlong`,
  `structureHom_comp_testMapAlong`.
- `secMapAlong_sub_mem`: if `t : A →ₐ[R] A''` is surjective and `t ∘ s = t ∘ s'`, then
  `secMapAlong s x - secMapAlong s' x` lies in the extension of `ker t` to the sections
  over `(testCover f K A).inter σ`. This uses the Library's `ker_appLE_eq_map`, Mathlib's
  `Scheme.Hom.appLE_comp_appLE`, and the Library's `relMap_comp`. It needs `f` separated,
  so that the intersections are affine.
- `mul_eq_zero_of_mem_map`: an element `c` with `c * k = 0` for all `k ∈ I` kills the
  extension of `I` (span induction).
- `compMap_natural_of_mul_eq_zero`: naturality of `compMap` along an `R`-algebra map
  `h : A →ₐ[R] A'` that is only compatible with the `P`-structures modulo `ker t`, for a
  surjective `t : A' →ₐ[R] A''` with `t ∘ h ∘ (P → A) = t ∘ (P → A')`. It assumes that the
  coefficients `j' : M' →ₗ[P] A'` kill `ker t` (`hj' : t a = 0 → j' m' * a = 0`) and
  that `φ : M →ₗ[A₀] M'` satisfies `j' (φ m) = h (j m)`. Conclusion:
  `testMapAlong h (compMap j y σ) = compMap j' (φ.lTensor _ y) σ`. Proof: on
  `(a ⊗ x) ⊗ m` both sides are products of a structure-map value with section maps of
  `x σ`. These section maps differ by an element of the extension of `ker t`
  (`secMapAlong_sub_mem`), which `j'` kills.

## Pairwise data and the Čech differential (`Pairs`, `Cores`)

For a scheme `Y` with an ordered affine cover `K'`:

- `pr K' u σ a b`: the restriction of `u (σ a) (σ b) ∈ Γ(Y, K'.U (σ a) ⊓ K'.U (σ b))` to
  `K'.inter σ`. `res_pr`: restricting `pr K' u σ a b` along `K'.inter τ ≤ K'.inter σ` gives
  `pr K' u τ a' b'` when `σ a = τ a'` and `σ b = τ b'`. `uval K' g`, `uinv K' g`: the
  values and inverses of a family of units. `pr_val_mul_pr_inv`: their restrictions
  multiply to `1`. `map_map_apply` and `map_pair_congr` are helper lemmas.
- `d_one_apply`, `d_two_apply`: the FLT differential `(unit π).d K'` in degrees one and
  two, written out: `(d c) s = c|face 0 - c|face 1 + c|face 2` and
  `c|face 0 - c|face 1 + c|face 2 - c|face 3`.
- `mul_eq_zero_of_mem_map_sq`: products in the extension of an ideal with `I * I = 0`
  vanish (Mathlib's `Ideal.map_mul`).
- `dz_core`, `dtheta_core`: two identities in commutative rings, proved with
  `linear_combination`. `dz_core`: with `x₀₂ y₀₂ = 1`, `x₁₃ y₁₃ = 1` and the products
  `(w₁₂₃ - 1)(w₀₁₃ - 1) = 0`, `(w₀₂₃ - 1)(w₀₁₂ - 1) = 0` of the quantities
  `w_{abc} = x_{ab} x_{bc} y_{ac}`, the alternating sum
  `(w₁₂₃ - 1) - (w₀₂₃ - 1) + (w₀₁₃ - 1) - (w₀₁₂ - 1)` vanishes. `dtheta_core`: if
  `A_{ab} I_{ab} = 1`, `B₀₂ J₀₂ = 1`, `A₀₁ A₁₂ I₀₂ = 1`, and the differences
  `B_{ab} - A_{ab}` have pairwise vanishing products, then
  `(B₁₂ I₁₂ - 1) - (B₀₂ I₀₂ - 1) + (B₀₁ I₀₁ - 1) = B₀₁ B₁₂ J₀₂ - 1`.

## The cochains (`Defs`)

- `structureHom_map`, `res_mem_map`, `secMap_mem_map`: the structure maps commute with
  restriction and section maps. So extensions of ideals of `P` are preserved, with
  `secMap` sending the extension of `I` into that of `Ideal.map (P → A) I`.
- `defect f K g s = g₀₁ g₁₂ g₀₂⁻¹ - 1 ∈ Γ(relSpace f P, K.inter s)` for `s : K.Idx 2`,
  where `g_{ab} = pr K (uval/uinv K g) s a b`.
- `zObs f K jQ hjQ g hg : cplx f K A₀ 2 ⊗[A₀] Q`. Its comparison image is the defect:
  `compMap f K jQ 2 (zObs …) = fun s => secMap s (defect f K g s)` (`compMap_zObs`).
  Existence is `exists_compMap_eq_iff` of `CechData` with the ideal `ker π`, by `hg` and
  `secMap_mem_map`. `zObs` is the witness chosen by `Classical.choose`.
- `preimage_ofDerivation`: the maps `Θ = Thick.ofDerivation D` and the structure map
  `P → Thick P F` have the same preimages, by the Library's `preimage_relMap_eq` for
  `t = fst` and `surjective_relMap`.
- `thetaCochain f K D g σ = Θ_* g_σ · (g_σ⁻¹ pushed by the structure map) - 1` on
  `relSpace f (Thick P F)`, for `σ : K.Idx 1` and `g_σ = pr K (uval K g) σ 0 1`.
  `thetaCochain_mem`: it lies in the extension of `ker fst`, by `secMapAlong_sub_mem`.
- `thetaObs f K D g : cplx f K A₀ 1 ⊗[A₀] F` with
  `compMap f K Thick.inr 1 (thetaObs …) = thetaCochain f K D g` (`compMap_thetaObs`), by
  `exists_compMap_eq_iff` with the ideal `ker fst` and `Thick.mem_ker_fstHom_iff`.
- `deltaMap hπ jQ hjQ0 D : Q →ₗ[A₀] F`, `q ↦ D (jQ q)` (`deltaMap_apply`). Its
  `A₀`-linearity uses a lift `p` of the scalar and the Leibniz rule. The extra term
  `jQ q • D p` vanishes because `jQ q ∈ ker π` (`hjQ0_of`).

## `d z = 0` (`Cocycle`)

- `res_defect_face`: the restriction of `defect (K.face t j)` to `K.inter t` is
  `g_{ab} g_{bc} g_{ac}⁻¹ - 1` for the vertices `a < b < c` of the face.
- `ker_mul_eq_zero`: `ker π` is square-zero (from `hjQ`, `hsq`).
- `defect_alt_sum`: the alternating sum of the four restricted defects on a quadruple
  intersection vanishes. The restricted defects lie in the square-zero extension of `ker π`
  (`res_mem_map`, `mul_eq_zero_of_mem_map_sq`), and `dz_core` applies.
- `dif_zObs` (for `f` flat and `jQ` injective):
  `(dif f K A₀ 2).rTensor Q (zObs …) = 0`. Proof: `compMap_injective` reduces to the
  comparison images, and `compMap_dif` turns the left side into the FLT differential of
  the defect cochain. `d_two_apply` and `secMap_res` reduce it to `secMap` of
  `defect_alt_sum`, which is zero.

## `d θ = δ_* z` (`Faces`, `Theta`)

- `res_secMapAlong_face`, `res_secMap_face`: restricting a section-map value of
  `pr K u (face t j) a b` to `t` gives the section-map value of `pr K u t a' b'`.
- `thickRed : Thick P F →ₐ[R] Thick A₀ F`, `(p, f) ↦ (π p, f)`, and
  `thetaRed A₀ D = thickRed ∘ Θ : P →ₐ[R] Thick A₀ F`, `p ↦ (π p, D p)`. Lemmas:
  `fst_thickRed`, `snd_thickRed`, `thickRed_comp` (`thickRed` respects the structure maps),
  `fst_comp_thetaRed`, `surjective_relMap_fst`, `preimage_thickRed`, `preimage_thetaRed`,
  `preimage_thetaRed_comp`, and `inr_mul_eq_zero` (`inr` kills `ker fst`).
- `compMap_thetaObs_red`, `compMap_thetaObs_red_apply`: the comparison image of `thetaObs` in
  `Thick A₀ F` is `σ ↦ Θ'_* g_σ · (g_σ⁻¹ pushed by the structure map) - 1`. This is
  `compMap_natural_of_mul_eq_zero` along `thickRed` with `φ = id`.
- `compMap_deltaZ`: the comparison image of `δ_* z` in `Thick A₀ F` is
  `secMapAlong (thetaRed A₀ D) s (defect s)`. This is `compMap_natural_of_mul_eq_zero`
  along `thetaRed` from the test algebra `P`, with `φ = deltaMap`, since
  `thetaRed (jQ q) = (0, D (jQ q)) = inr (δ q)`.
- `secMap_defect_red`: the defect is `0` after the structure map to `Thick A₀ F`, which kills
  `ker π`. So the pushed `g` is a cocycle there.
- `thetaRed_sub_mem`, `ker_fst_mul`: the two pushforwards of a section differ by an
  element of the square-zero extension of `ker fst`.
- `dif_thetaObs_apply`: pointwise identity of the comparison images. It combines
  `compMap_dif`, `d_one_apply`, `res_secMapAlong_face`, `res_secMap_face`, and `dtheta_core`
  applied to `A_{ab}` = structure pushforward of `g_{ab}`, `B_{ab}` = `Θ'`-pushforward.
- `dif_thetaObs` (for `f` flat):
  `(dif f K A₀ 1).rTensor F (thetaObs …) = (deltaMap …).lTensor _ (zObs …)`, by
  `compMap_injective` for `Thick.inr`.

## Provenance

Internal construction for the proof of the Library statement
`Langlands.AlgebraicGeometry.Picard.PicardOpennessOfVersalityStatement`. It describes, in
Čech terms, the obstruction to deforming a line bundle along a square-zero thickening
(`z`) and the Kodaira–Spencer-type cochain of a derivation (`θ`). These are standard
deformation-theoretic constructions, implemented here directly. No literature statement
is formalized.
