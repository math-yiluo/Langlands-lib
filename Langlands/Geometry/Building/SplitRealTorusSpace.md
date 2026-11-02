# Split-torus real coordinates

Author: Worker 185.

Let `k : Type u` be an arbitrary field and `I : Type u` an arbitrary finite type. For the actual commutative split torus `𝕋 = splitTorus.commGroupScheme (Spec k) I`, the namespace `Langlands.GroupScheme.RealTorusSpace` defines real linear equivalences

`splitCocharacterCoordinates k I : V 𝕋 ≃ₗ[ℝ] (I → ℝ)`

and

`splitCharacterCoordinates k I : Vstar 𝕋 ≃ₗ[ℝ] (I → ℝ)`.

Each construction takes the existing `splitTorus.cocharacterLatticeEquiv` or `splitTorus.characterLatticeEquiv`, converts its additive equivalence to an integer-linear equivalence, applies `LinearEquiv.baseChange`, and composes with `TensorProduct.piScalarRight ℤ ℝ ℝ I`. The construction requires only `Finite I`, choosing a finite enumeration internally. On pure tensors the coordinates are

`splitCocharacterCoordinates k I (r ⊗ ν) j = r * (splitTorus.cocharacterLatticeEquiv k I ν j : ℝ)`

and the corresponding formula for characters. The pure-tensor identities compute scalar extension and the finite-product tensor equivalence; integer scalar multiplication on the real numbers is rewritten as multiplication.

With a `Fintype I` instance to write the finite sum, `pair_eq_sum` gives

`pair 𝕋 x v = ∑ j, splitCharacterCoordinates k I x j * splitCocharacterCoordinates k I v j`.

The proof uses tensor induction in both variables. On pure tensors it applies the Library's `splitTorus.latticePairing_eq_sum`, casts the integer sum and products to the reals, distributes the scalar product through the sum, and reassociates each summand. Additivity proves the induction steps.

The type `I` may be empty. The two coordinate equivalences still have the actual codomain `I → ℝ`; its subsingleton property and injectivity show every element of each tensor space equals zero (`eq_zero_of_isEmpty_cocharacter` and `eq_zero_of_isEmpty_character`). The coordinate values themselves equal the zero function (`splitCocharacterCoordinates_eq_zero_of_isEmpty` and `splitCharacterCoordinates_eq_zero_of_isEmpty`). The identity `pair_eq_zero_of_isEmpty` specializes the finite dot product to the empty sum. No nonempty index or positive-rank assumption is used, and no restriction on the characteristic of `k` is imposed.

This is an internal scalar-extension construction implementing the vector-space notation of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023), Chapter 6 introduction and §6.1.6–8, PDF pages 226–234 (printed 195–203), registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The authors' corrections of 1 November 2024, registered as `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF page 32, correct the signs in the proof of Lemma 6.1.12(1). This coordinate construction makes no assertion about that lemma's affine translations or valuations.

The spaces remain prospective translation spaces. There is no choice of an apartment origin, valued-field or Henselian hypothesis, apartment, equipollence class, root-group valuation, affine Weyl group, Iwahori–Weyl group or building construction. The separate derived/adjoint and central directions of reduced and enlarged buildings are outside this unit, which closes no bundle or release gate.
