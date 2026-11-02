# Real character and cocharacter spaces

Author: Worker 185.

For a field `k : Type u` and an actual commutative group scheme `T` over `Spec k`, the namespace `Langlands.GroupScheme.RealTorusSpace` defines `V T = ℝ ⊗[ℤ] cocharacterLattice T` and `Vstar T = ℝ ⊗[ℤ] characterLattice T`. These are the existing categorical Hom lattices, with Mathlib's tensor-product real module structures. No finite-rank, splitness or characteristic hypothesis is imposed. In particular, for a general commutative group scheme the name `Vstar` does not assert that it is the full dual of `V`.

The real bilinear map `pair T : Vstar T →ₗ[ℝ] V T →ₗ[ℝ] ℝ` extends the existing `latticePairing T` in both variables. Its constructor identity is

`pair T (r ⊗ χ) (s ⊗ ν) = r * s * (latticePairing T χ ν : ℝ)`.

The helper `extend` is the real-linear universal tensor lift of `r, x ↦ r • f x`; `extendHom` packages its additivity and integer linearity in `f`. First the integer-valued pairing is composed with the integer-to-real linear map, then extended in the cocharacter variable, then in the character variable. Thus the two input lattices remain distinct throughout. `pair_tmul_tmul` computes the resulting lift and associates the product.

The map `eval T χ : V T →ₗ[ℝ] ℝ` is the real extension of the integer pairing against `χ`. The identities `eval_tmul` and `eval_eq_pair` compute it on pure tensors and identify it with pairing against `1 ⊗ χ`. For an actual homomorphism `i : T.toGrp ⟶ G` with `G` affine over the field, `rootEval T i α` applies this construction to the underlying character of `α : relativeRoots i`. The identity `rootEval_apply` is definitional. The construction does not assume that these functionals separate points for general `T`.

This is an internal scalar-extension construction implementing the notation of Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (Cambridge, 2023), Chapter 6 introduction and §6.1.6–8, book PDF pages 226–234 (printed pages 195–203). The source is registered as `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. The authors' corrections of 1 November 2024, registered as `kaletha-prasad-2024-corrections`, SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`, PDF page 32, replace the negative signs in the proof of Lemma 6.1.12(1) by positive signs. No root-datum valuation or statement of that lemma is constructed here.

The book distinguishes the cocharacter vector space from its affine apartment, and distinguishes the derived/adjoint direction of the reduced building from the central direction of the enlarged building. This module supplies prospective translation spaces and functionals, with no choice of an apartment origin. It constructs no apartment, equipollence class, root-group valuation, affine Weyl group, Iwahori–Weyl group or building. There is no valued-field or Henselian hypothesis and this unit closes no building bundle or release gate.
