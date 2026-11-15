# The inductive step over a non-nilpotent prime

Module `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocusStep`,
namespace `Langlands.AlgebraicGeometry.UnramifiedFunctor.EtaleLocus`. This is a
supporting module of the proof of `ClosedOfGenericStatement`. It imports
`EtaleLocusCaseA`.

## `van_succ`

Let `R'` be noetherian, `I` an ideal of `R'`, `Lvs n` levels for
`R' → R'/I^{n+1}`, and `w` a point with `I ⊆ P_w`. Let `c` be such that
`𝔍 ∩ I^m ⊆ I𝔍` for all `m ≥ c + 1` (an Artin–Rees constant). Then for
`n ≥ c`, `VanN n w` implies `VanN (n+1) w`.

This step replaces the formal-scheme argument of Murre's case (a) (printed
p.251). It works with the stalks `Λ_n` of the representing schemes `X_n` at
the points given by `ξ` and compares consecutive levels only through
elements of `F`. No compatibility between the schemes `X_n` and `X_{n+1}` is
used.

Proof. Write:

- `d`, `d'` for the data at levels `n` and `n+1`;
- `Λ'` for the stalk at level `n+1`, with `θ' : R'/I^{n+2} → Λ'` and
  `ψ' : Λ' → O_w/(𝔍 + I^{n+2})O_w`.

1. Extension to `O_w`. For `s ∉ P_w`, `θ'(s)` is a unit, since its image under
   the local map `ψ'` is. So `R' → Λ'` extends to `θt : O_w → Λ'`, with
   `ψ' ∘ θt` the quotient map (`ringHom_ext_Ow`).
2. `θ'(𝔍) ⊆ J'`, where `J' = θ'(I^{n+1})Λ'`. `J'` lies in the maximal ideal,
   since `ψ'` is local and `I ⊆ P_w`. So `Ā = Λ'/J'` is local, and `R' → Ā`
   factors through `δb : R'/I^{n+1} → Ā`. The point `Spec Ā → Spec Λ' → X_{n+1}`
   gives an element `z` over `Spec Ā`. At level `n`, `z` corresponds to
   `h : Spec Ā ⟶ X_n` over `Spec δb`. Let `π : Ā → L_n` be induced by `ψ'`
   and `O_w/(𝔍 + I^{n+2}) → O_w/(𝔍 + I^{n+1})`; it is surjective, hence
   local. The restriction of `z` along `Spec π` is the element `ζ` of level
   `n` (`map_ζ` at level `n+1`, `elemEquiv_congr`). By `left_of_map_eq` and
   `pt_eq_of`, `h` sends the closed point to the point of level `n`. By
   `exists_stalkHom`, `δb = χ ∘ θ_n` for a local `χ`. `VanN n w` gives
   `δb(𝔍) = 0`, that is, `θ'(𝔍) ⊆ J'`.
3. `θt` is surjective. By `ker_ψ_le` at level `n+1`,
   `ker ψ' ⊆ θ'(𝔍)Λ' ⊆ J'`. Since `ψ' ∘ θt` is surjective, `Λ' = θt(O_w) + J'`.
   Also `J' = θt(I^{n+1}O_w)Λ'` and `J'^2 = 0`, because
   `I^{2n+2} ⊆ I^{n+2}`. Apply `surjective_of_isNilpotent_map`.
4. Let `Q = ker θt`. Then:
   - `I^{n+2}O_w ⊆ Q`;
   - `Q ⊆ 𝔍O_w + I^{n+2}O_w`, as `ψ' ∘ θt` is the quotient map;
   - `𝔍O_w ⊆ Q + I^{n+1}O_w`, from step 2 and surjectivity
     (`Ideal.mem_map_iff_of_surjective`).
5. Artin–Rees, localized. `𝔍O_w ∩ I^{n+1}O_w = (𝔍 ∩ I^{n+1})O_w`
   (`IsLocalization.map_inf`), and this is contained in `(I𝔍)O_w` since
   `n + 1 ≥ c + 1`.
6. `𝔍O_w ⊆ Q + (IO_w)(𝔍O_w)`. Write `x ∈ 𝔍O_w` as `q + a` with `q ∈ Q` and
   `a ∈ I^{n+1}O_w`, and `q = j' + b` with `j' ∈ 𝔍O_w` and
   `b ∈ I^{n+2}O_w ⊆ Q`. Then `a + b = x − j'` lies in
   `𝔍O_w ∩ I^{n+1}O_w ⊆ I𝔍O_w`, and `x = (q − b) + (a + b)`.
7. Nakayama. `IO_w` is in the maximal ideal, and `𝔍O_w` is finitely generated.
   So `𝔍O_w ⊆ Q` (`Submodule.le_of_le_smul_of_le_jacobson_bot`). Hence
   `θ'(𝔍) = θt(𝔍O_w) = 0`, which is `VanN (n+1) w`.
