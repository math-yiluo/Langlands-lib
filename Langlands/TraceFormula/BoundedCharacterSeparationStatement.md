# Separation of bounded algebra characters in absolutely convergent sums

`Langlands.TraceFormula.BoundedCharacterSeparationStatement` is a proposition
definition with independent universe parameters `u`, `v`, and `w`.

## Notation

- `ι : Type u` indexes the coefficients `c : ι → ℂ`, and `W : Type v` indexes the
  places. Each `H x` in the family `H : W → Type w` is a complex algebra with
  `Semiring (H x)` and `Algebra ℂ (H x)` instances.
- `χ : ι → (x : W) → (H x →ₐ[ℂ] ℂ)` assigns to each index and place a complex
  algebra homomorphism. In particular, `χ i x 1 = 1`.
- `Summable` and `HasSum` use Mathlib's unconditional sums over finite subsets
  of the index type. For complex families, `Summable c` is equivalent to
  `Summable (fun i => ‖c i‖)` by `summable_norm_iff` in finite real dimension.
- `starRingEnd ℂ` is complex conjugation.

## Statement

For every choice of the data above, assume the following.

1. The coefficients satisfy `Summable c`.
2. For each `x : W` and `h : H x` there is a real `C` such that
   `‖χ i x h‖ ≤ C` for all `i : ι`.
3. For each `x : W` and `h : H x` there is an `h' : H x` such that
   `χ i x h' = starRingEnd ℂ (χ i x h)` for all `i : ι`.
4. For every `T : Finset W` and every family `h : (x : W) → H x`, the
   weighted product sum satisfies
   `HasSum (fun i => c i * ∏ x ∈ T, χ i x (h x)) 0`.

Both `C` and `h'` are chosen for the given `x` and `h` and work simultaneously
for all `i`. Taking `T = ∅` in the fourth hypothesis gives `HasSum c 0`.

For every `i₀ : ι`, the sum over the fibre of its character family satisfies
`HasSum (fun i : {i : ι // ∀ x, χ i x = χ i₀ x} => c i) 0`. The subtype
tests equality of algebra homomorphisms at every place. When the character
families are distinct, each fibre is a singleton and each coefficient vanishes.

## Trace formula application and provenance

This is derived content formulated for the comparison of absolutely convergent
spectral sums in local cyclic base change. The model for the separation step is
Henniart–Lemaire, II.6.10, printed pp. 125–126 (PDF pp. 133–134), from (2) to (3).

Fix the local tests at the places in `S`. Take `W` to be the places outside `S`,
`H v` to be the spherical Hecke algebra `H_{E_v,χ_v}` in the source's notation,
and `ι` to be the disjoint union of the contributing spectral indices. For the
twisted terms the character is `h ↦ tr(Π_v(h))` and the coefficient is
`d ∏_{v∈S} tr(Π_v(φ_v) ∘ A_{Π_v})`. For the untwisted terms the character is
`h ↦ tr(π_v(b_v(h)))` and the coefficient is `−∏_{v∈S} tr(π_v(f_v))`. The
local traces outside `S` are the scalars on the spherical lines. Choosing the
Hecke units outside a finite `T ⊆ W` makes (2) the fourth hypothesis. The fibre
conclusion gives equality of the two sums for a fixed system of eigencharacters
outside `S`. The single twisted representation in (3) uses strong multiplicity
one, as recalled in Henniart–Lemaire, IV.3.3, printed p. 174 (PDF p. 182).

For a spherical line in a unitary representation, the operator norm bound gives
`|χ(h)| ≤ ‖h‖₁`, and the convolution involution `h*(g) = conj (h(g⁻¹))` gives
the conjugate character value. For a character pulled back along `b_v`, the norm
bound uses `‖b_v(h)‖₁` and the involution calculation uses compatibility of `b_v`
with the convolution involutions. The application takes absolute summability of
the fixed coefficients and the two character conditions as inputs.

Arthur–Clozel use finiteness at fixed level and infinitesimal character to reduce
their identity (4.7) to finitely many terms, then use the linear-independence
argument of Lemma 4.10 for their permitted Hecke tests. In (6.2) they refer back
to §4 to separate by components at infinity and Hecke eigenvalues. See Chapter 1,
§4, printed pp. 44–46 (PDF pp. 58–60), especially p. 45, and §6, printed p. 55
(PDF p. 69). The proposition here accommodates the infinite spectral families
from the Hilbert-sum model.

An involution-closed algebra of tests also appears in the definition of an
ample subalgebra before Jacquet–Langlands, Lemma 16.1.1, printed p. 260
of the retypeset edition (PDF p. 264).

## Proof sketch

1. The absolute summability of `c` and the uniform bounds on the finitely many
   factors ensure absolute convergence for every product test.
2. Fix `i₀` and a finite set `T`. In the product of the closed discs of radii
   `C(x, h)` over `x ∈ T` and `h : H x`, let `p i` be the point with coordinates
   `χ i x h`. The closure `Y` of these points is compact Hausdorff. The coordinate
   identities for multiplication, the unit and conjugation through `h'` hold
   on `Y` because they are closed conditions.
3. The functions `F_h(y) = ∏_{x∈T} y_x(h x)` have a complex linear span that is
   a unital subalgebra closed under conjugation. Using the unit at all but one
   place gives every coordinate function, so the span separates points. Complex
   Stone–Weierstrass makes the span uniformly dense in `C(Y, ℂ)`. The functional
   `F ↦ ∑ i, c i * F (p i)` is continuous in the uniform norm with bound
   `∑ i, ‖c i‖`. Hypothesis 4 makes it zero on the span and hence on all of
   `C(Y, ℂ)`.
4. Given `ε > 0`, choose a finite set of indices outside which the sum of
   `‖c i‖` is below `ε`. By Urysohn's lemma there is a continuous `[0, 1]`-valued
   function that equals `1` at `p i₀` and `0` at the other points represented
   by these finitely many indices. Its values agree with the indicator of
   `p i = p i₀` on the chosen indices. The fibre sum therefore has norm below
   `ε`, since the functional vanishes on this function and the error is bounded
   by the tail. Thus the sum over the fibre at the places in `T` is zero.
5. For the full fibre, again choose a finite set of indices with absolute tail
   below `ε`. For each chosen index outside the full fibre, put a place where
   its character differs from that of `i₀` into `T`. The fibre at the places
   in `T` now agrees with the full fibre on the chosen indices. The full fibre
   sum differs from the zero sum for `T` by norm below `ε`, which proves the
   conclusion.

## Sources

- Guy Henniart and Bertrand Lemaire, *Changement de base et induction automorphe
  pour GL(n) en caractéristique non nulle*, Mémoires de la SMF 124 (2011),
  II.6.10, printed pp. 125–126, and IV.3.3, printed p. 174.
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced
  Theory of the Trace Formula*, Annals of Mathematics Studies 120 (1989),
  Chapter 1, §4, printed pp. 44–46, and §6, (6.2), printed p. 55.
- Hervé Jacquet and Robert P. Langlands, *Automorphic Forms on GL(2)*,
  Lecture Notes in Mathematics 114 (1970), §16, preceding Lemma 16.1.1,
  printed p. 260 in the retypeset edition.
