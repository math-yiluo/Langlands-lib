# Opposite adjoint determinants on a dynamic Levi are inverse

Author: Worker 1415.

`Langlands.GroupScheme.Dynamic.LeviAdjointDeterminantReciprocityStatement`
is a proposition definition awaiting proof. It asserts that on the common
centralizer of a cocharacter and of its inverse, the determinant characters
of the adjoint actions on the two opposite dynamic unipotent Lie algebras
add to zero in the character group. It supplies no proof or additional
axiom.

## Scope and actual objects

- `k : Type u` is any field. No topology, completeness or characteristic
  restriction occurs.
- `G` is any group scheme over `Spec k` with `IsConnectedReductive G`.
- `T` is a commutative group scheme over `Spec k` and `i : T.toGrp ⟶ G`
  satisfies `IsMaximalSplitTorus i`.
- `ζ : cocharacterLattice T` is any cocharacter of `T`. It is not required to
  be generic or standard, and `ζ = 0` is allowed. Write
  `χ = CommGroupScheme.groupHom ζ ≫ i` and
  `χ' = CommGroupScheme.groupHom (-ζ) ≫ i` for the two cocharacters of `G`.
  The Library theorem `groupHom_neg_comp_eq_oppositeCocharacter` identifies
  `χ'` with `Dynamic.oppositeCocharacter χ`, the composite of `χ` with
  inversion `t ↦ t⁻¹` on `Gm`.
- `Z` with `iZ : Z ⟶ G` is any group scheme representing the subgroup
  functor `centralizer χ` (premise `hZ`). The same `iZ` is also required to
  represent `centralizer χ'` (premise `hZ'`). This premise is satisfiable for
  every representing model of `centralizer χ`. The Library theorem
  `Dynamic.centralizer_inverseCocharacter` states that a cocharacter and its
  inverse have equal centralizer subgroup functors. Using one common model
  makes both determinant characters live in the same group
  `rationalCharacters Z`.
- `U` with `iU` represents `unipotent χ` (premise `hU`), and `V` with `iV`
  represents `unipotent χ'` (premise `hV`). These are the dynamic contraction
  subgroups `U_G(χ)` and `U_G(-χ)`.
- The instance premises `[IsAffine Z.X.left]`, `[IsAffineHom U.X.hom]` and
  `[IsAffineHom V.X.hom]` are the hypotheses under which the Library forms
  determinant characters of actions on Lie algebras.
- `c : Lie.FiniteCoordinates U d` and `c' : Lie.FiniteCoordinates V e` are any
  finite coordinates of the Lie modules. Such a structure is a family of
  `A`-linear isomorphisms `Lie(U)(A) ≃ A^d`, one for each `k`-algebra `A`,
  natural in `A`. Here `Lie(U)(A)` is the kernel of
  `U(A[ε]) → U(A)`.

For actual connected reductive `G` all of these premises can be met. The
models `Dynamic.Affine.centralizerHom`, `Dynamic.Affine.unipotentHom`, and
`Dynamic.Affine.parabolicHom` represent the corresponding subgroup functors.
The proved `dynamicAdjointDeterminantStructure` supplies the affineness
instances and the existence of finite coordinates for represented dynamic
subgroups of connected reductive groups over a field. The proposition is
therefore not vacuous.

## Conclusion

`(centralizerAdjointAction hZ hU).determinantCharacter c` is the determinant
of the Library's actual action of `Z` on `U`, `m • u = m u m⁻¹` computed
after the inclusions into `G`, differentiated on `Lie(U)` and read in the
coordinates `c`. It is an element of the additive group
`rationalCharacters Z`. The second term is the same construction for `V`
with coordinates `c'`, and it uses the same model `Z`. The conclusion is

`det(Ad | Lie U(χ)) + det(Ad | Lie U(χ')) = 0` in `rationalCharacters Z`.

Addition of rational characters is pointwise multiplication of their values
in `Gm`. Equivalently, for every point `m` of `Z`,
`det(Ad m | Lie U(χ)) · det(Ad m | Lie U(χ⁻¹)) = 1`. The statement makes no
claim about the analytic Haar scaling factors of rational points. The
Library's `adjointDeterminantModelIndependence` shows that both characters
are independent of the chosen models and coordinates up to the canonical
isomorphisms.

## Original sources and provenance

Provenance: derived.

Conrad, Gabber and Prasad, *Pseudo-reductive groups*, second edition, source
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
Printed p. 50 (PDF p. 76) writes `-λ` for the reciprocal homomorphism
`t ↦ λ(1/t) = λ(t)⁻¹`. Lemma 2.1.5 there defines
`Z_G(λ) = P_G(λ) ∩ P_G(-λ)`, which is symmetric in `λ` and `-λ`.
Proposition 2.1.8(1), printed p. 53 (PDF p. 79), states for an affine
`k`-group `G` of finite presentation:

"We have Lie(Z_G(λ)) = g_0, Lie(U_G(±λ)) = g_±, and Lie(P_G(λ)) = g_0 ⊕ g_+
inside g."

Here `g_n` is the weight-`n` space of `GL_1` acting on `g = Lie(G)` through
`λ`, and `g_± = ⊕_{±n>0} g_n`. Thus `Lie U(χ)` and `Lie U(χ')` are the
positive and negative weight parts of `Lie(G)` under `χ`. The centralizer
`Z(χ)` acts on each part through the adjoint action.

The asserted identity is derived as follows; neither source states it in
this form. Over an algebraic closure, `Z(χ)` is connected reductive and
contains a maximal torus `S` through which `χ` factors. On `S` the weights
of `Lie U(χ)` are the roots `α` with `⟨α, χ⟩ > 0`, and the weights of
`Lie U(χ')` are the roots `α` with `⟨α, χ⟩ < 0`. Root spaces are lines and the
root system is stable under negation, so the two determinant restrictions to
`S` are negatives of each other. The restriction of characters of a
connected reductive group to a maximal torus is injective, which gives the
identity on `Z(χ)`. This sketch only explains why the statement is true. The
proof of this proposition is a separate task and may take another route.

The identity is the algebraic counterpart of Renard's reciprocity between
opposite radicals. That source is David Renard, *Représentations des
groupes réductifs p-adiques*, 2026 version, source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Section V.5.4, printed pp. 126–127 (PDF pp. 132–133), has the Lemme

"pour tout m ∈ M, δ_{P\G}(m) = δ_G(m)/δ_P(m) = δ_P(m)⁻¹ = δ_N(m)⁻¹ =
δ_N̄(m)".

On the split component `A`, its proof computes
`δ_P(a) = ∏_{γ ∈ Σ(P)} |γ(a)^{-(m_γ + 2m_{2γ})}|_F` and notes
`δ_P(a) = δ_N(a) = δ_N̄(a)⁻¹`. In this product, `m_γ` and `m_{2γ}`
are Renard's multiplicities of the roots `γ` and `2γ`. The proof of the
preceding Proposition computes the opposite radical, which is generated by
the root subgroups `U_{-γ}`, with the same multiplicities and the inverse
exponents. Renard's identity concerns absolute values of rational points
over a local field.
The present statement is the corresponding equality of algebraic characters
over any field.

## Restriction to cocharacters of a maximal split torus

The identity holds for every cocharacter of `G`. The statement only
quantifies over cocharacters of the form `ζ` followed by a maximal split
torus `i`. This is the case needed for standard Levi subgroups, where the
inducing cocharacter is a standard cocharacter of `T`. The restriction also
lets a proof work over `k` with the torus `T`, which lies in `Z(χ)`, and with
its relative roots and their multiplicities. The common-model premise `hZ'`
records that `Z(χ) = Z(χ')`, so it does not restrict generality.

## Intended use

Over a nonarchimedean local field, the separate proposition
`Langlands.Aubert.General.RationalPointFamily.DynamicUnipotentHaarDeterminantStatement`
identifies the Haar scaling factor of conjugation on `U(χ)(k)` with the
normalized absolute value of the adjoint determinant. Together with that
proposition, this statement is intended as an input to a proof of
`Langlands.Aubert.General.RationalPointFamily.RationalOppositeHaarReciprocityStatement`.
That derivation is not part of this statement.
